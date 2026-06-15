//! ML-based transaction categorization.
//!
//! Trains a Multinomial Naive Bayes classifier on existing ledger transactions
//! to predict the expense/income account for new transactions based on their
//! payee and narration text.
//!
//! Uses TF-IDF vectorization plus a small, self-contained Multinomial
//! Naive Bayes classifier (see [`MultinomialNB`]) implemented in pure
//! `std` — no external ML or linear-algebra crates. Earlier versions
//! delegated to `linfa-bayes` and then `ferrolearn-bayes`, but both
//! dragged heavy, occasionally wasm-incompatible dependencies in for an
//! algorithm that is ~80 lines of textbook arithmetic.
//!
//! # Example
//!
//! ```rust,ignore
//! let model = CategorizationModel::train(&existing_directives)?;
//! let predictions = model.predict("WHOLE FOODS", Some("groceries"));
//! // → [("Expenses:Groceries", 0.92), ("Expenses:Dining", 0.05), ...]
//! ```

use rustledger_plugin_types::{DirectiveData, DirectiveWrapper};
use std::collections::HashMap;

/// A trained categorization model.
///
/// Wraps a Multinomial Naive Bayes classifier trained on TF-IDF features
/// extracted from transaction payee/narration text.
pub struct CategorizationModel {
    /// The trained classifier.
    model: MultinomialNB,
    /// Vocabulary: word → column index in the feature matrix.
    vocabulary: HashMap<String, usize>,
    /// IDF weights for each word in the vocabulary.
    idf: Vec<f64>,
    /// Label map: index → account name.
    labels: Vec<String>,
}

/// Error type for ML operations.
///
/// Training is the only fallible step, and it fails only when there's too
/// little data to build a useful model — fitting itself is infallible.
///
/// Marked `#[non_exhaustive]` so future failure modes can be added without
/// breaking downstream matches.
#[derive(Debug)]
#[non_exhaustive]
pub enum MlError {
    /// Not enough training data (too few transactions or categories).
    InsufficientData(String),
}

impl std::fmt::Display for MlError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self::InsufficientData(msg) = self;
        write!(f, "insufficient training data: {msg}")
    }
}

impl std::error::Error for MlError {}

impl CategorizationModel {
    /// Train a model from existing ledger directives.
    ///
    /// Extracts (text, account) pairs from transactions where the second
    /// posting's account is the categorization target. Requires at least
    /// 2 distinct categories with at least 1 transaction each.
    ///
    /// # Errors
    ///
    /// Returns `MlError::InsufficientData` if there aren't enough transactions
    /// or distinct categories to train a useful model.
    pub fn train(directives: &[DirectiveWrapper]) -> Result<Self, MlError> {
        // Extract training data: (text, account) pairs
        let mut samples: Vec<(String, String)> = Vec::new();

        for d in directives {
            if let DirectiveData::Transaction(txn) = &d.data {
                // Skip transactions with fewer than 2 postings
                if txn.postings.len() < 2 {
                    continue;
                }

                // The target account is the second posting (contra-account)
                let account = &txn.postings[1].account;

                // Build text from payee + narration
                let mut text = String::new();
                if let Some(ref payee) = txn.payee {
                    text.push_str(payee);
                    text.push(' ');
                }
                text.push_str(&txn.narration);

                if !text.trim().is_empty() {
                    samples.push((text.to_lowercase(), account.clone()));
                }
            }
        }

        if samples.len() < 2 {
            return Err(MlError::InsufficientData(format!(
                "need at least 2 transactions, got {}",
                samples.len()
            )));
        }

        // Build label map
        let mut label_set: Vec<String> = samples.iter().map(|(_, a)| a.clone()).collect();
        label_set.sort();
        label_set.dedup();

        if label_set.len() < 2 {
            return Err(MlError::InsufficientData(
                "need at least 2 distinct categories".to_string(),
            ));
        }

        let label_to_idx: HashMap<&str, usize> = label_set
            .iter()
            .enumerate()
            .map(|(i, s)| (s.as_str(), i))
            .collect();

        // Build vocabulary from all tokens
        let mut vocab: HashMap<String, usize> = HashMap::new();
        let tokenized: Vec<Vec<String>> = samples.iter().map(|(text, _)| tokenize(text)).collect();

        for tokens in &tokenized {
            for token in tokens {
                let len = vocab.len();
                vocab.entry(token.clone()).or_insert(len);
            }
        }

        if vocab.is_empty() {
            return Err(MlError::InsufficientData(
                "no tokens found in training data".to_string(),
            ));
        }

        // Compute IDF weights
        let n_docs = samples.len() as f64;
        let mut doc_freq = vec![0u32; vocab.len()];
        for tokens in &tokenized {
            let mut seen = std::collections::HashSet::new();
            for token in tokens {
                if let Some(&idx) = vocab.get(token)
                    && seen.insert(idx)
                {
                    doc_freq[idx] += 1;
                }
            }
        }
        let idf: Vec<f64> = doc_freq
            .iter()
            .map(|&df| (n_docs / (1.0 + f64::from(df))).ln() + 1.0)
            .collect();

        // Build sparse TF-IDF rows — only the non-zero `(vocab index,
        // weight)` entries, sorted by index for deterministic summation.
        // TF-IDF vectors are mostly zero, so a dense matrix would cost
        // O(n_samples × vocab); sparse rows cost O(total tokens).
        let n_features = vocab.len();
        let mut features: Vec<Vec<(usize, f64)>> = Vec::with_capacity(samples.len());
        let mut targets: Vec<usize> = Vec::with_capacity(samples.len());

        for (tokens, (_, account)) in tokenized.iter().zip(samples.iter()) {
            features.push(tfidf_row(tokens, &vocab, &idf));
            targets.push(label_to_idx[account.as_str()]);
        }

        // Train the classifier. Laplace smoothing (alpha = 1.0) matches
        // the linfa-bayes / ferrolearn defaults this replaced.
        let model = MultinomialNB::fit(&features, &targets, label_set.len(), n_features);

        Ok(Self {
            model,
            vocabulary: vocab,
            idf,
            labels: label_set,
        })
    }

    /// Predict the account for a transaction.
    ///
    /// Returns predictions sorted by confidence (highest first). Each
    /// prediction is an `(account, probability)` pair. The probabilities
    /// are the class-conditional posteriors from
    /// [`MultinomialNB::predict_proba`] (they sum to 1.0 across all
    /// classes), so callers can treat them as honest scores.
    #[must_use]
    pub fn predict(&self, narration: &str, payee: Option<&str>) -> Vec<(String, f64)> {
        let mut text = String::new();
        if let Some(p) = payee {
            text.push_str(p);
            text.push(' ');
        }
        text.push_str(narration);

        let features = self.vectorize(&text.to_lowercase());

        // Pair each class posterior with its label, then sort descending;
        // callers take the top-k. Softmax posteriors are all > 0, so
        // every known category is returned.
        let mut results: Vec<(String, f64)> = self
            .labels
            .iter()
            .cloned()
            .zip(self.model.predict_proba(&features))
            .collect();

        results.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        results
    }

    /// Vectorize text into a sparse TF-IDF feature vector (the non-zero
    /// `(vocab index, weight)` entries).
    fn vectorize(&self, text: &str) -> Vec<(usize, f64)> {
        tfidf_row(&tokenize(text), &self.vocabulary, &self.idf)
    }

    /// Number of distinct categories the model was trained on.
    #[must_use]
    pub const fn num_categories(&self) -> usize {
        self.labels.len()
    }

    /// Number of features (vocabulary size).
    #[must_use]
    pub fn vocab_size(&self) -> usize {
        self.vocabulary.len()
    }
}

/// A Multinomial Naive Bayes classifier with Laplace (add-α) smoothing.
///
/// This is the standard multinomial NB used for text classification —
/// equivalent to scikit-learn's `MultinomialNB` with `alpha = 1.0`, and
/// to the `linfa-bayes` / `ferrolearn-bayes` implementations this
/// replaced. Samples are passed as **sparse** `(feature index, value)`
/// rows; values are treated as fractional counts, so TF-IDF weights are
/// valid inputs directly.
///
/// `fit` computes, per class `c`: a log prior `ln(n_c / n)` and smoothed
/// feature log-probabilities `ln((Σᵢ xᵢⱼ + α) / (Σⱼ Σᵢ xᵢⱼ + α·n_features))`.
/// `predict_proba` forms the joint log-likelihood
/// `log_prior[c] + Σⱼ xⱼ · feature_log_prob[c][j]` per class and
/// normalizes it with a numerically-stable softmax (log-sum-exp).
struct MultinomialNB {
    /// `ln P(class)` for each class — indexed `[class]`.
    class_log_prior: Vec<f64>,
    /// `ln P(feature | class)` — indexed `[class][feature]`.
    feature_log_prob: Vec<Vec<f64>>,
}

impl MultinomialNB {
    /// Laplace / additive smoothing parameter (the sklearn / linfa /
    /// ferrolearn default).
    const ALPHA: f64 = 1.0;

    /// Fit on sparse feature rows and their class-index targets.
    ///
    /// `features[i]` is sample `i` as `(feature index, value)` pairs and
    /// `targets[i]` is its class. Preconditions, all guaranteed by the
    /// caller (which builds both from the same sample set):
    /// `features.len() == targets.len()`; every feature index is
    /// `< n_features`; every class index is `< n_classes`; and every
    /// class occurs at least once, so no class prior is `-inf`.
    fn fit(
        features: &[Vec<(usize, f64)>],
        targets: &[usize],
        n_classes: usize,
        n_features: usize,
    ) -> Self {
        debug_assert_eq!(
            features.len(),
            targets.len(),
            "features and targets must be parallel"
        );
        let n_samples = features.len() as f64;

        // Per-class sample counts and summed feature weights.
        let mut class_count = vec![0.0_f64; n_classes];
        let mut feature_count = vec![vec![0.0_f64; n_features]; n_classes];
        for (row, &class) in features.iter().zip(targets) {
            class_count[class] += 1.0;
            let counts = &mut feature_count[class];
            for &(j, value) in row {
                counts[j] += value;
            }
        }

        let class_log_prior = class_count.iter().map(|&n| (n / n_samples).ln()).collect();

        let feature_log_prob = feature_count
            .iter()
            .map(|counts| {
                let denom: f64 = Self::ALPHA.mul_add(n_features as f64, counts.iter().sum::<f64>());
                counts
                    .iter()
                    .map(|&count| ((count + Self::ALPHA) / denom).ln())
                    .collect()
            })
            .collect();

        Self {
            class_log_prior,
            feature_log_prob,
        }
    }

    /// Posterior class probabilities for one sparse sample, summing to 1.0.
    ///
    /// `x` is the sample as `(feature index, value)` pairs. The returned
    /// vector is indexed by class, in the order the model was trained with.
    fn predict_proba(&self, x: &[(usize, f64)]) -> Vec<f64> {
        // Joint log-likelihood per class.
        let jll: Vec<f64> = self
            .class_log_prior
            .iter()
            .zip(&self.feature_log_prob)
            .map(|(&prior, log_prob)| prior + x.iter().map(|&(j, v)| v * log_prob[j]).sum::<f64>())
            .collect();

        // Stable softmax: subtract the max before exponentiating.
        let max = jll.iter().copied().fold(f64::NEG_INFINITY, f64::max);
        let exps: Vec<f64> = jll.iter().map(|&v| (v - max).exp()).collect();
        let total: f64 = exps.iter().sum();
        exps.iter().map(|&e| e / total).collect()
    }
}

/// Tokenize text into lowercase words, filtering out short tokens.
fn tokenize(text: &str) -> Vec<String> {
    text.split(|c: char| !c.is_alphanumeric())
        .filter(|s| s.len() >= 2)
        .map(str::to_lowercase)
        .collect()
}

/// Build a sparse TF-IDF row: the non-zero `(vocab index, weight)` entries
/// for `tokens`, sorted by index. Tokens absent from `vocab` are ignored.
/// Sorting makes the row order (and thus the downstream summation)
/// deterministic, independent of `HashMap` iteration order.
fn tfidf_row(tokens: &[String], vocab: &HashMap<String, usize>, idf: &[f64]) -> Vec<(usize, f64)> {
    let mut tf: HashMap<usize, u32> = HashMap::new();
    for token in tokens {
        if let Some(&idx) = vocab.get(token) {
            *tf.entry(idx).or_insert(0) += 1;
        }
    }
    let mut row: Vec<(usize, f64)> = tf
        .into_iter()
        .map(|(idx, count)| (idx, f64::from(count) * idf[idx]))
        .collect();
    row.sort_unstable_by_key(|&(idx, _)| idx);
    row
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustledger_plugin_types::{AmountData, PostingData, TransactionData};

    fn make_txn(
        payee: Option<&str>,
        narration: &str,
        from_account: &str,
        to_account: &str,
    ) -> DirectiveWrapper {
        DirectiveWrapper {
            directive_type: "transaction".to_string(),
            date: "2024-01-15".to_string(),
            filename: None,
            lineno: None,
            data: DirectiveData::Transaction(TransactionData {
                flag: "*".to_string(),
                payee: payee.map(String::from),
                narration: narration.to_string(),
                tags: vec![],
                links: vec![],
                metadata: vec![],
                postings: vec![
                    PostingData {
                        account: from_account.to_string(),
                        units: Some(AmountData {
                            number: "-50.00".to_string(),
                            currency: "USD".to_string(),
                        }),
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                    PostingData {
                        account: to_account.to_string(),
                        units: None,
                        cost: None,
                        price: None,
                        flag: None,
                        metadata: vec![],
                        span: None,
                    },
                ],
            }),
        }
    }

    fn training_data() -> Vec<DirectiveWrapper> {
        vec![
            make_txn(
                Some("Whole Foods"),
                "Groceries",
                "Assets:Bank",
                "Expenses:Groceries",
            ),
            make_txn(
                Some("Trader Joe's"),
                "Weekly groceries",
                "Assets:Bank",
                "Expenses:Groceries",
            ),
            make_txn(
                Some("Safeway"),
                "Food shopping",
                "Assets:Bank",
                "Expenses:Groceries",
            ),
            make_txn(
                Some("Kroger"),
                "Groceries",
                "Assets:Bank",
                "Expenses:Groceries",
            ),
            make_txn(
                Some("Starbucks"),
                "Coffee",
                "Assets:Bank",
                "Expenses:Dining",
            ),
            make_txn(
                Some("McDonald's"),
                "Lunch",
                "Assets:Bank",
                "Expenses:Dining",
            ),
            make_txn(Some("Chipotle"), "Dinner", "Assets:Bank", "Expenses:Dining"),
            make_txn(
                Some("Panera"),
                "Coffee and sandwich",
                "Assets:Bank",
                "Expenses:Dining",
            ),
            make_txn(Some("Shell"), "Gas", "Assets:Bank", "Expenses:Transport"),
            make_txn(Some("Chevron"), "Fuel", "Assets:Bank", "Expenses:Transport"),
            make_txn(
                Some("Uber"),
                "Ride to airport",
                "Assets:Bank",
                "Expenses:Transport",
            ),
        ]
    }

    #[test]
    fn train_and_predict() {
        let data = training_data();
        let model = CategorizationModel::train(&data).unwrap();

        assert_eq!(model.num_categories(), 3);
        assert!(model.vocab_size() > 5);

        let predictions = model.predict("Weekly food shopping at the store", None);
        assert!(!predictions.is_empty());
        // Should predict Groceries (most similar to training data)
        assert_eq!(predictions[0].0, "Expenses:Groceries");
    }

    #[test]
    fn predict_dining() {
        let data = training_data();
        let model = CategorizationModel::train(&data).unwrap();

        let predictions = model.predict("Coffee", Some("Starbucks"));
        assert!(!predictions.is_empty());
        assert_eq!(predictions[0].0, "Expenses:Dining");
    }

    #[test]
    fn predict_transport() {
        let data = training_data();
        let model = CategorizationModel::train(&data).unwrap();

        let predictions = model.predict("Fuel for car", Some("Shell"));
        assert!(!predictions.is_empty());
        assert_eq!(predictions[0].0, "Expenses:Transport");
    }

    #[test]
    fn insufficient_data() {
        let data = vec![make_txn(
            Some("Store"),
            "Stuff",
            "Assets:Bank",
            "Expenses:Misc",
        )];
        let result = CategorizationModel::train(&data);
        assert!(result.is_err());
    }

    #[test]
    fn insufficient_categories() {
        let data = vec![
            make_txn(Some("Store"), "Stuff", "Assets:Bank", "Expenses:Misc"),
            make_txn(Some("Shop"), "Things", "Assets:Bank", "Expenses:Misc"),
        ];
        let result = CategorizationModel::train(&data);
        assert!(result.is_err());
    }

    #[test]
    fn tokenize_basic() {
        let tokens = tokenize("WHOLE FOODS MARKET #1234");
        assert!(tokens.contains(&"whole".to_string()));
        assert!(tokens.contains(&"foods".to_string()));
        assert!(tokens.contains(&"market".to_string()));
        assert!(tokens.contains(&"1234".to_string()));
    }

    #[test]
    fn naive_bayes_known_values() {
        // Two classes, two features: class 0 sees feature 0, class 1 sees
        // feature 1. With Laplace alpha = 1.0 and equal priors:
        //   feature_log_prob[0] = ln([3/4, 1/4]),  [1] = ln([1/4, 3/4])
        //   class_log_prior      = ln([1/2, 1/2])
        // For x = [1, 0]: jll = ln(3/8) vs ln(1/8) → softmax = [0.75, 0.25].
        // Sparse rows: class 0's sample is feature 0 = 2.0, class 1's is
        // feature 1 = 2.0; two features total.
        let nb = MultinomialNB::fit(&[vec![(0, 2.0)], vec![(1, 2.0)]], &[0, 1], 2, 2);

        let p = nb.predict_proba(&[(0, 1.0)]);
        assert!((p[0] - 0.75).abs() < 1e-9, "p[0] = {}", p[0]);
        assert!((p[1] - 0.25).abs() < 1e-9, "p[1] = {}", p[1]);
        assert!(
            (p.iter().sum::<f64>() - 1.0).abs() < 1e-12,
            "posteriors must sum to 1.0"
        );

        // The symmetric input flips the posteriors.
        let q = nb.predict_proba(&[(1, 1.0)]);
        assert!((q[0] - 0.25).abs() < 1e-9 && (q[1] - 0.75).abs() < 1e-9);
    }
}
