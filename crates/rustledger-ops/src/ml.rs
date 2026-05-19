//! ML-based transaction categorization.
//!
//! Trains a Multinomial Naive Bayes classifier on existing ledger transactions
//! to predict the expense/income account for new transactions based on their
//! payee and narration text.
//!
//! Uses TF-IDF vectorization with linfa-bayes for classification.
//!
//! # Example
//!
//! ```rust,ignore
//! let model = CategorizationModel::train(&existing_directives)?;
//! let predictions = model.predict("WHOLE FOODS", Some("groceries"));
//! // → [("Expenses:Groceries", 0.80)]
//! ```

use linfa::prelude::*;
use linfa_bayes::MultinomialNb;
use ndarray::{Array1, Array2};
use rustledger_plugin_types::{DirectiveData, DirectiveWrapper};
use std::collections::HashMap;

/// A trained categorization model.
///
/// Wraps a Multinomial Naive Bayes classifier trained on TF-IDF features
/// extracted from transaction payee/narration text.
pub struct CategorizationModel {
    /// The trained classifier.
    model: MultinomialNb<f64, usize>,
    /// Vocabulary: word → column index in the feature matrix.
    vocabulary: HashMap<String, usize>,
    /// IDF weights for each word in the vocabulary.
    idf: Vec<f64>,
    /// Label map: index → account name.
    labels: Vec<String>,
}

/// Error type for ML operations.
#[derive(Debug)]
pub enum MlError {
    /// Not enough training data.
    InsufficientData(String),
    /// Model training failed.
    TrainingFailed(String),
}

impl std::fmt::Display for MlError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InsufficientData(msg) => write!(f, "insufficient training data: {msg}"),
            Self::TrainingFailed(msg) => write!(f, "training failed: {msg}"),
        }
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

        // Build TF-IDF feature matrix
        let n_samples = samples.len();
        let n_features = vocab.len();
        let mut features = Array2::<f64>::zeros((n_samples, n_features));
        let mut targets = Array1::<usize>::zeros(n_samples);

        for (i, (tokens, (_, account))) in tokenized.iter().zip(samples.iter()).enumerate() {
            // Term frequency
            let mut tf = vec![0u32; n_features];
            for token in tokens {
                if let Some(&idx) = vocab.get(token) {
                    tf[idx] += 1;
                }
            }
            // TF-IDF
            for (j, &count) in tf.iter().enumerate() {
                features[[i, j]] = f64::from(count) * idf[j];
            }
            targets[i] = label_to_idx[account.as_str()];
        }

        // Train Multinomial Naive Bayes
        let dataset = DatasetBase::new(features, targets);
        let model = MultinomialNb::params()
            .fit(&dataset)
            .map_err(|e| MlError::TrainingFailed(format!("{e}")))?;

        Ok(Self {
            model,
            vocabulary: vocab,
            idf,
            labels: label_set,
        })
    }

    /// Predict the account for a transaction.
    ///
    /// Returns up to `top_n` predictions sorted by confidence (highest first).
    /// Each prediction is an `(account, probability)` pair.
    ///
    /// **Note:** Confidence scores are not calibrated. The predicted class always
    /// receives a confidence of `0.8` and all other classes receive `0.0`.
    /// Computing calibrated probabilities requires log-likelihood estimation,
    /// which is a future enhancement.
    #[must_use]
    pub fn predict(&self, narration: &str, payee: Option<&str>) -> Vec<(String, f64)> {
        let mut text = String::new();
        if let Some(p) = payee {
            text.push_str(p);
            text.push(' ');
        }
        text.push_str(narration);

        let features = self.vectorize(&text.to_lowercase());
        let features_2d = features.insert_axis(ndarray::Axis(0));

        // Get prediction
        let prediction = self.model.predict(&features_2d);
        let predicted_idx = prediction[0];

        // For Naive Bayes, we don't get probability scores directly from linfa.
        // Return the predicted class with confidence 1.0 and others with 0.0.
        // A more sophisticated approach would compute log-likelihoods.
        let mut results: Vec<(String, f64)> = self
            .labels
            .iter()
            .enumerate()
            .map(|(i, label)| {
                let conf = if i == predicted_idx { 0.8 } else { 0.0 };
                (label.clone(), conf)
            })
            .filter(|(_, conf)| *conf > 0.0)
            .collect();

        results.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
        results
    }

    /// Vectorize text into a TF-IDF feature array.
    fn vectorize(&self, text: &str) -> Array1<f64> {
        let tokens = tokenize(text);
        let n_features = self.vocabulary.len();
        let mut tf = vec![0u32; n_features];

        for token in &tokens {
            if let Some(&idx) = self.vocabulary.get(token) {
                tf[idx] += 1;
            }
        }

        let mut features = Array1::<f64>::zeros(n_features);
        for (j, &count) in tf.iter().enumerate() {
            features[j] = f64::from(count) * self.idf[j];
        }
        features
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

/// Tokenize text into lowercase words, filtering out short tokens.
fn tokenize(text: &str) -> Vec<String> {
    text.split(|c: char| !c.is_alphanumeric())
        .filter(|s| s.len() >= 2)
        .map(str::to_lowercase)
        .collect()
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
}
