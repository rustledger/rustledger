//! An LR driver replaying bison's `yacc.c` skeleton over the generated
//! beancount tables ([`super::tables`]), error recovery included.
//!
//! Provenance: the driver implements GNU bison 3.8's documented `yacc.c`
//! semantics, following pta-standards' MIT-licensed `harness/lalr.py`
//! (rustledger/pta-standards@1463db773ac5), which replays the same tables in
//! Python and matches beancount 3.2.3's syntax errors on every input of its
//! corpora. It is not derived from beancount's sources.
//!
//! What it replays, step for step:
//!
//! * default reductions (`yypact` at `YYPACT_NINF`), shifts and reductions
//!   from `yytable`, gotos from `yypgoto` / `yydefgoto`;
//! * a syntax error is REPORTED only while `yyerrstatus` is 0; on any error the
//!   stack pops to a state that shifts `error`, shifts it, and sets
//!   `yyerrstatus` to 3; each later token shift lowers it by one;
//! * at `yyerrstatus` 3 an unacceptable lookahead is discarded, or the parse
//!   aborts if it is the end of input;
//! * a lexer error (the scanner's `YYerror`) enters recovery directly, without
//!   a syntax error, and the lookahead becomes `YYUNDEF`, which is then
//!   discarded like any other token;
//! * the end of input is delivered as token 0 for as long as the parser asks;
//! * the stack is capped at `YYMAXDEPTH` (10000) states: reaching it is bison's
//!   "memory exhausted", which aborts the parse.
//!
//! No recursion and no panics (every table read goes through `get`), and the
//! work is linear in the number of tokens: each token is shifted or discarded
//! once, reductions are bounded by shifts, and recovery pops only what was
//! pushed.

use super::lexer::Lexeme;
use super::tables::{
    CHECK, DEFACT, DEFGOTO, NT_DIRECTIVE, NT_ENTRY, PACT, PGOTO, R1, R2, TABLE,
    TABLE_NINF_IS_ERROR, Tok, YYFINAL, YYLAST, YYNTOKENS, YYPACT_NINF, YYTABLE_NINF,
};

/// bison's default `YYMAXDEPTH`.
pub const YYMAXDEPTH: usize = 10_000;

/// The most steps the driver takes without reading a token: more than the
/// reductions a stack of `YYMAXDEPTH` states can make, so only a defect in the
/// tables could reach it, and it stops the parse rather than loop.
const MAX_IDLE_STEPS: usize = 8 * YYMAXDEPTH + 1024;

/// What the parser reported, in order.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Event {
    /// The lexer's own error (an invalid token, date or number): beancount's
    /// `LexerError`. bison enters recovery without a report of its own.
    Lexer(Lexeme),
    /// A reported syntax error at the lookahead `at`. `expected` is the set of
    /// terminals the state could shift (bit `n` for symbol `n`), as bison's
    /// verbose message lists them.
    Syntax { at: Lexeme, expected: u64 },
    /// bison's "memory exhausted": the stack reached `YYMAXDEPTH`. The parse
    /// stops there.
    Exhausted(Lexeme),
}

/// One declaration of the reduction trace: its byte range, and whether bison
/// built it (reduced it to an `entry` or `directive`) or dropped it (popped
/// it off the stack in error recovery, half read).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Statement {
    pub start: u32,
    pub end: u32,
    pub built: bool,
}

/// The result of one parse.
#[derive(Default, Debug)]
pub struct Outcome {
    pub events: Vec<Event>,
    /// Byte ranges of the tokens bison consumed while recovering: discarded,
    /// or shifted while `yyerrstatus` was above 0. Sorted, adjacent tokens
    /// merged.
    pub recovery: Vec<(u32, u32)>,
    /// Dropped declarations always; built ones too when the caller asked for
    /// the full trace.
    pub statements: Vec<Statement>,
    /// Whether the parse reached bison's accepting state.
    pub accepted: bool,
}

impl Outcome {
    fn mark_recovery(&mut self, l: Lexeme) {
        if l.end <= l.start {
            return;
        }
        match self.recovery.last_mut() {
            Some(last) if last.1 >= l.start => last.1 = last.1.max(l.end),
            _ => self.recovery.push((l.start, l.end)),
        }
    }
}

fn table(i: i32) -> Option<i16> {
    usize::try_from(i).ok().and_then(|i| TABLE.get(i).copied())
}

fn check(i: i32) -> Option<i16> {
    usize::try_from(i).ok().and_then(|i| CHECK.get(i).copied())
}

fn pact(state: i16) -> i16 {
    usize::try_from(state)
        .ok()
        .and_then(|s| PACT.get(s).copied())
        .unwrap_or(YYPACT_NINF)
}

/// `yytable[yypact[state] + sym]`, when `yycheck` confirms the entry is the
/// state's.
fn action(state: i16, sym: i16) -> Option<i16> {
    let base = pact(state);
    if base == YYPACT_NINF {
        return None;
    }
    let k = i32::from(base) + i32::from(sym);
    if (0..=i32::from(YYLAST)).contains(&k) && check(k) == Some(sym) {
        table(k)
    } else {
        None
    }
}

const fn table_value_is_error(v: i16) -> bool {
    TABLE_NINF_IS_ERROR && v == YYTABLE_NINF
}

/// The terminals bison lists as expected in `state`, as a bit set.
pub fn expected(state: i16) -> u64 {
    let base = pact(state);
    if base == YYPACT_NINF {
        return 0;
    }
    let base = i32::from(base);
    let xbegin = if base < 0 { -base } else { 0 };
    let xend = (i32::from(YYLAST) - base + 1).min(i32::from(YYNTOKENS));
    let mut set = 0u64;
    for x in xbegin..xend {
        if check(x + base) == Some(x as i16)
            && x != Tok::Error as i32
            && !table(x + base).is_some_and(table_value_is_error)
        {
            set |= 1 << x;
        }
    }
    set
}

/// The goto from `top` on nonterminal `lhs` (an internal symbol number).
fn goto(top: i16, lhs: i16) -> i16 {
    let nt = lhs - YYNTOKENS;
    let Some(nt_index) = usize::try_from(nt).ok() else {
        return 0;
    };
    let gi = PGOTO.get(nt_index).map(|&b| i32::from(b) + i32::from(top));
    match gi {
        Some(gi) if (0..=i32::from(YYLAST)).contains(&gi) && check(gi) == Some(top) => {
            table(gi).unwrap_or(0)
        }
        _ => DEFGOTO.get(nt_index).map_or(0, |&s| i16::from(s)),
    }
}

/// Runs the parser over `tokens` (a source of `src_len` bytes). `full_trace`
/// also records every built declaration.
pub fn run(tokens: impl Iterator<Item = Lexeme>, src_len: u32, full_trace: bool) -> Outcome {
    let mut tokens = tokens;
    let mut out = Outcome::default();
    // (state, byte offset where the symbol under it starts)
    let mut stack: Vec<(i16, u32)> = Vec::with_capacity(64);
    stack.push((0, 0));
    let mut state: i16 = 0;
    let mut errstatus: u8 = 0;
    let mut lookahead: Option<Lexeme> = None;
    let mut last_line: u32 = 1;
    // The end of the last token shifted or discarded: where a reduction made
    // without a lookahead ends.
    let mut last_end: u32 = 0;
    // Steps since a token was last read: bounded by the reductions a stack of
    // `YYMAXDEPTH` states can make, so a table defect cannot loop forever.
    let mut idle_steps: usize = 0;

    loop {
        idle_steps += 1;
        if idle_steps > MAX_IDLE_STEPS {
            return out;
        }
        if state == YYFINAL {
            out.accepted = true;
            return out;
        }
        // Decide: shift, reduce by `rule`, or error.
        let mut rule: Option<u8> = None;
        let mut error = false;
        let base = pact(state);
        if base == YYPACT_NINF {
            if let Some(&r) = usize::try_from(state).ok().and_then(|s| DEFACT.get(s))
                && r != 0
            {
                rule = Some(r);
            } else {
                error = true;
            }
        } else {
            let la = if let Some(l) = lookahead {
                l
            } else {
                {
                    idle_steps = 0;
                    let next = match tokens.next() {
                        Some(l) => {
                            last_line = l.line;
                            l
                        }
                        None => Lexeme {
                            tok: Tok::Eof,
                            start: src_len,
                            end: src_len,
                            line: last_line,
                        },
                    };
                    if next.tok == Tok::Error {
                        // The scanner's YYerror: reported by the lexer, then
                        // straight to yyerrlab1 with YYUNDEF as the lookahead.
                        out.events.push(Event::Lexer(next));
                        lookahead = Some(Lexeme {
                            tok: Tok::Undef,
                            ..next
                        });
                        if !recover(&mut stack, &mut state, &mut out, next.start, full_trace) {
                            return out;
                        }
                        errstatus = 3;
                        if stack.len() >= YYMAXDEPTH {
                            out.events.push(Event::Exhausted(next));
                            return out;
                        }
                        continue;
                    }
                    lookahead = Some(next);
                    next
                }
            };
            match action(state, la.tok as i16) {
                Some(act) if act > 0 => {
                    // Shift.
                    if errstatus > 0 {
                        errstatus -= 1;
                        out.mark_recovery(la);
                    }
                    stack.push((act, la.start));
                    state = act;
                    last_end = la.end;
                    lookahead = None;
                    if stack.len() >= YYMAXDEPTH {
                        out.events.push(Event::Exhausted(la));
                        return out;
                    }
                    continue;
                }
                Some(act) if table_value_is_error(act) => error = true,
                Some(act) => match u8::try_from(-i32::from(act)) {
                    Ok(r) => rule = Some(r),
                    Err(_) => error = true,
                },
                None => {
                    if let Some(&r) = usize::try_from(state).ok().and_then(|s| DEFACT.get(s))
                        && r != 0
                    {
                        rule = Some(r);
                    } else {
                        error = true;
                    }
                }
            }
        }

        if error {
            // yyerrlab
            let at = lookahead.unwrap_or(Lexeme {
                tok: Tok::Undef,
                start: src_len,
                end: src_len,
                line: last_line,
            });
            if errstatus == 0 {
                out.events.push(Event::Syntax {
                    at,
                    expected: expected(state),
                });
            }
            if errstatus == 3 {
                match lookahead {
                    Some(l) if l.tok == Tok::Eof => return out, // YYABORT
                    Some(l) => {
                        out.mark_recovery(l);
                        last_end = l.end;
                        lookahead = None;
                    }
                    None => {}
                }
            }
            // yyerrlab1
            if !recover(&mut stack, &mut state, &mut out, at.start, full_trace) {
                return out;
            }
            errstatus = 3;
            if stack.len() >= YYMAXDEPTH {
                out.events.push(Event::Exhausted(at));
                return out;
            }
            continue;
        }

        // Reduce.
        let Some(rule) = rule else { return out };
        let len = R2.get(usize::from(rule)).map_or(0, |&n| usize::from(n));
        let here = lookahead.map_or(last_end, |l| l.start);
        let start = if len == 0 {
            here
        } else {
            stack
                .len()
                .checked_sub(len)
                .and_then(|i| stack.get(i))
                .map_or(here, |&(_, s)| s)
        };
        let keep = stack.len().saturating_sub(len).max(1);
        stack.truncate(keep);
        let lhs = R1.get(usize::from(rule)).map_or(0, |&n| i16::from(n));
        if full_trace && (lhs == NT_ENTRY || lhs == NT_DIRECTIVE) {
            out.statements.push(Statement {
                start,
                end: here,
                built: true,
            });
        }
        let top = stack.last().map_or(0, |&(s, _)| s);
        state = goto(top, lhs);
        stack.push((state, start));
        if stack.len() >= YYMAXDEPTH {
            if let Some(l) = lookahead {
                out.events.push(Event::Exhausted(l));
            }
            return out;
        }
    }
}

/// yyerrlab1: pops states until one shifts `error`, then shifts it. Whatever
/// it pops was a declaration in progress, recorded as dropped (ending at
/// `error_at`). `false` when the stack empties: bison's YYABORT.
fn recover(
    stack: &mut Vec<(i16, u32)>,
    state: &mut i16,
    out: &mut Outcome,
    error_at: u32,
    _full_trace: bool,
) -> bool {
    let mut dropped_from: Option<u32> = None;
    loop {
        let Some(&(top, start)) = stack.last() else {
            return false;
        };
        if let Some(act) = action(top, Tok::Error as i16)
            && act > 0
        {
            if let Some(from) = dropped_from
                && from < error_at
            {
                out.statements.push(Statement {
                    start: from,
                    end: error_at,
                    built: false,
                });
            }
            stack.push((act, error_at));
            *state = act;
            return true;
        }
        if stack.len() == 1 {
            return false;
        }
        dropped_from = Some(start);
        stack.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::super::lexer::Lexer;
    use super::*;

    /// `(line, message)` per reported error, as beancount prints them.
    fn errors(src: &str) -> Vec<(u32, String)> {
        let out = run(Lexer::new(src.as_bytes()), src.len() as u32, false);
        out.events
            .iter()
            .map(|e| match *e {
                Event::Lexer(l) => (
                    l.line,
                    format!(
                        "Invalid token: {:?}",
                        &src[l.start as usize..l.end as usize]
                    ),
                ),
                Event::Syntax { at, expected } => {
                    (at.line, super::super::syntax_message(at.tok, expected))
                }
                Event::Exhausted(l) => (l.line, "memory exhausted".to_string()),
            })
            .collect()
    }

    #[test]
    fn test_run_clean_input_accepts() {
        let src = "option \"title\" \"x\"\n2024-01-01 open Assets:A USD\n2024-01-02 * \"p\" \"n\" #t\n  Assets:A  1 USD\n  Assets:B\n";
        let out = run(Lexer::new(src.as_bytes()), src.len() as u32, true);
        assert!(out.accepted);
        assert!(out.events.is_empty());
        assert_eq!(out.statements.iter().filter(|s| s.built).count(), 3);
    }

    #[test]
    fn test_run_messages_from_pta_standards_provenance() {
        assert_eq!(
            errors("2024-01-01 open"),
            [(
                1,
                "syntax error, unexpected end of file, expecting ACCOUNT".to_string()
            )]
        );
        assert_eq!(
            errors("option \"a\"\n"),
            [(
                2,
                "syntax error, unexpected EOL, expecting STRING".to_string()
            )]
        );
        assert_eq!(
            errors("option \"a\" \"b\"\n  ;c\n"),
            [(2, "syntax error, unexpected INDENT".to_string())]
        );
        assert_eq!(
            errors("2024-01-01 open Assets:A\n  1\n"),
            [(
                2,
                "syntax error, unexpected NUMBER, expecting end of file or EOL or KEY".to_string()
            )]
        );
    }

    #[test]
    fn test_run_lexer_error_enters_recovery_without_a_report() {
        // The entry is dropped and only the lexer error is reported.
        let src = "2024-01-01 open Assets:A $\n  kk: 1\n";
        let out = run(Lexer::new(src.as_bytes()), src.len() as u32, false);
        assert_eq!(out.events.len(), 1);
        assert!(matches!(out.events[0], Event::Lexer(_)));
        assert_eq!(
            out.statements,
            [Statement {
                start: 0,
                end: 25,
                built: false
            }]
        );
    }

    #[test]
    fn test_run_recovery_resumes_mid_line_at_a_declaration_start() {
        let src = "pushtag #a #b 2024-01-01 open Assets:A\n";
        let out = run(Lexer::new(src.as_bytes()), src.len() as u32, true);
        assert_eq!(out.events.len(), 1);
        assert!(out.statements.iter().any(|s| s.built && s.start == 14));
    }

    #[test]
    fn test_run_three_shifts_before_reporting_again() {
        // The second bad line follows the first within bison's window.
        assert_eq!(errors("$\n$\n").len(), 2); // lexer errors are always reported
        assert_eq!(errors("2024-01-01 open\n1\n").len(), 1);
    }

    #[test]
    fn test_run_deep_nesting_exhausts_the_stack() {
        let src = format!("2024-01-01 custom \"x\" {}1\n", "-".repeat(20_000));
        let out = run(Lexer::new(src.as_bytes()), src.len() as u32, false);
        assert!(matches!(out.events.last(), Some(Event::Exhausted(_))));
    }
}
