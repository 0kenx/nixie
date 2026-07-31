//! Iterative regex matching machine.
//!
//! The matcher for [`AdvancedRegex`] lives here, split out of the module root
//! to keep each file well under the 2000-line limit. It is an explicit
//! machine rather than a recursive descent: see [`RegexMatcher::match_regex`].

use super::{AdvancedRegex, CaptureGroup, Condition, RegexMatcher};
#[allow(unused_imports)]
use crate::prelude::*;

impl RegexMatcher {
    /// Match a regex pattern against the state
    ///
    /// Driven by an explicit machine rather than natural recursion: the pattern
    /// nests as deeply as the caller builds it (`Star(Star(Star(...)))`,
    /// `Concat` chains produced by a parser, ...) and this is reached from the
    /// public `is_match`/`find`/`find_all` entry points, so the nesting depth is
    /// attacker-controlled. The return type is a bare `bool`, so a depth cap
    /// could only report "no match" for a pattern that does match -- a silently
    /// wrong answer. The machine reproduces the recursive semantics exactly:
    /// every recursive call becomes an `Eval` step plus a continuation step
    /// holding the locals (saved position, loop counter, capture group) the
    /// recursive frame used to hold.
    pub(super) fn match_regex(&self, regex: &AdvancedRegex, state: &mut MatchState) -> bool {
        let mut machine = MatchMachine {
            current: state.clone(),
            steps: vec![MatchStep::Eval(regex)],
            result: false,
        };

        while let Some(step) = machine.steps.pop() {
            self.run_match_step(step, &mut machine);
        }

        *state = machine.current;
        machine.result
    }

    /// Execute one step of the matching machine.
    fn run_match_step<'a, 'r>(&self, step: MatchStep<'a, 'r>, machine: &mut MatchMachine<'a, 'r>) {
        match step {
            MatchStep::Eval(node) => self.eval_regex_node(node, machine),

            MatchStep::SetTrue => machine.result = true,

            MatchStep::ConcatNext {
                parts,
                index,
                saved,
            } => {
                if !machine.result {
                    machine.current.restore(saved);
                    machine.result = false;
                } else if let Some(next) = parts.get(index + 1) {
                    machine.steps.push(MatchStep::ConcatNext {
                        parts,
                        index: index + 1,
                        saved,
                    });
                    machine.steps.push(MatchStep::Eval(next));
                } else {
                    machine.result = true;
                }
            }

            MatchStep::AltNext {
                branches,
                index,
                saved,
            } => {
                if machine.result {
                    machine.result = true;
                } else {
                    machine.current.restore(saved);
                    if let Some(next) = branches.get(index + 1) {
                        let next_saved = machine.current.save();
                        machine.steps.push(MatchStep::AltNext {
                            branches,
                            index: index + 1,
                            saved: next_saved,
                        });
                        machine.steps.push(MatchStep::Eval(next));
                    } else {
                        machine.result = false;
                    }
                }
            }

            MatchStep::GreedyNext { inner, before } => {
                // The greedy loop stops when the body fails **or stops
                // consuming input**. Without the progress check, every body
                // that can match the empty string -- `(a*)*`, `(?:)*`,
                // `x{0}*` -- loops forever: it keeps reporting success
                // without ever advancing `pos`. That is a hang, not an
                // overflow, and no timeout in this crate covers it.
                if !machine.result || machine.current.pos == before {
                    machine.result = true;
                } else {
                    machine.start_greedy(inner);
                }
            }

            MatchStep::PlusFirst { inner } => {
                if machine.result {
                    machine.start_greedy(inner);
                } else {
                    machine.result = false;
                }
            }

            MatchStep::RepeatNext {
                inner,
                remaining,
                saved,
            } => {
                if !machine.result {
                    machine.current.restore(saved);
                    machine.result = false;
                } else if remaining > 0 {
                    machine.steps.push(MatchStep::RepeatNext {
                        inner,
                        remaining: remaining - 1,
                        saved,
                    });
                    machine.steps.push(MatchStep::Eval(inner));
                } else {
                    machine.result = true;
                }
            }

            MatchStep::RangeMinNext {
                inner,
                remaining,
                saved,
                extra,
            } => {
                if !machine.result {
                    machine.current.restore(saved);
                    machine.result = false;
                } else if remaining > 0 {
                    machine.steps.push(MatchStep::RangeMinNext {
                        inner,
                        remaining: remaining - 1,
                        saved,
                        extra,
                    });
                    machine.steps.push(MatchStep::Eval(inner));
                } else {
                    machine.start_range_extra(inner, extra);
                }
            }

            MatchStep::RangeExtraNext {
                inner,
                remaining,
                before,
            } => {
                // Same empty-progress guard as `GreedyNext` above: an optional
                // repetition that consumes no input would otherwise repeat up
                // to `remaining` more times (`usize::MAX` when `max` is
                // unbounded) without ever failing or advancing, which is a
                // hang, not an overflow. Stopping here is sound because a
                // zero-width repetition adds nothing to the match either way.
                if !machine.result || machine.current.pos == before {
                    // The optional repetitions stop at the first failure (or
                    // the first non-advancing iteration) and the range as a
                    // whole still succeeds.
                    machine.result = true;
                } else {
                    machine.start_range_extra(inner, remaining);
                }
            }

            MatchStep::CaptureDone { group, start } => {
                if machine.result {
                    let captured = machine.current.text[start..machine.current.pos].to_string();
                    machine.current.add_capture(group.number, captured.clone());
                    if let Some(name) = &group.name {
                        machine.current.add_named_capture(name.clone(), captured);
                    }
                    machine.result = true;
                } else {
                    machine.result = false;
                }
            }

            MatchStep::LookaheadDone { saved, negate } => {
                machine.current.restore(saved);
                if negate {
                    machine.result = !machine.result;
                }
            }

            MatchStep::LookbehindTry {
                inner,
                start,
                saved,
                negate,
            } => {
                machine.current.pos = start;
                machine.steps.push(MatchStep::LookbehindDone {
                    inner,
                    start,
                    saved,
                    negate,
                });
                machine.steps.push(MatchStep::Eval(inner));
            }

            MatchStep::LookbehindDone {
                inner,
                start,
                saved,
                negate,
            } => {
                if machine.result && machine.current.pos == saved {
                    machine.current.restore(saved);
                    machine.result = !negate;
                } else if start < saved {
                    machine.steps.push(MatchStep::LookbehindTry {
                        inner,
                        start: start + 1,
                        saved,
                        negate,
                    });
                } else {
                    machine.current.restore(saved);
                    machine.result = negate;
                }
            }

            MatchStep::ExitTempState(outer) => {
                // The conditional's look-ahead ran on a throwaway copy; its
                // captures and position never reach the enclosing match.
                machine.current = outer;
            }

            MatchStep::CondBranch {
                yes_branch,
                no_branch,
            } => {
                if machine.result {
                    machine.steps.push(MatchStep::Eval(yes_branch));
                } else if let Some(no) = no_branch {
                    machine.steps.push(MatchStep::Eval(no));
                } else {
                    machine.result = true;
                }
            }
        }
    }

    /// Start matching one node: consume input directly for the leaf operators,
    /// or queue operand evaluations plus a continuation for the rest.
    fn eval_regex_node<'a, 'r>(&self, node: &'r AdvancedRegex, machine: &mut MatchMachine<'a, 'r>) {
        match node {
            AdvancedRegex::Empty => machine.result = true,

            AdvancedRegex::Char(c) => {
                if machine.current.peek() == Some(*c) {
                    machine.current.advance();
                    machine.result = true;
                } else {
                    machine.result = false;
                }
            }

            AdvancedRegex::Class(cls) => {
                if let Some(c) = machine.current.peek()
                    && cls.matches(c)
                {
                    machine.current.advance();
                    machine.result = true;
                } else {
                    machine.result = false;
                }
            }

            AdvancedRegex::AnyChar => {
                if machine.current.peek().is_some() {
                    machine.current.advance();
                    machine.result = true;
                } else {
                    machine.result = false;
                }
            }

            AdvancedRegex::Concat(parts) => {
                let saved = machine.current.save();
                if let Some(first) = parts.first() {
                    machine.steps.push(MatchStep::ConcatNext {
                        parts,
                        index: 0,
                        saved,
                    });
                    machine.steps.push(MatchStep::Eval(first));
                } else {
                    machine.result = true;
                }
            }

            AdvancedRegex::Alt(branches) => {
                if let Some(first) = branches.first() {
                    let saved = machine.current.save();
                    machine.steps.push(MatchStep::AltNext {
                        branches,
                        index: 0,
                        saved,
                    });
                    machine.steps.push(MatchStep::Eval(first));
                } else {
                    machine.result = false;
                }
            }

            AdvancedRegex::Star(inner) | AdvancedRegex::StarPossessive(inner) => {
                // Greedy (and possessive) star: match as many as possible.
                machine.start_greedy(inner);
            }

            AdvancedRegex::Plus(inner) | AdvancedRegex::PlusPossessive(inner) => {
                machine.steps.push(MatchStep::PlusFirst { inner });
                machine.steps.push(MatchStep::Eval(inner));
            }

            AdvancedRegex::Optional(inner) | AdvancedRegex::OptionalPossessive(inner) => {
                machine.steps.push(MatchStep::SetTrue);
                machine.steps.push(MatchStep::Eval(inner));
            }

            AdvancedRegex::Repeat(inner, n) => {
                let saved = machine.current.save();
                if *n == 0 {
                    machine.result = true;
                } else {
                    machine.steps.push(MatchStep::RepeatNext {
                        inner,
                        remaining: n - 1,
                        saved,
                    });
                    machine.steps.push(MatchStep::Eval(inner));
                }
            }

            AdvancedRegex::RepeatRange(inner, min, max) => {
                let saved = machine.current.save();
                // `{5,2}` is a legal thing to *write*; `m - min` underflowed on
                // it (and, with overflow checks off in release, wrapped to a
                // near-`usize::MAX` repetition count instead of failing).
                let extra = max.map(|m| m.saturating_sub(*min)).unwrap_or(usize::MAX);
                if *min == 0 {
                    machine.start_range_extra(inner, extra);
                } else {
                    machine.steps.push(MatchStep::RangeMinNext {
                        inner,
                        remaining: min - 1,
                        saved,
                        extra,
                    });
                    machine.steps.push(MatchStep::Eval(inner));
                }
            }

            // Lazy star / lazy optional: match zero times.
            AdvancedRegex::StarLazy(_) | AdvancedRegex::OptionalLazy(_) => machine.result = true,

            AdvancedRegex::PlusLazy(inner) => {
                // Lazy plus: match exactly once.
                machine.steps.push(MatchStep::Eval(inner));
            }

            AdvancedRegex::Capture(inner, group) => {
                let start = machine.current.pos;
                machine.steps.push(MatchStep::CaptureDone { group, start });
                machine.steps.push(MatchStep::Eval(inner));
            }

            // Non-capturing and atomic groups are transparent here.
            AdvancedRegex::Group(inner) | AdvancedRegex::Atomic(inner) => {
                machine.steps.push(MatchStep::Eval(inner));
            }

            AdvancedRegex::Backref(n) => {
                machine.result = match machine.current.get_capture(*n) {
                    Some(captured) => machine.current.consume_literal(&captured),
                    None => false,
                };
            }

            AdvancedRegex::NamedBackref(name) => {
                machine.result = match machine.current.get_named_capture(name) {
                    Some(captured) => machine.current.consume_literal(&captured),
                    None => false,
                };
            }

            AdvancedRegex::LookaheadPos(inner) | AdvancedRegex::LookaheadNeg(inner) => {
                let saved = machine.current.save();
                let negate = matches!(node, AdvancedRegex::LookaheadNeg(_));
                machine
                    .steps
                    .push(MatchStep::LookaheadDone { saved, negate });
                machine.steps.push(MatchStep::Eval(inner));
            }

            AdvancedRegex::LookbehindPos(inner) | AdvancedRegex::LookbehindNeg(inner) => {
                // Lookbehind is tricky - need to match in reverse.
                // Simplified: look for a body match that ends exactly here.
                let saved = machine.current.save();
                let negate = matches!(node, AdvancedRegex::LookbehindNeg(_));
                machine.steps.push(MatchStep::LookbehindTry {
                    inner,
                    start: 0,
                    saved,
                    negate,
                });
            }

            AdvancedRegex::Conditional {
                condition,
                yes_branch,
                no_branch,
            } => {
                let branch = MatchStep::CondBranch {
                    yes_branch,
                    no_branch: no_branch.as_deref(),
                };
                match condition {
                    Condition::GroupExists(n) => {
                        machine.result = machine.current.get_capture(*n).is_some();
                        machine.steps.push(branch);
                    }
                    Condition::NamedGroupExists(name) => {
                        machine.result = machine.current.get_named_capture(name).is_some();
                        machine.steps.push(branch);
                    }
                    Condition::Lookahead(regex) => {
                        // The condition is evaluated on a throwaway copy, so
                        // park the real state in the step that restores it.
                        let temp = machine.current.clone();
                        let outer = core::mem::replace(&mut machine.current, temp);
                        machine.steps.push(branch);
                        machine.steps.push(MatchStep::ExitTempState(outer));
                        machine.steps.push(MatchStep::Eval(regex));
                    }
                }
            }

            AdvancedRegex::StartAnchor => machine.result = machine.current.pos == 0,

            AdvancedRegex::EndAnchor => {
                machine.result = machine.current.pos >= machine.current.text.len();
            }

            AdvancedRegex::WordBoundary => {
                machine.result = machine.current.at_word_boundary();
            }

            AdvancedRegex::NonWordBoundary => {
                machine.result = !machine.current.at_word_boundary();
            }
        }
    }
}

/// Check if a character is a word character
fn is_word_char(c: Option<char>) -> bool {
    c.is_some_and(|ch| ch.is_alphanumeric() || ch == '_')
}

/// One pending step of the iterative regex matcher.
///
/// `Eval` is "call `match_regex` on this node"; every other variant is a
/// continuation carrying the locals a recursive frame would have kept alive
/// across that call.
enum MatchStep<'a, 'r> {
    /// Begin matching `node` against the current state.
    Eval(&'r AdvancedRegex),
    /// Overwrite the result register with `true`.
    SetTrue,
    /// The `index`-th part of a concatenation finished.
    ConcatNext {
        /// All parts of the concatenation.
        parts: &'r [AdvancedRegex],
        /// Index of the part that just finished.
        index: usize,
        /// Position to restore to if the concatenation fails.
        saved: usize,
    },
    /// The `index`-th branch of an alternation finished.
    AltNext {
        /// All branches of the alternation.
        branches: &'r [AdvancedRegex],
        /// Index of the branch that just finished.
        index: usize,
        /// Position recorded before that branch was tried.
        saved: usize,
    },
    /// One turn of a greedy repetition finished.
    GreedyNext {
        /// Repeated body.
        inner: &'r AdvancedRegex,
        /// Position before the turn that just finished.
        before: usize,
    },
    /// The mandatory first repetition of a `+` operator finished.
    PlusFirst {
        /// Repeated body.
        inner: &'r AdvancedRegex,
    },
    /// One of the `{n}` mandatory repetitions finished.
    RepeatNext {
        /// Repeated body.
        inner: &'r AdvancedRegex,
        /// Repetitions still required after this one.
        remaining: usize,
        /// Position to restore to if the repetition fails.
        saved: usize,
    },
    /// One of the `{min,_}` mandatory repetitions finished.
    RangeMinNext {
        /// Repeated body.
        inner: &'r AdvancedRegex,
        /// Mandatory repetitions still required after this one.
        remaining: usize,
        /// Position to restore to if the repetition fails.
        saved: usize,
        /// Optional repetitions allowed once the minimum is met.
        extra: usize,
    },
    /// One of the optional `{min,max}` repetitions finished.
    RangeExtraNext {
        /// Repeated body.
        inner: &'r AdvancedRegex,
        /// Optional repetitions still allowed after this one.
        remaining: usize,
        /// Position before the turn that just finished.
        before: usize,
    },
    /// A capture group's body finished.
    CaptureDone {
        /// Group the captured text belongs to.
        group: &'r CaptureGroup,
        /// Position the group started at.
        start: usize,
    },
    /// A look-ahead's body finished.
    LookaheadDone {
        /// Position to rewind to (look-ahead consumes nothing).
        saved: usize,
        /// Whether this is a negative look-ahead.
        negate: bool,
    },
    /// Try a look-behind body starting at `start`.
    LookbehindTry {
        /// Look-behind body.
        inner: &'r AdvancedRegex,
        /// Start position for this attempt.
        start: usize,
        /// Position the look-behind must end at.
        saved: usize,
        /// Whether this is a negative look-behind.
        negate: bool,
    },
    /// The look-behind attempt that started at `start` finished.
    LookbehindDone {
        /// Look-behind body.
        inner: &'r AdvancedRegex,
        /// Start position of the attempt that just finished.
        start: usize,
        /// Position the look-behind must end at.
        saved: usize,
        /// Whether this is a negative look-behind.
        negate: bool,
    },
    /// Reinstate the match state parked during a conditional's look-ahead.
    ExitTempState(MatchState<'a>),
    /// A conditional's condition has been decided.
    CondBranch {
        /// Branch taken when the condition holds.
        yes_branch: &'r AdvancedRegex,
        /// Branch taken when it does not.
        no_branch: Option<&'r AdvancedRegex>,
    },
}

/// State of the iterative matcher: the match state being advanced, the pending
/// steps, and the register holding the most recent sub-match result.
struct MatchMachine<'a, 'r> {
    /// Match state the steps operate on.
    current: MatchState<'a>,
    /// Pending steps, innermost on top.
    steps: Vec<MatchStep<'a, 'r>>,
    /// Result of the most recently finished sub-match.
    result: bool,
}

impl<'r> MatchMachine<'_, 'r> {
    /// Queue one turn of a greedy repetition of `inner`.
    fn start_greedy(&mut self, inner: &'r AdvancedRegex) {
        let before = self.current.pos;
        self.steps.push(MatchStep::GreedyNext { inner, before });
        self.steps.push(MatchStep::Eval(inner));
    }

    /// Queue the optional repetitions of a `{min,max}` range.
    fn start_range_extra(&mut self, inner: &'r AdvancedRegex, extra: usize) {
        if extra == 0 {
            self.result = true;
            return;
        }
        let before = self.current.pos;
        self.steps.push(MatchStep::RangeExtraNext {
            inner,
            remaining: extra - 1,
            before,
        });
        self.steps.push(MatchStep::Eval(inner));
    }
}

/// Matching state with backtracking support
#[derive(Debug, Clone)]
pub(super) struct MatchState<'a> {
    /// Input text
    text: &'a str,
    /// Current position
    pub(super) pos: usize,
    /// Captured groups
    pub(super) captures: Vec<Option<String>>,
    /// Named captures
    pub(super) named_captures: FxHashMap<String, String>,
}

impl<'a> MatchState<'a> {
    /// Create a new match state
    pub(super) fn new(text: &'a str, pos: usize) -> Self {
        Self {
            text,
            pos,
            captures: Vec::new(),
            named_captures: FxHashMap::default(),
        }
    }

    /// Peek at current character
    fn peek(&self) -> Option<char> {
        self.text[self.pos..].chars().next()
    }

    /// Advance to next character
    fn advance(&mut self) {
        if let Some(c) = self.peek() {
            self.pos += c.len_utf8();
        }
    }

    /// Save current state
    fn save(&self) -> usize {
        self.pos
    }

    /// Restore to saved state
    fn restore(&mut self, saved: usize) {
        self.pos = saved;
    }

    /// Consume `literal` verbatim, rewinding to the start on mismatch
    ///
    /// This is the back-reference body: a plain character-by-character walk of
    /// an already-captured string, no recursion involved.
    fn consume_literal(&mut self, literal: &str) -> bool {
        let saved = self.save();
        for c in literal.chars() {
            if self.peek() != Some(c) {
                self.restore(saved);
                return false;
            }
            self.advance();
        }
        true
    }

    /// Whether the current position sits on a `\b` word boundary
    fn at_word_boundary(&self) -> bool {
        let before = self.pos > 0 && is_word_char(self.text[..self.pos].chars().last());
        let after = self.pos < self.text.len() && is_word_char(self.peek());
        before != after
    }

    /// Add a capture group
    fn add_capture(&mut self, index: usize, value: String) {
        // Extend captures vector if needed
        while self.captures.len() < index {
            self.captures.push(None);
        }
        if index > 0 {
            self.captures[index - 1] = Some(value);
        }
    }

    /// Get a capture group
    fn get_capture(&self, index: usize) -> Option<String> {
        if index > 0 && index <= self.captures.len() {
            self.captures[index - 1].clone()
        } else {
            None
        }
    }

    /// Add a named capture
    fn add_named_capture(&mut self, name: String, value: String) {
        self.named_captures.insert(name, value);
    }

    /// Get a named capture
    fn get_named_capture(&self, name: &str) -> Option<String> {
        self.named_captures.get(name).cloned()
    }
}
