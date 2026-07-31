//! Advanced Regular Expression Engine
//!
//! Extended regex support with:
//! - **Capture groups**: Named and numbered groups
//! - **Backreferences**: \1, \2, \k\<name\>
//! - **Lookahead/Lookbehind**: (?=...), (?!...), (?<=...), (?<!...)
//! - **Atomic groups**: (?>...)
//! - **Conditional patterns**: (?(condition)yes|no)
//! - **Unicode properties**: \p{L}, \p{N}, etc.
//! - **Word boundaries**: \b, \B
//! - **Advanced quantifiers**: Possessive (+, *, ?) and lazy (?, *?, +?)
//!
//! Implements a hybrid NFA/DFA approach with backtracking for advanced features.

#![allow(missing_docs)]

use super::unicode::UnicodeCategory;
#[allow(unused_imports)]
use crate::prelude::*;
use core::fmt;

mod machine;

use machine::MatchState;

/// Advanced regex pattern
///
/// # Depth invariant
///
/// There is deliberately no bound on how deep an `AdvancedRegex` may be: the
/// variants are public, so callers build values directly, and a pattern
/// compiled from external source text nests as deeply as that source does.
/// [`Clone`] and [`PartialEq`] are therefore iterative -- see their impls
/// below -- rather than derived, exactly like the [`Drop`] impl already in
/// this file. Do **not** replace any of them with a `derive`.
#[derive(Debug)]
pub enum AdvancedRegex {
    /// Empty regex (matches empty string)
    Empty,
    /// Single character
    Char(char),
    /// Character class
    Class(CharacterClass),
    /// Any character (.)
    AnyChar,
    /// Concatenation
    Concat(Vec<AdvancedRegex>),
    /// Alternation (|)
    Alt(Vec<AdvancedRegex>),
    /// Zero or more (*)
    Star(Box<AdvancedRegex>),
    /// One or more (+)
    Plus(Box<AdvancedRegex>),
    /// Zero or one (?)
    Optional(Box<AdvancedRegex>),
    /// Exact repetition {n}
    Repeat(Box<AdvancedRegex>, usize),
    /// Range repetition {n,m}
    RepeatRange(Box<AdvancedRegex>, usize, Option<usize>),
    /// Lazy star (*?)
    StarLazy(Box<AdvancedRegex>),
    /// Lazy plus (+?)
    PlusLazy(Box<AdvancedRegex>),
    /// Lazy optional (??）
    OptionalLazy(Box<AdvancedRegex>),
    /// Possessive star (*+)
    StarPossessive(Box<AdvancedRegex>),
    /// Possessive plus (++)
    PlusPossessive(Box<AdvancedRegex>),
    /// Possessive optional (?+)
    OptionalPossessive(Box<AdvancedRegex>),
    /// Capturing group
    Capture(Box<AdvancedRegex>, CaptureGroup),
    /// Non-capturing group
    Group(Box<AdvancedRegex>),
    /// Backreference
    Backref(usize),
    /// Named backreference
    NamedBackref(String),
    /// Positive lookahead (?=...)
    LookaheadPos(Box<AdvancedRegex>),
    /// Negative lookahead (?!...)
    LookaheadNeg(Box<AdvancedRegex>),
    /// Positive lookbehind (?<=...)
    LookbehindPos(Box<AdvancedRegex>),
    /// Negative lookbehind (?<!...)
    LookbehindNeg(Box<AdvancedRegex>),
    /// Atomic group (?>...)
    Atomic(Box<AdvancedRegex>),
    /// Conditional (?(cond)yes|no)
    Conditional {
        condition: Condition,
        yes_branch: Box<AdvancedRegex>,
        no_branch: Option<Box<AdvancedRegex>>,
    },
    /// Start anchor (^)
    StartAnchor,
    /// End anchor ($)
    EndAnchor,
    /// Word boundary (\b)
    WordBoundary,
    /// Non-word boundary (\B)
    NonWordBoundary,
}

/// Capture group information
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CaptureGroup {
    /// Group number (1-indexed)
    pub number: usize,
    /// Optional group name
    pub name: Option<String>,
}

impl CaptureGroup {
    /// Create a numbered capture group
    pub fn numbered(n: usize) -> Self {
        Self {
            number: n,
            name: None,
        }
    }

    /// Create a named capture group
    pub fn named(n: usize, name: String) -> Self {
        Self {
            number: n,
            name: Some(name),
        }
    }
}

/// Conditional pattern condition
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Condition {
    /// Check if group number exists
    GroupExists(usize),
    /// Check if named group exists
    NamedGroupExists(String),
    /// Lookahead assertion
    Lookahead(Box<AdvancedRegex>),
}

/// Character class (e.g., [a-z], [^0-9])
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CharacterClass {
    /// Character ranges
    pub ranges: Vec<(char, char)>,
    /// Individual characters
    pub chars: Vec<char>,
    /// Unicode properties
    pub properties: Vec<UnicodeProperty>,
    /// Negated class
    pub negated: bool,
}

impl CharacterClass {
    /// Create a new character class
    pub fn new() -> Self {
        Self {
            ranges: Vec::new(),
            chars: Vec::new(),
            properties: Vec::new(),
            negated: false,
        }
    }

    /// Add a character
    pub fn add_char(&mut self, c: char) {
        self.chars.push(c);
    }

    /// Add a range
    pub fn add_range(&mut self, start: char, end: char) {
        self.ranges.push((start, end));
    }

    /// Add a Unicode property
    pub fn add_property(&mut self, prop: UnicodeProperty) {
        self.properties.push(prop);
    }

    /// Negate this class
    pub fn negate(mut self) -> Self {
        self.negated = !self.negated;
        self
    }

    /// Check if a character matches this class
    pub fn matches(&self, c: char) -> bool {
        let result = self.chars.contains(&c)
            || self
                .ranges
                .iter()
                .any(|&(start, end)| c >= start && c <= end)
            || self.properties.iter().any(|p| p.matches(c));

        if self.negated { !result } else { result }
    }

    /// Predefined digit class [0-9]
    pub fn digit() -> Self {
        let mut cls = Self::new();
        cls.add_range('0', '9');
        cls
    }

    /// Predefined word class [a-zA-Z0-9_]
    pub fn word() -> Self {
        let mut cls = Self::new();
        cls.add_range('a', 'z');
        cls.add_range('A', 'Z');
        cls.add_range('0', '9');
        cls.add_char('_');
        cls
    }

    /// Predefined whitespace class
    pub fn whitespace() -> Self {
        let mut cls = Self::new();
        cls.add_char(' ');
        cls.add_char('\t');
        cls.add_char('\n');
        cls.add_char('\r');
        cls
    }
}

impl Default for CharacterClass {
    fn default() -> Self {
        Self::new()
    }
}

/// Unicode property matcher
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnicodeProperty {
    /// General category
    Category(UnicodeCategory),
    /// Script (e.g., Latin, Greek, Cyrillic)
    Script(UnicodeScript),
    /// Block (e.g., Basic Latin, Latin-1 Supplement)
    Block(UnicodeBlock),
    /// Binary property (e.g., Alphabetic, Lowercase)
    Binary(BinaryProperty),
}

impl UnicodeProperty {
    /// Check if a character matches this property
    pub fn matches(&self, c: char) -> bool {
        match self {
            UnicodeProperty::Category(cat) => cat.contains(c),
            UnicodeProperty::Script(script) => script.contains(c),
            UnicodeProperty::Block(block) => block.contains(c),
            UnicodeProperty::Binary(prop) => prop.matches(c),
        }
    }
}

/// Unicode script
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnicodeScript {
    Latin,
    Greek,
    Cyrillic,
    Arabic,
    Hebrew,
    Han,
    Hiragana,
    Katakana,
    Hangul,
    Thai,
    Devanagari,
}

impl UnicodeScript {
    /// Check if a character belongs to this script
    pub fn contains(&self, c: char) -> bool {
        let cp = c as u32;
        match self {
            UnicodeScript::Latin => {
                matches!(cp, 0x0041..=0x005A | 0x0061..=0x007A | 0x00C0..=0x00FF | 0x0100..=0x017F | 0x0180..=0x024F)
            }
            UnicodeScript::Greek => matches!(cp, 0x0370..=0x03FF | 0x1F00..=0x1FFF),
            UnicodeScript::Cyrillic => matches!(cp, 0x0400..=0x052F),
            UnicodeScript::Arabic => {
                matches!(cp, 0x0600..=0x06FF | 0x0750..=0x077F | 0x08A0..=0x08FF)
            }
            UnicodeScript::Hebrew => matches!(cp, 0x0590..=0x05FF | 0xFB1D..=0xFB4F),
            UnicodeScript::Han => {
                matches!(cp, 0x4E00..=0x9FFF | 0x3400..=0x4DBF | 0x20000..=0x2A6DF)
            }
            UnicodeScript::Hiragana => matches!(cp, 0x3040..=0x309F),
            UnicodeScript::Katakana => matches!(cp, 0x30A0..=0x30FF | 0x31F0..=0x31FF),
            UnicodeScript::Hangul => {
                matches!(cp, 0xAC00..=0xD7AF | 0x1100..=0x11FF | 0x3130..=0x318F)
            }
            UnicodeScript::Thai => matches!(cp, 0x0E00..=0x0E7F),
            UnicodeScript::Devanagari => matches!(cp, 0x0900..=0x097F),
        }
    }
}

/// Unicode block
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnicodeBlock {
    BasicLatin,
    Latin1Supplement,
    LatinExtendedA,
    GreekAndCoptic,
    CJKUnifiedIdeographs,
}

impl UnicodeBlock {
    /// Check if a character belongs to this block
    pub fn contains(&self, c: char) -> bool {
        let cp = c as u32;
        match self {
            UnicodeBlock::BasicLatin => matches!(cp, 0x0000..=0x007F),
            UnicodeBlock::Latin1Supplement => matches!(cp, 0x0080..=0x00FF),
            UnicodeBlock::LatinExtendedA => matches!(cp, 0x0100..=0x017F),
            UnicodeBlock::GreekAndCoptic => matches!(cp, 0x0370..=0x03FF),
            UnicodeBlock::CJKUnifiedIdeographs => matches!(cp, 0x4E00..=0x9FFF),
        }
    }
}

/// Binary Unicode property
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinaryProperty {
    Alphabetic,
    Lowercase,
    Uppercase,
    WhiteSpace,
    HexDigit,
    AsciiHexDigit,
}

impl BinaryProperty {
    /// Check if a character has this property
    pub fn matches(&self, c: char) -> bool {
        match self {
            BinaryProperty::Alphabetic => c.is_alphabetic(),
            BinaryProperty::Lowercase => c.is_lowercase(),
            BinaryProperty::Uppercase => c.is_uppercase(),
            BinaryProperty::WhiteSpace => c.is_whitespace(),
            BinaryProperty::HexDigit => c.is_ascii_hexdigit(),
            BinaryProperty::AsciiHexDigit => c.is_ascii_hexdigit(),
        }
    }
}

/// Match result with captures
#[derive(Debug, Clone)]
pub struct Match {
    /// Full match string
    pub text: String,
    /// Start position
    pub start: usize,
    /// End position
    pub end: usize,
    /// Captured groups
    pub captures: Vec<Option<String>>,
    /// Named captures
    pub named_captures: FxHashMap<String, String>,
}

impl Match {
    /// Create a new match
    pub fn new(text: String, start: usize, end: usize) -> Self {
        Self {
            text,
            start,
            end,
            captures: Vec::new(),
            named_captures: FxHashMap::default(),
        }
    }

    /// Get a capture group by index (0 = full match)
    pub fn get(&self, index: usize) -> Option<&str> {
        if index == 0 {
            Some(&self.text)
        } else {
            self.captures.get(index - 1).and_then(|opt| opt.as_deref())
        }
    }

    /// Get a named capture group
    pub fn name(&self, name: &str) -> Option<&str> {
        self.named_captures.get(name).map(|s| s.as_str())
    }
}

/// Regex matcher with backtracking support
#[derive(Debug)]
pub struct RegexMatcher {
    /// The regex pattern
    pattern: AdvancedRegex,
    /// Next capture group number
    #[allow(dead_code)]
    next_capture: usize,
}

impl RegexMatcher {
    /// Create a new regex matcher
    pub fn new(pattern: AdvancedRegex) -> Self {
        Self {
            pattern,
            next_capture: 1,
        }
    }

    /// Check if the pattern matches the entire string
    pub fn is_match(&self, text: &str) -> bool {
        if let Some(m) = self.match_at(text, 0) {
            // If pattern has positional anchors (but not EndAnchor), allow partial matches
            // Otherwise, require full string consumption
            if self.has_start_anchor_only() {
                // Anchored pattern - match succeeds if pattern matches at the position
                true
            } else {
                // Non-anchored pattern - must consume entire string
                m.end == text.len()
            }
        } else {
            false
        }
    }

    /// Check if pattern has positional constraints that allow partial matches
    fn has_start_anchor_only(&self) -> bool {
        let has_positional = self.contains_start_anchor() || self.contains_lookahead();
        let has_end = self.contains_end_anchor();
        has_positional && !has_end
    }

    /// Check if pattern contains lookahead/lookbehind assertions
    fn contains_lookahead(&self) -> bool {
        Self::pattern_has_lookahead(&self.pattern)
    }

    /// Whether the pattern contains any look-around operator.
    ///
    /// Explicit stack, not recursion: the pattern nests as deeply as the
    /// caller builds it, this runs on every `is_match` call, and the return
    /// type is `bool` — a depth cap could only answer "no look-around" for a
    /// pattern that has one, which silently changes how it is matched.
    fn pattern_has_lookahead(regex: &AdvancedRegex) -> bool {
        Self::pattern_contains(regex, |node| {
            matches!(
                node,
                AdvancedRegex::LookaheadPos(_)
                    | AdvancedRegex::LookaheadNeg(_)
                    | AdvancedRegex::LookbehindPos(_)
                    | AdvancedRegex::LookbehindNeg(_)
            )
        })
    }

    /// Whether any node reachable through `Concat`/`Alt`/`Group`/`Capture`
    /// satisfies `predicate`. This is the shared driver behind the three
    /// `pattern_has_*` probes; the set of operators it descends through is
    /// exactly the set the recursive versions descended through.
    fn pattern_contains(regex: &AdvancedRegex, predicate: impl Fn(&AdvancedRegex) -> bool) -> bool {
        let mut stack: Vec<&AdvancedRegex> = vec![regex];
        while let Some(node) = stack.pop() {
            if predicate(node) {
                return true;
            }
            match node {
                AdvancedRegex::Concat(parts) | AdvancedRegex::Alt(parts) => {
                    stack.extend(parts.iter().rev());
                }
                AdvancedRegex::Group(inner) | AdvancedRegex::Capture(inner, _) => {
                    stack.push(inner);
                }
                _ => {}
            }
        }
        false
    }

    /// Check if pattern contains StartAnchor
    fn contains_start_anchor(&self) -> bool {
        match self.pattern {
            AdvancedRegex::StartAnchor => true,
            AdvancedRegex::Concat(ref parts) => parts.iter().any(Self::pattern_has_start_anchor),
            _ => Self::pattern_has_start_anchor(&self.pattern),
        }
    }

    /// Check if pattern contains EndAnchor
    fn contains_end_anchor(&self) -> bool {
        match self.pattern {
            AdvancedRegex::EndAnchor => true,
            AdvancedRegex::Concat(ref parts) => parts.iter().any(Self::pattern_has_end_anchor),
            _ => Self::pattern_has_end_anchor(&self.pattern),
        }
    }

    /// Iterative for the same reason as [`Self::pattern_has_lookahead`].
    fn pattern_has_start_anchor(regex: &AdvancedRegex) -> bool {
        Self::pattern_contains(regex, |node| matches!(node, AdvancedRegex::StartAnchor))
    }

    /// Iterative for the same reason as [`Self::pattern_has_lookahead`].
    fn pattern_has_end_anchor(regex: &AdvancedRegex) -> bool {
        Self::pattern_contains(regex, |node| matches!(node, AdvancedRegex::EndAnchor))
    }

    /// Find the first match in the string
    pub fn find(&self, text: &str) -> Option<Match> {
        for i in 0..=text.len() {
            if let Some(m) = self.match_at(text, i) {
                return Some(m);
            }
        }
        None
    }

    /// Find all matches in the string
    pub fn find_all(&self, text: &str) -> Vec<Match> {
        let mut matches = Vec::new();
        let mut pos = 0;

        while pos <= text.len() {
            if let Some(m) = self.match_at(text, pos) {
                pos = m.end.max(pos + 1); // Avoid infinite loop on empty matches
                matches.push(m);
            } else {
                pos += 1;
            }
        }

        matches
    }

    /// Try to match at a specific position
    fn match_at(&self, text: &str, pos: usize) -> Option<Match> {
        let mut state = MatchState::new(text, pos);
        if self.match_regex(&self.pattern, &mut state) {
            Some(Match {
                text: text[pos..state.pos].to_string(),
                start: pos,
                end: state.pos,
                captures: state.captures.clone(),
                named_captures: state.named_captures.clone(),
            })
        } else {
            None
        }
    }
}

/// Regex builder for constructing patterns programmatically
#[derive(Debug)]
pub struct RegexBuilder {
    parts: Vec<AdvancedRegex>,
    next_group: usize,
}

impl RegexBuilder {
    /// Create a new regex builder
    pub fn new() -> Self {
        Self {
            parts: Vec::new(),
            next_group: 1,
        }
    }

    /// Add a literal string
    pub fn literal(mut self, s: &str) -> Self {
        for c in s.chars() {
            self.parts.push(AdvancedRegex::Char(c));
        }
        self
    }

    /// Add a character class
    pub fn class(mut self, cls: CharacterClass) -> Self {
        self.parts.push(AdvancedRegex::Class(cls));
        self
    }

    /// Add any character (.)
    pub fn any(mut self) -> Self {
        self.parts.push(AdvancedRegex::AnyChar);
        self
    }

    /// Add a digit class (\d)
    pub fn digit(mut self) -> Self {
        self.parts
            .push(AdvancedRegex::Class(CharacterClass::digit()));
        self
    }

    /// Add a word class (\w)
    pub fn word(mut self) -> Self {
        self.parts
            .push(AdvancedRegex::Class(CharacterClass::word()));
        self
    }

    /// Add a whitespace class (\s)
    pub fn whitespace(mut self) -> Self {
        self.parts
            .push(AdvancedRegex::Class(CharacterClass::whitespace()));
        self
    }

    /// Add a capturing group
    pub fn capture(mut self, inner: AdvancedRegex) -> Self {
        let group = CaptureGroup::numbered(self.next_group);
        self.next_group += 1;
        self.parts
            .push(AdvancedRegex::Capture(Box::new(inner), group));
        self
    }

    /// Add a named capturing group
    pub fn named_capture(mut self, name: &str, inner: AdvancedRegex) -> Self {
        let group = CaptureGroup::named(self.next_group, name.to_string());
        self.next_group += 1;
        self.parts
            .push(AdvancedRegex::Capture(Box::new(inner), group));
        self
    }

    /// Add zero or more (*)
    pub fn star(mut self, inner: AdvancedRegex) -> Self {
        self.parts.push(AdvancedRegex::Star(Box::new(inner)));
        self
    }

    /// Add one or more (+)
    pub fn plus(mut self, inner: AdvancedRegex) -> Self {
        self.parts.push(AdvancedRegex::Plus(Box::new(inner)));
        self
    }

    /// Add optional (?)
    pub fn optional(mut self, inner: AdvancedRegex) -> Self {
        self.parts.push(AdvancedRegex::Optional(Box::new(inner)));
        self
    }

    /// Add alternation (|)
    pub fn alt(mut self, branches: Vec<AdvancedRegex>) -> Self {
        self.parts.push(AdvancedRegex::Alt(branches));
        self
    }

    /// Add start anchor (^)
    pub fn start_anchor(mut self) -> Self {
        self.parts.push(AdvancedRegex::StartAnchor);
        self
    }

    /// Add end anchor ($)
    pub fn end_anchor(mut self) -> Self {
        self.parts.push(AdvancedRegex::EndAnchor);
        self
    }

    /// Build the final regex
    pub fn build(mut self) -> AdvancedRegex {
        if self.parts.len() == 1 {
            // `pop` on a length-1 vec always yields the element; the fallback
            // exists so the impossible case is not written as an `expect`, and
            // returns exactly what the empty case returns.
            return self.parts.pop().unwrap_or(AdvancedRegex::Empty);
        }
        if self.parts.is_empty() {
            AdvancedRegex::Empty
        } else {
            AdvancedRegex::Concat(self.parts)
        }
    }
}

impl Default for RegexBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// One pending piece of a rendered pattern.
enum RegexRender<'a> {
    /// A sub-pattern still to be expanded.
    Node(&'a AdvancedRegex),
    /// Borrowed literal text.
    Text(&'a str),
    /// Text built for one node (repetition counts, group names, ...).
    Owned(String),
}

/// Dismantling worklist entry: one owned operand awaiting its own dismantling.
enum RegexDropNode {
    /// A boxed operand.
    Boxed(Box<AdvancedRegex>),
    /// A list of operands.
    List(Vec<AdvancedRegex>),
    /// A condition, which may itself hold a boxed operand.
    Cond(Condition),
}

/// A childless stand-in, dropped immediately and never observed.
fn regex_placeholder() -> Box<AdvancedRegex> {
    Box::new(AdvancedRegex::Empty)
}

/// Move `regex`'s operands onto `out`, leaving a childless node behind.
///
/// Operands are swapped out one field at a time: [`AdvancedRegex`] implements
/// [`Drop`], so its fields cannot be moved out wholesale.
fn take_regex_children(regex: &mut AdvancedRegex, out: &mut Vec<RegexDropNode>) {
    match regex {
        AdvancedRegex::Empty
        | AdvancedRegex::Char(_)
        | AdvancedRegex::Class(_)
        | AdvancedRegex::AnyChar
        | AdvancedRegex::Backref(_)
        | AdvancedRegex::NamedBackref(_)
        | AdvancedRegex::StartAnchor
        | AdvancedRegex::EndAnchor
        | AdvancedRegex::WordBoundary
        | AdvancedRegex::NonWordBoundary => {}
        AdvancedRegex::Concat(parts) | AdvancedRegex::Alt(parts) => {
            out.push(RegexDropNode::List(core::mem::take(parts)));
        }
        AdvancedRegex::Star(inner)
        | AdvancedRegex::Plus(inner)
        | AdvancedRegex::Optional(inner)
        | AdvancedRegex::Repeat(inner, _)
        | AdvancedRegex::RepeatRange(inner, _, _)
        | AdvancedRegex::StarLazy(inner)
        | AdvancedRegex::PlusLazy(inner)
        | AdvancedRegex::OptionalLazy(inner)
        | AdvancedRegex::StarPossessive(inner)
        | AdvancedRegex::PlusPossessive(inner)
        | AdvancedRegex::OptionalPossessive(inner)
        | AdvancedRegex::Capture(inner, _)
        | AdvancedRegex::Group(inner)
        | AdvancedRegex::LookaheadPos(inner)
        | AdvancedRegex::LookaheadNeg(inner)
        | AdvancedRegex::LookbehindPos(inner)
        | AdvancedRegex::LookbehindNeg(inner)
        | AdvancedRegex::Atomic(inner) => {
            out.push(RegexDropNode::Boxed(core::mem::replace(
                inner,
                regex_placeholder(),
            )));
        }
        AdvancedRegex::Conditional {
            condition,
            yes_branch,
            no_branch,
        } => {
            out.push(RegexDropNode::Cond(core::mem::replace(
                condition,
                Condition::GroupExists(0),
            )));
            out.push(RegexDropNode::Boxed(core::mem::replace(
                yes_branch,
                regex_placeholder(),
            )));
            if let Some(branch) = no_branch.take() {
                out.push(RegexDropNode::Boxed(branch));
            }
        }
    }
}

impl Drop for AdvancedRegex {
    /// Dismantle the operand tree iteratively.
    ///
    /// Compiler-generated drop glue recurses once per nesting level, so a
    /// pattern deep enough to build is deep enough to abort the process at
    /// scope exit, after it has already been matched against successfully.
    fn drop(&mut self) {
        let mut worklist: Vec<RegexDropNode> = Vec::new();
        take_regex_children(self, &mut worklist);
        while let Some(node) = worklist.pop() {
            match node {
                RegexDropNode::Boxed(mut inner) => take_regex_children(&mut inner, &mut worklist),
                RegexDropNode::List(parts) => {
                    for mut part in parts {
                        take_regex_children(&mut part, &mut worklist);
                    }
                }
                RegexDropNode::Cond(condition) => {
                    if let Condition::Lookahead(inner) = condition {
                        worklist.push(RegexDropNode::Boxed(inner));
                    }
                }
            }
        }
    }
}

/// The shape of a node being rebuilt by the iterative [`Clone`] impl: which
/// variant it is, plus anything that is not one of the cloned children.
enum RegexCloneShape {
    /// `Concat` with the given arity.
    Concat(usize),
    /// `Alt` with the given arity.
    Alt(usize),
    /// `Star`, one child.
    Star,
    /// `Plus`, one child.
    Plus,
    /// `Optional`, one child.
    Optional,
    /// `Repeat`, one child plus its exact count.
    Repeat(usize),
    /// `RepeatRange`, one child plus its bounds.
    RepeatRange(usize, Option<usize>),
    /// `StarLazy`, one child.
    StarLazy,
    /// `PlusLazy`, one child.
    PlusLazy,
    /// `OptionalLazy`, one child.
    OptionalLazy,
    /// `StarPossessive`, one child.
    StarPossessive,
    /// `PlusPossessive`, one child.
    PlusPossessive,
    /// `OptionalPossessive`, one child.
    OptionalPossessive,
    /// `Capture`, one child plus its group info.
    Capture(CaptureGroup),
    /// `Group`, one child.
    Group,
    /// `LookaheadPos`, one child.
    LookaheadPos,
    /// `LookaheadNeg`, one child.
    LookaheadNeg,
    /// `LookbehindPos`, one child.
    LookbehindPos,
    /// `LookbehindNeg`, one child.
    LookbehindNeg,
    /// `Atomic`, one child.
    Atomic,
    /// `Conditional`. See [`ConditionCloneLeaf`] for how its condition is
    /// carried.
    Conditional {
        /// The non-regex part of the condition, or `None` when the
        /// condition is a [`Condition::Lookahead`] (whose regex was queued
        /// on the worklist like any other child instead).
        condition_leaf: Option<ConditionCloneLeaf>,
        /// Whether a `no_branch` operand was queued.
        has_no_branch: bool,
    },
}

/// A [`Condition`] variant that carries no [`AdvancedRegex`] operand, so it
/// can be cloned as plain data rather than through the worklist.
enum ConditionCloneLeaf {
    /// [`Condition::GroupExists`]
    GroupExists(usize),
    /// [`Condition::NamedGroupExists`]
    NamedGroupExists(String),
}

/// Work item for the iterative [`Clone`] impl.
enum RegexCloneTask<'a> {
    /// Clone this subterm.
    Visit(&'a AdvancedRegex),
    /// Rebuild a node from the already-cloned children on the result stack.
    Rebuild(RegexCloneShape),
}

impl Clone for AdvancedRegex {
    /// Iterative clone.
    ///
    /// The derived recursive `Clone` walked the operand tree with one native
    /// call frame per nesting level -- the same hazard the [`Drop`] impl
    /// above exists to avoid, just triggered by a different standard-library
    /// entry point (`.clone()` / `#[derive(Clone)]` callers).
    /// [`Condition`]'s own derived `Clone` is bypassed for its `Lookahead`
    /// case for the same reason `Drop` bypasses it: that variant embeds
    /// another `AdvancedRegex`, so cloning it through `Condition::clone`
    /// would reintroduce native recursion, one level per
    /// `Conditional`/`Lookahead` alternation.
    fn clone(&self) -> Self {
        /// Detach the top `n` results, preserving their original order.
        fn take(results: &mut Vec<AdvancedRegex>, n: usize) -> Vec<AdvancedRegex> {
            let start = results.len().saturating_sub(n);
            results.split_off(start)
        }

        /// Rebuild a one-child node, or fall back to `Empty` if starved.
        fn one(results: &mut Vec<AdvancedRegex>) -> Box<AdvancedRegex> {
            let mut operand = take(results, 1);
            Box::new(operand.pop().unwrap_or(AdvancedRegex::Empty))
        }

        let mut tasks = vec![RegexCloneTask::Visit(self)];
        let mut results: Vec<Self> = Vec::new();

        while let Some(task) = tasks.pop() {
            match task {
                RegexCloneTask::Visit(node) => match node {
                    Self::Empty => results.push(Self::Empty),
                    Self::Char(c) => results.push(Self::Char(*c)),
                    Self::Class(cls) => results.push(Self::Class(cls.clone())),
                    Self::AnyChar => results.push(Self::AnyChar),
                    Self::Concat(parts) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::Concat(
                            parts.len(),
                        )));
                        tasks.extend(parts.iter().rev().map(RegexCloneTask::Visit));
                    }
                    Self::Alt(parts) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::Alt(parts.len())));
                        tasks.extend(parts.iter().rev().map(RegexCloneTask::Visit));
                    }
                    Self::Star(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::Star));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::Plus(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::Plus));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::Optional(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::Optional));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::Repeat(inner, n) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::Repeat(*n)));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::RepeatRange(inner, min, max) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::RepeatRange(
                            *min, *max,
                        )));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::StarLazy(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::StarLazy));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::PlusLazy(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::PlusLazy));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::OptionalLazy(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::OptionalLazy));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::StarPossessive(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::StarPossessive));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::PlusPossessive(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::PlusPossessive));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::OptionalPossessive(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::OptionalPossessive));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::Capture(inner, group) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::Capture(
                            group.clone(),
                        )));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::Group(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::Group));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::Backref(n) => results.push(Self::Backref(*n)),
                    Self::NamedBackref(name) => results.push(Self::NamedBackref(name.clone())),
                    Self::LookaheadPos(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::LookaheadPos));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::LookaheadNeg(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::LookaheadNeg));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::LookbehindPos(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::LookbehindPos));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::LookbehindNeg(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::LookbehindNeg));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::Atomic(inner) => {
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::Atomic));
                        tasks.push(RegexCloneTask::Visit(inner));
                    }
                    Self::Conditional {
                        condition,
                        yes_branch,
                        no_branch,
                    } => {
                        let condition_leaf = match condition {
                            Condition::GroupExists(n) => Some(ConditionCloneLeaf::GroupExists(*n)),
                            Condition::NamedGroupExists(name) => {
                                Some(ConditionCloneLeaf::NamedGroupExists(name.clone()))
                            }
                            Condition::Lookahead(_) => None,
                        };
                        let has_no_branch = no_branch.is_some();
                        tasks.push(RegexCloneTask::Rebuild(RegexCloneShape::Conditional {
                            condition_leaf,
                            has_no_branch,
                        }));
                        if let Some(no) = no_branch {
                            tasks.push(RegexCloneTask::Visit(no));
                        }
                        tasks.push(RegexCloneTask::Visit(yes_branch));
                        if let Condition::Lookahead(inner) = condition {
                            tasks.push(RegexCloneTask::Visit(inner));
                        }
                    }
                    Self::StartAnchor => results.push(Self::StartAnchor),
                    Self::EndAnchor => results.push(Self::EndAnchor),
                    Self::WordBoundary => results.push(Self::WordBoundary),
                    Self::NonWordBoundary => results.push(Self::NonWordBoundary),
                },
                RegexCloneTask::Rebuild(shape) => {
                    let rebuilt = match shape {
                        RegexCloneShape::Concat(n) => Self::Concat(take(&mut results, n)),
                        RegexCloneShape::Alt(n) => Self::Alt(take(&mut results, n)),
                        RegexCloneShape::Star => Self::Star(one(&mut results)),
                        RegexCloneShape::Plus => Self::Plus(one(&mut results)),
                        RegexCloneShape::Optional => Self::Optional(one(&mut results)),
                        RegexCloneShape::Repeat(n) => Self::Repeat(one(&mut results), n),
                        RegexCloneShape::RepeatRange(min, max) => {
                            Self::RepeatRange(one(&mut results), min, max)
                        }
                        RegexCloneShape::StarLazy => Self::StarLazy(one(&mut results)),
                        RegexCloneShape::PlusLazy => Self::PlusLazy(one(&mut results)),
                        RegexCloneShape::OptionalLazy => Self::OptionalLazy(one(&mut results)),
                        RegexCloneShape::StarPossessive => Self::StarPossessive(one(&mut results)),
                        RegexCloneShape::PlusPossessive => Self::PlusPossessive(one(&mut results)),
                        RegexCloneShape::OptionalPossessive => {
                            Self::OptionalPossessive(one(&mut results))
                        }
                        RegexCloneShape::Capture(group) => Self::Capture(one(&mut results), group),
                        RegexCloneShape::Group => Self::Group(one(&mut results)),
                        RegexCloneShape::LookaheadPos => Self::LookaheadPos(one(&mut results)),
                        RegexCloneShape::LookaheadNeg => Self::LookaheadNeg(one(&mut results)),
                        RegexCloneShape::LookbehindPos => Self::LookbehindPos(one(&mut results)),
                        RegexCloneShape::LookbehindNeg => Self::LookbehindNeg(one(&mut results)),
                        RegexCloneShape::Atomic => Self::Atomic(one(&mut results)),
                        RegexCloneShape::Conditional {
                            condition_leaf,
                            has_no_branch,
                        } => {
                            let condition_regex_pushed = condition_leaf.is_none();
                            let count = usize::from(condition_regex_pushed)
                                + 1
                                + usize::from(has_no_branch);
                            let mut operands = take(&mut results, count).into_iter();
                            let condition = match condition_leaf {
                                Some(ConditionCloneLeaf::GroupExists(n)) => {
                                    Condition::GroupExists(n)
                                }
                                Some(ConditionCloneLeaf::NamedGroupExists(name)) => {
                                    Condition::NamedGroupExists(name)
                                }
                                None => {
                                    let inner = operands.next().unwrap_or(AdvancedRegex::Empty);
                                    Condition::Lookahead(Box::new(inner))
                                }
                            };
                            let yes_branch =
                                Box::new(operands.next().unwrap_or(AdvancedRegex::Empty));
                            let no_branch = if has_no_branch {
                                Some(Box::new(operands.next().unwrap_or(AdvancedRegex::Empty)))
                            } else {
                                None
                            };
                            Self::Conditional {
                                condition,
                                yes_branch,
                                no_branch,
                            }
                        }
                    };
                    results.push(rebuilt);
                }
            }
        }

        results.pop().unwrap_or(Self::Empty)
    }
}

impl PartialEq for AdvancedRegex {
    /// Iterative structural equality.
    ///
    /// The derived `PartialEq` walked both patterns with one native call
    /// frame per nesting level, mirroring the [`Clone`]/[`Drop`] hazard
    /// above. The pairs still to be compared live on the heap instead; the
    /// relation itself is unchanged. As in `InterpolantTerm`
    /// (`oxiz-proof/src/craig/term.rs`), the outer `match` is exhaustive over
    /// `self`'s variants on purpose: a new variant is a compile error here,
    /// not a silent "not equal".
    ///
    /// `Condition::Lookahead`'s embedded regex is compared through the same
    /// worklist rather than via `Condition`'s own derived `PartialEq`, for
    /// the same reason [`Clone`] bypasses it.
    fn eq(&self, other: &Self) -> bool {
        /// Queue every positional child pair, left to right.
        fn push_all<'a>(
            worklist: &mut Vec<(&'a AdvancedRegex, &'a AdvancedRegex)>,
            lhs: &'a [AdvancedRegex],
            rhs: &'a [AdvancedRegex],
        ) {
            worklist.extend(lhs.iter().zip(rhs.iter()).rev());
        }

        let mut worklist = vec![(self, other)];

        while let Some((a, b)) = worklist.pop() {
            match a {
                Self::Empty => {
                    if !matches!(b, Self::Empty) {
                        return false;
                    }
                }
                Self::Char(x) => {
                    let Self::Char(y) = b else { return false };
                    if x != y {
                        return false;
                    }
                }
                Self::Class(x) => {
                    let Self::Class(y) = b else { return false };
                    if x != y {
                        return false;
                    }
                }
                Self::AnyChar => {
                    if !matches!(b, Self::AnyChar) {
                        return false;
                    }
                }
                Self::Concat(xs) => {
                    let Self::Concat(ys) = b else { return false };
                    if xs.len() != ys.len() {
                        return false;
                    }
                    push_all(&mut worklist, xs, ys);
                }
                Self::Alt(xs) => {
                    let Self::Alt(ys) = b else { return false };
                    if xs.len() != ys.len() {
                        return false;
                    }
                    push_all(&mut worklist, xs, ys);
                }
                Self::Star(x) => {
                    let Self::Star(y) = b else { return false };
                    worklist.push((x, y));
                }
                Self::Plus(x) => {
                    let Self::Plus(y) = b else { return false };
                    worklist.push((x, y));
                }
                Self::Optional(x) => {
                    let Self::Optional(y) = b else { return false };
                    worklist.push((x, y));
                }
                Self::Repeat(x, n) => {
                    let Self::Repeat(y, m) = b else { return false };
                    if n != m {
                        return false;
                    }
                    worklist.push((x, y));
                }
                Self::RepeatRange(x, min1, max1) => {
                    let Self::RepeatRange(y, min2, max2) = b else {
                        return false;
                    };
                    if min1 != min2 || max1 != max2 {
                        return false;
                    }
                    worklist.push((x, y));
                }
                Self::StarLazy(x) => {
                    let Self::StarLazy(y) = b else { return false };
                    worklist.push((x, y));
                }
                Self::PlusLazy(x) => {
                    let Self::PlusLazy(y) = b else { return false };
                    worklist.push((x, y));
                }
                Self::OptionalLazy(x) => {
                    let Self::OptionalLazy(y) = b else {
                        return false;
                    };
                    worklist.push((x, y));
                }
                Self::StarPossessive(x) => {
                    let Self::StarPossessive(y) = b else {
                        return false;
                    };
                    worklist.push((x, y));
                }
                Self::PlusPossessive(x) => {
                    let Self::PlusPossessive(y) = b else {
                        return false;
                    };
                    worklist.push((x, y));
                }
                Self::OptionalPossessive(x) => {
                    let Self::OptionalPossessive(y) = b else {
                        return false;
                    };
                    worklist.push((x, y));
                }
                Self::Capture(x, g1) => {
                    let Self::Capture(y, g2) = b else {
                        return false;
                    };
                    if g1 != g2 {
                        return false;
                    }
                    worklist.push((x, y));
                }
                Self::Group(x) => {
                    let Self::Group(y) = b else { return false };
                    worklist.push((x, y));
                }
                Self::Backref(n) => {
                    let Self::Backref(m) = b else { return false };
                    if n != m {
                        return false;
                    }
                }
                Self::NamedBackref(n) => {
                    let Self::NamedBackref(m) = b else {
                        return false;
                    };
                    if n != m {
                        return false;
                    }
                }
                Self::LookaheadPos(x) => {
                    let Self::LookaheadPos(y) = b else {
                        return false;
                    };
                    worklist.push((x, y));
                }
                Self::LookaheadNeg(x) => {
                    let Self::LookaheadNeg(y) = b else {
                        return false;
                    };
                    worklist.push((x, y));
                }
                Self::LookbehindPos(x) => {
                    let Self::LookbehindPos(y) = b else {
                        return false;
                    };
                    worklist.push((x, y));
                }
                Self::LookbehindNeg(x) => {
                    let Self::LookbehindNeg(y) = b else {
                        return false;
                    };
                    worklist.push((x, y));
                }
                Self::Atomic(x) => {
                    let Self::Atomic(y) = b else { return false };
                    worklist.push((x, y));
                }
                Self::Conditional {
                    condition: c1,
                    yes_branch: y1,
                    no_branch: n1,
                } => {
                    let Self::Conditional {
                        condition: c2,
                        yes_branch: y2,
                        no_branch: n2,
                    } = b
                    else {
                        return false;
                    };
                    match (c1, c2) {
                        (Condition::GroupExists(a1), Condition::GroupExists(b1)) => {
                            if a1 != b1 {
                                return false;
                            }
                        }
                        (Condition::NamedGroupExists(a1), Condition::NamedGroupExists(b1)) => {
                            if a1 != b1 {
                                return false;
                            }
                        }
                        (Condition::Lookahead(a1), Condition::Lookahead(b1)) => {
                            worklist.push((a1, b1));
                        }
                        _ => return false,
                    }
                    match (n1, n2) {
                        (Some(a1), Some(b1)) => worklist.push((a1, b1)),
                        (None, None) => {}
                        _ => return false,
                    }
                    worklist.push((y1, y2));
                }
                Self::StartAnchor => {
                    if !matches!(b, Self::StartAnchor) {
                        return false;
                    }
                }
                Self::EndAnchor => {
                    if !matches!(b, Self::EndAnchor) {
                        return false;
                    }
                }
                Self::WordBoundary => {
                    if !matches!(b, Self::WordBoundary) {
                        return false;
                    }
                }
                Self::NonWordBoundary => {
                    if !matches!(b, Self::NonWordBoundary) {
                        return false;
                    }
                }
            }
        }

        true
    }
}

impl Eq for AdvancedRegex {}

/// Wrap `inner` as `prefix inner suffix` on the render stack.
fn push_wrapped<'a>(
    stack: &mut Vec<RegexRender<'a>>,
    prefix: RegexRender<'a>,
    inner: &'a AdvancedRegex,
    suffix: RegexRender<'a>,
) {
    stack.push(suffix);
    stack.push(RegexRender::Node(inner));
    stack.push(prefix);
}

impl fmt::Display for AdvancedRegex {
    /// Render the pattern using an explicit stack.
    ///
    /// `write!(f, "{}", inner)` recurses once per nesting level, and the
    /// return type (`fmt::Result`) has no "too deep" variant to report -- so a
    /// pattern that builds and matches fine would abort the process when
    /// formatted, e.g. by a `Debug`-printing assertion.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut stack: Vec<RegexRender<'_>> = vec![RegexRender::Node(self)];

        while let Some(item) = stack.pop() {
            let node = match item {
                RegexRender::Text(text) => {
                    f.write_str(text)?;
                    continue;
                }
                RegexRender::Owned(text) => {
                    f.write_str(&text)?;
                    continue;
                }
                RegexRender::Node(node) => node,
            };

            match node {
                AdvancedRegex::Empty => f.write_str("ε")?,
                AdvancedRegex::Char(c) => write!(f, "{}", c)?,
                AdvancedRegex::Class(_) => f.write_str("[...]")?,
                AdvancedRegex::AnyChar => f.write_str(".")?,
                AdvancedRegex::Concat(parts) => {
                    stack.extend(parts.iter().rev().map(RegexRender::Node));
                }
                AdvancedRegex::Alt(branches) => {
                    for (i, branch) in branches.iter().enumerate().rev() {
                        stack.push(RegexRender::Node(branch));
                        if i > 0 {
                            stack.push(RegexRender::Text("|"));
                        }
                    }
                }
                AdvancedRegex::Star(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("("),
                        inner,
                        RegexRender::Text(")*"),
                    );
                }
                AdvancedRegex::Plus(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("("),
                        inner,
                        RegexRender::Text(")+"),
                    );
                }
                AdvancedRegex::Optional(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("("),
                        inner,
                        RegexRender::Text(")?"),
                    );
                }
                AdvancedRegex::Repeat(inner, n) => {
                    let suffix = RegexRender::Owned(format!("){{{}}}", n));
                    push_wrapped(&mut stack, RegexRender::Text("("), inner, suffix);
                }
                AdvancedRegex::RepeatRange(inner, min, max) => {
                    let suffix = match max {
                        Some(m) => RegexRender::Owned(format!("){{{},{}}}", min, m)),
                        None => RegexRender::Owned(format!("){{{},}}", min)),
                    };
                    push_wrapped(&mut stack, RegexRender::Text("("), inner, suffix);
                }
                AdvancedRegex::StarLazy(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("("),
                        inner,
                        RegexRender::Text(")*?"),
                    );
                }
                AdvancedRegex::PlusLazy(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("("),
                        inner,
                        RegexRender::Text(")+?"),
                    );
                }
                AdvancedRegex::OptionalLazy(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("("),
                        inner,
                        RegexRender::Text(")??"),
                    );
                }
                AdvancedRegex::StarPossessive(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("("),
                        inner,
                        RegexRender::Text(")*+"),
                    );
                }
                AdvancedRegex::PlusPossessive(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("("),
                        inner,
                        RegexRender::Text(")++"),
                    );
                }
                AdvancedRegex::OptionalPossessive(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("("),
                        inner,
                        RegexRender::Text(")?+"),
                    );
                }
                AdvancedRegex::Capture(inner, group) => {
                    let prefix = match &group.name {
                        Some(name) => RegexRender::Owned(format!("(?<{}>", name)),
                        None => RegexRender::Text("("),
                    };
                    push_wrapped(&mut stack, prefix, inner, RegexRender::Text(")"));
                }
                AdvancedRegex::Group(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("(?:"),
                        inner,
                        RegexRender::Text(")"),
                    );
                }
                AdvancedRegex::Backref(n) => write!(f, "\\{}", n)?,
                AdvancedRegex::NamedBackref(name) => write!(f, "\\k<{}>", name)?,
                AdvancedRegex::LookaheadPos(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("(?="),
                        inner,
                        RegexRender::Text(")"),
                    );
                }
                AdvancedRegex::LookaheadNeg(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("(?!"),
                        inner,
                        RegexRender::Text(")"),
                    );
                }
                AdvancedRegex::LookbehindPos(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("(?<="),
                        inner,
                        RegexRender::Text(")"),
                    );
                }
                AdvancedRegex::LookbehindNeg(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("(?<!"),
                        inner,
                        RegexRender::Text(")"),
                    );
                }
                AdvancedRegex::Atomic(inner) => {
                    push_wrapped(
                        &mut stack,
                        RegexRender::Text("(?>>"),
                        inner,
                        RegexRender::Text(")"),
                    );
                }
                AdvancedRegex::Conditional { .. } => f.write_str("(?(...)...)")?,
                AdvancedRegex::StartAnchor => f.write_str("^")?,
                AdvancedRegex::EndAnchor => f.write_str("$")?,
                AdvancedRegex::WordBoundary => f.write_str("\\b")?,
                AdvancedRegex::NonWordBoundary => f.write_str("\\B")?,
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The stack the small-stack regressions below run on: a scaled-down model
    /// of an embedder's worker thread.
    ///
    /// This constant and [`DEEP_NESTING`] are scaled **together**, and only
    /// their ratio -- about 21 bytes of stack per nesting level -- decides what
    /// those tests detect. A recursive walk needs tens of bytes per frame at
    /// the very least, so it still overflows; an iterative one uses O(1) native
    /// stack, so it still returns. Never raise one without the other.
    const WORKER_STACK: usize = 1 << 17;

    /// Nesting depth paired with [`WORKER_STACK`].
    const DEEP_NESTING: usize = 6_250;

    /// Build `Group(Group(... Char(c) ...))` nested `depth` levels deep.
    fn nested_groups(depth: usize, c: char) -> AdvancedRegex {
        let mut regex = AdvancedRegex::Char(c);
        for _ in 0..depth {
            regex = AdvancedRegex::Group(Box::new(regex));
        }
        regex
    }

    #[test]
    fn test_match_deeply_nested_pattern_small_stack() {
        // `match_regex` used to recurse once per nesting level of a
        // caller-supplied pattern, and its return type is a bare `bool` -- a
        // depth cap could only report "no match" for a pattern that matches.
        // Run on a deliberately small (128 KiB) stack: a stack overflow aborts
        // the process, so "the thread returned at all" is part of the
        // assertion. Dropping the pattern afterwards exercises the iterative
        // `Drop`, and formatting it exercises the iterative `Display`.
        let handle = std::thread::Builder::new()
            .stack_size(WORKER_STACK)
            .spawn(|| {
                let depth = DEEP_NESTING;

                let rendered = nested_groups(depth, 'a').to_string();
                assert!(rendered.starts_with("(?:(?:"));
                assert!(rendered.ends_with("))"));
                assert_eq!(rendered.matches('a').count(), 1);

                let matcher = RegexMatcher::new(nested_groups(depth, 'a'));
                assert!(matcher.is_match("a"));
                assert!(!matcher.is_match("b"));
            })
            .expect("spawning a thread with an explicit stack size must succeed");
        handle
            .join()
            .expect("a deeply nested regex must not overflow a 128 KiB stack");
    }

    #[test]
    fn test_deeply_nested_pattern_drop_small_stack() {
        // Compiler-generated drop glue recurses once per level; the explicit
        // `Drop` dismantles the tree with a worklist instead.
        let handle = std::thread::Builder::new()
            .stack_size(WORKER_STACK)
            .spawn(|| {
                let regex = AdvancedRegex::Alt(vec![
                    nested_groups(DEEP_NESTING, 'a'),
                    AdvancedRegex::Star(Box::new(nested_groups(DEEP_NESTING, 'b'))),
                ]);
                drop(regex);
            })
            .expect("spawning a thread with an explicit stack size must succeed");
        handle
            .join()
            .expect("dropping a deeply nested regex must not overflow a 128 KiB stack");
    }

    #[test]
    fn test_conditional_lookahead_condition_does_not_leak_state() {
        // Semantic pin for the machine's temp-state handling: the conditional's
        // look-ahead runs on a throwaway copy, so the branch it selects starts
        // from the outer position and sees no captures from the condition.
        let regex = AdvancedRegex::Conditional {
            condition: Condition::Lookahead(Box::new(AdvancedRegex::Char('a'))),
            yes_branch: Box::new(AdvancedRegex::Concat(vec![
                AdvancedRegex::Char('a'),
                AdvancedRegex::Char('b'),
            ])),
            no_branch: Some(Box::new(AdvancedRegex::Char('z'))),
        };
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match("ab"));
        assert!(!matcher.is_match("b"));

        let no_branch_only = RegexMatcher::new(AdvancedRegex::Conditional {
            condition: Condition::GroupExists(1),
            yes_branch: Box::new(AdvancedRegex::Char('a')),
            no_branch: Some(Box::new(AdvancedRegex::Char('z'))),
        });
        assert!(no_branch_only.is_match("z"));
    }

    #[test]
    fn test_repeat_range_reversed_bounds_still_matches_minimum() {
        // `{5,2}` is writable; the optional-repetition count saturates to zero
        // instead of wrapping, and the mandatory five still have to match.
        let regex = AdvancedRegex::RepeatRange(Box::new(AdvancedRegex::Char('a')), 5, Some(2));
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match("aaaaa"));
        assert!(!matcher.is_match("aaa"));
    }

    #[test]
    fn test_star_over_empty_matching_body_terminates() {
        // `(x{0})*` matches the empty string forever; the greedy loop stops as
        // soon as an iteration consumes nothing.
        let regex = AdvancedRegex::Star(Box::new(AdvancedRegex::Repeat(
            Box::new(AdvancedRegex::Char('x')),
            0,
        )));
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match(""));
    }

    #[test]
    fn test_repeat_range_unbounded_over_empty_matching_body_terminates() {
        // `{0,}` (an unbounded `max`) sets the optional-repetition count to
        // `usize::MAX`; a body that matches the empty string used to loop
        // that many times instead of failing or advancing. The same
        // empty-progress guard the greedy `Star` loop already has now applies
        // to the `RepeatRange` "extra" phase too, so this must terminate
        // (and still report a match, since zero-width repetition adds
        // nothing either way).
        let empty_body = AdvancedRegex::Repeat(Box::new(AdvancedRegex::Char('x')), 0);
        let regex = AdvancedRegex::RepeatRange(Box::new(empty_body), 0, None);
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match(""));

        // Same shape via `Star` of an empty literal, and with a non-empty
        // mandatory minimum in front of the unbounded optional phase.
        let star_empty = AdvancedRegex::Star(Box::new(AdvancedRegex::Repeat(
            Box::new(AdvancedRegex::Char('y')),
            0,
        )));
        let with_min = AdvancedRegex::RepeatRange(Box::new(star_empty), 2, None);
        let matcher = RegexMatcher::new(AdvancedRegex::Concat(vec![
            AdvancedRegex::Char('a'),
            AdvancedRegex::Char('a'),
            with_min,
        ]));
        assert!(matcher.is_match("aa"));
    }

    #[test]
    fn test_deep_clone_eq_and_drop_small_stack() {
        // The derived recursive `Clone`/`PartialEq` were the last remaining
        // native-stack walks over this type once `Drop` was made iterative;
        // both would overflow on a pattern deep enough to build. Run on a
        // deliberately small (128 KiB) stack: a stack overflow aborts the
        // process, so "the thread returned at all" is part of the assertion.
        let handle = std::thread::Builder::new()
            .stack_size(WORKER_STACK)
            .spawn(|| {
                let depth = DEEP_NESTING;
                let regex = nested_groups(depth, 'a');
                let cloned = regex.clone();

                assert_eq!(regex, cloned);

                drop(regex);
                drop(cloned);
            })
            .expect("spawning a thread with an explicit stack size must succeed");
        handle
            .join()
            .expect("cloning, comparing and dropping a deeply nested pattern must not overflow a 128 KiB stack");
    }

    #[test]
    fn test_char_class_digit() {
        let cls = CharacterClass::digit();
        assert!(cls.matches('0'));
        assert!(cls.matches('9'));
        assert!(!cls.matches('a'));
    }

    #[test]
    fn test_char_class_word() {
        let cls = CharacterClass::word();
        assert!(cls.matches('a'));
        assert!(cls.matches('Z'));
        assert!(cls.matches('0'));
        assert!(cls.matches('_'));
        assert!(!cls.matches(' '));
    }

    #[test]
    fn test_char_class_negation() {
        let cls = CharacterClass::digit().negate();
        assert!(!cls.matches('5'));
        assert!(cls.matches('a'));
    }

    #[test]
    fn test_simple_char_match() {
        let regex = AdvancedRegex::Char('a');
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match("a"));
        assert!(!matcher.is_match("b"));
    }

    #[test]
    fn test_concat_match() {
        let regex = AdvancedRegex::Concat(vec![
            AdvancedRegex::Char('a'),
            AdvancedRegex::Char('b'),
            AdvancedRegex::Char('c'),
        ]);
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match("abc"));
        assert!(!matcher.is_match("ab"));
    }

    #[test]
    fn test_alt_match() {
        let regex = AdvancedRegex::Alt(vec![AdvancedRegex::Char('a'), AdvancedRegex::Char('b')]);
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match("a"));
        assert!(matcher.is_match("b"));
        assert!(!matcher.is_match("c"));
    }

    #[test]
    fn test_star_match() {
        let regex = AdvancedRegex::Star(Box::new(AdvancedRegex::Char('a')));
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match(""));
        assert!(matcher.is_match("a"));
        assert!(matcher.is_match("aaa"));
    }

    #[test]
    fn test_plus_match() {
        let regex = AdvancedRegex::Plus(Box::new(AdvancedRegex::Char('a')));
        let matcher = RegexMatcher::new(regex);
        assert!(!matcher.is_match(""));
        assert!(matcher.is_match("a"));
        assert!(matcher.is_match("aaa"));
    }

    #[test]
    fn test_optional_match() {
        let regex = AdvancedRegex::Optional(Box::new(AdvancedRegex::Char('a')));
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match(""));
        assert!(matcher.is_match("a"));
    }

    #[test]
    fn test_capture_group() {
        let regex = AdvancedRegex::Capture(
            Box::new(AdvancedRegex::Concat(vec![
                AdvancedRegex::Char('a'),
                AdvancedRegex::Char('b'),
            ])),
            CaptureGroup::numbered(1),
        );
        let matcher = RegexMatcher::new(regex);
        let m = matcher.find("ab").expect("should match");
        assert_eq!(m.get(0), Some("ab"));
        assert_eq!(m.get(1), Some("ab"));
    }

    #[test]
    fn test_named_capture() {
        let regex = AdvancedRegex::Capture(
            Box::new(AdvancedRegex::Char('x')),
            CaptureGroup::named(1, "test".to_string()),
        );
        let matcher = RegexMatcher::new(regex);
        let m = matcher.find("x").expect("should match");
        assert_eq!(m.name("test"), Some("x"));
    }

    #[test]
    fn test_backreference() {
        let regex = AdvancedRegex::Concat(vec![
            AdvancedRegex::Capture(
                Box::new(AdvancedRegex::Char('a')),
                CaptureGroup::numbered(1),
            ),
            AdvancedRegex::Backref(1),
        ]);
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match("aa"));
        assert!(!matcher.is_match("ab"));
    }

    #[test]
    fn test_lookahead_positive() {
        let regex = AdvancedRegex::Concat(vec![
            AdvancedRegex::Char('a'),
            AdvancedRegex::LookaheadPos(Box::new(AdvancedRegex::Char('b'))),
        ]);
        let matcher = RegexMatcher::new(regex);
        let m = matcher.find("ab");
        assert!(m.is_some());
        let m = m.expect("matched");
        assert_eq!(m.text, "a"); // Lookahead doesn't consume
    }

    #[test]
    fn test_lookahead_negative() {
        let regex = AdvancedRegex::Concat(vec![
            AdvancedRegex::Char('a'),
            AdvancedRegex::LookaheadNeg(Box::new(AdvancedRegex::Char('b'))),
        ]);
        let matcher = RegexMatcher::new(regex);
        assert!(!matcher.is_match("ab"));
        assert!(matcher.is_match("ac"));
    }

    #[test]
    fn test_word_boundary() {
        let regex = AdvancedRegex::Concat(vec![
            AdvancedRegex::WordBoundary,
            AdvancedRegex::Char('a'),
            AdvancedRegex::WordBoundary,
        ]);
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.find("a").is_some());
        assert!(matcher.find(" a ").is_some());
    }

    #[test]
    fn test_start_anchor() {
        let regex =
            AdvancedRegex::Concat(vec![AdvancedRegex::StartAnchor, AdvancedRegex::Char('a')]);
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match("a"));
        assert!(matcher.is_match("abc"));
    }

    #[test]
    fn test_end_anchor() {
        let regex = AdvancedRegex::Concat(vec![AdvancedRegex::Char('a'), AdvancedRegex::EndAnchor]);
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match("a"));
    }

    #[test]
    fn test_repeat_exact() {
        let regex = AdvancedRegex::Repeat(Box::new(AdvancedRegex::Char('a')), 3);
        let matcher = RegexMatcher::new(regex);
        assert!(!matcher.is_match("aa"));
        assert!(matcher.is_match("aaa"));
        assert!(!matcher.is_match("aaaa"));
    }

    #[test]
    fn test_repeat_range() {
        let regex = AdvancedRegex::RepeatRange(Box::new(AdvancedRegex::Char('a')), 2, Some(4));
        let matcher = RegexMatcher::new(regex);
        assert!(!matcher.is_match("a"));
        assert!(matcher.is_match("aa"));
        assert!(matcher.is_match("aaa"));
        assert!(matcher.is_match("aaaa"));
    }

    #[test]
    fn test_unicode_category() {
        let prop = UnicodeProperty::Category(UnicodeCategory::Letter);
        assert!(prop.matches('a'));
        assert!(prop.matches('Z'));
        assert!(!prop.matches('1'));
    }

    #[test]
    fn test_unicode_script() {
        assert!(UnicodeScript::Latin.contains('a'));
        assert!(UnicodeScript::Greek.contains('α'));
        assert!(UnicodeScript::Cyrillic.contains('Б'));
    }

    #[test]
    fn test_binary_property() {
        assert!(BinaryProperty::Alphabetic.matches('a'));
        assert!(BinaryProperty::Lowercase.matches('a'));
        assert!(!BinaryProperty::Lowercase.matches('A'));
    }

    #[test]
    fn test_regex_builder() {
        let regex = RegexBuilder::new()
            .start_anchor()
            .literal("hello")
            .end_anchor()
            .build();

        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match("hello"));
        assert!(!matcher.is_match("hello world"));
    }

    #[test]
    fn test_find_all() {
        let regex = AdvancedRegex::Char('a');
        let matcher = RegexMatcher::new(regex);
        let matches = matcher.find_all("banana");
        assert_eq!(matches.len(), 3);
    }

    #[test]
    fn test_any_char() {
        let regex = AdvancedRegex::AnyChar;
        let matcher = RegexMatcher::new(regex);
        assert!(matcher.is_match("a"));
        assert!(matcher.is_match("1"));
        assert!(matcher.is_match("!"));
        assert!(!matcher.is_match(""));
    }

    #[test]
    fn test_display() {
        let regex = AdvancedRegex::Star(Box::new(AdvancedRegex::Char('a')));
        assert_eq!(format!("{}", regex), "(a)*");
    }
}
