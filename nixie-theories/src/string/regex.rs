//! Regular Expression Engine
//!
//! Implements regular expressions with Brzozowski derivatives for efficient
//! membership testing during SMT solving.

use super::unicode::UnicodeCategory;
#[allow(unused_imports)]
use crate::prelude::*;
use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use smallvec::SmallVec;

/// Regular expression operation kinds
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RegexOp {
    /// Empty string (epsilon)
    Epsilon,
    /// Empty language (no strings)
    None,
    /// Full language (all strings)
    All,
    /// Full character set (any single character)
    AllChar,
    /// Single character literal
    Char(char),
    /// Character range [a-z]
    Range(char, char),
    /// Unicode category (e.g., \p{L} for letters)
    UnicodeClass(UnicodeCategory),
    /// Concatenation of regexes
    Concat(Vec<Arc<Regex>>),
    /// Union of regexes (alternation)
    Union(Vec<Arc<Regex>>),
    /// Intersection of regexes
    Inter(Vec<Arc<Regex>>),
    /// Complement of a regex
    Complement(Arc<Regex>),
    /// Kleene star (zero or more)
    Star(Arc<Regex>),
    /// Kleene plus (one or more)
    Plus(Arc<Regex>),
    /// Optional (zero or one)
    Option(Arc<Regex>),
    /// Bounded loop {min, max}
    Loop(Arc<Regex>, u32, Option<u32>),
}

/// A compiled regular expression
///
/// # Structural hashing is cached, not recomputed
///
/// `Regex` nodes are shared through `Arc`, so the value a user sees as a
/// *tree* is physically a *DAG*. A derived `Hash`/`PartialEq` walks that DAG
/// as if it were a tree and therefore re-visits every shared node once per
/// path that reaches it – exponential in the amount of sharing, on a type that
/// is used as a `FxHashMap` key on the `check_sat` path
/// (`DerivativeCache`). Neither `Hash` nor `PartialEq` has an error channel,
/// so that could not be capped, only removed.
///
/// Each node therefore caches the structural hash of its own subtree,
/// computed once at construction from its children's cached hashes (O(arity),
/// never a walk). [`Hash`] writes that one `u64`; [`PartialEq`] rejects on it
/// before doing any structural work and otherwise compares with an explicit
/// stack. The cache is a pure function of `op`, so equal values still hash
/// equally – the `Hash`/`Eq` contract is preserved.
#[derive(Debug, Clone)]
pub struct Regex {
    /// The operation
    pub op: RegexOp,
    /// Cached nullable status
    nullable: bool,
    /// Cached structural hash of this node's whole subtree.
    subtree_hash: u64,
}

/// Structural-equality rank of an operation; injective over the variants, and
/// the primary key of both [`regex_op_cmp`] and [`subtree_hash_of`].
fn op_rank(op: &RegexOp) -> u8 {
    match op {
        RegexOp::Epsilon => 0,
        RegexOp::None => 1,
        RegexOp::All => 2,
        RegexOp::AllChar => 3,
        RegexOp::Char(_) => 4,
        RegexOp::Range(..) => 5,
        RegexOp::UnicodeClass(_) => 6,
        RegexOp::Concat(_) => 7,
        RegexOp::Union(_) => 8,
        RegexOp::Inter(_) => 9,
        RegexOp::Complement(_) => 10,
        RegexOp::Star(_) => 11,
        RegexOp::Plus(_) => 12,
        RegexOp::Option(_) => 13,
        RegexOp::Loop(..) => 14,
    }
}

/// Compute a node's structural hash from its own payload plus its children's
/// already-cached hashes. Cost is O(arity); it never descends.
fn subtree_hash_of(op: &RegexOp) -> u64 {
    let mut hasher = rustc_hash::FxHasher::default();
    op_rank(op).hash(&mut hasher);
    match op {
        RegexOp::Epsilon | RegexOp::None | RegexOp::All | RegexOp::AllChar => {}
        RegexOp::Char(c) => c.hash(&mut hasher),
        RegexOp::Range(lo, hi) => {
            lo.hash(&mut hasher);
            hi.hash(&mut hasher);
        }
        RegexOp::UnicodeClass(cat) => (*cat as u32).hash(&mut hasher),
        RegexOp::Concat(parts) | RegexOp::Union(parts) | RegexOp::Inter(parts) => {
            parts.len().hash(&mut hasher);
            for p in parts {
                p.subtree_hash.hash(&mut hasher);
            }
        }
        RegexOp::Complement(r) | RegexOp::Star(r) | RegexOp::Plus(r) | RegexOp::Option(r) => {
            r.subtree_hash.hash(&mut hasher);
        }
        RegexOp::Loop(r, lo, hi) => {
            r.subtree_hash.hash(&mut hasher);
            lo.hash(&mut hasher);
            hi.hash(&mut hasher);
        }
    }
    hasher.finish()
}

impl Hash for Regex {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // O(1): the subtree hash was folded in at construction time.
        state.write_u64(self.subtree_hash);
    }
}

impl PartialEq for Regex {
    fn eq(&self, other: &Self) -> bool {
        if self.subtree_hash != other.subtree_hash {
            return false;
        }
        // Explicit stack, not recursion: the operand tree is as deep as the
        // input regex (and grows further with every Brzozowski derivative
        // step), and `eq` has no channel through which a depth limit could be
        // reported.
        let mut stack: Vec<(&RegexOp, &RegexOp)> = vec![(&self.op, &other.op)];
        while let Some((a, b)) = stack.pop() {
            if op_rank(a) != op_rank(b) {
                return false;
            }
            match (a, b) {
                (RegexOp::Epsilon, _)
                | (RegexOp::None, _)
                | (RegexOp::All, _)
                | (RegexOp::AllChar, _) => {}
                (RegexOp::Char(x), RegexOp::Char(y)) => {
                    if x != y {
                        return false;
                    }
                }
                (RegexOp::Range(x1, x2), RegexOp::Range(y1, y2)) => {
                    if (x1, x2) != (y1, y2) {
                        return false;
                    }
                }
                (RegexOp::UnicodeClass(x), RegexOp::UnicodeClass(y)) => {
                    if x != y {
                        return false;
                    }
                }
                (RegexOp::Concat(x), RegexOp::Concat(y))
                | (RegexOp::Union(x), RegexOp::Union(y))
                | (RegexOp::Inter(x), RegexOp::Inter(y)) => {
                    if !push_pairs(x, y, &mut stack) {
                        return false;
                    }
                }
                (RegexOp::Complement(x), RegexOp::Complement(y))
                | (RegexOp::Star(x), RegexOp::Star(y))
                | (RegexOp::Plus(x), RegexOp::Plus(y))
                | (RegexOp::Option(x), RegexOp::Option(y)) => {
                    if !push_pair(x, y, &mut stack) {
                        return false;
                    }
                }
                (RegexOp::Loop(x, xlo, xhi), RegexOp::Loop(y, ylo, yhi)) => {
                    if (xlo, xhi) != (ylo, yhi) || !push_pair(x, y, &mut stack) {
                        return false;
                    }
                }
                // `op_rank` is injective and was checked equal above, so the
                // two sides are always the same variant here.
                _ => return false,
            }
        }
        true
    }
}

impl Eq for Regex {}

/// Queue one child pair for structural comparison, short-circuiting on
/// pointer identity (shared subterm) and on the cached subtree hash.
/// Returns `false` when the pair is already known to differ.
fn push_pair<'a>(
    x: &'a Arc<Regex>,
    y: &'a Arc<Regex>,
    stack: &mut Vec<(&'a RegexOp, &'a RegexOp)>,
) -> bool {
    if Arc::ptr_eq(x, y) {
        return true;
    }
    if x.subtree_hash != y.subtree_hash {
        return false;
    }
    stack.push((&x.op, &y.op));
    true
}

/// [`push_pair`] over two operand lists; `false` if the lengths differ or any
/// pair is already known to differ.
fn push_pairs<'a>(
    xs: &'a [Arc<Regex>],
    ys: &'a [Arc<Regex>],
    stack: &mut Vec<(&'a RegexOp, &'a RegexOp)>,
) -> bool {
    if xs.len() != ys.len() {
        return false;
    }
    for (x, y) in xs.iter().zip(ys.iter()) {
        if !push_pair(x, y, stack) {
            return false;
        }
    }
    true
}

impl Drop for Regex {
    /// Dismantle the operand DAG iteratively.
    ///
    /// Compiler-generated drop glue recurses once per nesting level, so a
    /// regex deep enough to build is deep enough to abort the process at scope
    /// exit – after the value has already been used successfully. Children are
    /// moved onto an explicit stack and only descended into when this was the
    /// last `Arc` referencing them; a node reached this way has had its
    /// operands taken already, so the nested `drop` the stack triggers is a
    /// leaf drop and terminates immediately.
    fn drop(&mut self) {
        let mut stack: Vec<Arc<Regex>> = Vec::new();
        take_children(&mut self.op, &mut stack);
        while let Some(node) = stack.pop() {
            if let Ok(mut owned) = Arc::try_unwrap(node) {
                take_children(&mut owned.op, &mut stack);
            }
        }
    }
}

/// Move `op`'s operands onto `out`, leaving a childless operation behind.
fn take_children(op: &mut RegexOp, out: &mut Vec<Arc<Regex>>) {
    match core::mem::replace(op, RegexOp::None) {
        RegexOp::Epsilon
        | RegexOp::None
        | RegexOp::All
        | RegexOp::AllChar
        | RegexOp::Char(_)
        | RegexOp::Range(..)
        | RegexOp::UnicodeClass(_) => {}
        RegexOp::Concat(parts) | RegexOp::Union(parts) | RegexOp::Inter(parts) => {
            out.extend(parts);
        }
        RegexOp::Complement(r)
        | RegexOp::Star(r)
        | RegexOp::Plus(r)
        | RegexOp::Option(r)
        | RegexOp::Loop(r, _, _) => out.push(r),
    }
}

/// Deterministic total order over `RegexOp`, used to canonicalize the
/// operand order of `Union`/`Inter` (see [`Regex::union`]/[`Regex::inter`])
/// so that the same set of alternatives combined in a different input
/// order ends up structurally equal after sorting + `dedup`.
///
/// This used to be done via `format!("{:?}", ...).cmp(...)` on the WHOLE
/// (potentially deeply nested) regex for every comparison during the
/// sort -- correct only incidentally (derived `Debug` output happens to be
/// consistent with derived `Eq` here), but wasteful (a fresh `String`
/// allocated per comparison) and fragile (silently depends on `Debug`'s
/// output format never changing in a way that breaks the total order,
/// e.g. via a future hand-written `Debug` impl).
///
/// A `#[derive(Ord)]` on `RegexOp` itself is not available: the
/// `UnicodeClass` variant carries a `UnicodeCategory`, defined in a sibling
/// module this cluster does not own, which does not derive `Ord`. Instead,
/// `UnicodeCategory` is a plain fieldless enum, so its discriminant (via
/// `as u32`) already gives it a real total order without needing to modify
/// that module.
/// The comparator was three mutually recursive functions
/// (`regex_op_cmp` ↔ `regex_cmp` ↔ `regex_vec_cmp`) descending once per
/// nesting level, invoked O(n log n) times by the `sort_by` in
/// [`Regex::union`]/[`Regex::inter`] – i.e. on every `re.union`/`re.inter`
/// compile *and* on every derivative that rebuilds one. It returns `Ordering`,
/// which has no channel for "too deep", and a truncated comparison is not a
/// degraded answer: it breaks the total order `sort_by` requires. It is now a
/// single explicit-stack traversal.
fn regex_op_cmp(a: &RegexOp, b: &RegexOp) -> Ordering {
    /// One pending unit of the depth-first, left-to-right comparison.
    enum CmpStep<'a> {
        /// Compare these two operations.
        Pair(&'a RegexOp, &'a RegexOp),
        /// A tie-break already decided by the parent, consulted only after
        /// everything pushed above it has compared `Equal`.
        Fixed(Ordering),
    }

    let mut stack: Vec<CmpStep<'_>> = vec![CmpStep::Pair(a, b)];
    while let Some(step) = stack.pop() {
        let (x, y) = match step {
            CmpStep::Fixed(ord) => {
                if ord.is_eq() {
                    continue;
                }
                return ord;
            }
            CmpStep::Pair(x, y) => (x, y),
        };

        let (rx, ry) = (op_rank(x), op_rank(y));
        if rx != ry {
            return rx.cmp(&ry);
        }

        match (x, y) {
            (RegexOp::Epsilon, _)
            | (RegexOp::None, _)
            | (RegexOp::All, _)
            | (RegexOp::AllChar, _) => {}
            (RegexOp::Char(p), RegexOp::Char(q)) if p != q => return p.cmp(q),
            (RegexOp::Char(_), RegexOp::Char(_)) => {}
            (RegexOp::Range(p1, p2), RegexOp::Range(q1, q2)) => {
                let ord = (p1, p2).cmp(&(q1, q2));
                if !ord.is_eq() {
                    return ord;
                }
            }
            (RegexOp::UnicodeClass(p), RegexOp::UnicodeClass(q)) => {
                let ord = (*p as u32).cmp(&(*q as u32));
                if !ord.is_eq() {
                    return ord;
                }
            }
            (RegexOp::Concat(p), RegexOp::Concat(q))
            | (RegexOp::Union(p), RegexOp::Union(q))
            | (RegexOp::Inter(p), RegexOp::Inter(q)) => {
                // Lexicographic by length, then element-wise: the operands are
                // pushed in reverse so they pop left to right, and anything a
                // child expands into lands above its siblings.
                let ord = p.len().cmp(&q.len());
                if !ord.is_eq() {
                    return ord;
                }
                for (pi, qi) in p.iter().zip(q.iter()).rev() {
                    if !Arc::ptr_eq(pi, qi) {
                        stack.push(CmpStep::Pair(&pi.op, &qi.op));
                    }
                }
            }
            (RegexOp::Complement(p), RegexOp::Complement(q))
            | (RegexOp::Star(p), RegexOp::Star(q))
            | (RegexOp::Plus(p), RegexOp::Plus(q))
            | (RegexOp::Option(p), RegexOp::Option(q))
                if !Arc::ptr_eq(p, q) =>
            {
                stack.push(CmpStep::Pair(&p.op, &q.op));
            }
            (RegexOp::Complement(_), RegexOp::Complement(_))
            | (RegexOp::Star(_), RegexOp::Star(_))
            | (RegexOp::Plus(_), RegexOp::Plus(_))
            | (RegexOp::Option(_), RegexOp::Option(_)) => {}
            (RegexOp::Loop(p, plo, phi), RegexOp::Loop(q, qlo, qhi)) => {
                // The bounds break the tie only if the bodies compare equal,
                // so they go on the stack *below* the body comparison.
                stack.push(CmpStep::Fixed(plo.cmp(qlo).then_with(|| phi.cmp(qhi))));
                if !Arc::ptr_eq(p, q) {
                    stack.push(CmpStep::Pair(&p.op, &q.op));
                }
            }
            // `op_rank` is injective and was checked equal above, so the two
            // sides are always the same variant here.
            _ => {}
        }
    }
    Ordering::Equal
}

/// Total order over `Regex`, delegating to [`regex_op_cmp`] (the cached
/// `nullable` flag is redundant with `op` and not compared).
fn regex_cmp(a: &Regex, b: &Regex) -> Ordering {
    regex_op_cmp(&a.op, &b.op)
}

impl Regex {
    /// Build a node, folding in its cached structural hash. Every constructor
    /// goes through here so `subtree_hash` can never fall out of sync with
    /// `op`.
    fn make(op: RegexOp, nullable: bool) -> Arc<Self> {
        let subtree_hash = subtree_hash_of(&op);
        Arc::new(Self {
            op,
            nullable,
            subtree_hash,
        })
    }

    /// Create epsilon (empty string)
    pub fn epsilon() -> Arc<Self> {
        Self::make(RegexOp::Epsilon, true)
    }

    /// Create empty language (no matches)
    pub fn none() -> Arc<Self> {
        Self::make(RegexOp::None, false)
    }

    /// Create regex matching all strings
    pub fn all() -> Arc<Self> {
        Self::make(RegexOp::All, true)
    }

    /// Create regex matching any single character
    pub fn all_char() -> Arc<Self> {
        Self::make(RegexOp::AllChar, false)
    }

    /// Create a single character regex
    pub fn char(c: char) -> Arc<Self> {
        Self::make(RegexOp::Char(c), false)
    }

    /// Create a character range [lo-hi]
    pub fn range(lo: char, hi: char) -> Arc<Self> {
        if lo > hi {
            return Self::none();
        }
        Self::make(RegexOp::Range(lo, hi), false)
    }

    /// Create a string literal regex
    pub fn literal(s: &str) -> Arc<Self> {
        if s.is_empty() {
            return Self::epsilon();
        }
        let parts: Vec<Arc<Regex>> = s.chars().map(Self::char).collect();
        Self::concat(parts)
    }

    /// Create concatenation of regexes
    pub fn concat(parts: Vec<Arc<Regex>>) -> Arc<Self> {
        // Flatten nested concats and filter out epsilons
        let mut flat: Vec<Arc<Regex>> = Vec::new();
        for p in parts {
            match &p.op {
                RegexOp::Epsilon => continue,
                RegexOp::None => return Self::none(),
                RegexOp::Concat(inner) => flat.extend(inner.iter().cloned()),
                _ => flat.push(p),
            }
        }
        if flat.len() == 1 {
            // `pop` on a length-1 vec always yields the element; the fallback
            // exists so the impossible case is not written as an `expect`, and
            // returns exactly what the empty case returns.
            return flat.pop().unwrap_or_else(Self::epsilon);
        }
        if flat.is_empty() {
            return Self::epsilon();
        }
        let nullable = flat.iter().all(|r| r.nullable);
        Self::make(RegexOp::Concat(flat), nullable)
    }

    /// Create union of regexes
    pub fn union(parts: Vec<Arc<Regex>>) -> Arc<Self> {
        // Flatten nested unions and filter out nones
        let mut flat: Vec<Arc<Regex>> = Vec::new();
        for p in parts {
            match &p.op {
                RegexOp::None => continue,
                RegexOp::All => return Self::all(),
                RegexOp::Union(inner) => flat.extend(inner.iter().cloned()),
                _ => flat.push(p),
            }
        }
        if flat.len() == 1 {
            // See `concat`: total `pop`, no `expect`, empty-case fallback.
            return flat.pop().unwrap_or_else(Self::none);
        }
        if flat.is_empty() {
            return Self::none();
        }
        // Deduplicate
        flat.sort_by(|a, b| regex_cmp(a, b));
        flat.dedup();
        let nullable = flat.iter().any(|r| r.nullable);
        Self::make(RegexOp::Union(flat), nullable)
    }

    /// Create intersection of regexes
    pub fn inter(parts: Vec<Arc<Regex>>) -> Arc<Self> {
        let mut flat: Vec<Arc<Regex>> = Vec::new();
        for p in parts {
            match &p.op {
                RegexOp::All => continue,
                RegexOp::None => return Self::none(),
                RegexOp::Inter(inner) => flat.extend(inner.iter().cloned()),
                _ => flat.push(p),
            }
        }
        if flat.len() == 1 {
            // See `concat`: total `pop`, no `expect`, empty-case fallback.
            return flat.pop().unwrap_or_else(Self::all);
        }
        if flat.is_empty() {
            return Self::all();
        }
        flat.sort_by(|a, b| regex_cmp(a, b));
        flat.dedup();
        let nullable = flat.iter().all(|r| r.nullable);
        Self::make(RegexOp::Inter(flat), nullable)
    }

    /// Create complement of a regex
    pub fn complement(r: Arc<Regex>) -> Arc<Self> {
        match &r.op {
            RegexOp::None => Self::all(),
            RegexOp::All => Self::none(),
            RegexOp::Complement(inner) => inner.clone(),
            _ => {
                let nullable = !r.nullable;
                Self::make(RegexOp::Complement(r.clone()), nullable)
            }
        }
    }

    /// Create Kleene star
    pub fn star(r: Arc<Regex>) -> Arc<Self> {
        match &r.op {
            RegexOp::Epsilon | RegexOp::None => Self::epsilon(),
            RegexOp::Star(_) | RegexOp::All => r,
            _ => Self::make(RegexOp::Star(r), true),
        }
    }

    /// Create Kleene plus
    pub fn plus(r: Arc<Regex>) -> Arc<Self> {
        match &r.op {
            RegexOp::Epsilon => Self::epsilon(),
            RegexOp::None => Self::none(),
            RegexOp::Star(_) | RegexOp::Plus(_) => r,
            _ => {
                let nullable = r.nullable;
                Self::make(RegexOp::Plus(r.clone()), nullable)
            }
        }
    }

    /// Create optional (zero or one)
    pub fn option(r: Arc<Regex>) -> Arc<Self> {
        if r.nullable {
            return r;
        }
        match &r.op {
            RegexOp::None => Self::epsilon(),
            _ => Self::make(RegexOp::Option(r), true),
        }
    }

    /// Create bounded loop
    pub fn loop_bounded(r: Arc<Regex>, min: u32, max: Option<u32>) -> Arc<Self> {
        if min == 0 && max == Some(0) {
            return Self::epsilon();
        }
        if let Some(m) = max
            && m < min
        {
            return Self::none();
        }
        if matches!(r.op, RegexOp::None) && min > 0 {
            return Self::none();
        }
        if matches!(r.op, RegexOp::Epsilon) {
            return Self::epsilon();
        }
        let nullable = min == 0 || r.nullable;
        Self::make(RegexOp::Loop(r, min, max), nullable)
    }

    /// Check if regex accepts the empty string
    #[inline]
    pub fn is_nullable(&self) -> bool {
        self.nullable
    }

    /// Check if this is the empty language
    #[inline]
    pub fn is_empty(&self) -> bool {
        matches!(self.op, RegexOp::None)
    }

    /// Check if this accepts all strings
    #[inline]
    pub fn is_all(&self) -> bool {
        matches!(self.op, RegexOp::All)
    }

    /// Compute Brzozowski derivative with respect to a character
    ///
    /// The walk is an explicit post-order stack rather than recursion. Depth
    /// here is the *input regex's* nesting depth, which every derivative step
    /// preserves or grows, and this is called O(states × alphabet) times by
    /// `regex_membership::search_word` and once per input character by
    /// [`Regex::matches`]. The return type is `Arc<Regex>` – no error channel –
    /// so a depth cap could only fabricate a wrong language.
    pub fn derivative(&self, c: char) -> Arc<Regex> {
        // One shallow clone of the root: `Star` needs the node itself as an
        // operand, and the iterative walk carries `Arc`s from there down.
        // Cloning a node copies its `op` (a vector of `Arc` handles), not its
        // subtree.
        derivative_of(Arc::new(self.clone()), c)
    }

    /// Check if a string matches this regex
    pub fn matches(&self, s: &str) -> bool {
        let mut current: Arc<Regex> = Arc::new(self.clone());
        for c in s.chars() {
            current = current.derivative(c);
            if current.is_empty() {
                return false;
            }
        }
        current.is_nullable()
    }
}

/// How a node's result is rebuilt once its operands' derivatives are known.
///
/// Every variant consumes the whole operand-result vector, so none of them can
/// be written in a form that needs to assert an element is present.
enum DerivBuild {
    /// `D(r1 … rn)`: the full operand list plus the prefix of indices whose
    /// derivatives were actually taken (the recursive version stopped at the
    /// first non-nullable operand, and so does this).
    Concat {
        /// The concatenation's operands.
        parts: Vec<Arc<Regex>>,
        /// Indices of the operands whose derivative was requested, in order.
        taken: Vec<usize>,
    },
    /// `D(r1 + … + rn) = D(r1) + … + D(rn)`.
    Union,
    /// `D(r1 ∩ … ∩ rn) = D(r1) ∩ … ∩ D(rn)`.
    Inter,
    /// `D(¬r) = ¬D(r)`; `Regex::union` of the single result is that result.
    Complement,
    /// `D(r*) = D(r) r*`, carrying the star node itself as the suffix.
    Suffix(Arc<Regex>),
}

/// One pending node of the iterative derivative walk.
struct DerivFrame {
    /// How to rebuild this node.
    build: DerivBuild,
    /// Operands still to be differentiated, reversed so `pop` yields them
    /// left to right.
    pending: Vec<Arc<Regex>>,
    /// Operand derivatives collected so far, in operand order.
    done: Vec<Arc<Regex>>,
}

impl DerivFrame {
    /// Rebuild this node from its operands' derivatives.
    fn finish(self) -> Arc<Regex> {
        match self.build {
            DerivBuild::Concat { parts, taken } => {
                let mut result: Vec<Arc<Regex>> = Vec::new();
                for (d, &i) in self.done.iter().zip(taken.iter()) {
                    if !d.is_empty() {
                        let mut suffix: Vec<Arc<Regex>> = vec![d.clone()];
                        suffix.extend(parts[i + 1..].iter().cloned());
                        result.push(Regex::concat(suffix));
                    }
                }
                Regex::union(result)
            }
            DerivBuild::Union => Regex::union(self.done),
            DerivBuild::Inter => Regex::inter(self.done),
            DerivBuild::Complement => Regex::complement(Regex::union(self.done)),
            DerivBuild::Suffix(rest) => {
                let mut parts = self.done;
                parts.push(rest);
                Regex::concat(parts)
            }
        }
    }
}

/// What differentiating one node needs: an answer already, or its operands.
enum DerivOpened {
    /// The derivative is known without looking at any operand.
    Leaf(Arc<Regex>),
    /// The operands must be differentiated first.
    Frame(DerivFrame),
}

/// Decide what `node`'s derivative w.r.t. `c` needs.
fn open_derivative(node: Arc<Regex>, c: char) -> DerivOpened {
    // `D(r?) = D(r)`: unwrap `Option` chains here rather than through a frame,
    // so an `(re.opt (re.opt …))` tower costs no stack at all.
    let mut node = node;
    while let RegexOp::Option(inner) = &node.op {
        let inner = inner.clone();
        node = inner;
    }

    let leaf = |r: Arc<Regex>| DerivOpened::Leaf(r);
    match &node.op {
        RegexOp::Epsilon | RegexOp::None => leaf(Regex::none()),
        RegexOp::All => leaf(Regex::all()),
        RegexOp::AllChar => leaf(Regex::epsilon()),
        RegexOp::Char(ch) => leaf(if *ch == c {
            Regex::epsilon()
        } else {
            Regex::none()
        }),
        RegexOp::Range(lo, hi) => leaf(if c >= *lo && c <= *hi {
            Regex::epsilon()
        } else {
            Regex::none()
        }),
        RegexOp::UnicodeClass(cat) => leaf(if cat.contains(c) {
            Regex::epsilon()
        } else {
            Regex::none()
        }),
        RegexOp::Concat(parts) => {
            let mut taken: Vec<usize> = Vec::new();
            for (i, part) in parts.iter().enumerate() {
                taken.push(i);
                if !part.nullable {
                    break;
                }
            }
            let pending: Vec<Arc<Regex>> = taken.iter().rev().map(|&i| parts[i].clone()).collect();
            DerivOpened::Frame(DerivFrame {
                build: DerivBuild::Concat {
                    parts: parts.clone(),
                    taken,
                },
                pending,
                done: Vec::new(),
            })
        }
        RegexOp::Union(parts) => DerivOpened::Frame(DerivFrame {
            build: DerivBuild::Union,
            pending: parts.iter().rev().cloned().collect(),
            done: Vec::new(),
        }),
        RegexOp::Inter(parts) => DerivOpened::Frame(DerivFrame {
            build: DerivBuild::Inter,
            pending: parts.iter().rev().cloned().collect(),
            done: Vec::new(),
        }),
        RegexOp::Complement(inner) => DerivOpened::Frame(DerivFrame {
            build: DerivBuild::Complement,
            pending: vec![inner.clone()],
            done: Vec::new(),
        }),
        RegexOp::Star(inner) => DerivOpened::Frame(DerivFrame {
            // D(r*) = D(r) r*
            build: DerivBuild::Suffix(node.clone()),
            pending: vec![inner.clone()],
            done: Vec::new(),
        }),
        RegexOp::Plus(inner) => DerivOpened::Frame(DerivFrame {
            // D(r+) = D(r) r*
            build: DerivBuild::Suffix(Regex::star(inner.clone())),
            pending: vec![inner.clone()],
            done: Vec::new(),
        }),
        RegexOp::Loop(inner, min, max) => DerivOpened::Frame(DerivFrame {
            // D(r{m,n}) = D(r) r{max(0, m-1), n-1}
            build: DerivBuild::Suffix(Regex::loop_bounded(
                inner.clone(),
                min.saturating_sub(1),
                max.map(|m| m.saturating_sub(1)),
            )),
            pending: vec![inner.clone()],
            done: Vec::new(),
        }),
        // `Option` was unwrapped above, so it cannot reach here; listing it
        // keeps the match exhaustive without a catch-all, so a new operator
        // becomes a compile error rather than a silently wrong derivative.
        RegexOp::Option(inner) => DerivOpened::Frame(DerivFrame {
            build: DerivBuild::Union,
            pending: vec![inner.clone()],
            done: Vec::new(),
        }),
    }
}

/// Explicit-stack driver behind [`Regex::derivative`].
fn derivative_of(root: Arc<Regex>, c: char) -> Arc<Regex> {
    let mut frames: Vec<DerivFrame> = match open_derivative(root, c) {
        DerivOpened::Leaf(r) => return r,
        DerivOpened::Frame(f) => vec![f],
    };
    // A finished operand derivative travelling back to the frame that asked
    // for it.
    let mut carry: Option<Arc<Regex>> = None;

    while !frames.is_empty() {
        let next = match frames.last_mut() {
            Some(top) => {
                if let Some(d) = carry.take() {
                    top.done.push(d);
                }
                top.pending.pop()
            }
            // Unreachable: the loop condition just checked non-emptiness.
            None => break,
        };
        match next {
            Some(child) => match open_derivative(child, c) {
                DerivOpened::Leaf(r) => carry = Some(r),
                DerivOpened::Frame(f) => frames.push(f),
            },
            None => match frames.pop() {
                Some(frame) => carry = Some(frame.finish()),
                // Unreachable for the same reason as above.
                None => break,
            },
        }
    }

    // The root frame's `finish` result is the last value handed back, and the
    // root is only a frame when `open_derivative` did not answer outright.
    carry.unwrap_or_else(Regex::none)
}

/// A regex derivative cache for efficient repeated derivative computation
#[allow(dead_code)]
#[derive(Debug, Default)]
pub struct DerivativeCache {
    /// Cache: (regex, char) -> derivative.
    ///
    /// Keyed by the actual `Regex` value (which derives `Eq`/`Hash`), not a
    /// raw pre-computed `u64` hash: using a bare hash AS the map key means
    /// any hash collision between two DIFFERENT regexes silently returns
    /// the wrong cached derivative (no equality check ever happens, since
    /// the original regex value isn't retained to check against). Keying
    /// on the value itself lets `FxHashMap`'s normal collision handling
    /// (hash bucket + `Eq` verification) do this correctly.
    cache: FxHashMap<(Regex, char), Arc<Regex>>,
}

#[allow(dead_code)]
impl DerivativeCache {
    /// Create a new derivative cache
    pub fn new() -> Self {
        Self {
            cache: FxHashMap::default(),
        }
    }

    /// Get or compute derivative
    pub fn derivative(&mut self, r: &Arc<Regex>, c: char) -> Arc<Regex> {
        let key = ((**r).clone(), c);

        if let Some(d) = self.cache.get(&key) {
            return d.clone();
        }

        let d = r.derivative(c);
        self.cache.insert(key, d.clone());
        d
    }

    /// Clear the cache
    pub fn clear(&mut self) {
        self.cache.clear();
    }
}

/// State in an automaton derived from a regex
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct AutomatonState {
    /// The regex representing this state
    pub regex: Arc<Regex>,
    /// State ID
    pub id: u32,
    /// Whether this is an accepting state
    pub accepting: bool,
}

/// A DFA built from a regex using derivative-based construction
#[allow(dead_code)]
#[derive(Debug)]
pub struct RegexAutomaton {
    /// All states
    states: Vec<AutomatonState>,
    /// Transition table: state_id -> [(char_range, target_state_id)]
    transitions: Vec<SmallVec<[(char, char, u32); 8]>>,
    /// Regex to state ID mapping.
    ///
    /// Keyed by the regex *value*, not by a bare `u64` hash: a bare hash as
    /// the key has no equality check behind it, so two different regexes that
    /// collide silently become the same DFA state and the automaton then
    /// accepts the wrong language. (Same defect, same fix as
    /// [`DerivativeCache`].) With the cached subtree hash on [`Regex`] this
    /// costs no more than the hash-keyed version did.
    regex_to_state: FxHashMap<Regex, u32>,
    /// Initial state ID
    initial: u32,
    /// Derivative cache
    cache: DerivativeCache,
}

#[allow(dead_code)]
impl RegexAutomaton {
    /// Build a DFA from a regex (lazy construction)
    pub fn new(regex: Arc<Regex>) -> Self {
        let initial_accepting = regex.is_nullable();

        let mut regex_to_state = FxHashMap::default();
        regex_to_state.insert((*regex).clone(), 0);

        Self {
            states: vec![AutomatonState {
                regex,
                id: 0,
                accepting: initial_accepting,
            }],
            transitions: vec![SmallVec::new()],
            regex_to_state,
            initial: 0,
            cache: DerivativeCache::new(),
        }
    }

    /// Get or create state for a regex
    fn get_or_create_state(&mut self, regex: Arc<Regex>) -> u32 {
        if let Some(&id) = self.regex_to_state.get(&*regex) {
            return id;
        }

        let id = self.states.len() as u32;
        let accepting = regex.is_nullable();
        let key = (*regex).clone();
        self.states.push(AutomatonState {
            regex,
            id,
            accepting,
        });
        self.transitions.push(SmallVec::new());
        self.regex_to_state.insert(key, id);
        id
    }

    /// Get transition for a character, computing derivatives lazily
    pub fn transition(&mut self, state: u32, c: char) -> u32 {
        // Check existing transitions
        for &(lo, hi, target) in &self.transitions[state as usize] {
            if c >= lo && c <= hi {
                return target;
            }
        }

        // Compute derivative
        let regex = self.states[state as usize].regex.clone();
        let derivative = self.cache.derivative(&regex, c);

        if derivative.is_empty() {
            // Create dead state if needed
            let dead = self.get_or_create_state(Regex::none());
            self.transitions[state as usize].push((c, c, dead));
            return dead;
        }

        let target = self.get_or_create_state(derivative);
        self.transitions[state as usize].push((c, c, target));
        target
    }

    /// Check if a string is accepted
    pub fn accepts(&mut self, s: &str) -> bool {
        let mut current = self.initial;
        for c in s.chars() {
            current = self.transition(current, c);
            // Early exit on dead state
            if self.states[current as usize].regex.is_empty() {
                return false;
            }
        }
        self.states[current as usize].accepting
    }

    /// Check if a state is accepting
    pub fn is_accepting(&self, state: u32) -> bool {
        self.states.get(state as usize).is_some_and(|s| s.accepting)
    }

    /// Check if a state is dead (rejects all strings)
    pub fn is_dead(&self, state: u32) -> bool {
        self.states
            .get(state as usize)
            .is_none_or(|s| s.regex.is_empty())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_epsilon() {
        let r = Regex::epsilon();
        assert!(r.is_nullable());
        assert!(r.matches(""));
        assert!(!r.matches("a"));
    }

    #[test]
    fn test_char() {
        let r = Regex::char('a');
        assert!(!r.is_nullable());
        assert!(r.matches("a"));
        assert!(!r.matches("b"));
        assert!(!r.matches(""));
        assert!(!r.matches("aa"));
    }

    #[test]
    fn test_literal() {
        let r = Regex::literal("hello");
        assert!(r.matches("hello"));
        assert!(!r.matches("hell"));
        assert!(!r.matches("hello!"));
        assert!(!r.matches(""));
    }

    #[test]
    fn test_concat() {
        let r = Regex::concat(vec![Regex::char('a'), Regex::char('b')]);
        assert!(r.matches("ab"));
        assert!(!r.matches("a"));
        assert!(!r.matches("b"));
        assert!(!r.matches("abc"));
    }

    #[test]
    fn test_union() {
        let r = Regex::union(vec![Regex::char('a'), Regex::char('b')]);
        assert!(r.matches("a"));
        assert!(r.matches("b"));
        assert!(!r.matches("c"));
        assert!(!r.matches("ab"));
    }

    #[test]
    fn test_star() {
        let r = Regex::star(Regex::char('a'));
        assert!(r.is_nullable());
        assert!(r.matches(""));
        assert!(r.matches("a"));
        assert!(r.matches("aaa"));
        assert!(!r.matches("b"));
        assert!(!r.matches("ab"));
    }

    #[test]
    fn test_plus() {
        let r = Regex::plus(Regex::char('a'));
        assert!(!r.is_nullable());
        assert!(!r.matches(""));
        assert!(r.matches("a"));
        assert!(r.matches("aaa"));
        assert!(!r.matches("b"));
    }

    #[test]
    fn test_option() {
        let r = Regex::option(Regex::char('a'));
        assert!(r.is_nullable());
        assert!(r.matches(""));
        assert!(r.matches("a"));
        assert!(!r.matches("aa"));
    }

    #[test]
    fn test_range() {
        let r = Regex::range('a', 'z');
        assert!(r.matches("a"));
        assert!(r.matches("m"));
        assert!(r.matches("z"));
        assert!(!r.matches("A"));
        assert!(!r.matches("1"));
    }

    #[test]
    fn test_loop() {
        let r = Regex::loop_bounded(Regex::char('a'), 2, Some(4));
        assert!(!r.matches(""));
        assert!(!r.matches("a"));
        assert!(r.matches("aa"));
        assert!(r.matches("aaa"));
        assert!(r.matches("aaaa"));
        assert!(!r.matches("aaaaa"));
    }

    #[test]
    fn test_complement() {
        let a = Regex::char('a');
        let not_a = Regex::complement(a);
        assert!(not_a.matches(""));
        assert!(!not_a.matches("a"));
        assert!(not_a.matches("b"));
        assert!(not_a.matches("ab"));
    }

    #[test]
    fn test_intersection() {
        // a* ∩ a+ = a+
        let star = Regex::star(Regex::char('a'));
        let plus = Regex::plus(Regex::char('a'));
        let inter = Regex::inter(vec![star, plus]);
        assert!(!inter.matches(""));
        assert!(inter.matches("a"));
        assert!(inter.matches("aa"));
    }

    #[test]
    fn test_automaton() {
        let r = Regex::star(Regex::union(vec![Regex::char('a'), Regex::char('b')]));
        let mut dfa = RegexAutomaton::new(r);
        assert!(dfa.accepts(""));
        assert!(dfa.accepts("a"));
        assert!(dfa.accepts("ab"));
        assert!(dfa.accepts("aabbab"));
        assert!(!dfa.accepts("c"));
    }

    #[test]
    fn test_email_like_pattern() {
        // Simplified email pattern: \w+@\w+\.\w+
        let word_char = Regex::union(vec![
            Regex::range('a', 'z'),
            Regex::range('A', 'Z'),
            Regex::range('0', '9'),
            Regex::char('_'),
        ]);
        let word = Regex::plus(word_char.clone());
        let email = Regex::concat(vec![
            word.clone(),
            Regex::char('@'),
            word.clone(),
            Regex::char('.'),
            word,
        ]);
        assert!(email.matches("user@example.com"));
        assert!(email.matches("test_123@domain.org"));
        assert!(!email.matches("invalid"));
        assert!(!email.matches("@missing.com"));
    }

    // Audit regression (theories-string): `DerivativeCache` keyed its
    // entries by a raw pre-computed `u64` hash with no follow-up equality
    // check, so two DIFFERENT regexes that happen to hash-collide would
    // silently share (and return each other's) cached derivative. This
    // constructs two structurally different regexes and confirms each
    // gets its own, independently-correct cached derivative.
    #[test]
    fn audit_derivative_cache_distinguishes_different_regexes() {
        let mut cache = DerivativeCache::new();

        let a = Regex::char('a');
        let b = Regex::char('b');

        let d_a = cache.derivative(&a, 'a');
        let d_b = cache.derivative(&b, 'b');

        // derivative of `a` w.r.t. 'a' is epsilon (nullable, matches "").
        assert!(d_a.matches(""));
        // derivative of `b` w.r.t. 'b' is ALSO epsilon -- but it must have
        // been computed independently (from `b`, not misappropriated from
        // the cached entry for `a`), and cross-checking against the wrong
        // *source* regex is exactly the failure mode a hash collision (or
        // a cache bug) would produce.
        assert!(d_b.matches(""));

        // A derivative that should NOT match must not do so because of a
        // cache mix-up: derivative of `a` w.r.t. 'b' is the empty language.
        let d_a_wrt_b = cache.derivative(&a, 'b');
        assert!(!d_a_wrt_b.matches(""));
        assert!(!d_a_wrt_b.matches("a"));

        // Re-querying the same (regex, char) pair must return the SAME
        // (cached) derivative rather than recomputing something different.
        let d_a_again = cache.derivative(&a, 'a');
        assert_eq!(*d_a_again, *d_a);
    }

    // Audit regression (theories-string): `Regex::union`/`Regex::inter`
    // used to canonicalize operand order via
    // `format!("{:?}", ...).cmp(...)` on the whole regex tree. Confirm the
    // real replacement (`regex_op_cmp`) still produces order-independent,
    // deduplicated results.
    #[test]
    fn audit_union_canonicalizes_regardless_of_input_order() {
        let a = Regex::char('a');
        let b = Regex::char('b');
        let c = Regex::char('c');

        let u1 = Regex::union(vec![a.clone(), b.clone(), c.clone()]);
        let u2 = Regex::union(vec![c.clone(), a.clone(), b.clone()]);
        let u3 = Regex::union(vec![b, c, a]);

        assert_eq!(u1, u2, "union must not depend on input order");
        assert_eq!(u1, u3, "union must not depend on input order");
    }

    #[test]
    fn audit_union_deduplicates_repeated_operands() {
        let a = Regex::char('a');
        let b = Regex::char('b');

        let u = Regex::union(vec![a.clone(), b.clone(), a.clone(), b]);
        if let RegexOp::Union(parts) = &u.op {
            assert_eq!(
                parts.len(),
                2,
                "duplicate operands must be removed after canonical sort"
            );
        } else {
            panic!("expected a Union node, got {:?}", u.op);
        }
    }

    #[test]
    fn audit_regex_op_cmp_is_consistent_with_eq() {
        // Structurally-equal regexes must compare as `Equal`, and the
        // comparator must be antisymmetric for structurally different
        // ones -- basic total-order sanity checks for the hand-written
        // comparator that replaced the `Debug`-string-based sort.
        let variants = vec![
            Regex::epsilon(),
            Regex::none(),
            Regex::all(),
            Regex::all_char(),
            Regex::char('x'),
            Regex::range('a', 'z'),
            Regex::star(Regex::char('x')),
            Regex::plus(Regex::char('x')),
            Regex::concat(vec![Regex::char('x'), Regex::char('y')]),
        ];

        for v in &variants {
            assert_eq!(regex_cmp(v, v), Ordering::Equal);
        }

        for i in 0..variants.len() {
            for j in 0..variants.len() {
                if i == j {
                    continue;
                }
                let ord_ij = regex_cmp(&variants[i], &variants[j]);
                let ord_ji = regex_cmp(&variants[j], &variants[i]);
                assert_eq!(
                    ord_ij,
                    ord_ji.reverse(),
                    "comparator must be antisymmetric for distinct regexes"
                );
                assert_ne!(
                    ord_ij,
                    Ordering::Equal,
                    "structurally different regexes must not compare Equal"
                );
            }
        }
    }
}
