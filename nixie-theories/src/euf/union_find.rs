//! Union-Find data structure for congruence closure

#[allow(unused_imports)]
use crate::prelude::*;

/// An undo entry for reverting a union-find mutation.
///
/// Both union merges and (scoped) path-compression rewrites are recorded on the
/// same trail so that [`UnionFind::pop`] restores the *exact* parent/rank state
/// that existed at the matching [`UnionFind::push`] boundary.
#[derive(Debug, Clone, Copy)]
enum UndoEntry {
    /// A union merge: `loser` (a former root) became a child of `winner`.
    Union {
        /// The root that lost the union and became a child.
        loser: u32,
        /// The root that won the union.  Only its rank is touched, and only if
        /// `rank_incremented` is true.
        winner: u32,
        /// Whether the winner's rank was incremented by this merge.
        rank_incremented: bool,
    },
    /// A path-compression rewrite performed inside a scope: `node`'s parent was
    /// changed from `old_parent` to a deeper root.  Recorded so `pop()` can put
    /// the pointer back exactly, preventing a compressed pointer from surviving a
    /// backtrack and corrupting equivalence classes.
    Compress {
        /// The node whose parent pointer was rewritten.
        node: u32,
        /// The parent pointer value before compression.
        old_parent: u32,
    },
}

/// Union-Find with (backtrack-safe) path compression and union by rank.
///
/// # Backtracking soundness
///
/// Path compression rewrites parent pointers, which is unsound under `push`/`pop`
/// unless every rewrite is undone on backtrack: a pointer compressed to a deep
/// root at level N would otherwise survive a `pop` that dissolves the union it
/// short-circuited, wrongly reporting two nodes as equal (or unequal).
///
/// To stay sound *and* keep compression's asymptotic benefit, `find` records each
/// compression rewrite on the undo trail **whenever a scope is active** (i.e. at
/// least one `push` is outstanding).  At the base level, where nothing is ever
/// popped, compression is applied without recording, exactly like the classic
/// non-incremental structure.  `pop` replays both union and compression undo
/// entries in LIFO order, restoring the precise pre-scope parent array.
#[derive(Debug, Clone)]
pub struct UnionFind {
    /// Parent pointers (root points to itself)
    parent: Vec<u32>,
    /// Rank for union by rank
    rank: Vec<u32>,
    /// Trail of undo entries for backtracking
    trail: Vec<UndoEntry>,
    /// Trail size at each decision level
    trail_limits: Vec<usize>,
}

impl UnionFind {
    /// Create a new Union-Find with n elements
    #[must_use]
    pub fn new(n: usize) -> Self {
        Self {
            parent: (0..n as u32).collect(),
            rank: vec![0; n],
            trail: Vec::new(),
            trail_limits: vec![0],
        }
    }

    /// Find the representative of an element with backtrack-safe path compression.
    ///
    /// When a scope is active (an outstanding `push`), every pointer rewritten by
    /// compression is recorded on the undo trail so `pop` can restore it. At the
    /// base level compression is applied without recording, since base-level state
    /// is never popped. See the type-level docs for the soundness argument.
    #[inline]
    pub fn find(&mut self, mut x: u32) -> u32 {
        let mut root = x;
        while self.parent[root as usize] != root {
            root = self.parent[root as usize];
        }

        // Path compression. `trail_limits` always holds at least the base marker
        // (index 0); a length > 1 means at least one push is outstanding, so any
        // compression could later need undoing and must be trailed.
        let in_scope = self.trail_limits.len() > 1;
        while self.parent[x as usize] != root {
            let next = self.parent[x as usize];
            if in_scope {
                self.trail.push(UndoEntry::Compress {
                    node: x,
                    old_parent: next,
                });
            }
            self.parent[x as usize] = root;
            x = next;
        }

        root
    }

    /// Find the representative of an element without path compression (immutable)
    #[inline]
    #[must_use]
    pub fn find_no_compress(&self, mut x: u32) -> u32 {
        while self.parent[x as usize] != x {
            x = self.parent[x as usize];
        }
        x
    }

    /// Check if two elements are in the same set (immutable version)
    #[inline]
    #[must_use]
    pub fn same_no_compress(&self, x: u32, y: u32) -> bool {
        self.find_no_compress(x) == self.find_no_compress(y)
    }

    /// Union two elements, returns true if they were in different sets
    /// This version tracks the merge for backtracking
    pub fn union(&mut self, x: u32, y: u32) -> bool {
        let root_x = self.find_no_compress(x);
        let root_y = self.find_no_compress(y);

        if root_x == root_y {
            return false;
        }

        // Union by rank (track for undo)
        match self.rank[root_x as usize].cmp(&self.rank[root_y as usize]) {
            core::cmp::Ordering::Less => {
                // root_x becomes child of root_y
                self.trail.push(UndoEntry::Union {
                    loser: root_x,
                    winner: root_y,
                    rank_incremented: false,
                });
                self.parent[root_x as usize] = root_y;
            }
            core::cmp::Ordering::Greater => {
                // root_y becomes child of root_x
                self.trail.push(UndoEntry::Union {
                    loser: root_y,
                    winner: root_x,
                    rank_incremented: false,
                });
                self.parent[root_y as usize] = root_x;
            }
            core::cmp::Ordering::Equal => {
                // root_y becomes child of root_x, rank increases
                self.trail.push(UndoEntry::Union {
                    loser: root_y,
                    winner: root_x,
                    rank_incremented: true,
                });
                self.parent[root_y as usize] = root_x;
                self.rank[root_x as usize] += 1;
            }
        }

        true
    }

    /// Union two elements without tracking (for non-incremental use).
    ///
    /// Uses the non-compressing lookup so it records nothing on the trail, keeping
    /// its "no undo state" contract intact regardless of the current scope depth.
    pub fn union_no_trail(&mut self, x: u32, y: u32) -> bool {
        let root_x = self.find_no_compress(x);
        let root_y = self.find_no_compress(y);

        if root_x == root_y {
            return false;
        }

        match self.rank[root_x as usize].cmp(&self.rank[root_y as usize]) {
            core::cmp::Ordering::Less => {
                self.parent[root_x as usize] = root_y;
            }
            core::cmp::Ordering::Greater => {
                self.parent[root_y as usize] = root_x;
            }
            core::cmp::Ordering::Equal => {
                self.parent[root_y as usize] = root_x;
                self.rank[root_x as usize] += 1;
            }
        }

        true
    }

    /// Check if two elements are in the same set
    #[inline]
    pub fn same(&mut self, x: u32, y: u32) -> bool {
        self.find(x) == self.find(y)
    }

    /// Add a new element
    pub fn add(&mut self) -> u32 {
        let id = self.parent.len() as u32;
        self.parent.push(id);
        self.rank.push(0);
        id
    }

    /// Get the number of elements
    #[must_use]
    pub fn len(&self) -> usize {
        self.parent.len()
    }

    /// Check if empty
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.parent.is_empty()
    }

    /// Push a new decision level (save current trail position)
    pub fn push(&mut self) {
        self.trail_limits.push(self.trail.len());
    }

    /// Pop to previous decision level, undoing all unions since then
    pub fn pop(&mut self) {
        if let Some(limit) = self.trail_limits.pop() {
            // Undo all merges and compression rewrites since the limit, in LIFO
            // order so that each parent pointer is restored to its exact prior
            // value even when it was mutated multiple times within the scope.
            while self.trail.len() > limit {
                match self.trail.pop() {
                    Some(UndoEntry::Union {
                        loser,
                        winner,
                        rank_incremented,
                    }) => {
                        // A losing root was made a child of itself again.
                        self.parent[loser as usize] = loser;
                        if rank_incremented {
                            self.rank[winner as usize] -= 1;
                        }
                    }
                    Some(UndoEntry::Compress { node, old_parent }) => {
                        self.parent[node as usize] = old_parent;
                    }
                    None => break,
                }
            }
        }
    }

    /// Backtrack to a specific decision level
    pub fn backtrack_to(&mut self, level: usize) {
        while self.trail_limits.len() > level + 1 {
            self.pop();
        }
    }

    /// Get the current decision level
    #[must_use]
    pub fn decision_level(&self) -> usize {
        self.trail_limits.len().saturating_sub(1)
    }

    /// Get the trail size
    #[must_use]
    pub fn trail_size(&self) -> usize {
        self.trail.len()
    }

    /// Clear all state
    pub fn clear(&mut self) {
        self.parent.clear();
        self.rank.clear();
        self.trail.clear();
        self.trail_limits.clear();
        self.trail_limits.push(0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_union_find_basic() {
        let mut uf = UnionFind::new(5);

        assert!(!uf.same(0, 1));
        assert!(uf.union(0, 1));
        assert!(uf.same(0, 1));

        assert!(!uf.same(1, 2));
        assert!(uf.union(1, 2));
        assert!(uf.same(0, 2));
    }

    #[test]
    fn test_union_find_redundant() {
        let mut uf = UnionFind::new(3);

        assert!(uf.union(0, 1));
        assert!(!uf.union(0, 1)); // Already in same set
        assert!(!uf.union(1, 0)); // Already in same set
    }

    #[test]
    fn test_union_find_add() {
        let mut uf = UnionFind::new(2);

        let x = uf.add();
        assert_eq!(x, 2);
        assert!(!uf.same(0, x));

        uf.union(0, x);
        assert!(uf.same(0, x));
    }

    #[test]
    fn test_union_find_push_pop() {
        let mut uf = UnionFind::new(5);

        // Initial state: all separate
        assert!(!uf.same_no_compress(0, 1));
        assert!(!uf.same_no_compress(2, 3));

        // Level 0: merge 0 and 1
        uf.union(0, 1);
        assert!(uf.same_no_compress(0, 1));

        // Push to level 1
        uf.push();

        // Level 1: merge 2 and 3
        uf.union(2, 3);
        assert!(uf.same_no_compress(2, 3));

        // Also merge 0 with 2
        uf.union(0, 2);
        assert!(uf.same_no_compress(0, 2));
        assert!(uf.same_no_compress(1, 3)); // Transitive

        // Pop back to level 0
        uf.pop();

        // 0 and 1 should still be merged
        assert!(uf.same_no_compress(0, 1));

        // 2 and 3 should be separate again
        assert!(!uf.same_no_compress(2, 3));

        // 0 and 2 should be separate again
        assert!(!uf.same_no_compress(0, 2));
    }

    #[test]
    fn test_union_find_multiple_levels() {
        let mut uf = UnionFind::new(6);

        // Level 0
        uf.union(0, 1);

        uf.push(); // Level 1
        uf.union(2, 3);

        uf.push(); // Level 2
        uf.union(4, 5);
        uf.union(0, 4); // Merge two groups

        assert!(uf.same_no_compress(0, 1));
        assert!(uf.same_no_compress(2, 3));
        assert!(uf.same_no_compress(4, 5));
        assert!(uf.same_no_compress(0, 5)); // Through 0-4-5

        // Pop to level 1
        uf.pop();
        assert!(uf.same_no_compress(0, 1));
        assert!(uf.same_no_compress(2, 3));
        assert!(!uf.same_no_compress(4, 5)); // Undone
        assert!(!uf.same_no_compress(0, 4)); // Undone

        // Pop to level 0
        uf.pop();
        assert!(uf.same_no_compress(0, 1));
        assert!(!uf.same_no_compress(2, 3)); // Undone
    }

    /// Finding 1 (direct reproduction): a scoped path-compression rewrite of an
    /// *intermediate* parent pointer must be undone exactly on `pop()`.
    ///
    /// Union-by-rank keeps trees shallow, so with only a handful of nodes `find()`
    /// never even enters the compression loop. To exercise the trailed-compression
    /// path we must deliberately build a depth-2 tree: two equal-rank rank-1 trees
    /// merged inside a scope leave a grandchild sitting two hops below the root.
    /// A `find()` on that grandchild then rewrites its intermediate pointer, and
    /// `pop()` must restore it precisely.
    ///
    /// This test FAILS on the pre-fix code (compression not trail-recorded): after
    /// pop the grandchild would remain pointing at the deep, retracted root.
    #[test]
    fn scoped_deep_path_compression_is_undone_on_pop() {
        let mut uf = UnionFind::new(4);

        // Base level (no scope): build two rank-1 trees.
        //   union(0,1): equal ranks -> parent[1]=0, rank[0]=1  (root 0, child 1)
        //   union(2,3): equal ranks -> parent[3]=2, rank[2]=1  (root 2, child 3)
        assert!(uf.union(0, 1));
        assert!(uf.union(2, 3));

        // Enter a scope, then merge the two equal-rank trees. root_y (2) becomes a
        // child of root_x (0), rank[0] -> 2. Node 3 now sits at depth 2:
        //   parent[3] = 2, parent[2] = 0, parent[0] = 0.
        uf.push();
        assert!(uf.union(0, 2));
        // Pre-condition: node 3 really is two hops from the root (a compression
        // opportunity actually exists). Uses the immutable walk so we don't perturb
        // the structure before the load-bearing `find`.
        assert_eq!(uf.find_no_compress(3), 0);
        assert_eq!(
            uf.parent[3], 2,
            "node 3 must sit below the intermediate node 2"
        );

        // The load-bearing call: a mutating find(3) that path-compresses the
        // intermediate pointer parent[3] from 2 straight to the root 0. Under the
        // fix this rewrite is trail-recorded because a scope is active.
        assert_eq!(uf.find(3), 0);
        assert_eq!(
            uf.parent[3], 0,
            "find must have compressed parent[3] to the root"
        );

        // Pop the scope: the union(0,2) is retracted, so 3 must return to the {2,3}
        // class and must NOT stay attached to the {0,1} class.
        uf.pop();

        assert!(
            uf.same_no_compress(2, 3),
            "3 must be back with 2 after pop (compression must be undone)"
        );
        assert!(
            !uf.same_no_compress(0, 3),
            "3 must NOT remain equal to 0 after the scoped union is popped \
             (a surviving compressed pointer would corrupt this class)"
        );
        assert!(
            !uf.same_no_compress(1, 3),
            "3 must NOT be equal to 1 after pop"
        );
        // The exact parent array must be restored: 3 -> 2 (root), 2 -> 2.
        assert_eq!(
            uf.parent[3], 2,
            "parent[3] must be restored to its pre-scope value"
        );
        assert_eq!(uf.find_no_compress(3), 2);
    }

    #[test]
    fn test_union_find_backtrack_to() {
        let mut uf = UnionFind::new(4);

        uf.union(0, 1); // Level 0

        uf.push(); // Level 1
        uf.union(1, 2);

        uf.push(); // Level 2
        uf.union(2, 3);

        assert!(uf.same_no_compress(0, 3));

        // Backtrack to level 0
        uf.backtrack_to(0);

        assert!(uf.same_no_compress(0, 1));
        assert!(!uf.same_no_compress(1, 2));
        assert!(!uf.same_no_compress(2, 3));
    }
}
