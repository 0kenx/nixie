# Stale long-watchers XOR-corrupted clauses

`ext_con_064_002_0512` (known-UNSAT guard) paniced in the list kernel:

```
pair[0] == false_lit || pair[1] == false_lit
```

The watcher was on `Lit(1998)` for a live 11-lit clause whose pair was
`(Lit(733), Lit(735))`. The trigger was not in the clause at all.

Release builds compile that `debug_assert` out. The next two stores are

```
first = pair[0] ^ pair[1] ^ false_lit;
pair[0] = first;
pair[1] = false_lit;
```

so a stale watcher rewrites two live literals to values that were never in
the clause. That is fabricated syntax, not a missed unit.

After dropping the stale watcher without rewriting, compaction reported the
paired hole: `Lit(735)` sat in the watched pair with no watcher on its
negation. A Gent replacement had updated the pair, but the destination
watcher was not installed (delayed flush) and the source watcher remained.

Production now:

1. Never XOR-normalizes unless the trigger is already in the pair.
2. Drops a stale watcher and re-installs watches on the current pair.
3. Installs Gent replacement watches immediately on the destination list,
   not through the delayed buffer.

`known_unsound_regressions` (6) pass, including `ext_con_064`. SAT lib 825
tests pass. The delayed `MoveWriter::push` path is unused on the complete
session; it remains wired for the empty flush.
