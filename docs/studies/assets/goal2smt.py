#!/usr/bin/env python3
"""Convert z3 `(goals (goal f1 f2 ... :precision p :depth d))` output to a
standalone SMT2 file with one (assert f) per goal formula. Declarations are
copied from the ORIGINAL file (z3's goal print omits them; without them z3
errors per-command and answers sat on the empty problem!)."""
import sys

src, dst, orig = sys.argv[1], sys.argv[2], sys.argv[3]
text = open(src).read()

# strip the wrapper: (goals\n(goal\n ... :precision precise :depth 6)\n)
start = text.index("(goal", text.index("(goals") + 1)
# find the inner body between "(goal" and the matching close before :precision
depth = 0
i = start + len("(goal")
body_start = i
while i < len(text):
    c = text[i]
    if c == '(':
        depth += 1
    elif c == ')':
        depth -= 1
        if depth == -1:
            break
    i += 1
body = text[body_start:i]

# split body into top-level forms by paren matching
forms = []
depth = 0
cur_start = None
for j, c in enumerate(body):
    if c == '(':
        if depth == 0:
            cur_start = j
        depth += 1
    elif c == ')':
        depth -= 1
        if depth == 0:
            forms.append(body[cur_start : j + 1])
    elif c == ';' and depth == 0:
        # comment to end of line outside any form
        k = body.find('\n', j)
        j = k if k != -1 else len(body)

decls = [l.strip() for l in open(orig) if l.strip().startswith("(declare-fun") or l.strip().startswith("(declare-const")]
# z3's goal printer emits internal div/rem variants (`bvsdiv_i`, `bvudiv_i`,
# ...): the "semantic-attached" total-function versions. SMT-LIB bvsdiv/bvudiv
# have identical semantics, so mapping back is faithful.
for pat, rep in (("bvsdiv_i", "bvsdiv"), ("bvudiv_i", "bvudiv"),
                 ("bvsrem_i", "bvsrem"), ("bvurem_i", "bvurem"),
                 ("bvsmod_i", "bvsmod")):
    forms = [f.replace(pat, rep) for f in forms]
with open(dst, "w") as f:
    f.write("(set-logic QF_BV)\n")
    for d in decls:
        f.write(d + "\n")
    for form in forms:
        f.write("(assert %s)\n" % form)
    f.write("(check-sat)\n")
print(f"{len(forms)} asserts, {len(decls)} decls -> {dst}")
