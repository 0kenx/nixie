#!/usr/bin/env python3
"""SMT2 (QF_BV) -> DIMACS via z3's `apply (then simplify bit-blast tseitin-cnf)`.

z3 prints the equisatisfiable CNF as an SMT2 goal with Boolean atoms `k!N`.
We tokenize the printed goals, map each distinct k!N to a DIMACS variable
(first-appearance order), and emit one clause per goal assertion.

Fidelity contract: the emitted CNF is equisatisfiable with the input formula
(tseitin encoding, free Boolean/BV vars stay free), so
  kissat(cnf) == z3(smt2)
must hold for every instance; any mismatch is a converter (or solver) bug.
"""
import re
import sys
import subprocess

# A DIMACS-variable-able atom: z3's k!N tseitin names, or any simple
# SMT-LIB identifier (free Booleans keep their declared names).
ATOM_OK = re.compile(r'[A-Za-z0-9_!?.$@#~^&*+/<>=%-]+')


def tokenize(text: str):
    """Yield S-expression tokens: '(', ')', and atoms."""
    for m in re.finditer(r'\(|\)|[^\s()]+', text):
        yield m.group(0)


def parse_sexps(tokens):
    """Parse all top-level S-expressions from a token stream."""
    stack, top = [], []
    for t in tokens:
        if t == '(':
            stack.append(top)
            top = []
        elif t == ')':
            if not stack:
                raise ValueError("unbalanced ')'")
            done, top = top, stack.pop()
            top.append(done)
        else:
            top.append(t)
    if stack:
        raise ValueError("unbalanced '('")
    return top


def collect_goals(node, out):
    """Walk the parsed (goals (goal ...) ...) tree; append clause sexps."""
    if isinstance(node, list):
        if node and node[0] == 'goal':
            # children up to the first :keyword are assertions
            for c in node[1:]:
                if isinstance(c, str) and c.startswith(':'):
                    break
                out.append(c)
        else:
            for c in node:
                collect_goals(c, out)


def clause_of(sexp, varmap):
    """Convert one assertion sexp to a DIMACS clause (list of ints).

    Returns None for `true` (no constraint); returns [] for `false`/empty or
    (or false ...)-style contradictions (empty clause = unsat).
    Free Boolean atoms keep their names (z3 renames tseitin auxiliaries to
    k!N but leaves declared Booleans as-is) — both are keyed by symbol.
    """
    def lit(node):
        if isinstance(node, str):
            if node == 'true':
                return 'T'
            if node == 'false':
                return 'F'
            if re.fullmatch(r'k!\d+', node) or ATOM_OK.match(node):
                if node not in varmap:
                    varmap[node] = len(varmap) + 1
                return varmap[node]
            raise ValueError(f"unexpected atom {node!r}")
        if isinstance(node, list) and len(node) == 2 and node[0] == 'not':
            v = lit(node[1])
            return -v if isinstance(v, int) else ('F' if v == 'T' else 'T')
        if isinstance(node, list) and node and node[0] == 'or':
            lits = []
            for c in node[1:]:
                v = lit(c)
                if v == 'T':
                    return 'T'          # clause subsumed
                if v != 'F':
                    lits.append(v)
            return lits
        raise ValueError(f"unexpected form {node!r}")

    r = lit(sexp)
    if r == 'T':
        return None                     # tautology -> drop
    if r == 'F':
        return []                       # false -> empty clause
    if isinstance(r, int):
        return [r]                      # bare unit clause
    return r


def smt2_to_dimacs(smt2_path: str, cnf_path: str, z3: str = 'z3') -> None:
    script = (f'(set-option :model false)\n'
              f'(apply (then simplify bit-blast tseitin-cnf))\n')
    src = open(smt2_path, 'r', errors='replace').read()
    # corpus files end with (check-sat)/(exit); z3 stops executing at (exit),
    # so strip both before appending the tactic application
    src = re.sub(r'\(exit\)\s*$', '', src.strip())
    src = re.sub(r'\(check-sat\)\s*$', '', src.strip())
    p = subprocess.run([z3, '-in', '-smt2'], input=src + '\n' + script,
                       capture_output=True, text=True, timeout=1800)
    if p.returncode != 0 or '(error' in p.stdout or '(error' in p.stderr:
        raise RuntimeError(f"z3 apply failed: {p.stdout[:400]} {p.stderr[:400]}")
    goals = []
    collect_goals(parse_sexps(list(tokenize(p.stdout))), goals)
    if not goals:
        raise RuntimeError("no goals parsed")
    varmap, clauses = {}, []
    for g in goals:
        c = clause_of(g, varmap)
        if c is not None:
            clauses.append(c)
    with open(cnf_path, 'w') as f:
        f.write(f"p cnf {len(varmap)} {len(clauses)}\n")
        for c in clauses:
            f.write(' '.join(map(str, c)) + ' 0\n')
    return len(varmap), len(clauses)


if __name__ == '__main__':
    nv, nc = smt2_to_dimacs(sys.argv[1], sys.argv[2])
    print(f"{sys.argv[2]}: {nv} vars, {nc} clauses")
