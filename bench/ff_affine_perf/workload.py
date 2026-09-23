"""Fixed coupled-field corpus and independent coefficient-array model oracle."""
from pathlib import Path
import re
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'ff_extension_perf'))
import run as legacy
import z3_reference as reference

CASES = [
    ('pair-f256', 'legacy', 283, 1, True),
    ('budget-f256', 'legacy', 283, 16, True),
    ('coupled-f256-1', 'coupled', 283, 1, True),
    ('coupled-f256-16', 'coupled', 283, 16, True),
    ('certified-coupled-f256', 'certified', 283, 16, True),
    ('inconsistent-f256', 'inconsistent', 283, 1, True),
    ('rank-deficient-f256', 'rank', 283, 1, False),
    ('coupled-f8-a', 'coupled', 11, 3, False),
    ('coupled-f8-b', 'coupled', 13, 3, False),
    ('nonlinear-f16', 'nonlinear', 19, 1, False),
    ('disequality-f16', 'disequality', 19, 1, False),
    ('control-prime', 'legacy', 257, 1, False),
    ('control-wide', 'legacy', 0, 1, False),
]


def generate(case, seed, z3=False):
    name, kind, polynomial, depth, hard = case
    if kind == 'legacy':
        c = next(c for c in legacy.CASES if c['name'] == name)
        if z3:
            script, expected, _ = reference.problem(c, seed)
        else:
            script, expected = legacy.problem(c, seed)
            if name == 'budget-f256':
                script += '(get-value (x y))\n'
                expected['answer'] = 'sat'
        return script, {'legacy': expected}
    k = polynomial.bit_length()-1
    q = 1 << k
    nodes = []
    def op(kind, a, b):
        ident = f't{len(nodes)}'
        nodes.append((ident, kind, a, b))
        return ident
    def square(a): return op('mul', a, a)
    u, v = 'x', 'y'
    if kind in ['coupled', 'certified']:
        for _ in range(depth):
            u, v = op('add', square(u), op('mul', 2, v)), op('add', u, square(v))
        roots = [(u, '='), (v, '=')]
    elif kind in ['rank', 'inconsistent']:
        u = op('add', op('add', square(u), u), op('add', square(v), v))
        roots = [(u, '=')]
    elif kind == 'nonlinear':
        roots = [(op('mul', u, v), '='), (op('add', u, v), '=')]
    else:
        roots = [(op('add', square(u), u), 'distinct'), (v, '=')]
    plants = {'x': 3*q//4 + (seed*7+3) % (q//4),
              'y': 3*q//4 + (seed*11+1) % (q//4)}
    values = evaluate(nodes, plants, polynomial)
    equations = [(root, relation, values[root]) for root, relation in roots]
    answer = 'sat'
    if kind == 'inconsistent':
        image = {legacy.mul(a,a,polynomial)^a for a in range(q)}
        sums = {a^b for a in image for b in image}
        missing = sorted(set(range(q))-sums)
        assert missing
        equations = [(u, '=', missing[seed % len(missing)])]
        answer = 'unsat'
    elif kind == 'disequality':
        equations[0] = (equations[0][0], 'distinct', equations[0][2]^1)
    sort = f'(_ BitVec {k})' if z3 else f'(_ BinaryField {polynomial})'
    literal = lambda a: reference.bv(a,k) if z3 else f'(as ff{a} {sort})'
    text = lambda a: literal(a) if isinstance(a,int) else a
    script = '(set-logic QF_BV)\n' if z3 else '(set-logic QF_FF)\n'
    if z3: script += reference.definitions(polynomial)
    if kind == 'certified' and not z3: script += '(set-option :certified-mode true)\n'
    script += f'(declare-const x {sort}) (declare-const y {sort})\n'
    for ident, operation, a, b in nodes:
        if z3:
            expr = f'(square {text(a)})' if operation == 'mul' and a == b else f'({"bvxor" if operation == "add" else "multiply"} {text(a)} {text(b)})'
        else:
            expr = f'(ff.{operation} {text(a)} {text(b)})'
        script += f'(define-fun {ident} () {sort} {expr})\n'
    for root, relation, target in equations:
        script += f'(assert ({relation} {root} {literal(target)}))\n'
    script += '(check-sat)\n'
    if answer == 'sat': script += '(get-value (x y))\n'
    expected = {'polynomial': polynomial, 'nodes': nodes, 'equations': equations, 'answer': answer, 'plants': plants}
    if answer == 'sat': check_values(plants, expected)
    return script, expected


def evaluate(nodes, values, polynomial):
    values = dict(values)
    for ident, op, a, b in nodes:
        a = a if isinstance(a,int) else values[a]
        b = b if isinstance(b,int) else values[b]
        values[ident] = a^b if op == 'add' else legacy.mul(a,b,polynomial)
    return values


def check_values(values, expected):
    q = 1 << (expected['polynomial'].bit_length()-1)
    assert all(0 <= values[var] < q for var in ['x','y'])
    values = evaluate(expected['nodes'], values, expected['polynomial'])
    assert all((values[root] == target) == (relation == '=') for root, relation, target in expected['equations'])


def verify(output, expected, z3=False):
    answers = re.findall(r'^(sat|unsat|unknown)$', output, re.M)
    assert len(answers) == 1, output
    if answers[0] == 'unknown':
        # Requesting a model after Unknown must not fabricate one.
        errors = re.findall(r'\(error .*', output)
        assert not errors or errors == ['(error "No model available")'], output
        return 'unknown', False
    if 'legacy' in expected:
        (reference.verify if z3 else legacy.verify)(output, expected['legacy'])
        return answers[0], True
    assert answers == [expected['answer']] and '(error' not in output, output
    if answers[0] == 'unsat': return 'unsat', True
    values = {}
    k = expected['polynomial'].bit_length()-1
    for var in ['x','y']:
        if z3:
            match = re.search(r'\('+var+r'\s+(#x[0-9a-fA-F]+|#b[01]+|\(_ bv\d+ \d+\))\)', output)
            assert match, output
            value = match[1]
            if value.startswith('#x'):
                assert 4*(len(value)-2) == k
                values[var] = int(value[2:],16)
            elif value.startswith('#b'):
                assert len(value)-2 == k
                values[var] = int(value[2:],2)
            else:
                v, width = map(int,re.findall(r'\d+',value));assert width==k
                values[var] = v
        else:
            match = re.search(r'\('+var+r' \(as ff(\d+) \(_ BinaryField (\d+)\)\)\)',output)
            assert match and int(match[2]) == expected['polynomial'], output
            values[var] = int(match[1])
    check_values(values, expected)
    return 'sat', True
