"""Authenticated heap workloads, including symbolic data and incremental checks."""
import copy
import run as original
import anchor_cases

CASES = [(f, n) for f in original.FAMILIES for n in (4, 16)] + [
    (f, n) for f in ('views', 'free_views') for n in (8, 16, 32)] + [
    (f, n) for f in ('symbolic_views', 'offset_views', 'cache_scopes',
                    'boolean_sat', 'boolean_unsat') for n in (8, 16)] + [('boolean_alias', 16)]


def generate(family, n):
    assert n >= 2
    if family in original.FAMILIES:
        return original.generate(family, n)
    if family == 'views':
        return anchor_cases.generate(family, n)
    if family == 'free_views':
        lines = [f'vars {4*n}']
        lines += ['heap 4 '+' '.join(f'{4*j+i} {i}' for i in range(4)) for j in range(n)]
        lines += [f'bound {i} 1 4' for i in range(4)]
        lines += [f'assert {j} 1' for j in range(n)]
    elif family == 'symbolic_views':
        lines = [f'vars {8*n}']
        lines += ['heapv 4 '+ ' '.join(f'{8*j+i} {8*j+4+i}' for i in range(4)) for j in range(n)]
        lines += [f'bound {i} 1 4' for i in range(4)]
        lines += [f'eq {8*j+i} {i}' for j in range(1, n) for i in range(8)]
        lines += [f'assert {j} 1' for j in range(n)]
    elif family == 'offset_views':
        lines = [f'vars {n}']
        lines += [f'offset {j} {i}' for j in range(n) for i in range(4)]
        lines += ['heap 4 '+' '.join(f'{n+4*j+i} {i}' for i in range(4)) for j in range(n)]
        lines += [f'bound 0 1 {n}'] + [f'eq {j} 0' for j in range(1, n)]
        lines += [f'assert {j} 1' for j in range(n)]
    elif family == 'cache_scopes':
        lines = ['vars 1'] + [f'offset 0 {i}' for i in range(32)]
        for j in range(n):
            order = [(i+j) % 32 for i in range(32)]
            lines.append('heap 32 '+' '.join(f'{i+1} {i}' for i in order))
        lines += [f'bound 0 1 {n+1}', 'assert 0 1']
        for j in range(n):
            lines += ['push', f'assert {j} 1', 'check', 'push', f'assert {j} 0',
                      'check', 'pop', 'check', 'pop']
    elif family in ('boolean_sat', 'boolean_unsat'):
        lines = ['vars 1'] + [f'heap 1 0 {j}' for j in range(n)]
        lines += [f'bound 0 1 {n}']
        groups = [list(range(n))] if family == 'boolean_sat' else [list(range(n//2)), list(range(n//2, n))]
        for j, group in enumerate(groups):
            lines += [f'or {len(group)} '+' '.join(map(str, group)), f'assert {n+j} 1']
    elif family == 'boolean_alias':
        lines = ['vars 2'] + ['heap 2 0 7 1 9']*n
        lines += [f'bound 0 1 {n}', f'bound 1 1 {n}', f'or {n} '+' '.join(map(str, range(n))), f'assert {n} 1']
    else:
        raise ValueError(family)
    return '\n'.join(lines)+'\n'


def parse(text):
    lines = [line.split() for line in text.splitlines()]
    assert lines and lines[0][0] == 'vars' and len(lines[0]) == 2
    count = int(lines[0][1]); assert count >= 0
    case = dict(count=count, terms=[('var', i) for i in range(count)], heaps=[], formulas=[], checks=[])
    active, scopes = [], []
    closed = False
    def term(i):
        assert 0 <= i < len(case['terms'])
        return i
    def formula(i):
        assert 0 <= i < len(case['formulas'])
        return i
    for words in lines[1:]:
        op, nums = words[0], list(map(int, words[1:]))
        if op == 'offset':
            assert len(nums) == 2
            case['terms'].append(('offset', term(nums[0]), nums[1]))
        elif op in ('heap', 'heapv'):
            assert not closed and nums[0] >= 0 and len(nums) == 1+2*nums[0]
            cells = [(term(l), ('term', term(v)) if op == 'heapv' else ('constant', v))
                     for l, v in zip(nums[1::2], nums[2::2])]
            case['formulas'].append(('heap', len(case['heaps'])))
            case['heaps'].append(cells)
        elif op == 'not':
            assert len(nums) == 1
            case['formulas'].append(('not', formula(nums[0])))
        elif op in ('and', 'or'):
            assert nums[0] >= 0 and len(nums) == nums[0]+1
            case['formulas'].append((op, [formula(i) for i in nums[1:]]))
        elif op == 'bound':
            assert len(nums) == 3 and nums[1] <= nums[2]
            active.append(('bound', term(nums[0]), nums[1], nums[2]))
        elif op == 'eq':
            assert len(nums) == 2
            active.append(('eq', term(nums[0]), term(nums[1])))
        elif op == 'assert':
            assert len(nums) == 2 and nums[1] in (0, 1)
            active.append(('assert', formula(nums[0]), bool(nums[1])))
        elif op == 'push':
            assert not nums
            closed = True
            scopes.append(len(active))
        elif op == 'pop':
            assert not nums and scopes
            active = active[:scopes.pop()]
        elif op == 'check':
            assert not nums
            closed = True
            case['checks'].append(copy.deepcopy(active))
        else:
            raise ValueError(op)
    assert not scopes
    if not case['checks']: case['checks'].append(active)
    return case


def term_values(case, values):
    assert all(f'x{i}' in values for i in range(case['count']))
    terms = []
    for expression in case['terms']:
        if expression[0] == 'var': terms.append(values[f'x{expression[1]}'])
        elif expression[0] == 'offset': terms.append(terms[expression[1]]+expression[2])
        else: raise ValueError(expression)
    return terms


def concrete(cells, terms):
    heap = {}
    for location, (kind, value) in cells:
        address = terms[location]
        if address == 0 or address in heap: return None
        if kind == 'term': value = terms[value]
        else: assert kind == 'constant'
        heap[address] = value
    return heap


def validate(case, check, values, heap):
    assert 0 not in heap
    terms = term_values(case, values)
    formulas = []
    for node in case['formulas']:
        kind = node[0]
        if kind == 'heap': value = concrete(case['heaps'][node[1]], terms) == heap
        elif kind == 'not': value = not formulas[node[1]]
        elif kind == 'and': value = all(formulas[i] for i in node[1])
        elif kind == 'or': value = any(formulas[i] for i in node[1])
        else: raise ValueError(node)
        formulas.append(value)
    for constraint in case['checks'][check]:
        kind = constraint[0]
        if kind == 'bound':
            _, term, lo, hi = constraint
            assert lo <= terms[term] <= hi
        elif kind == 'eq': assert terms[constraint[1]] == terms[constraint[2]]
        elif kind == 'assert': assert formulas[constraint[1]] == constraint[2]
        else: raise ValueError(constraint)


def oracle(family, n, text):
    assert text == generate(family, n), 'authenticate the whole program before using its schema'
    case = parse(text)
    if family in original.FAMILIES:
        return [original.oracle(family, n, text)]
    if family == 'views':
        return [anchor_cases.oracle(family, n, text)]
    if family == 'boolean_unsat':
        # Both asserted disjunctions demand one singleton at the same address,
        # but their disjoint sets of stored constants cannot describe one map.
        assert len(case['heaps']) == n
        left = {j for j in range(n//2)}; right = {j for j in range(n//2, n)}
        assert left and right and left.isdisjoint(right)
        return ['unsat']
    values = {f'x{i}': 1 for i in range(case['count'])}
    if family == 'symbolic_views':
        values = {f'x{8*j+i}': i+1 if i < 4 else i-4 for j in range(n) for i in range(8)}
    elif family == 'free_views':
        values = {f'x{4*j+i}': i+1 for j in range(n) for i in range(4)}
    elif family == 'boolean_alias':
        values['x1'] = 2
    heap = concrete(case['heaps'][0], term_values(case, values))
    assert heap is not None
    expected = []
    for check, active in enumerate(case['checks']):
        if family == 'cache_scopes' and check % 3 == 1:
            positive = {c[1] for c in active if c[0] == 'assert' and c[2]}
            negative = {c[1] for c in active if c[0] == 'assert' and not c[2]}
            assert positive & negative
            expected.append('unsat')
        else:
            validate(case, check, values, heap)
            expected.append('sat')
    return expected
