"""Authenticated many-view heap cases; preserve the original checker semantics."""
import run as original

BASE_ORACLE = original.oracle
NEW_FAMILIES = ('views', 'view_conflict', 'unasserted_views')
CASES = [(f, n) for f in original.FAMILIES for n in (2, 4, 8, 16)] + [
    (f, n) for f in NEW_FAMILIES for n in (8, 16, 32, 64)]


def generate(family, n):
    if family not in NEW_FAMILIES:
        return original.generate(family, n)
    assert n >= 2
    lines = [f'vars {4*n}']
    for j in range(n):
        values = [0, 1, 2, 3]
        if family == 'view_conflict' and j == n-1:
            values[3] = 4
        elif family == 'unasserted_views':
            values[3] += j
        lines.append('heap 4 ' + ' '.join(f'{4*j+i} {v}' for i, v in enumerate(values)))
    lines += [f'bound {4*j+i} {i+1} {i+1}' for j in range(n) for i in range(4)]
    lines += [f'assert {i} 1' for i in range(1 if family == 'unasserted_views' else n)]
    return '\n'.join(lines) + '\n'


def oracle(family, n, text):
    if family not in NEW_FAMILIES:
        return BASE_ORACLE(family, n, text)
    assert text == generate(family, n)
    case = original.parse_case(text)
    values = {f'x{i}': i % 4 + 1 for i in range(4*n)}
    heap = {i+1: i for i in range(4)}
    if family == 'view_conflict':
        # Bounds fix a shared address; two asserted exact maps disagree there.
        assert original.concrete(case['heaps'][0], values) == heap
        assert original.concrete(case['heaps'][-1], values)[4] == 4
        assert heap[4] == 3
        return 'unsat'
    original.validate(case, values, heap)
    return 'sat'
