"""One complete workload, with independent checking of every SAT snapshot."""
import argparse
import json
import re
import resource
import subprocess
from pathlib import Path

import next_cases as cases
import run as original


def numeral(value):
    return str(value) if value >= 0 else f'(- {-value})'


def smt(case, check, native, want_model):
    lines = ['(set-logic ALL)', '(set-option :produce-models true)']
    if native:
        lines += ['(declare-heap (Int Int))', '(assert (= (as sep.nil Int) 0))']
    else:
        lines += ['(declare-const domain (Array Int Bool))', '(declare-fun data (Int) Int)',
                  '(assert (not (select domain 0)))']
    lines += [f'(declare-const x{i} Int)' for i in range(case['count'])]
    terms = []
    for index, expression in enumerate(case['terms']):
        if expression[0] == 'var': terms.append(f'x{expression[1]}')
        else:
            assert expression[0] == 'offset'
            name = f't{index}'
            lines.append(f'(define-fun {name} () Int (+ {terms[expression[1]]} {numeral(expression[2])}))')
            terms.append(name)
    for index, heap in enumerate(case['heaps']):
        cells = [(terms[l], terms[v] if kind == 'term' else numeral(v)) for l, (kind, v) in heap]
        if native:
            cells = [f'(pto {l} {v})' for l, v in cells]
            body = 'sep.emp' if not cells else cells[0] if len(cells) == 1 else '(sep '+' '.join(cells)+')'
        else:
            domain = '((as const (Array Int Bool)) false)'
            for location, _ in cells: domain = f'(store {domain} {location} true)'
            parts = [f'(= domain {domain})']
            parts += [f'(not (= {location} 0))' for location, _ in cells]
            parts += [f'(not (= {location} {other}))' for j, (location, _) in enumerate(cells) for other, _ in cells[:j]]
            parts += [f'(= (data {location}) {value})' for location, value in cells]
            body = '(and '+' '.join(parts)+')'
        lines.append(f'(define-fun h{index} () Bool {body})')
    for index, node in enumerate(case['formulas']):
        if node[0] == 'heap': body = f'h{node[1]}'
        elif node[0] == 'not': body = f'(not f{node[1]})'
        elif node[0] in ('or', 'and'):
            body = f'({node[0]} '+ ' '.join(f'f{i}' for i in node[1])+')' if node[1] else ('true' if node[0] == 'and' else 'false')
        else: raise ValueError(node)
        lines.append(f'(define-fun f{index} () Bool {body})')
    for constraint in case['checks'][check]:
        if constraint[0] == 'bound':
            _, index, lo, hi = constraint
            body = f'(and (<= {numeral(lo)} {terms[index]}) (<= {terms[index]} {numeral(hi)}))'
        elif constraint[0] == 'eq': body = f'(= {terms[constraint[1]]} {terms[constraint[2]]})'
        elif constraint[0] == 'assert': body = f'f{constraint[1]}' if constraint[2] else f'(not f{constraint[1]})'
        else: raise ValueError(constraint)
        lines.append(f'(assert {body})')
    lines.append('(check-sat)')
    if want_model:
        names = [f'x{i}' for i in range(case['count'])]
        if not native: names += [f'h{i}' for i in range(len(case['heaps']))]
        if names: lines.append('(get-value ('+' '.join(names)+'))')
        if native: lines.append('(get-model)')
    return '\n'.join(lines)+'\n'


def reference_model(case, check, output, native):
    roots = original.sexprs(output)
    pairs = roots[1]
    assert isinstance(pairs, list)
    values = {name: original.integer(value) for name, value in pairs if name.startswith('x')}
    if native:
        models = [r for r in roots if isinstance(r, list) and r and r[0] == 'heap']
        assert len(models) == 1
        heap, stack = {}, [models[0][1]]
        while stack:
            cell = stack.pop()
            if cell == 'sep.emp': continue
            assert isinstance(cell, list) and cell
            if cell[0] == 'sep': stack.extend(cell[1:])
            else:
                assert cell[0] == 'pto' and len(cell) == 3
                location, value = original.integer(cell[1]), original.integer(cell[2])
                assert location not in heap
                heap[location] = value
    else:
        phases = {int(name[1:]): value == 'true' for name, value in pairs if name.startswith('h')}
        assert all(value in ('true', 'false') for name, value in pairs if name.startswith('h'))
        assert len(phases) == len(case['heaps'])
        terms = cases.term_values(case, values)
        selected = next((i for i, value in phases.items() if value), None)
        heap = cases.concrete(case['heaps'][selected], terms) if selected is not None else {
            i+1: 0 for i in range(max(map(len, case['heaps']), default=0)+1)}
        assert heap is not None
        assert all((cases.concrete(h, terms) == heap) == phases[i] for i, h in enumerate(case['heaps']))
    cases.validate(case, check, values, heap)


def driver_result(case, expected, output, arm):
    blocks = re.findall(r'^begin (\d+)\n(.*?)^end (\d+)\n', output, re.M | re.S)
    assert len(blocks) == len(expected), 'missing check snapshot'
    answers, diagnostics = [], []
    for index, ((begin, block, end), wanted) in enumerate(zip(blocks, expected)):
        assert int(begin) == index == int(end)
        answers_here = re.findall(r'^(sat|unsat|unknown)$', block, re.M)
        assert len(answers_here) == 1
        answer = answers_here[0]
        assert answer in (wanted, 'unknown'), f'WRONG ANSWER at check {index}: {block}'
        if answer == 'sat':
            values, heap = {}, {}
            for line in block.splitlines():
                parts = line.split()
                if parts[0] == 'var':
                    assert parts[1] not in values
                    values[parts[1]] = int(parts[2])
                elif parts[0] == 'cell':
                    address = int(parts[1]); assert address not in heap
                    heap[address] = int(parts[2])
            cases.validate(case, index, values, heap)
        stats = {}
        for label, width in [('sizes', 3), ('definitions', 1), ('comparisons', 1), ('search', 3), ('optimization', 4)]:
            matches = re.findall(rf'^{label} ((?:\d+ ?)+)$', block, re.M)
            if label == 'optimization' and arm == 'baseline':
                assert not matches
                continue
            assert len(matches) == 1
            stats[label] = list(map(int, matches[0].split()))
            assert len(stats[label]) == width
        answers.append(answer); diagnostics.append(stats)
    return answers, diagnostics


def worker(args):
    text = args.case.read_text()
    family, n = args.case.stem.rsplit('-', 1)
    expected = cases.oracle(family, int(n), text)
    case = cases.parse(text)
    if args.arm in ('cvc5-sl', 'z3-array'):
        answers, outputs, errors = [], [], []
        native = args.arm == 'cvc5-sl'
        for index, wanted in enumerate(expected):
            command = ([args.cvc5, '--lang=smt2', f'--seed={args.seed}', f'--sat-random-seed={args.seed}', '--rlimit=2000000']
                       if native else [args.z3, '-in', f'smt.random_seed={args.seed}', 'rlimit=2000000'])
            result = subprocess.run(command, input=smt(case, index, native, wanted == 'sat'), text=True, capture_output=True)
            found = re.findall(r'^(sat|unsat|unknown)$', result.stdout, re.M)
            assert len(found) == 1 and found[0] in (wanted, 'unknown'), result
            if found[0] != 'unknown': assert result.returncode == 0, result
            if found[0] == 'sat': reference_model(case, index, result.stdout, native)
            answers.append(found[0]); outputs.append(result.stdout); errors.append(result.stderr)
        output, stderr, diagnostics = '\n'.join(outputs), '\n'.join(errors), []
    else:
        command = [args.driver, str(args.case), str(args.seed), args.arm]
        result = subprocess.run(command, text=True, capture_output=True)
        assert result.returncode == 0, result
        output, stderr = result.stdout, result.stderr
        answers, diagnostics = driver_result(case, expected, output, args.arm)
    answer = 'unknown' if 'unknown' in answers else answers[-1]
    print(json.dumps(dict(answer=answer, verified=answer != 'unknown', check_answers=answers,
                         diagnostics=diagnostics, stdout=output, stderr=stderr,
                         solver_peak_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', type=Path, required=True)
    parser.add_argument('--driver', required=True)
    parser.add_argument('--arm', required=True)
    parser.add_argument('--seed', type=int, required=True)
    parser.add_argument('--cvc5', required=True)
    parser.add_argument('--z3', required=True)
    worker(parser.parse_args())
