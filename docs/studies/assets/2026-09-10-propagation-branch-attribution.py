"""Offline decoding for the registered exact PEBS + flagged LBR layout.

Raw sample IPs and LBR history are separate observations. Only IP == the
newest M-flagged branch source is associated without ambiguity here.
"""
import collections
import json
from pathlib import Path
import re
import struct
import subprocess

GROUPS = {
    'binary span empty': [0x638c3],
    'binary loop end': [0x638f7],
    'binary truth': [0x63903, 0x63909],
    'long list empty': [0x63a19],
    'long list loop end': [0x63a67, 0x63bec, 0x63bfa, 0x63c53, 0x63f03],
    'long blocker truth': [0x63a7c, 0x63c69, 0x63f1c],
    'header null/deleted': [0x63a86, 0x63a92, 0x63c94, 0x63c9c, 0x63f44, 0x63f4c],
    'other watched truth': [0x63ac6, 0x63cd0, 0x63f80],
    'long tail bound': [0x63ae3, 0x63d13, 0x63fc3],
    'long tail positive': [0x63af1, 0x63d21, 0x63fd1],
    'long tail false vs undefined': [0x63afd, 0x63d2d, 0x63fdd],
    'long unit vs conflict': [0x63b10, 0x63db9, 0x6405b],
    'destination capacity': [0x63bcf, 0x63d73, 0x6401e],
}


def group_sites(result):
    """Reviewed, nonoverlapping branch addresses for this exact binary."""
    groups, seen = [], set()
    for name, addresses in GROUPS.items():
        assert not seen.intersection(addresses)
        seen.update(addresses)
        n = sum(row['samples'] for row in result['sampled_ips'] if int(row['ip'], 16) in addresses)
        groups.append(dict(group=name, ips=[hex(a) for a in addresses], samples=n,
                           percent_all=100*n/result['samples']))
    return groups


def records(path):
    with Path(path).open('rb') as f:
        header = struct.unpack('<13Q', f.read(104))
        assert header[0] == 0x32454C4946524550 and header[1:3] == (104, 160)
        assert header[4] == 480
        f.seek(header[3])
        attrs = f.read(header[4])
        leader, follower = [struct.unpack_from('<II6Q', attrs, off) for off in (0, 160)]
        assert leader[:6] == (10, 144, 197, 200003, 67991, 31), leader
        assert follower[:6] == (10, 144, 192, 0, 67991, 23), follower
        assert (leader[6] >> 15) & 3 == 2  # precise_ip
        assert leader[6] & (1 << 5)       # exclude_kernel
        assert struct.unpack_from('<Q', attrs, 72)[0] == 9  # USER | ANY
        f.seek(header[5])
        end = header[5] + header[6]
        while f.tell() < end:
            kind, misc, size = struct.unpack('<IHH', f.read(8))
            assert size >= 8 and f.tell() + size - 8 <= end
            yield kind, misc, f.read(size - 8)
        assert f.tell() == end


def mapping(path, binary):
    with binary.open('rb') as f:
        elf = struct.unpack('<16sHHIQQQIHHHHHH', f.read(64))
        assert elf[0][:6] == b'\x7fELF\x02\x01' and elf[9] == 56
        f.seek(elf[5])
        segments = [struct.unpack('<II6Q', f.read(56)) for _ in range(elf[10])]
        executable = [s for s in segments if s[0] == 1 and s[1] & 1]
        assert len(executable) == 1
        seg = executable[0]
    offsets = set()
    for kind, _, data in records(path):
        if kind != 10 or data[64:].split(b'\0', 1)[0] != str(binary).encode():
            continue
        addr, _, pgoff = struct.unpack_from('<3Q', data, 8)
        if pgoff == seg[2] // 4096 * 4096:
            offsets.add(addr - seg[3] // 4096 * 4096)
    assert len(offsets) == 1, offsets
    return offsets.pop(), (seg[3], seg[3] + seg[5])


def assembly(binary, folder):
    path = folder / 'disassembly.txt'
    if not path.exists():
        with path.open('x') as out:
            subprocess.run(['objdump', '-d', '-w', '-C', '--no-show-raw-insn', '-Mintel', str(binary)],
                           stdout=out, check=True)
    instructions = {}
    function = None
    for line in path.read_text().splitlines():
        symbol = re.fullmatch(r'([0-9a-f]+) <(.*)>:', line)
        if symbol:
            function = symbol[2]
            continue
        instruction = re.fullmatch(r'\s*([0-9a-f]+):\s+(.+)', line)
        if instruction:
            assert function is not None
            instructions[int(instruction[1], 16)] = (function, instruction[2])
    assert instructions[0x63790][0].endswith('propagation_engine::propagate')
    return instructions


def analyze(path, binary, folder):
    bias, extent = mapping(path, binary)
    instructions = assembly(binary, folder)
    counts, cpus, modes, ids, exact = [collections.Counter() for _ in range(5)]
    ips, newest, direct, relations, stack_flags = [collections.Counter() for _ in range(5)]
    minimum, previous, first, lost, periods = 1., None, None, 0, 0
    for kind, misc, data in records(path):
        counts[kind] += 1
        if kind != 9:
            continue
        identifier, ip, pid, tid, timestamp, cpu, reserved, period = struct.unpack_from('<QQIIQIIQ', data)
        assert reserved == 0 and period > 0 and pid == tid
        nr, enabled, running = struct.unpack_from('<3Q', data, 48)
        assert nr == 2 and 0 < running <= enabled
        values = [struct.unpack_from('<3Q', data, 72 + i * 24) for i in range(2)]
        assert values[0][1] == identifier and all(v[0] > 0 for v in values)
        state = (timestamp, enabled, running, values[0][0], values[1][0])
        if previous is not None:
            assert all(a >= b for a, b in zip(state, previous))
        else:
            first = state
        previous = state
        minimum = min(minimum, running / enabled)
        lost += sum(v[2] for v in values)
        periods += period
        cpus[cpu] += 1; modes[misc & 7] += 1; ids[identifier] += 1
        exact[bool(misc & (1 << 14))] += 1
        ips[ip - bias] += 1
        branches = struct.unpack_from('<Q', data, 120)[0]
        assert 128 + branches * 24 == len(data)
        if branches == 0:
            relations['empty_history'] += 1
            continue
        source, target, flags = struct.unpack_from('<3Q', data, 128)
        stack_flags[flags & 3] += 1
        newest[(source - bias, bool(flags & 1))] += 1
        if ip == source and flags & 1:
            relations['ip_equals_newest_mispredicted_source'] += 1
            direct[source - bias] += 1
        elif ip == target and flags & 1:
            relations['ip_equals_newest_mispredicted_target'] += 1
        else:
            relations['unassociated'] += 1
    assert previous is not None and sum(ips.values()) == counts[9]

    def desc(ip):
        if ip in instructions:
            symbol, insn = instructions[ip]
            return dict(ip=hex(ip), function=symbol, instruction=insn)
        return dict(ip=hex(ip), function='unresolved in executable' if extent[0] <= ip < extent[1]
                    else 'external mapping', instruction='unknown')

    functions = collections.Counter()
    for ip, n in ips.items():
        functions[desc(ip)['function']] += n
    result = dict(samples=counts[9], record_counts=dict(counts), sample_cpus=dict(cpus),
                  sample_modes=dict(modes), sample_identifiers=dict(ids), precise_ip_flags=dict(exact),
                  minimum_read_coverage=minimum, first_read=first, last_read=previous,
                  sampled_period_sum=periods, lost_read_sum=lost,
                  newest_history_flags=dict(stack_flags), ip_history_associations=dict(relations),
                  load_bias=bias, executable_extent=extent, self_functions=dict(functions.most_common()),
                  sampled_ips=[dict(desc(ip), samples=n, sample_share=n/counts[9]) for ip,n in ips.most_common()],
                  directly_associated_sources=[dict(desc(ip), samples=n, sample_share=n/counts[9])
                                               for ip,n in direct.most_common()],
                  newest_history_sources=[dict(desc(ip), mispredicted=miss, samples=n)
                                          for (ip,miss),n in newest.most_common()],
                  counters_are_sampled_prefix_only=True)
    result['quality_passed'] = (counts[2] == counts[13] == counts[5] == counts[6] == lost == 0
                               and minimum >= .999 and set(cpus) == {15} and len(ids) == 1
                               and counts[9] >= 1000 and modes[2] == counts[9]
                               and exact[True] == counts[9]
                               and functions['unresolved in executable'] == 0)
    result['source_groups'] = group_sites(result)
    with (folder/'branch-misses.folded').open('x') as out:
        for ip,n in sorted(ips.items()):
            d = desc(ip)
            label = d['function'].replace(';', ':')
            out.write(f"Precise branch-miss sample IP (not cycles);{label};{d['ip']} {d['instruction']} {n}\n")
    return result


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('data', type=Path)
    parser.add_argument('binary', type=Path)
    parser.add_argument('output', type=Path, help='new, empty output directory')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    result = analyze(args.data, args.binary.resolve(), args.output)
    (args.output/'analysis.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps(dict(samples=result['samples'], quality_passed=result['quality_passed'],
                          source_groups=result['source_groups']), indent=2))
