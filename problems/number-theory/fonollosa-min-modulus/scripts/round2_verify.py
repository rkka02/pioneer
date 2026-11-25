"""Independent exact checks for Round 2. Python integers store residue bitsets."""

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from functools import cache
from itertools import combinations, product
from math import comb, gcd
from pathlib import Path
from subprocess import check_output
from random import Random


def rotate(x, s, n, mask):
    return ((x << s) & mask) | (x >> (n - s))


def adjoin(rows, x, n):
    """Capped multiplicities. The two bitsets mean at least one and at least two."""
    seen, twice = rows
    mask = (1 << n) - 1
    new, duplicate = [1], [0]
    for k in range(1, len(seen)):
        with_x = rotate(new[-1], x, n, mask)
        duplicate.append(twice[k] | rotate(duplicate[-1], x, n, mask) | (with_x & seen[k]))
        new.append(seen[k] | with_x)
    return new, duplicate


def empty(k):
    return [1] + [0] * k, [0] * (k + 1)


def valid(A, n):
    rows = empty(len(A))
    for x in A:
        rows = adjoin(rows, x, n)
    return not (rows[1][-1] >> (sum(A) % n) & 1)


def certificates(path):
    totals = Counter()
    for line in Path(path).read_text().splitlines():
        if not line.startswith('case '):
            continue
        _, family, ns, ms, ks, ss, *data = line.split()
        size, n, k, simple = map(int, (ns, ms, ks, ss))
        a, rival = list(map(int, data[:size])), list(map(int, data[size:]))
        assert len(a) == size and n < 2**size - 2 ** (size.bit_length() - 1)
        if k == -1:
            assert len(set(a)) < size
            totals['collapsed'] += 1
        else:
            assert 2 <= k <= 6 and simple.bit_count() == len(rival) == k
            baseline = [i for i in range(size) if simple >> i & 1]
            assert sorted(rival) != baseline and all(0 <= i < size for i in rival)
            assert sum(a[i] for i in baseline) % n == sum(a[i] for i in rival) % n
            totals['witnesses'] += 1
        totals[family] += 1
    assert totals['witnesses'] + totals['collapsed'] == 3036
    print('checked', dict(sorted(totals.items())))


def packing(A, n, a, b):
    d = (b - a) % n
    R = [x for x in A if x != a and x != b]
    C = [(0, 0)]
    for x in R:
        C += [((s + x - a) % n, h + 1) for s, h in C]
    positions = set(C)
    E = sum(((s + 2 * d) % n, h) in positions for s, h in C)
    slots = {((s + ((i - h) // 2) * d) % n, (i - h) % 2) for s, h in C for i in range(5)}
    assert len(slots) == 5 * len(C) - E
    if 2 * d % n:
        assert 2 * E <= len(C)
    return E


def all_pivot_intervals(A, n):
    for a, b in combinations(A, 2):
        R = [x for x in A if x != a and x != b]
        cube = [(0, 0)]
        for x in R:
            cube += [((s + x - a) % n, h + 1) for s, h in cube]
        masks = {pair: i for i, pair in enumerate(cube)}
        if len(masks) != len(cube):
            return False
        for i, (s, h) in enumerate(cube):
            for k in range(len(R) + 1):
                for j in range(min(0, h - k) - 1, max(0, h - k) + 2):
                    other = masks.get(((s - j * (b - a)) % n, k), i)
                    if other != i:
                        return False
    return True


def ten_exceptions(A, n):
    total = sum(A) % n
    for triple in combinations(A, 3):
        s = 3 * sum(triple)
        # The extra point is either the singleton or the point of multiplicity four.
        if any((s + x) % n == total for x in A):
            return True
    return False


def structure():
    # All weak compositions of ten into ten multiplicities.
    shapes = Counter()
    for cuts in combinations(range(19), 9):
        stops = (-1, *cuts, 19)
        counts = tuple(stops[i + 1] - stops[i] - 1 for i in range(10))
        if sum(k >= 3 for k in counts) >= 3:
            shapes[tuple(sorted(k for k in counts if k))] += 1
    assert shapes == {(1, 3, 3, 3): 840, (3, 3, 4): 360}
    A = (0, 1, 3, 63, 75, 91, 115)
    for a in A:
        cube = {0}
        for x in A:
            if x != a:
                cube |= {(s + x - a) % 120 for s in cube}
        assert len(cube) == 64
    rival = (0, 0, 0, 3, 75, 75, 75)
    assert len(rival) == len(A) and sum(A) % 120 == sum(rival) % 120 and tuple(sorted(rival)) != A
    assert not all_pivot_intervals(A, 120)
    # Build an integer example for each exceptional multiplicity shape. One
    # coefficient -1 allows eliminating a coordinate of a positional basis.
    rng = Random(260708366)
    controls = [(tuple((1 << j) - 1 for j in range(10)), 1016)]
    for coeff in ((2, 2, 2, 0, -1, -1, -1, -1, -1, -1), (3, 2, 2, -1, -1, -1, -1, -1, -1, -1)):
        basis = tuple(64**j for j in range(9))
        last = sum(a * c for a, c in zip(basis, coeff))
        points = basis + (last,)
        modulus = 100 * sum(map(abs, points))
        signed = tuple(x % modulus for x in points)
        assert all_pivot_intervals(signed, modulus) and ten_exceptions(signed, modulus)
    for _ in range(100):
        n = rng.randrange(569, 1017)
        controls.append((tuple(sorted(rng.sample(range(n), 10))), n))
    for points, n in controls:
        assert valid(points, n) == (
            all_pivot_intervals(points, n) and not ten_exceptions(points, n)
        )
    print(
        'heavy multiplicity patterns',
        dict(shapes),
        'two exact integer examples',
        'DP comparisons',
        len(controls),
    )


def targets():
    binary = tuple((1 << i) - 1 for i in range(10))
    defects = []
    for a, b in combinations(binary, 2):
        cube = [(0, 0)]
        for x in binary:
            if x != a and x != b:
                cube += [((s + x - a) % 1016, h + 1) for s, h in cube]
        image = {
            ((s + (j - h) // 2 * (b - a)) % 1016, (j - h) % 2) for s, h in cube for j in range(8)
        }
        defects.append(2048 - len(image))
    print('eight-label endpoint defects', min(defects), max(defects))
    prefixes = [
        (0, 1, 3, 120, 161, 265),
        (0, 1, 4, 113, 164, 248),
        (0, 1, 5, 85, 119, 126),
        (0, 1, 3, 56, 233, 253),
        binary[:6],
    ]
    n = 1015
    mask = (1 << n) - 1
    for P in prefixes:
        rows = empty(10)
        for x in P:
            rows = adjoin(rows, x, n)
        assert not (rows[1][6] >> (sum(P) % n) & 1)
        vertices = {}
        extensions = {}
        for x in range(P[-1] + 1, n):
            child = adjoin(rows, x, n)
            if child[1][7] >> ((sum(P) + x) % n) & 1:
                continue
            holes = mask ^ child[0][10]
            if holes:
                extensions[x] = child
            while holes:
                bit = holes & -holes
                vertices.setdefault(bit.bit_length() - 1, []).append(x)
                holes ^= bit
        viable = [(s, L) for s, L in vertices.items() if len(L) >= 4]
        print(
            'prefix',
            P,
            'holes',
            (mask ^ rows[0][10]).bit_count(),
            'viable targets',
            len(viable),
            end=' ',
        )
        if P != binary[:6]:
            edges = cliques = 0
            for s, L in viable:
                pairs = {
                    (x, y)
                    for x, y in combinations(L, 2)
                    if not (adjoin(extensions[x], y, n)[0][10] >> s & 1)
                }
                edges += len(pairs)
                cliques += sum(
                    (sum(P) + sum(Q)) % n == s and all(pair in pairs for pair in combinations(Q, 2))
                    for Q in combinations(L, 4)
                )
            print('edges', edges, 'cliques with required sum', cliques, end=' ')
            assert cliques == 0
        print()


def small():
    tally = Counter()
    for n in range(3, 29):
        for sz in range(3, min(6, n + 1)):
            for rest in combinations(range(1, n), sz - 1):
                A = (0,) + rest
                if not valid(A, n):
                    continue
                tally['anchored_valid'] += 1
                for a, b in combinations(A, 2):
                    packing(A, n, a, b)
                    tally['pivot_pairs'] += 1
                assert 9 * 2 ** (sz - 2) <= 4 * n
    # A prime-modulus example for the one-pivot Fourier and sumset relaxations.
    B = [1 << i for i in range(9)]
    p = 521
    U = {0}
    for x in B:
        U |= {(y + x) % p for y in U}
    assert U == set(range(512))
    diff = Counter((x - y) % p for x in U for y in U)
    assert len(diff) == p and sum(diff.values()) == 512**2 and diff[0] == 512
    assert not valid([0] + B, p)
    # Rational primal feasible point for the pairwise, rank-coloured LP on 569 residues.
    ranks = [comb(8, i) for i in range(9)]
    assert sum(ranks) == 256 and 2 * sum(ranks) <= 569
    assert all(u + v <= 569 for u in ranks for v in ranks)
    A = [(1 << i) - 1 for i in range(10)]
    assert valid(A, 1016)
    found = {}
    for x in A[1:]:
        P = [(0, ())]
        for v in A[1:]:
            if v != x:
                P += [(s + v, t + (v,)) for s, t in P]
        U = {
            s: t
            for s, t in [(s % 1016, t) for s, t in P] + [((s + x) % 1016, t + (x,)) for s, t in P]
        }
        for mult in (2, 3):
            for s, t in P:
                residue = (mult * x + s) % 1016
                if residue in U:
                    found.setdefault(mult, (x, t, U[residue]))
                    break
    print('small', dict(tally), 'binary translated overlaps', found)


@cache
def line_signatures(prime, size, center):
    result = Counter()
    for extra in combinations(range(2, prime), size - 1):
        points = (1,) + extra
        if center and not valid((0,) + points, prime):
            continue
        rows = empty(10)
        for x in points:
            rows = adjoin(rows, x, prime)
        total = sum(points) % prime
        signature = tuple((a >> total & 1) + (b >> total & 1) for a, b in zip(*rows))
        if signature[size] == 1:
            result[signature] += 1
    return result


def nonunits():
    for primes in ((5, 11, 17), (3, 11, 29), (3, 17, 19), (2, 17, 29), (7, 11, 13), (5, 7, 29)):
        n = primes[0] * primes[1] * primes[2]
        checked = hits = 0
        for center in (0, 1):
            ranges = [range(1, min(p - 1, p.bit_length() - center) + 1) for p in primes]
            for sizes in product(*ranges):
                if sum(sizes) + center != 10:
                    continue
                local = [line_signatures(p, k, center) for p, k in zip(primes, sizes)]
                for (a, na), (b, nb), (c, nc) in product(*(sig.items() for sig in local)):
                    # A zero at the center can fill any unused multiplicity.
                    reps = sum(
                        a[i] * b[j] * c[k]
                        for i in range(11)
                        for j in range(11 - i)
                        for k in (range(11 - i - j) if center else (10 - i - j,))
                    )
                    checked += na * nb * nc
                    if reps == 1:
                        hits += na * nb * nc
        print('three axes', n, 'normalized candidates', checked, 'valid', hits, flush=True)


def nonunit_range(binary, first, last, workers):
    def prime_factors(n):
        count = 0
        for p in range(2, n + 1):
            if n % p == 0:
                count += 1
                while n % p == 0:
                    n //= p
        return count

    def solve(n):
        return check_output([binary, str(n), '-1', '2', str(n), '1'], text=True).strip()

    assert 512 <= first <= last < 1024 and workers > 0
    required = [n for n in range(first, last + 1) if prime_factors(n) >= 3]
    total = 0
    with ThreadPoolExecutor(max_workers=workers) as pool:
        jobs = {pool.submit(solve, n): n for n in reversed(required)}
        for job in as_completed(jobs):
            result = job.result()
            print(result, flush=True)
            row = result.splitlines()[-1].split()
            assert row[:3] == ['complete', str(jobs[job]), '-1'] and row[7] == 'leaves'
            total += int(row[8])
    print(
        'nonunit range',
        first,
        last,
        'enumerated',
        len(required),
        'by generation',
        last - first + 1 - len(required),
        'leaves',
        total,
    )


def census(n, seed, lower=None, upper=None):
    """Fixed increasing prefix or interval of unit-normalized third coordinates."""
    allbits = (1 << n) - 1
    inv = [pow(x, -1, n) if gcd(x, n) == 1 else 0 for x in range(n)]
    visits = Counter()

    def triple_good(a, b, c, minimum):
        if minimum <= 2:
            return True
        for i, j, k in ((a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)):
            u = inv[(j - i) % n]
            if u and (k - i) * u % n < minimum:
                return False
        return True

    def dfs(A, rows, possible, minimum):
        k = len(A)
        total = sum(A) % n
        visits[k] += 1
        if rows[1][k] >> total & 1 or rows[0][10] == allbits:
            return
        if len(possible) < 10 - k:
            return
        if k == 8:
            # Both remaining values are determined by one value and the final target.
            allowed = set(possible)
            holes = allbits ^ rows[0][10]
            while holes:
                bit = holes & -holes
                holes ^= bit
                p = bit.bit_length() - 1
                for x in possible:
                    y = (p - total - x) % n
                    if y <= x or y not in allowed:
                        continue
                    if minimum and any(not triple_good(a, x, y, minimum) for a in A):
                        continue
                    if valid(A + (x, y), n):
                        visits[10] += 1
                        print('FOUND', n, A + (x, y), flush=True)
            return
        for idx, x in enumerate(possible):
            if idx + 10 - k > len(possible):
                break
            # Omitting x already witnesses a second representation of this child.
            if rows[0][k + 1] >> ((total + x) % n) & 1:
                continue
            child = adjoin(rows, x, n)
            if child[1][k + 1] >> ((total + x) % n) & 1:
                continue
            future = [
                y
                for y in possible[idx + 1 :]
                if not minimum or all(triple_good(a, x, y, minimum) for a in A)
            ]
            dfs(A + (x,), child, future, minimum)

    seeds = [seed] if lower is None else [(0, 1, z) for z in range(lower, min(upper, n - 8) + 1)]
    for A in seeds:
        minimum = 0 if lower is None else A[2]
        if minimum and not triple_good(*A, minimum):
            continue
        rows = empty(10)
        for x in A:
            rows = adjoin(rows, x, n)
        possible = [
            x
            for x in range(A[-1] + 1, n)
            if not minimum or all(triple_good(a, b, x, minimum) for a, b in combinations(A, 2))
        ]
        dfs(A, rows, possible, minimum)
    print(
        'complete',
        n,
        seed if lower is None else (lower, upper),
        'nodes',
        dict(sorted(visits.items())),
    )


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='command', required=True)
    sp.add_parser('small')
    sp.add_parser('structure')
    sp.add_parser('targets')
    sp.add_parser('nonunits')
    p = sp.add_parser('nonunit-range')
    p.add_argument('binary')
    p.add_argument('first', type=int)
    p.add_argument('last', type=int)
    p.add_argument('workers', type=int)
    p = sp.add_parser('certificates')
    p.add_argument('file')
    p = sp.add_parser('prefix')
    p.add_argument('N', type=int)
    p.add_argument('points')
    p = sp.add_parser('shards')
    p.add_argument('N', type=int)
    p.add_argument('lo', type=int)
    p.add_argument('hi', type=int)
    a = ap.parse_args()
    if a.command == 'small':
        small()
    elif a.command == 'structure':
        structure()
    elif a.command == 'targets':
        targets()
    elif a.command == 'nonunits':
        nonunits()
    elif a.command == 'nonunit-range':
        nonunit_range(a.binary, a.first, a.last, a.workers)
    elif a.command == 'certificates':
        certificates(a.file)
    elif a.command == 'prefix':
        census(a.N, tuple(map(int, a.points.split(','))))
    else:
        census(a.N, None, a.lo, a.hi)
