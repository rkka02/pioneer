"""Exact finite exchange and odd-quotient tests for unrestricted ten-sets.

Masks label the eight nonpivot coordinates. Integer linear combinations rejected
here are actual forbidden signed relations. The graph search deliberately keeps
all configurations that these necessary conditions do not reject.
"""

from functools import cache
from itertools import permutations, product
from math import gcd
import argparse
import numpy as np


@cache
def rules(r, t):
    masks = [s for s in range(1 << r) if s.bit_count() == t]
    return [(d, c) for d in masks for c in masks if not d & c]


def cross(x, y):
    return bool(x[0] & y[1] and y[0] & x[1])


@cache
def row(r, rule):
    d, c = rule
    return tuple((c >> j & 1) - (d >> j & 1) for j in range(r))


@cache
def coefficients(k):
    values = [
        p
        for p in product(range(-2, 3), repeat=k)
        if sum(p) == 0 and any(p) and next(z for z in p if z) > 0
    ]
    return np.asarray(values, dtype=np.int16).reshape(-1, k)


def consistent(r, family):
    if len(family) < 2:
        return True
    combinations = coefficients(len(family)) @ np.asarray(
        [row(r, f) for f in family], dtype=np.int16
    )
    forbidden = np.any(combinations != 0, axis=1) & (
        (combinations.min(axis=1) >= -1) | (combinations.max(axis=1) <= 1)
    )
    return not np.any(forbidden)


def canonical(r, family):
    columns = list(zip(*(row(r, f) for f in family)))
    return min(
        tuple(sorted(tuple(c[j] for j in p) for c in columns))
        for p in permutations(range(len(family)))
    )


def augment(r, families, t):
    out = {}
    for family in families:
        for v in rules(r, t):
            if not all(cross(v, f) and v != f[::-1] for f in family):
                continue
            if t == 2 and any(
                (v[0] | v[1]) == (f[0] | f[1]) for f in family if f[0].bit_count() == 2
            ):
                continue
            candidate = family + [v]
            if consistent(r, candidate):
                out.setdefault(canonical(r, candidate), candidate)
    return list(out.values())


def indices(bits):
    while bits:
        b = bits & -bits
        bits ^= b
        yield b.bit_length() - 1


def clique_number(adj):
    def color(P):
        classes = []
        for i in sorted(indices(P), key=lambda v: -(adj[v] & P).bit_count()):
            for j, cl in enumerate(classes):
                if not cl & adj[i]:
                    classes[j] |= 1 << i
                    break
            else:
                classes.append(1 << i)
        return classes

    def can(P, k):
        if k <= 1:
            return bool(P) if k else True
        classes = color(P)
        for j in range(len(classes) - 1, k - 2, -1):
            for i in indices(classes[j]):
                if can(P & adj[i], k - 1):
                    return True
                P ^= 1 << i
        return False

    P = (1 << len(adj)) - 1
    k = len(color(P))
    while k and not can(P, k):
        k -= 1
    return k


def triple_graph(r, base):
    candidates = [
        v
        for v in rules(r, 3)
        if all(cross(v, w) and v != w[::-1] for w in base) and consistent(r, base + [v])
    ]
    adj = [0] * len(candidates)
    for i, v in enumerate(candidates):
        for j, w in enumerate(candidates[:i]):
            if w != v[::-1] and cross(v, w) and consistent(r, base + [v, w]):
                adj[i] |= 1 << j
                adj[j] |= 1 << i
    return candidates, adj


def independent_upper(adj, bound):
    """Verify that there is no larger clique, branching by inclusion or exclusion."""

    def feasible(vertices, need):
        if need == 0:
            return True
        if vertices.bit_count() < need:
            return False
        # Partition into independent sets by repeatedly building one whole class.
        uncolored, colors = vertices, 0
        while uncolored and colors < need:
            candidates = uncolored
            colors += 1
            while candidates:
                bit = candidates & -candidates
                uncolored ^= bit
                candidates &= ~bit & ~adj[bit.bit_length() - 1]
        if colors < need:
            return False
        v = max(indices(vertices), key=lambda i: (adj[i] & vertices).bit_count())
        return feasible(vertices & adj[v], need - 1) or feasible(vertices ^ (1 << v), need)

    assert not feasible((1 << len(adj)) - 1, bound + 1)


def induced_graph(adj, keep):
    vertices = list(indices(keep))
    return [sum(1 << j for j, w in enumerate(vertices) if adj[v] >> w & 1) for v in vertices]


def profiles(audit):
    families = [[[]]]
    for _ in range(4):
        families.append(augment(8, families[-1], 2))
    assert not families[4]
    print('two-exchange orbit counts', [len(f) for f in families], flush=True)
    bounds = []
    for u, fs in enumerate(families[:4]):
        used = 2 if u == 0 else 1
        cases = fs
        for _ in range(used):
            cases = augment(8, cases, 3)
        graphs = []
        bounds_by_seed = {}
        for F in cases:
            candidates, adj = triple_graph(8, F)
            cap = clique_number(adj)
            if audit:
                independent_upper(adj, cap)
            bounds_by_seed[canonical(8, F)] = used + cap
            graphs.append((F, candidates, adj))
        raw = max([used - 1, *bounds_by_seed.values()])
        # Every eligible choice of the fixed triples in the same realized family
        # must itself be capable of reaching the target.
        cap = raw
        while cap >= used:
            allowed = {k for k, b in bounds_by_seed.items() if b >= cap}
            seen = False
            for F, candidates, adj in graphs:
                if canonical(8, F) not in allowed:
                    continue
                doubles = [v for v in F if v[0].bit_count() == 2]

                def eligible(v):
                    if u:
                        return canonical(8, doubles + [v]) in allowed
                    return all(canonical(8, [w, v]) in allowed for w in F)

                keep = sum(1 << i for i, v in enumerate(candidates) if eligible(v))
                edges = adj.copy()
                if not u:
                    for i in indices(keep):
                        for j in indices(keep & adj[i] & ((1 << i) - 1)):
                            if canonical(8, [candidates[i], candidates[j]]) not in allowed:
                                edges[i] ^= 1 << j
                                edges[j] ^= 1 << i
                small = induced_graph(edges, keep)
                residual = clique_number(small)
                if audit:
                    independent_upper(small, residual)
                if used + residual >= cap:
                    seen = True
                    break
            if seen:
                break
            cap -= 1
        bounds.append(cap)
        print(
            'double rules, seeded profiles, raw and refined triple caps',
            u,
            len(cases),
            raw,
            cap,
            flush=True,
        )
    return bounds


def partitions(total, slots, ceiling):
    if not total:
        yield ()
    elif slots:
        for i in range(1, min(total, ceiling) + 1):
            for rest in partitions(total - i, slots - 1, i):
                yield (i,) + rest


def same_class_pairs(size, p):
    a, b = divmod(size, p)
    return (p - b) * a * (a - 1) + b * a * (a + 1)


def anchor_capacity(profile, h, q):
    for c in profile:
        # Erasing the pivot leaves c-1 other points trivial modulo h.
        wanted = 1 << (10 - c)
        capacity = h * (q // (1 << (c - 1)))
        if wanted > capacity:
            return False
        if wanted == capacity and len(profile) - 1 < h.bit_length() - 1:
            return False
    return True


def has_clique(P, k, adj):
    if k == 0:
        return True
    while P.bit_count() >= k:
        b = P & -P
        P ^= b
        if has_clique(P & adj[b.bit_length() - 1], k - 1, adj):
            return True
    return False


def orbit_unions(groups, sizes):
    """Enumerate exactly the unions of admissible size using suffix subset sums."""
    suffix = [0] * (len(groups) + 1)
    suffix[-1] = 1
    for j in reversed(range(len(groups))):
        suffix[j] = suffix[j + 1] | (suffix[j + 1] << len(groups[j]))

    def visit(j, remaining, chosen):
        if not remaining & suffix[j]:
            return
        if j == len(groups):
            yield chosen
            return
        yield from visit(j + 1, remaining, chosen)
        yield from visit(j + 1, remaining >> len(groups[j]), chosen | groups[j])

    yield from visit(0, sum(1 << s for s in sizes), set())


def quotient(n):
    h = n & -n
    q = n // h
    groups = []
    covered = {0}
    for x in range(1, q):
        if x in covered:
            continue
        orbit, y = set(), x
        while y not in orbit:
            orbit.update((y, -y % q))
            y = 2 * y % q
        groups.append(orbit)
        covered.update(orbit)
    profiles = list(partitions(10, h, q.bit_length()))
    if h > 1:
        profiles = [p for p in profiles if len(p) > 1]
    divisors = [j for j in range(2, q) if q % j == 0]
    primes = [p for p in divisors if all(p % j for j in range(2, int(p**0.5) + 1))]
    unit_pair = len(primes) <= 2  # a prime q itself has no proper prime divisor
    required = max(2, 10 - max(0, (h - 2) // 2))
    admissible = searched = survivors = 0
    sizes = {sum(x * (x - 1) for x in p) for p in profiles}
    for H in orbit_unions(groups, sizes):
        if (unit_pair and 1 not in H) or gcd(q, *H) > 1:
            continue
        cases = [p for p in profiles if sum(x * (x - 1) for x in p) == len(H)]
        if not cases:
            continue
        admissible += 1
        cases = [
            p
            for p in cases
            if all(
                sum(same_class_pairs(x, j) for x in p) <= sum(y % j == 0 for y in H)
                for j in divisors
            )
        ]
        if not cases or not any(anchor_capacity(p, h, q) for p in cases):
            continue
        if any(all(y % p == 0 or y % s == 0 for y in H) for p in primes for s in primes if p < s):
            continue
        searched += 1
        adj = [sum(1 << ((y + i) % q) for y in H) for i in range(q)]
        if unit_pair:
            survives = has_clique(adj[0] & adj[1], required - 2, adj)
        else:
            survives = has_clique(adj[0], required - 1, adj)
        survivors += survives
    return admissible, searched, survivors


def six_rule_systems():
    from sympy import Matrix, ZZ
    from sympy.matrices.normalforms import smith_normal_decomp

    families = [[]]
    for size in (2, 2, 2, 3, 3, 3):
        families = augment(8, families, size)
    systems = []
    for family in families:
        rows = [row(8, f) for f in family]
        support = [i for i in range(8) if any(v[i] for v in rows)]
        # Translate all active points so that the first one is zero.
        matrix = Matrix([[v[i] for i in support[1:]] for v in rows])
        diag, left, right = smith_normal_decomp(matrix, domain=ZZ)
        assert diag == left * matrix * right and abs(left.det()) == abs(right.det()) == 1
        assert all(diag[i, j] == 0 for i in range(diag.rows) for j in range(diag.cols) if i != j)
        systems.append(
            (
                list(map(int, diag.diagonal())),
                [sum(map(int, left.row(i))) for i in range(left.rows)],
                np.asarray(right.tolist(), dtype=np.int64),
            )
        )
    return systems


def modular_solutions(n, d, system):
    diag, rhs, right = system
    choices = []
    for i in range(max(len(right), len(rhs))):
        value = rhs[i] * 2 * d % n if i < len(rhs) else 0
        entry = diag[i] if i < len(diag) else 0
        divisor = gcd(entry, n)
        if value % divisor:
            return []
        if i < len(right):
            step = n // divisor
            base = (value // divisor * pow(entry // divisor, -1, step)) % step if step > 1 else 0
            choices.append(range(base, n, step))
    # Check the machine-integer bound for each matrix multiplication below.
    assert len(right) * (n - 1) * int(np.max(np.abs(right))) < 2**63
    free = np.asarray(list(product(*choices)), dtype=np.int64)
    points = free @ right.T % n
    return np.column_stack((np.zeros(len(points), dtype=np.int64), points))


def six_rule_test(n, systems):
    from round2_verify import valid

    solutions = hereditary = completions = untested = 0
    for d in range(1, n):
        # Unit multiplication normalizes each difference to its gcd with n.
        if n % d or 4 * d % n == 0 or (n // d == 3 and n < 768):
            continue
        for system in systems:
            points = modular_solutions(n, d, system)
            solutions += len(points)
            if not len(points):
                continue
            size = points.shape[1]
            differences = []
            usable = np.ones(len(points), dtype=bool)
            for i in range(size):
                for j in range(i):
                    delta = (points[:, i] - points[:, j]) % n
                    usable &= (delta != 0) & (2 * delta % n != 0)
                    differences.append(np.minimum(delta, n - delta))
            ordered = np.sort(np.column_stack(differences), axis=1)
            usable &= np.all(ordered[:, 1:] != ordered[:, :-1], axis=1)
            for values in points[usable]:
                R = tuple(values.tolist())
                if not valid(R, n):
                    continue
                hereditary += 1
                if size < 8:
                    untested += 1
                    continue
                for t in range(n):
                    A = (0, d, *((z + t) % n for z in R))
                    if len(set(A)) == 10 and valid(A, n):
                        completions += 1
    return solutions, hereditary, completions, untested


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        '--audit',
        action='store_true',
        help='verify graph upper bounds by a second branching algorithm',
    )
    bounds = profiles(parser.parse_args().audit)
    for parity in (0, 1):
        non_single = max(16 * u + 4 * v + 2 - parity for u, v in enumerate(bounds))
        print('parity, no-singleton overlap cap', parity, non_single)
        for n in range(598, 640):
            if n % 2 != parity or 1280 - 2 * n <= non_single:
                continue
            print('quotient', n, *quotient(n))
    systems = six_rule_systems()
    print('six-rule profiles', len(systems))
    for n in (610, 611):
        # Above the best overlap from each of the other three double-rule counts
        # and above the overlap from three doubles with at most two triples.
        target = 1280 - 2 * n
        full_support = gcd(n, 2)
        assert target > max(16 * u + 4 * b + full_support for u, b in enumerate(bounds[:3]))
        assert target > 48 + 8 + full_support and bounds[3] == 3
        result = six_rule_test(n, systems)
        print('six-rule lifts', n, *result, flush=True)
        if result[2:] == (0, 0):
            print('quotient', n, *quotient(n))
