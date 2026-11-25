"""Exact global electrical minimization on seven parallel-bundle arms."""

from fractions import Fraction as F
from itertools import combinations_with_replacement
from math import floor, isqrt

from flow_lab import divergence, mincut
from round1_repair import nontrivial_five_cut


def network(m):
    # Left vertices z=0, center=1, leaves=2..4. Right minority s=5.
    pairs = (
        [(0, r) for r in range(5, 10)]
        + [(1, r) for r in range(5, 10)]
        + [(l, 5) for l in range(2, 5)]
    )
    # Give each of the twelve replaced edges its own lane at every step.
    signs = [1 if (v - 5) == u else -1 for u, v in pairs]
    arms = [(v, [(v, r) for r in range(6, 10)]) for v in range(2, 5)]
    arms += [(v, [(l, v) for l in range(2, 5)]) for v in range(6, 10)]
    nxt = 11
    for vertex, lanes in arms:
        u = vertex
        for step in range(m):
            v = 10 if step == m - 1 else nxt
            nxt += int(step != m - 1)
            for l, r in lanes:
                pairs.append((u, v))
                signs.append((1 if r - 5 == l else -1) * (1 if vertex == l else -1))
            if step:
                pairs.extend([(u, v), (u, v)])
                signs.extend([1, -1])
            u = v
    assert all(d % 3 == 0 for d in divergence(nxt, pairs, signs))
    # Our explicit orientation has the minority out; reversal gives the
    # minority in as used for the electrical obstruction.
    assert signs[:5] == [1, -1, -1, -1, -1]
    return nxt, pairs


def exact_energy(m):
    rr, rl = F(1, 3) + F(m - 1, 5), F(1, 4) + F(m - 1, 6)
    a, b = 1 + rr, 1 + rl
    den = 4 / a + 3 / (b + 3)
    limit = int(44 * (1 + 4 / min(rr, rl)))
    imax = isqrt(limit)

    def vectors(d, residue):
        values = [v for v in range(-imax, imax + 1) if (v - residue) % 6 == 0]
        return [
            vs for vs in combinations_with_replacement(values, d) if sum(x * x for x in vs) <= limit
        ]

    best = F(44)
    centers = set()
    junctions = set()
    sorted_types = 0
    sample = None
    for right in vectors(4, -2):
        rsum = sum(right)
        r2 = sum(x * x for x in right)
        for left in vectors(3, 3):
            base = r2 + sum(x * x for x in left)
            for (s,) in vectors(1, -1):
                if base + s * s > limit:
                    continue
                weights = [x + s for x in left]
                total = sum(weights)
                mu = rsum / a + total / (b + 3)
                baseline = (
                    base
                    + s * s
                    - r2 / a
                    - sum(w * w for w in weights) / b
                    + total**2 / (b * (b + 3))
                )
                for q in (floor(mu / 6), floor(mu / 6) + 1):
                    value = baseline + (6 * q - mu) ** 2 / den
                    if value > best:
                        continue
                    if value < best:
                        best, centers, junctions, sorted_types = value, set(), set(), 0
                    centers.add(-rsum - s + 6 * q)
                    junctions.add(s - sum(left))
                    sorted_types += 1
                    # Verify the actual real currents and their energy without
                    # using the closed formula for the objective.
                    shift = (6 * q - mu) / den
                    er = [(w + shift) / a for w in right]
                    el = [(w + shift - (total + 3 * shift) / (b + 3)) / b for w in weights]
                    assert sum(er + el) == 6 * q
                    tr = [x - y for x, y in zip(right, er)]
                    tl = [x - y for x, y in zip(left, el)]
                    ts = s - sum(el)
                    assert value == sum(x * x for x in tr + tl + [ts]) + rr * sum(
                        x * x for x in er
                    ) + rl * sum(x * x for x in el)
                    assert -sum(tr) - ts == -rsum - s + 6 * q
                    sample = (tr, tl, ts, er, el)
    assert centers
    if m in (12, 13, 14):
        assert junctions == {8} and sorted_types == 1
    if m <= 15 or m == 89:
        tr, tl, ts, er, el = sample
        n, all_edges = network(m)
        potential = {1: F(0), 5: ts}
        flows = dict(zip(range(2, 5), el)) | dict(zip(range(6, 10), er))
        for u in range(2, 5):
            potential[u] = ts + tl[u - 2]
        for u in range(6, 10):
            potential[u] = tr[u - 6]
        new = 11
        for u, j in flows.items():
            v = u
            for i in range(m):
                w = 10 if i == m - 1 else new
                new += int(i != m - 1)
                value = potential[v] - j / (int(u < 5) + 3 + 2 * int(i > 0))
                assert w not in potential or potential[w] == value
                potential[w] = value
                v = w
        free = [edge for edge in all_edges if 0 not in edge]
        currents = [potential[u] - potential[v] for u, v in free]
        demand = divergence(n, free, currents)
        assert sum(j * j for j in currents) == best and demand[1] in centers
        degree = [0] * n
        for u, v in free:
            degree[u] += 1
            degree[v] += 1
        for v, x in enumerate(demand):
            assert (
                F(x).denominator == 1
                and (x - degree[v]) % 2 == 0
                and (x - (int(v in range(6, 10)) - int(v == 5))) % 3 == 0
            )
        if m < 15:
            import networkx as nx

            flow = nx.DiGraph()
            for i, (u, v) in enumerate(free):
                flow.add_edge(("source",), ("edge", i), capacity=1)
                for a in (u, v):
                    flow.add_edge(("edge", i), a, capacity=1)
            quota = [(degree[v] + int(x)) // 2 for v, x in enumerate(demand)]
            if min(quota) >= 0:
                for v, qv in enumerate(quota):
                    flow.add_edge(v, ("sink",), capacity=qv)
                possible = nx.maximum_flow_value(flow, ("source",), ("sink",)) == len(free)
            else:
                possible = False
            violating = [
                (v, int(demand[v]), degree[v]) for v in range(1, n) if abs(demand[v]) > degree[v]
            ]
            print(
                "small M",
                m,
                "feasible minimizer",
                possible,
                "violated singletons",
                violating,
                "max arm current",
                max(map(abs, er + el)),
                flush=True,
            )
            assert possible == (m <= 11)
    return best, sorted(centers), sorted_types


def weighted_control(weight):
    # Direct grounded Laplacian inversion on K4,5. The tree lower bound
    # ||h||^2 <= 44(1+36w) < 56 fixes all right and center-branch values.
    from sympy import Matrix, Rational, zeros
    from itertools import product

    mat = zeros(8, 8)  # omit vertex 1 and relabel 2..9
    for l in range(1, 5):
        for r in range(5, 10):
            w = Rational(1) if l == 1 or r == 5 else Rational(weight.numerator, weight.denominator)
            if l != 1:
                mat[l - 2, l - 2] += w
                mat[l - 2, r - 2] -= w
                mat[r - 2, l - 2] -= w
            mat[r - 2, r - 2] += w
    inv = mat.inv()
    values = []
    for left in product((-3, 3), repeat=3):
        d = Matrix([*left, -1 - sum(left), -2, -2, -2, -2])
        assert -sum(d) == 9
        values.append((d.T * inv * d)[0])
    assert min(values) <= 44 and 44 * (1 + 36 * weight) < 56
    return min(values)


if __name__ == "__main__":
    for weight in (F(1, 133), F(1, 256)):
        print("weighted K5,5", weight, weighted_control(weight))
    for m in [*range(1, 90), 100]:
        n, p = network(m)
        if m <= 3:
            assert mincut(n, p) == 5 and nontrivial_five_cut(n, p) is None
        value, centers, k = exact_energy(m)
        assert centers == ([3] if m < 15 else [9])
        print(m, n, value, centers, k, flush=True)
