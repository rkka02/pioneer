"""Direct integer counts for voltage double covers and optimal unsigned terminal-pair thinning."""

from collections import Counter
from fractions import Fraction
from itertools import combinations, product

import networkx as nx
import numpy as np

from flow_lab import boundary_counts, divergence, edges, jlpt
from round3_reduced import core, count, strong_witness


def cover(n, p, swap):
    return [(a + n*i, b + n*(i ^ (e in swap))) for e, (a, b) in enumerate(p) for i in (0, 1)]


def signed_counts(n, p, switch):
    result = Counter()
    for vals in product((1, -1), repeat=len(p)):
        beta = [0] * n
        for (a, b), s, flip in zip(p, vals, switch):
            beta[a] += s
            beta[b] += s if flip else -s
        result[tuple(x % 3 for x in beta)] += 1
    return result


def cover_identity(n, p, switch):
    # Partition edges between ordinary and signed channels, then invert the two boundary coordinates.
    result = np.zeros((3,) * (2*n-1), dtype=np.int64)
    for mask in range(1 << len(p)):
        left = [e for j, e in enumerate(p) if mask >> j & 1]
        right = [j for j in range(len(p)) if not mask >> j & 1]
        a = signed_counts(n, left, [False] * len(left))
        b = signed_counts(n, [p[i] for i in right], [i in switch for i in right])
        for x, cx in a.items():
            for y, cy in b.items():
                beta = tuple((-v-w) % 3 for v, w in zip(x, y)) + tuple((w-v) % 3 for v, w in zip(x, y))
                assert sum(beta) % 3 == 0
                result[beta[:-1]] += cx * cy
    assert np.array_equal(result, boundary_counts(2*n, cover(n, p, switch)))


def voltage():
    stats = Counter()
    for n, p in ((3, [(0, 1), (0, 1), (1, 2), (2, 0), (1, 1)]),
                 (4, edges(nx.complete_graph(4)))):
        for mask in range(1 << len(p)):
            cover_identity(n, p, {e for e in range(len(p)) if mask >> e & 1})
            stats['all-boundary signature checks'] += 1
    for n, p, beta in ((4, edges(nx.complete_graph(4)), [0]*4),
                       (8, core('three hubs', 8), [0]*8), (12, jlpt(), [1]*12)):
        assert count(n, p, beta) == 0
        for e in (0, len(p)-1):
            d = cover(n, p, {e})
            # Process the two sheets contiguously in the independent frontier counter.
            d.sort(key=lambda edge: (min(edge) // n, min(edge) % n, max(edge)))
            assert count(2*n, d, 2*beta) == 0
            assert sum((a < n) != (b < n) for a, b in d) == 2
            if n <= 4:
                assert strong_witness(2*n, d) is None
            stats['inherited symmetric gaps'] += 1
    # For every base boundary, compare the squared conditional counts with the lift.
    p = edges(nx.complete_graph(4))
    n = 4
    for e, (a, b) in enumerate(p):
        old = boundary_counts(n, p[:e] + p[e+1:])
        new = boundary_counts(2*n, cover(n, p, {e}))
        for d in product(range(3), repeat=n-1):
            beta = d + (-sum(d) % 3,)
            cs = [old[tuple((x+s*((v==a)-(v==b)))%3 for v, x in enumerate(beta[:-1]))] for s in (1,-1)]
            assert new[(beta+beta)[:-1]] == sum(x*x for x in cs)
            stats['squared count identities'] += 1
    print('voltage cuts and channels', dict(stats))


def all_pairings(vertices):
    if not vertices:
        yield ()
        return
    v = vertices[0]
    for i, w in enumerate(vertices[1:], 1):
        for tail in all_pairings(vertices[1:i] + vertices[i+1:]):
            yield ((v, w),) + tail


def pairing_optimum(g):
    p = edges(g)
    n = len(g)
    masks = np.arange(1, 1 << (n-1))
    cross = {(a, b): ((masks >> a ^ masks >> b) & 1) for a, b in combinations(range(n), 2)}
    cuts = sum(cross[e] for e in p)
    best = Fraction(n)
    for pairs in all_pairings(tuple(range(n))):
        counts = sum(cross[e] for e in pairs)
        # Exact comparison among all cut ratios using the small integer counts.
        worst = max(Fraction(k, int(cuts[counts == k].min())) for k in range(1, n//2+1) if (counts == k).any())
        best = min(best, worst)
    return best


def main():
    voltage()
    # Four triangles on K4 give an unsigned cycle double cover. Try all sixteen signs.
    k4 = edges(nx.complete_graph(4))
    triangles = list(combinations(range(4), 3))
    rows = []
    for a,b,c in triangles:
        rows.append([int((x,y) in ((a,b),(b,c))) - int((x,y) == (a,c)) for x,y in k4])
    assert all(sum(abs(row[i]) for row in rows) == 2 for i in range(6))
    assert not any(all(sum(s*r[i] for s,r in zip(signs,rows)) % 3 for i in range(6))
                   for signs in product((-1,1), repeat=4))
    for n in range(12, 41):
        lower = n*(n-1)//2 - (n*n)//4
        assert lower > 3*n-7
    print('four-triangle signed covers on K4, independence-two density checks', 16, 29)
    for g in (nx.complete_graph(6), nx.complete_bipartite_graph(5,5)):
        ratio = pairing_optimum(g)
        assert (ratio <= Fraction(1,3)) == (len(g) == 6)
        print('least worst pairing/cut ratio', len(g), ratio)


if __name__ == '__main__':
    main()
