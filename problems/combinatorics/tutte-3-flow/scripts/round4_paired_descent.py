"""Exact checks of the P=8 contraction budget, path signs and twelve-vertex degree bound."""

from collections import Counter
from itertools import combinations, product

import networkx as nx

from flow_lab import boundary_counts, edges, mincut
from round1_ports import LocalOrientations, port_pins, solve_checked
from round1_repair import nontrivial_five_cut
from round3_descent import moves, pairs_of
from round3_reduced import core, strong_witness


def hereditary(n, p):
    return all(sum((mask >> a) & (mask >> b) & 1 for a, b in p) <= 3 * mask.bit_count() - 7
               for mask in range(1 << n) if mask.bit_count() >= 5)


def savings():
    stats = Counter()
    for n in (8, 9, 10):
        rim = n - 2
        all_edges = [(i, (i + 1) % rim) for i in range(rim)] + [(i, h) for i in range(rim) for h in (rim, rim + 1)]
        # Four distinct types of holes in the triangulated bipyramid.
        for deleted in ((0, 2), (0, rim + 4), (rim, rim + 3), (rim, rim + 4)):
            p = [e for i, e in enumerate(all_edges) if i not in deleted]
            assert 3 * n - len(p) == 8 and hereditary(n, p)
            g = nx.Graph(p)
            assert min(dict(g.degree()).values()) >= 3
            stats['graphs'] += 1
            for u, d in g.degree():
                if d not in (3, 4, 5):
                    continue
                small = g.copy()
                small.remove_node(u)
                assert nx.is_connected(small) and not list(nx.bridges(small))
                ns = sorted(g[u])
                others = list(small)
                masks = [sum(1 << v for v in s) for k in range(2, n) for s in combinations(others, k)]
                internal = [sum(mask >> a & mask >> b & 1 for a, b in small.edges()) for mask in masks]
                for residue in (0, 1):
                    if d == 5 and residue == 0:
                        continue
                    k, _ = moves(d, residue)
                    for pairs in pairs_of(ns, k):
                        stats['splits'] += 1
                        for mask, m in zip(masks, internal):
                            s = mask.bit_count()
                            added = sum(mask >> a & mask >> b & 1 for a, b in pairs)
                            sigma = 3 * (s - 1) - m - added
                            assert sigma >= (1 if s == 2 else 2 if s <= 4 else 3)
                            if sigma == 1:
                                assert added == 1 and s == 2 and m == 1
                            stats['parts'] += 1
    print('P=8 contraction savings', dict(stats))


def splits_and_boundaries():
    for length in range(1, 10):
        for first, last in product((1, 2), repeat=2):
            charge = first
            for i in range(length):
                sign = (-charge) % 3
                assert 2 * sign % 3 == charge
                charge = ((last if i == length - 1 else 0) + sign) % 3
            assert (charge != 0) == ((last - (-1) ** length * first) % 3 == 0)
    # Critical reduced examples with a missing zero boundary, P=8 and cubic vertices.
    for n in (8, 9):
        p = core('three hubs', n)
        assert strong_witness(n, p) is None
        assert 3 * n - len(p) == 8
        deg = Counter(v for edge in p for v in edge)
        counts = boundary_counts(n, p)
        assert counts.flat[0] == 0
        ok = 0
        for prefix in product(range(3), repeat=n - 1):
            beta = prefix + (-sum(prefix) % 3,)
            x = sum(d > 6 or (d == 6 and beta[v] != 0) for v, d in deg.items())
            if x <= 2 and any(d == 3 and beta[v] for v, d in deg.items()):
                assert counts[prefix] > 0
                ok += 1
        assert ok
        print('certified reduced K3,t+ at n, eligible cubic boundaries', n, ok)


def rooted():
    # The three one-spoke leaves share the free degree-five center 1.
    stats = Counter()
    for r in (8, 9, 10, 12, 16, 20):
        n = 2 * r
        base = [(i, r + (i + j) % r) for i in range(r) for j in range(5)]
        special = {0, 1, r + 1, r + 2, r + 3}
        order = [v for v in range(n) if v not in special]
        for t in (1, 3):
            changed = n - 13
            if changed < t + 2:
                continue
            verts = order[:changed]
            p = base + list(zip(verts[:t + 1], verts[1:t + 2])) + list(zip(verts[t + 2::2], verts[t + 3::2]))
            deg = Counter(v for edge in p for v in edge)
            assert sum(deg[v] == 5 for v in range(1, n)) == 12
            assert sum(max(0, deg[v] - 6) for v in range(1, n)) == t
            assert all(deg[v] == 5 for v in special)
            assert mincut(n, p) == 5 and nontrivial_five_cut(n, p, 0) is None
            solver = LocalOrientations(n, p)
            for i, reverse in product(range(5), (False, True)):
                pins = port_pins(p, 0, i, reverse=reverse)
                assert solve_checked(solver, [0] * n, pins) is not None
                vals = [pins[p.index((0, r + j))] for j in (1, 2, 3)]
                assert max(vals.count(1), vals.count(-1)) >= 2
                stats[t] += 1
    print('b=12 rooted stars with the three leaves; by excess', dict(stats))


if __name__ == '__main__':
    savings()
    splits_and_boundaries()
    rooted()
