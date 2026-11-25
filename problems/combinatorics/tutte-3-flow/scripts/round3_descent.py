"""Finite checks for low-degree splitting, contraction costs, and the rooted degree bound."""

from collections import Counter
from itertools import combinations, product
import networkx as nx

from flow_lab import divergence, edges, mincut
from round1_ports import LocalOrientations, port_pins, solve_checked
from round1_repair import nontrivial_five_cut
from round3_reduced import core, count, strong_witness


def pairs_of(units, k):
    if k == 0:
        yield ()
        return
    for u, v in combinations(units, 2):
        for rest in pairs_of([x for x in units if x not in (u, v)], k - 1):
            if not rest or (u, v) < rest[0]:
                yield ((u, v),) + rest


def moves(d, residue):
    k = {(3, 0): 0, (4, 0): 2, (3, 1): 1, (4, 1): 1, (5, 1): 2}[(d, int(residue != 0))]
    return k, [s for s in (-1, 1) if (s * (d - 2 * k) - residue) % 3 == 0]


def local_tests():
    checks = Counter()
    for d in (3, 4, 5):
        for r in range(3):
            if (d, r) == (5, 0):
                continue
            k, signs = moves(d, r)
            assert 7 - 3 + d - k in (6, 7)
            for pairs in pairs_of(list(range(d)), k):
                remaining = {i for i in range(d) if all(i not in p for p in pairs)}
                for sign in signs:
                    for orient in product((-1, 1), repeat=k):
                        # Local coordinate is divergence contributed at the neighbour.
                        full = [-sign] * d
                        for (a, b), s in zip(pairs, orient):
                            full[a], full[b] = s, -s
                        assert (-sum(full) - r) % 3 == 0
                        assert all(full[i] == -sign for i in remaining)
                        assert all(full[a] + full[b] == 0 for a, b in pairs)
                        checks[d, r] += 1
            if d - k == 3:
                for size in range(3):
                    for exc in combinations(range(d), size):
                        assert any(
                            any(i not in exc and all(i not in p for p in pairs) for i in range(d))
                            for pairs in pairs_of(list(range(d)), k)
                        )
    print("splitting local orientations checked by (degree,boundary)", dict(checks))


def surgery_tests():
    # Deterministic 3-neighbour additions to K4-e. Keep only graphs satisfying
    # the full hereditary density hypotheses used in the contraction accounting.
    examples = 0
    seen = set()
    counts = Counter()
    for n in (8, 9, 10):
        for p0, q in product(range(1, 6), repeat=2):
            g = nx.complete_graph(4)
            g.remove_edge(2, 3)
            for i in range(4, n):
                start = (p0 * i + q) % i
                cand = list(
                    dict.fromkeys(
                        [(i - 1) % i, (i - 2) % i, start, (start + q) % i, (start + p0) % i]
                        + list(range(i))
                    )
                )
                g.add_edges_from(
                    (i, j) for j in (cand[0], cand[2], cand[3] if len(cand) > 3 else cand[1])
                )
            key = tuple(edges(g))
            if key in seen or min(dict(g.degree()).values()) < 3:
                continue
            seen.add(key)
            if any(
                g.subgraph(s).number_of_edges() > 3 * len(s) - 7
                for size in range(5, n + 1)
                for s in combinations(range(n), size)
            ):
                continue
            assert len(key) == 3 * n - 7
            examples += 1
            for u, d in g.degree():
                if d not in (3, 4, 5):
                    continue
                neighbors = sorted(g[u])
                for residue in range(2):
                    if (d, residue) == (5, 0):
                        continue
                    k, _ = moves(d, residue)
                    for pairs in pairs_of(neighbors, k):
                        raw = [e for e in key if u not in e] + list(pairs)
                        j = nx.MultiGraph()
                        j.add_nodes_from(v for v in range(n) if v != u)
                        j.add_edges_from(raw)
                        assert nx.is_connected(j) and not list(nx.bridges(j))
                        for size in range(2, n):
                            for s in combinations(j.nodes(), size):
                                subset = set(s)
                                m = sum(a in subset and b in subset for a, b in raw)
                                assert 3 * (size - 1) - m >= (1 if size == 2 else 2)
                        assert 3 * (n - 1) - len(raw) == 7 - 3 + d - k
                        counts[7 - 3 + d - k] += 1
    assert examples > 0 and min(counts.values()) > 0
    print("hereditary-sparse P=7 fixtures, all split/cut tests", examples, dict(counts))


def sharp_examples():
    # K3,5 plus a hub edge fails the extension of the P=7 statement to P=8.
    n = 8
    p = core("three hubs", n)
    assert strong_witness(n, p) is None and 3 * n - len(p) == 8
    assert count(n, p, [0] * n) == 0 and all(count(n, p, [0] * n, [e]) > 0 for e in range(len(p)))
    # Smaller P=7 exception: 2 copies of K4 sharing exactly one edge.
    p = core("edge books", 6)
    assert strong_witness(6, p) is None and 18 - len(p) == 7 and count(6, p, [0] * 6) == 0
    # Check the spoke capacity argument for every placement, allowing repetitions and
    # both possible global signs. Nonroot d=5/6 vertices incident with any spoke are active.
    tested = 0
    for vals in ((5, 5, 5, 5, 5), (6, 6, 6, 6, 6), (5, 6, 6, 6, 7), (8, 6, 5, 6, 6), (7, 7, 6, 6, 6)):
        for ds in product(range(5), repeat=5):
            for minority in range(5):
                gamma = [0] * 5
                for i, v in enumerate(ds):
                    gamma[v] += 1 if i == minority else -1
                assert any(
                    vals[v] - ds.count(v) <= 4 or (vals[v] - ds.count(v) == 5 and gamma[v] % 3 != 0)
                    for v in set(ds)
                )
                tested += 1
    print("P=8 and small P=7 obstructions verified; spoke placements/minorities", tested)


def test_pins(p, z):
    n = 1 + max(max(e) for e in p)
    assert mincut(n, p) == 5
    solver = LocalOrientations(n, p)
    for i in range(5):
        sol = solve_checked(solver, [0] * n, port_pins(p, z, i))
        assert sol and all(d % 3 == 0 for d in divergence(n, p, sol))
    return 5


def threshold_fixtures():
    # From a 5-regular bipartite circulant, add disjoint paths among free vertices.
    # A path's interior has degree seven, its ends degree six.
    stats = Counter()
    for r in (7, 8, 9, 12, 16):
        n = 2 * r
        base = [(i, r + (i + j) % r) for i in range(r) for j in range(5)]
        assert mincut(n, base) == 5 and nontrivial_five_cut(n, base, 0) is None
        for b in (9, 10, 11):
            changed = n - 1 - b
            for t in range(3):
                if changed < t + 2 or (changed - t) % 2:
                    continue
                vertices = list(range(1, changed + 1))
                augmented = (
                    base
                    + list(zip(vertices[: t + 1], vertices[1 : t + 2]))
                    + list(zip(vertices[t + 2 :: 2], vertices[t + 3 :: 2]))
                )
                degree = Counter(v for e in augmented for v in e)
                assert sum(d == 5 for v, d in degree.items() if v) == b
                assert sum(max(0, d - 6) for v, d in degree.items() if v) == t
                stats[b, t] += test_pins(augmented, 0)
    print("rooted checks at b=9..11 by (b,t); entries count labelled star prescriptions", dict(stats))
    # Splitting two edges at a nonroot vertex, including cases with loops at an unpinned end.
    # Reverse tests undo a complete splitting by routing selected edges through an even vertex.
    p = edges(nx.complete_graph(6))
    for selection in ((0, 1, 2), (0, 5, 9), (1, 3, 5, 8)):
        q = [e for i, e in enumerate(p) if i not in selection]
        routes = []
        for i in selection:
            a, bv = p[i]
            routes.append((len(q), len(q) + 1))
            q.extend([(a, 6), (6, bv)])
        q.extend([(5, 6), (6, 5)])
        assert mincut(7, q) == 5
        for i in range(5):
            old = solve_checked(LocalOrientations(6, p), [0] * 6, port_pins(p, 0, i))
            sol = [s for j, s in enumerate(old) if j not in selection]
            for j in selection:
                sol.extend((old[j], old[j]))
            sol.extend((1, 1))
            assert all(r % 3 == 0 for r in divergence(7, q, sol))
            # Carry directions with labelled old spokes, including rerouted ones.
            for e, sign in port_pins(p, 0, i).items():
                index = (
                    routes[selection.index(e)][0]
                    if e in selection
                    else sum(j not in selection for j in range(e))
                )
                assert sol[index] == sign
    print("complete-splitting root lifts with a discarded loop", 15)


if __name__ == "__main__":
    local_tests()
    surgery_tests()
    sharp_examples()
    threshold_fixtures()
