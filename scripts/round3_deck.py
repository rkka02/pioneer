"""Exact deletion counts on critical boundaries, across all edges, triangles and squares."""

from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import networkx as nx

from flow_lab import boundary_counts, edges, jlpt
from round3_reduced import core, count


def cycle_sets(n, pairs):
    """Each undirected triangle/square exactly once, regardless of chords."""
    g = nx.Graph(pairs)
    ids = {frozenset(e): i for i, e in enumerate(pairs)}
    cycles = {3: set(), 4: set()}
    for a in range(n):
        for b, d in combinations(g[a], 2):
            if g.has_edge(b, d):
                row = (a, b, d)
                cycles[3].add(
                    tuple(sorted(ids[frozenset((x, y))] for x, y in zip(row, row[1:] + row[:1])))
                )
            for c in (g[b].keys() & g[d].keys()) - {a}:
                row = (a, b, c, d)
                cycles[4].add(
                    tuple(sorted(ids[frozenset((x, y))] for x, y in zip(row, row[1:] + row[:1])))
                )
    return cycles


def check(n, pairs, beta, name):
    tensor = boundary_counts(n, pairs)
    assert int(tensor[tuple(beta[:-1])]) == 0
    # Sorting by later endpoint closes the K4 blocks early in the JLPT ring.
    order = sorted(range(len(pairs)), key=lambda i: max(pairs[i]))
    if name.startswith("three hubs") or name.startswith("book"):
        order = list(range(len(pairs)))

    @lru_cache(None)
    def holes(skip):
        return count(n, [pairs[i] for i in order if i not in skip], beta)

    singleton = [holes((i,)) for i in range(len(pairs))]
    assert min(singleton) > 0
    for e, (a, b) in enumerate(pairs):
        for s in (1, -1):
            shifted = beta.copy()
            shifted[a] = (shifted[a] + s) % 3
            shifted[b] = (shifted[b] - s) % 3
            assert int(tensor[tuple(shifted[:-1])]) == singleton[e]
    if name in ("three hubs 11", "JLPT all-one boundary"):
        nonedges = list(nx.non_edges(nx.Graph(pairs)))
        assert len(nonedges) == (30 if name == "three hubs 11" else 42)
        for a, b in nonedges:
            for s in (1, -1):
                shifted = beta.copy()
                shifted[a] = (shifted[a] + s) % 3
                shifted[b] = (shifted[b] - s) % 3
                assert tensor[tuple(shifted[:-1])] > 0
    cycles = cycle_sets(n, pairs)
    for tri in cycles[3]:
        assert len({singleton[e] for e in tri}) == 1
    for square in cycles[4]:
        for e in square:
            assert singleton[e] == sum(holes(ij) for ij in combinations([i for i in square if i != e], 2))
    print(
        name,
        "single-edge counts (count: multiplicity)",
        dict(sorted(Counter(singleton).items())),
        "triangles and squares",
        len(cycles[3]),
        len(cycles[4]),
        flush=True,
    )


def line_tables():
    for k in (3, 4):
        histogram = Counter()
        for row in product(range(3), repeat=k):
            classes = [frozenset(i for i, x in enumerate(row) if x == t) for t in range(3)]
            if not all(classes):
                continue
            histogram[tuple(sorted(map(len, classes)))] += 1
            if k == 3:
                assert all(len(s) == 1 for s in classes)
            else:
                for i in range(k):
                    assert int(frozenset([i]) in classes) == sum(
                        len(s) == 2 and i not in s for s in classes
                    )
        print("normalized cycle profiles", k, dict(histogram))


def theta_tables():
    # A nonempty path forbids at least one of the three shifts. Test all allowed sets.
    subsets = [{i for i in range(3) if mask >> i & 1} for mask in range(7)]
    misses = Counter()
    for a, b, c in product(subsets, repeat=3):
        if not any((x + y + z) % 3 == 0 for x, y, z in product(a, b, c)):
            profile = tuple(sorted(map(len, (a, b, c))))
            assert profile[0] == 0 or profile in ((1, 1, 1), (1, 1, 2))
            misses[profile] += 1
    print(
        "two-dimensional theta tests, 343 triples, nonempty missing profiles",
        {k: v for k, v in misses.items() if k[0]},
    )
    # Induced free graph outside the closed star in a regular completion.
    for r in range(7, 21):
        g = nx.Graph([(i, r + (i + j) % r) for i in range(r) for j in range(5)])
        h = 2 * r - 1
        k = len(g[0])
        rem = g.subgraph(set(g) - {0} - set(g[0]))
        assert 2 * (rem.number_of_edges() - len(rem)) >= 3 * h + 5 - 8 * k
        if h >= 15:
            assert 2 * rem.number_of_edges() > 3 * (len(rem) - 1)
            assert any(
                b.number_of_edges() > len(b)
                for s in nx.biconnected_components(rem)
                if len(s) >= 3
                for b in [rem.subgraph(s)]
            )


if __name__ == "__main__":
    line_tables()
    theta_tables()
    check(4, edges(nx.complete_graph(4)), [0] * 4, "K4")
    for n in (6, 8, 10):
        check(n, core("edge books", n), [0] * n, f"book {n}")
        check(n, core("odd wheel", n), [0] * n, f"odd wheel {n}")
    for n in (7, 9, 11):
        check(n, core("three hubs", n), [0] * n, f"three hubs {n}")
    check(12, jlpt(), [1] * 12, "JLPT all-one boundary")
