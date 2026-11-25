"""Explicit certificates for the bisection, two-root, splitting, and strict-descent obstructions."""
import itertools

import networkx as nx
import numpy as np

from bisections import component_defect
from flow_lab import boundary_counts, divergence, edges, lift, mincut, orient, splice


def seven_cut_graph():
    # Two copies of this nine-vertex shore. 0..5 are the majority color.
    paths = [(0, 1), (1, 2), (3, 4), (4, 5)]
    base = [(0, 6), (0, 7), (0, 8), (1, 6), (1, 8), (2, 7), (2, 8),
            (3, 6), (3, 7), (3, 8), (4, 6), (4, 7), (5, 6), (5, 7), (5, 8)]
    wires = [(3, 11), (4, 9), (0, 13), (5, 11), (2, 10), (1, 14), (2, 12)]
    shore = paths + base
    return shore + [(a+9, b+9) for a, b in shore] + wires


def bisection_witness():
    pairs = seven_cut_graph()
    graph = nx.Graph(pairs)
    assert len(pairs) == graph.number_of_edges() == 45 and set(dict(graph.degree()).values()) == {5}
    high = set(range(6)) | {15, 16, 17}
    top = sum(1 << v for v in high)
    assert component_defect(graph, high) == 1
    # Two-edge paths in crossing edges pay for every monochromatic edge.
    residual = graph.copy()
    for off in (0, 9):
        for a, b, h in ((0, 1, 6), (1, 2, 8), (3, 4, 6), (4, 5, 7)):
            for u, v in ((a, b), (a, h), (h, b)):
                residual.remove_edge(u+off, v+off)
    assert nx.is_connected(residual)
    assert all((u in high) != (v in high) for u, v in residual.edges())
    # Enumerate every set (including complements) independently.
    masks = np.arange(1 << 18, dtype=np.int32)
    sizes = np.bitwise_count(masks).astype(np.int32)
    cuts = sum(((masks >> u) ^ (masks >> v)) & 1 for u, v in pairs)
    assert cuts[(sizes > 0) & (sizes < 18)].min() == 5
    assert cuts[(sizes >= 2) & (sizes <= 16)].min() == 7
    assert set(masks[cuts == cuts.max()]) == {top, ((1 << 18)-1) ^ top}
    assert (int(cuts[top]), int(cuts[511])) == (37, 7)
    for mask in masks[(sizes == 9) & (cuts == 35)]:
        vertices = {v for v in range(18) if mask & (1 << v)}
        if component_defect(graph, vertices) == 0:
            break
    else:
        raise AssertionError("no realizable size-35 bisection")
    # Recover a certificate of those *exact* outdegrees by assigning every edge one tail.
    matching = nx.DiGraph()
    for e, (a, b) in enumerate(pairs):
        matching.add_edge("s", ("e", e), capacity=1)
        for v in (a, b):
            matching.add_edge(("e", e), ("v", v), capacity=1)
    for v in range(18):
        matching.add_edge(("v", v), "t", capacity=4 if v in vertices else 1)
    value, flow = nx.maximum_flow(matching, "s", "t")
    assert value == 45
    signs = [2*flow["e", e]["v", a]-1 for e, (a, _) in enumerate(pairs)]
    assert divergence(18, pairs, signs) == [3 if v in vertices else -3 for v in range(18)]
    print("18-vertex maximum cut", int(cuts.max()), "best realizable", int(cuts[mask]),
          "high", sorted(vertices), "integer flow", lift(18, pairs, signs))
    # A nonzero boundary with exactly two defects, and no improving directed path.
    beta = [2] + [0]*8 + [1] + [0]*8
    pins = {e: -1 for e in range(38, 45)}  # directs the entire cut into the first shore
    bad = orient(18, pairs, beta, pins)
    assert bad is not None
    directed = nx.DiGraph((a, b) if s == 1 else (b, a) for (a, b), s in zip(pairs, bad))
    assert not nx.has_path(directed, 0, 9)
    print("two defects signs in input order", bad)


def two_roots():
    pairs = edges(nx.complete_graph(6))
    frozen = {}
    for e, (a, b) in enumerate(pairs):
        if a == 0:
            frozen[e] = 1 if b == 1 else -1
        elif a == 1:
            frozen[e] = 1
    zero = [0]*6
    assert orient(6, pairs, zero, frozen) is None
    for root in (0, 1):
        assert orient(6, pairs, zero, {e: s for e, s in frozen.items() if root in pairs[e]})
    k4 = edges(nx.complete_graph(4))
    assert boundary_counts(4, k4).flat[0] == 0


def bad_split():
    k6 = edges(nx.complete_graph(6))
    p = [e for e in edges(nx.petersen_graph()) for _ in range(1 if e[1]-e[0] == 5 else 2)]
    pairs = splice(6, k6, 0, 10, p, 0, range(5))
    assert mincut(14, pairs) == 5
    wires = [(a, b) for a, b in pairs if a < 5 <= b]
    pair = next((x, y) for x, y in itertools.combinations(wires, 2) if x[1] == y[1])
    x, y = pair
    after = pairs.copy()
    after.remove(x)
    after.remove(y)
    after.append((x[0], y[0]))
    assert len(wires) == 5
    assert sum((a < 5) != (b < 5) for a, b in after) == 3
    print("bad lift", pair, "original cut", wires)


if __name__ == "__main__":
    bisection_witness()
    two_roots()
    bad_split()
