"""Reconstruct the 42-vertex witness from the archived order-48 seed and verify the tables."""

from collections import Counter
from functools import cache
from pathlib import Path

import networkx as nx


directory = Path(__file__).resolve().parent
g = nx.from_graph6_bytes((directory / "order48.g6").read_bytes().strip())
g.remove_nodes_from([2, 3, 18, 19, 32, 39])
g.add_edges_from([(1, 36), (1, 45), (8, 44), (12, 44), (13, 46), (20, 41), (25, 40)])
g = nx.convert_node_labels_to_integers(g, ordering="sorted")
record = nx.to_graph6_bytes(g, nodes=sorted(g), header=False)
if record != (directory / "counterexample.g6").read_bytes():
    raise ValueError("the reconstruction differs from the formal witness")

assert len(g) == 42 and g.size() == 63 and nx.is_connected(g)
assert all(d == 3 for _, d in g.degree)
assert all(g.has_edge(2*j, 2*j+1) for j in range(13))
assert all(min(u, v) < 26 for u, v in g.edges)
assert {(min(u, v), max(u, v)) for u, v in g.edges if u < 26 and v < 26 and u//2 != v//2} == {
    (3, 4), (6, 11)}
print("Unmatched vertex neighborhoods")
for v in range(26, 42):
    print(v, *sorted(g[v]))

histogram = Counter()
for choices in range(1 << 13):
    selected = {2*j + ((choices >> j) & 1) for j in range(13)}
    if any(u in selected and v in selected for u, v in g.edges):
        continue
    uncovered = sum(selected.isdisjoint(g[v]) for v in range(26, 42))
    histogram[uncovered] += 1
print("Independent endpoint transversals by number of uncovered vertices", dict(sorted(histogram.items())))

closed = {v: frozenset([v, *g[v]]) for v in g}
order = list(nx.bfs_tree(g, 15, sort_neighbors=sorted))
counts = Counter()


@cache
def induced_minimum(region):
    if not region:
        counts["empty"] += 1
        return 0
    component = frozenset(nx.node_connected_component(g.subgraph(region), min(region)))
    if component != region:
        counts["split"] += 1
        return induced_minimum(component) + induced_minimum(region - component)
    counts["pivot"] += 1
    pivot = min((v for v in order if v in region), key=lambda v: len(closed[v] & region))
    return 1 + min(induced_minimum(region - closed[x]) for x in closed[pivot] & region)


vertices = frozenset(g)
print("Induced-subgraph minimum", induced_minimum(vertices), dict(counts))
print("Root children", {x: induced_minimum(vertices - closed[x]) for x in order if x in closed[15]})
