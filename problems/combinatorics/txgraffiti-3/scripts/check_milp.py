"""Optimize directly over vertices and edges of a graph6 record with SciPy/HiGHS."""

import sys
from pathlib import Path

import networkx as nx
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp


def minimum(items, conflicts, neighborhoods):
    # One binary variable per candidate. Conflicts prohibit selecting both items.
    # Every closed neighborhood contains a selected item.
    index = {item: j for j, item in enumerate(items)}
    rows, lower, upper = [], [], []
    for a, b in conflicts:
        row = np.zeros(len(items))
        row[[index[a], index[b]]] = 1
        rows.append(row)
        lower.append(-np.inf)
        upper.append(1)
    for neighborhood in neighborhoods:
        row = np.zeros(len(items))
        row[[index[a] for a in neighborhood]] = 1
        rows.append(row)
        lower.append(1)
        upper.append(np.inf)
    result = milp(np.ones(len(items)), integrality=np.ones(len(items)), bounds=Bounds(0, 1),
                  constraints=LinearConstraint(np.array(rows), lower, upper),
                  options={"mip_rel_gap": 0.0})
    if not result.success or result.mip_gap != 0:
        raise RuntimeError(result.message)
    selected = {x for x, value in zip(items, result.x) if value > 0.5}
    if abs(result.fun - len(selected)) > 1e-6:
        raise RuntimeError("inconsistent objective")
    return selected


def check(graph):
    edges = [tuple(sorted(e)) for e in graph.edges]
    incident = {v: set() for v in graph}
    for edge in edges:
        for v in edge:
            incident[v].add(edge)
    d = minimum(list(graph), edges, [set(graph[v]) | {v} for v in graph])
    conflicts = [(a, b) for v in graph for a in incident[v] for b in incident[v] if a < b]
    m = minimum(edges, conflicts, [incident[u] | incident[v] for u, v in edges])
    covered = {v for edge in m for v in edge}
    assert all(u not in d or v not in d for u, v in edges)
    assert all(v in d or d.intersection(graph[v]) for v in graph)
    assert len(covered) == 2 * len(m) and all(u in covered or v in covered for u, v in edges)
    print(f"vertices={len(graph)} edges={len(edges)} degrees={sorted(set(dict(graph.degree).values()))}"
          f" connected={nx.is_connected(graph)}")
    print(f"i={len(d)} witness={sorted(d)}")
    print(f"mu={len(m)} witness={sorted(m)}")


if __name__ == "__main__":
    check(nx.from_graph6_bytes(Path(sys.argv[1]).read_bytes().strip()))
