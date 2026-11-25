"""Minimize the order of a counterexample among independent blow-ups of a template.

Read connected short graph6 templates from stdin. An optimum expands to an explicit
simple regular graph, which can be piped into check_graphs --exact.
"""

import sys

import networkx as nx
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp


def search(h, limit):
    n = len(h)
    a = nx.to_numpy_array(h, nodelist=range(n))
    if len({tuple(row) for row in a}) < n:
        return  # false twins are already represented by a single class
    edges = list(h.edges)
    d = n + len(edges)
    objective = np.r_[np.ones(n), np.zeros(len(edges))]
    rows, lower, upper = [], [], []

    def constrain(row, lo, hi):
        rows.append(row)
        lower.append(lo)
        upper.append(hi)

    # Class sizes s and matching multiplicities x. Require all neighbor-size sums equal.
    for j in range(1, n):
        constrain(np.r_[a[j] - a[0], np.zeros(len(edges))], 0, 0)
    sets = list(nx.find_cliques(nx.complement(h)))
    for independent in sets:
        row = np.r_[np.zeros(n), -np.ones(len(edges))]
        row[independent] = 1
        constrain(row, 1, np.inf)
    constrain(objective, n, limit)
    cap_start = len(rows)
    for v in range(n):
        row = np.zeros(d)
        row[v] = -1
        for k, edge in enumerate(edges):
            row[n + k] = v in edge
        constrain(row, -np.inf, 0)
    matrix = np.array(rows)
    bounds = Bounds(np.r_[np.ones(n), np.zeros(len(edges))], np.inf)
    # The LP relaxation can discard a template before any integer solves.
    relaxation = milp(objective, bounds=bounds, constraints=LinearConstraint(matrix, lower, upper))
    if relaxation.status == 2:
        return
    if not relaxation.success:
        raise RuntimeError(relaxation.message)
    for unmatched in sets:
        lo = lower.copy()
        for v in set(h) - set(unmatched):
            lo[cap_start + v] = 0
        result = milp(objective, integrality=np.ones(d), bounds=bounds,
                      constraints=LinearConstraint(matrix, lo, upper))
        if result.status == 2:
            continue
        if not result.success:
            raise RuntimeError(result.message)
        sizes = np.rint(result.x[:n]).astype(int)
        large = nx.Graph()
        groups = np.split(np.arange(sum(sizes)), sizes.cumsum()[:-1])
        large.add_nodes_from(range(sum(sizes)))
        for u, v in edges:
            large.add_edges_from((i, j) for i in groups[u] for j in groups[v])
        print(nx.to_graph6_bytes(large, header=False).decode().strip(), flush=True)


if __name__ == "__main__":
    limit = int(sys.argv[1])
    for line in sys.stdin.buffer:
        search(nx.from_graph6_bytes(line.strip()), limit)
