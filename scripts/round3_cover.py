"""Exact six-vertex-cover obstruction search. nauty genbg preserves the two vertex colours."""

from collections import Counter
from functools import lru_cache
from itertools import combinations
import shutil
import subprocess

import networkx as nx
from flow_lab import boundary_counts, edges
from round3_reduced import strong_witness


def bipartite(q, maximum, span):
    exe = shutil.which("genbg") or shutil.which("nauty-genbg")
    data = subprocess.check_output([exe, "-q", "-d0:3", f"-D{q}:{maximum}", "6", str(q), span])
    for line in data.splitlines():
        g = nx.from_graph6_bytes(line)
        assert all((a < 6) != (b < 6) for a, b in g.edges())
        yield g


def has_strong(g):
    # All vertices of a smallest nontrivial strong subgraph survive degree-two peeling.
    j = nx.convert_node_labels_to_integers(nx.k_core(g, 3))
    if not len(j):
        return False
    p = edges(j)
    return (2 ** len(p) >= 3 ** (len(j) - 1) and boundary_counts(len(j), p).min() > 0) or strong_witness(
        len(j), p
    ) is not None


def six_outsiders():
    sizes = Counter()
    for g in bipartite(6, 5, "25:25"):
        j = nx.convert_node_labels_to_integers(nx.k_core(g, 3))
        assert boundary_counts(len(j), edges(j)).min() > 0
        sizes[len(j)] += 1
    assert sizes == {9: 34, 10: 154, 11: 433, 12: 653}
    print("six by six, 25 cross edges; group-connected 3-core sizes", dict(sizes), flush=True)


def small_outside(q):
    hist = Counter()
    inside = list(combinations(range(6), 2))
    for g in bipartite(q, 6, f"{5*q-5}:0"):
        hist["bipartite inputs"] += 1
        deficit = sum(max(0, 5 - g.degree(v)) for v in range(6, 6 + q))
        if deficit > 5:
            continue
        hist["outer deficit passes"] += 1
        if has_strong(g):
            continue
        hist["reduced cross graph"] += 1
        allowed = []
        for a, b in inside:
            g.add_edge(a, b)
            if not has_strong(g):
                allowed.append((a, b))
            g.remove_edge(a, b)
        budget = 5 - deficit

        @lru_cache(None)
        def legal(mask):
            d = [g.degree(i) for i in range(6)]
            for k, (a, b) in enumerate(allowed):
                if mask >> k & 1:
                    d[a] += 1
                    d[b] += 1
            return min(d) >= 3 and sum(max(0, 5 - val) for val in d) <= budget

        top = (1 << len(allowed)) - 1
        if not legal(top):
            continue
        for mask in range(top + 1):
            if not legal(mask) or any(
                legal(mask ^ (1 << k)) for k in range(len(allowed)) if mask >> k & 1
            ):
                continue
            j = g.copy()
            j.add_edges_from(e for k, e in enumerate(allowed) if mask >> k & 1)
            assert has_strong(j), (q, nx.to_graph6_bytes(j, header=False), edges(j))
            hist["minimal augmentations checked"] += 1
        legal.cache_clear()
    expected = {4: (404, 393, 272, 50490), 5: (1438, 1309, 121, 0)}
    assert (
        tuple(
            hist[k]
            for k in (
                "bipartite inputs",
                "outer deficit passes",
                "reduced cross graph",
                "minimal augmentations checked",
            )
        )
        == expected[q]
    )
    print("six cover vertices with", q, "outsiders", dict(hist), flush=True)


if __name__ == "__main__":
    six_outsiders()
    for q in (4, 5):
        small_outside(q)
