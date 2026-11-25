"""Compare the worst integer cut deficit with matching deficiency, bisection by bisection."""
import itertools
from collections import Counter

import networkx as nx
import numpy as np

from flow_lab import edges, mincut, regular_census, splice


def component_defect(graph, high):
    trees = []
    for side in (high, set(graph)-high):
        induced = graph.subgraph(side)
        parts = []
        for c in nx.connected_components(induced):
            m = induced.subgraph(c).number_of_edges()
            if m > len(c):
                return None
            if m < len(c):
                parts.append(c)
        trees.append(parts)
    left, right = trees
    assert len(left) == len(right)
    aux = nx.Graph()
    aux.add_nodes_from(range(len(left)))
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            if any(v in b for u in a for v in graph[u]):
                aux.add_edge(i, ~j)
    matching = nx.bipartite.maximum_matching(aux, top_nodes=range(len(left)))
    return len(left) - len(matching)//2


def analyze(n, pairs, summary, examples, sample=None):
    graph = nx.MultiGraph()
    graph.add_edges_from(pairs)
    assert all(d == 5 for _, d in graph.degree()) and mincut(n, pairs) == 5
    masks = np.arange(1 << n, dtype=np.int32)
    sizes = np.bitwise_count(masks).astype(np.int32)
    internal = np.zeros_like(masks)
    for a, b in pairs:
        internal += (masks >> a) & (masks >> b) & 1
    cuts = 5*sizes - 2*internal
    bisections = [(0, *rest) for rest in itertools.combinations(range(1, n), n//2-1)]
    if sample is not None:
        import random
        bisections = random.Random(355).sample(bisections, min(sample, len(bisections)))
    cut_max = int(cuts[sizes == n//2].max())
    values = {}
    for group in bisections:
        high = sum(1 << v for v in group)
        deficit = internal - sizes - 3*np.bitwise_count(masks & high).astype(np.int32)
        d = int(deficit.max())
        values[high] = d
        match = component_defect(graph, set(group))
        summary["bisections"] += 1
        if match is not None:
            assert d == match
            summary["pseudo"] += 1
            summary["pseudo deficiency " + str(d)] += 1
        if d and (match is not None or cuts[high] == cut_max):
            key = "max cut bad" if cuts[high] == cut_max else "pseudo bad"
            w = int(np.argmax(deficit))
            examples.setdefault(key, (n, pairs, group, [v for v in range(n) if (w >> v) & 1],
                                      d, match, int(cuts[high]), cut_max))
    if sample is None:
        assert min(values.values()) == 0
        all_bits = (1 << n)-1
        for high, d in values.items():
            if d == 0:
                continue
            neighbors = []
            for a in range(n):
                for b in range(a+1, n):
                    if (high >> a ^ high >> b) & 1:
                        h = high ^ (1 << a) ^ (1 << b)
                        neighbors.append(values[h if h & 1 else all_bits ^ h])
            if d <= min(neighbors):
                summary["strict descent fails"] += 1
                examples.setdefault("strict descent fails", (n, pairs, high, d, min(neighbors)))
    return values


def main():
    stats, examples = Counter(), {}
    for n in (6, 8, 10):
        for pairs in regular_census(n):
            if mincut(n, pairs) == 5:
                analyze(n, pairs, stats, examples)
    print("census", stats)
    k6 = edges(nx.complete_graph(6))
    p = [e for e in edges(nx.petersen_graph()) for _ in range(1 if e[1]-e[0] == 5 else 2)]
    for pairs in (p, splice(6, k6, 0, 6, k6, 0, range(5))):
        analyze(10, pairs, stats, examples)
    for seed in range(8):
        analyze(12, edges(nx.random_regular_graph(5, 12, seed=seed)), stats, examples)
    print("combined", stats)
    for name, witness in examples.items():
        print(name, witness)


if __name__ == "__main__":
    main()
