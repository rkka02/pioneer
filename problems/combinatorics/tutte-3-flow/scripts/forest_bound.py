"""Stress the component-size sufficient condition, including a sharp five-connected example."""
import itertools
import random
from collections import Counter

import networkx as nx

from bisections import component_defect
from flow_lab import lift, mincut, orient, regular_census
from obstructions import seven_cut_graph
from search import named_cases


def near_uniform_obstruction():
    # 8 vertices in four doubletons, and 5 singleton vertices, per shore.
    shore = [(i, i+1) for i in range(0, 8, 2)]
    shore += [(8+j, (5*j+i) % 8) for i, j in itertools.product(range(5), range(5))]
    pairs = shore + [(u+13, v+13) for u, v in shore] + [(i, i+13) for i in range(1, 8)]
    high = set(range(8, 13)) | set(range(13, 21))
    graph = nx.Graph(pairs)
    assert len(pairs) == graph.number_of_edges() == 65
    assert set(dict(graph.degree()).values()) == {5} and mincut(26, pairs) == 5
    for side in (high, set(graph)-high):
        assert sorted(map(len, nx.connected_components(graph.subgraph(side)))) == [1]*5+[2]*4
    assert component_defect(graph, high) == 1
    assert 3*(8-5) > 7
    signs = orient(26, pairs, [0]*26)
    assert signs is not None
    lift(26, pairs, signs)
    print("26-vertex sharpness graph", "minimum cut 5, Hall deficiency 1, other signing feasible")
    return pairs


def test_partition(graph, high, lam, stats):
    components = []
    for side in (high, set(graph)-high):
        inside = graph.subgraph(side)
        if not nx.is_forest(inside):
            return
        components.append(list(map(len, nx.connected_components(inside))))
    stats["two forests"] += 1
    h, l = components
    assert len(h) == len(l) and sum(h) == sum(l)
    defect = component_defect(graph, high)
    for s in range(1, max(h+l)+1):
        spread = sum(max(0, a-s) for a in l) + sum(max(0, s-a) for a in h)
        if 3*spread < lam + 3*s + 2:
            assert defect == 0
            stats["criterion passes partition"] += 1
            if len(set(h+l)) > 1:
                stats["mixed sizes pass"] += 1
            return


def main():
    rng, stats = random.Random(355), Counter()
    for n in (6, 8, 10):
        for pairs in regular_census(n):
            graph = nx.MultiGraph(pairs)
            lam = mincut(n, pairs)
            for rest in itertools.combinations(range(1, n), n//2-1):
                test_partition(graph, {0, *rest}, lam, stats)
    for name, n, pairs in named_cases():
        if mincut(n, pairs) != 5 or 2*len(pairs) != 5*n:
            continue
        graph = nx.MultiGraph(pairs)
        for _ in range(120):
            test_partition(graph, set(rng.sample(range(n), n//2)), 5, stats)
    p = near_uniform_obstruction()
    test_partition(nx.MultiGraph(p), set(range(8, 13)) | set(range(13, 21)), 5, stats)
    high = set(range(6)) | {15,16,17}
    test_partition(nx.MultiGraph(seven_cut_graph()), high, 5, stats)
    print("forest criterion", stats)


if __name__ == "__main__":
    main()
