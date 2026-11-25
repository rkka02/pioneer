"""Enumerate all simple connected cubic reconnections after deleting two vertices."""

import itertools
import sys

import networkx as nx


def pairings(ports):
    if not ports:
        yield ()
        return
    for j in range(1, len(ports)):
        for tail in pairings(ports[1:j] + ports[j + 1:]):
            yield ((ports[0], ports[j]),) + tail


def reductions(graph):
    for u, v in itertools.combinations(graph, 2):
        ports = [a for x in (u, v) for a in graph[x] if a != u and a != v]
        base = graph.copy()
        base.remove_nodes_from((u, v))
        alternatives = set()
        for pairs in pairings(ports):
            edges = tuple(sorted(tuple(sorted(edge)) for edge in pairs))
            if edges in alternatives or len(set(edges)) != len(edges):
                continue
            if any(a == b or base.has_edge(a, b) for a, b in edges):
                continue
            alternatives.add(edges)
            base.add_edges_from(edges)
            if nx.is_connected(base):
                yield nx.to_graph6_bytes(base, header=False).strip()
            base.remove_edges_from(edges)


if __name__ == "__main__":
    with open(sys.argv[1], "rb") as source:
        for record in source:
            for reduced in reductions(nx.from_graph6_bytes(record.strip())):
                sys.stdout.buffer.write(reduced + b"\n")
