"""Integer dynamic programming on a graph and its line graph. Input is graph6."""

import sys
from pathlib import Path

import networkx as nx


def minimum(graph):
    # Label in BFS order. Choose the root with the smallest maximum number
    # of neighborhoods crossing a cut. This choice only affects memory use.
    vertices = list(graph)
    if not vertices:
        return 0
    if not nx.is_connected(graph):
        return sum(minimum(graph.subgraph(c)) for c in nx.connected_components(graph))

    def width(order):
        pos = {v: j for j, v in enumerate(order)}
        events = [0] * (len(order) + 1)
        for v in order:
            positions = [pos[v], *(pos[w] for w in graph[v])]
            events[min(positions)] += 1
            events[max(positions)] -= 1
        width_now = maximum = 0
        for event in events:
            width_now += event
            maximum = max(maximum, width_now)
        return maximum

    order = min((list(nx.bfs_tree(graph, v)) for v in vertices), key=width)
    pos = {v: j for j, v in enumerate(order)}
    closed = []
    expires = [0] * len(order)
    for j, v in enumerate(order):
        neighbors = [pos[v], *(pos[w] for w in graph[v])]
        closed.append(sum(1 << w for w in neighbors))
        expires[max(neighbors)] |= 1 << j

    # covered records which still-relevant vertices have a selected vertex in
    # their closed neighborhood. Equal states have identical possible continuations.
    state = {0: 0}
    for j, mask in enumerate(closed):
        next_state = {}
        required = expires[j]
        for covered, cost in state.items():
            if covered & required == required:
                key = covered & ~required
                next_state[key] = min(next_state.get(key, cost), cost)
            if not covered & (1 << j):
                selected = covered | mask
                if selected & required == required:
                    key = selected & ~required
                    next_state[key] = min(next_state.get(key, cost + 1), cost + 1)
        state = next_state
    return state[0]


if __name__ == "__main__":
    graph = nx.from_graph6_bytes(Path(sys.argv[1]).read_bytes().strip())
    print(f"i={minimum(graph)} mu={minimum(nx.line_graph(graph))}")
