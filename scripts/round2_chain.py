"""Sharp transfer size and branching tradeoff on the seven-cut family."""

import argparse
from functools import cache
from itertools import combinations
from math import inf

import networkx as nx

from flow_lab import divergence
from round1_repair import CAP_A, CAP_B, LEFT, MIDDLE, RIGHT, join_lobes
from round2_transfers import TransferSearch


def certificates(k):
    n, p, _ = join_lobes(k)
    z, x, y = 24, 6, 15
    # Local edge indices refer to CAP_A (19), CAP_B (19), and MIDDLE (24).
    # For the new orientation the indices name edges retained in their old direction.
    # This complement of the solved template fixes the given one-in/four-out star.
    kept_a = {4, 6, 7, 8, 15, 18}
    kept_b = {0, 1, 2, 4, 8, 9, 11, 12, 15, 17}
    kept_middle = {1, 2, 3, 8, 11, 13, 14, 15, 18, 22, 23}
    kept_l = {2, 3, 5}
    kept_r = {1, 4, 5}
    fixed = {1, 19 + 1, 19 + 14}
    few_branches = {1, 13, 19 + 2}
    path = {1, 19 + 14}
    kept = kept_a | {19 + i for i in kept_b}
    for j in range(k):
        start = 38 + 24 * j
        fixed.update((start + 5, start + 22))
        few_branches.update(start + i for i in ((0, 1, 6) if j == 0 else (0, 6)))
        path.add(start + 5)
        kept.update(start + i for i in kept_middle)
    start = 38 + 24 * k

    def wire(edge, side, i, left_cap=False):
        if (side == "L" and i == 0) or (side == "R" and i in (0, 4)):
            fixed.add(edge)
        if (side == "R" and i == 0) or (side == "L" and i in ((0, 4) if left_cap else (0, 1))):
            few_branches.add(edge)
        if (side == "L" and i == 0) or (side == "R" and i == 4):
            path.add(edge)
        if i in (kept_l if side == "L" else kept_r):
            kept.add(edge)

    for i in range(6):
        wire(start + 2 * i, "L", i, left_cap=True)
        wire(start + 2 * i + 1, "R", i)
    for j in range(k - 1):
        for i in range(6):
            wire(start + 12 + 6 * j + i, "L" if j % 2 else "R", i)
    new = [1 if i in kept else -1 for i in range(len(p))]
    assert all(new[i] == 1 for i, edge in enumerate(p) if z in edge)
    assert all(t % 3 == 0 for t in divergence(n, p, new))
    for signs, chosen, branches in [
        ([1] * len(p), fixed, k + 1),
        ([1] * len(p), few_branches, k),
        (new, path, 0),
    ]:
        assert not any(z in p[i] for i in chosen)
        delta = divergence(n, p, [s * int(i in chosen) for i, s in enumerate(signs)])
        assert delta[x] % 3 and (delta[x] + delta[y]) % 3 == 0
        assert all(t % 3 == 0 for v, t in enumerate(delta) if v not in (x, y))
        assert sum(bool(t) for v, t in enumerate(delta) if v not in (x, y)) == branches
        added = -1 if delta[x] % 3 == 1 else 1
        full = [s * (-1 if i in chosen else 1) for i, s in enumerate(signs)] + [added]
        assert all(t % 3 == 0 for t in divergence(n, p + [(x, y)], full))
    assert len(fixed) == (7 * k + 9) // 2
    assert len(few_branches) == len(fixed) + 1
    assert len(path) == 2 * k + 3
    digraph = nx.DiGraph()
    digraph.add_edges_from(p[i] if new[i] == 1 else p[i][::-1] for i in path)
    assert nx.is_directed_acyclic_graph(digraph)
    assert max(digraph.in_degree(v) for v in digraph) == max(digraph.out_degree(v) for v in digraph) == 1
    free = [e for e in p if z not in e]
    assert nx.shortest_path_length(nx.Graph(free), x, y) == len(path)
    if k == 1:
        assert len(TransferSearch(n, free).shortest(x, y)) == len(fixed)
    return n, len(fixed), len(few_branches), len(path)


def tight_interfaces():
    """With one branch per middle, a two-edge middle is precisely an inward fork on three ports."""
    masks = list(combinations(range(6), 1)) + list(combinations(range(6), 2))

    def fork(l, r, first=False):
        if len(l) + len(r) != 3:
            return False
        ports = {LEFT[i] for i in l} | {RIGHT[i] for i in r}
        if first and 6 in ports:
            return False
        return any(all((other, center) in MIDDLE for other in ports - {center}) for center in ports)

    for size in (1, 2):
        starts = [l for l in masks if len(l) == size and all((6, i) in CAP_A for i in l)]
        ends = [r for r in masks if len(r) == 3 - size and all((6, i) in CAP_B for i in r)]
        reached = {r for l in starts for r in masks if fork(l, r, first=True)}
        first_right = reached.copy()
        while True:
            left = {l for r in reached for l in masks if fork(l, r)}
            new = reached | {r for l in left for r in masks if fork(l, r)}
            if reached == new:
                break
            reached = new
        assert not reached.intersection(ends)
        if size == 1:
            assert starts == [(0,), (4,)] and ends == [(0, 1)]
            assert first_right == {(0, 4)} and left == {(0,)} and reached == {(0, 4), (4, 5)}
        else:
            assert starts == [(0, 4)] and ends == [(0,), (1,)] and not first_right
        print(
            "tight port masks, cap/first/closure/other cap",
            starts,
            sorted(first_right),
            sorted(reached),
            ends,
        )


def min_cost_check():
    """Independent finite-state minimization when every middle has exactly one branch."""
    masks = list(combinations(range(6), 1)) + list(combinations(range(6), 2))

    @cache
    def block_cost(kind, l, r=(), first=False):
        template = {"left cap": CAP_A, "right cap": CAP_B, "middle": MIDDLE}[kind]
        middle = kind == "middle"
        ports = tuple(LEFT[i] for i in l) + tuple(RIGHT[i] for i in r) if middle else l
        if first and 6 in ports:
            return inf
        graph = nx.DiGraph()
        graph.add_nodes_from(range(12 if middle else 9), demand=0)
        graph.add_edges_from((e for e in template if not first or 6 not in e), weight=1, capacity=1)
        for port in ports:
            graph.nodes[port]["demand"] = -1 if middle else 1
        best = inf
        for branch in (graph.nodes if middle else (6,)):
            if first and branch == 6:
                continue
            extra = len(ports) if middle else -len(ports)
            graph.nodes[branch]["demand"] += extra
            try:
                cost, _ = nx.network_simplex(graph)
                best = min(best, cost)
            except nx.NetworkXUnfeasible:
                pass
            finally:
                graph.nodes[branch]["demand"] -= extra
        return best

    costs = {l: block_cost("left cap", l) for l in masks}
    for i in range(101):
        costs = {
            b: min(
                value + (block_cost("middle", a, b, i == 0) if i % 2 == 0 else block_cost("middle", b, a))
                for a, value in costs.items()
                if len(a) + len(b) == 3
            )
            for b in masks
        }
        k = i + 1
        if k % 2:
            minimum = (
                min(value + block_cost("right cap", r) for r, value in costs.items()) + 3 * (k + 1) // 2
            )
            assert minimum == (7 * k + 11) // 2
    print("independent minimum-cost computation for all 51 odd lengths through 101")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--min-cost", action="store_true", help="also exhaust the one-branch template costs"
    )
    args = parser.parse_args()
    tight_interfaces()
    for k in (1, 3, 5, 7, 9, 15):
        print(
            "middle blocks/order/fixed optimum/minimum-branch optimum/free optimum",
            k,
            *certificates(k),
            flush=True
        )
    if args.min_cost:
        min_cost_check()
