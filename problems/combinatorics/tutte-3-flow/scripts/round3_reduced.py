"""Exact reducedness, five-spoke completion, and deterministic block/cover constructions."""

from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
import networkx as nx
import numpy as np

from flow_lab import boundary_counts, edges, flower, jlpt, mincut
from round1_ports import LocalOrientations, port_pins, solve_checked
from round1_repair import nontrivial_five_cut


def count(n, p, beta, skip=()):
    """Integer frontier DP with forgotten vertices tested at their last edge."""
    q = [e for i, e in enumerate(p) if i not in skip]
    last = {v: i for i, e in enumerate(q) for v in e}
    if any(beta[v] % 3 for v in range(n) if v not in last):
        return 0
    active = []
    state = {(): 1}
    for i, (a, b) in enumerate(q):
        work = active + [v for v in (a, b) if v not in active]
        keep = [j for j, v in enumerate(work) if last[v] > i]
        close = [(j, beta[v] % 3) for j, v in enumerate(work) if last[v] == i]
        ia, ib = work.index(a), work.index(b)
        result = Counter()
        for key, num in state.items():
            t = list(key) + [0] * (len(work) - len(active))
            for sign in (1, -1):
                r = t.copy()
                r[ia] = (r[ia] + sign) % 3
                r[ib] = (r[ib] - sign) % 3
                if all(r[j] == wanted for j, wanted in close):
                    result[tuple(r[j] for j in keep)] += num
        active = [work[j] for j in keep]
        state = result
    return state.get((), 0)


def strong_witness(n, p):
    """Find a strongly connected-in-the-group-sense induced subgraph, or prove reduced.

    Exhaustive fallback is exponential. Large structured examples use the certificates below.
    """
    graph = nx.Graph(p)
    graph.add_nodes_from(range(n))
    for size in range(2, n + 1):
        for s in combinations(range(n), size):
            g = graph.subgraph(s)
            # A smallest simple nontrivial strong subgraph has minimum degree at least three.
            if min((d for _, d in g.degree()), default=0) < 3 or 2 ** len(g.edges) < 3 ** (size - 1):
                continue
            pairs = edges(nx.convert_node_labels_to_integers(g))
            if size <= 12 and len(pairs) < 63:
                if boundary_counts(size, pairs).min() > 0:
                    return s
            else:
                solver = LocalOrientations(size, pairs)
                if all(
                    solver.solve((*d, -sum(d) % 3), {}) is not None
                    for d in product(range(3), repeat=size - 1)
                ):
                    return s
    return None


def port_assignments(n, p):
    d = Counter(v for e in p for v in e)
    forced = [v for v in range(n) for _ in range(max(0, 5 - d[v]))]
    if len(forced) > 5:
        return
    for extra in combinations_with_replacement(range(n), 5 - len(forced)):
        ports = tuple(sorted(forced + list(extra)))
        if any(d[v] < ports.count(v) + 1 for v in set(ports)) and n >= 3:
            continue
        whole = p + [(n, v) for v in ports]
        if mincut(n + 1, whole) >= 5 and nontrivial_five_cut(n + 1, whole, n) is None:
            yield ports


def test_reduced_core(n, p):
    # Call only after reducedness certification. Test every labelled minority, including repeats.
    count_ports = count_stars = 0
    for ports in port_assignments(n, p):
        count_ports += 1
        whole = p + [(n, v) for v in ports]
        solver = LocalOrientations(n + 1, whole)
        for minority in range(5):
            pins = port_pins(whole, n, minority)
            signs = solve_checked(solver, [0] * (n + 1), pins)
            if signs is None:
                raise RuntimeError(f"Missing minority: {n=} {p=} {ports=} {minority=}")
            count_stars += 1
    return count_ports, count_stars


def core(kind, n):
    if kind == "three hubs":
        return [(0, 1)] + [(v, i) for v in range(3, n) for i in range(3)]
    if kind == "edge books":
        return [(0, 1)] + [
            e for v in range(2, n, 2) for e in [(v, v + 1), (0, v), (1, v), (0, v + 1), (1, v + 1)]
        ]
    if kind == "odd wheel":
        return [e for i in range(1, n) for e in [(i, 1 + i % (n - 1)), (0, i)]]
    raise ValueError(kind)


def certified_families():
    stats = Counter()
    for kind in ("three hubs", "edge books", "odd wheel"):
        for n in range(10, 41, 1 if kind == "three hubs" else 2):
            p = core(kind, n)
            # For a missing boundary, private points at every edge prove reducedness.
            assert count(n, p, [0] * n) == 0
            # All edges in each orbit are equivalent for zero boundary.
            reps = [0, 1, 3] if kind == "three hubs" else [0, 1, 2] if kind == "edge books" else [0, 1]
            assert all(count(n, p, [0] * n, [i]) > 0 for i in reps)
            if n == 10:
                assert all(count(n, p, [0] * n, [i]) > 0 for i in range(len(p)))
                assert strong_witness(n, p) is None
            assert test_reduced_core(n, p) == (0, 0)
            stats[kind] += 1
    # Nonbipartite cubic connected graphs have no zero flow, and their proper subgraphs peel to degree two.
    for g in [nx.petersen_graph(), nx.from_edgelist(flower(9))]:
        n = len(g)
        p = edges(g)
        assert nx.is_connected(g) and not nx.is_bipartite(g) and set(dict(g.degree()).values()) == {3}
        assert test_reduced_core(n, p) == (0, 0)
    print(
        "exact reduced core constructions and zero eligible completions",
        dict(stats),
        "plus two cubic cores",
        flush=True,
    )


def deficit_patterns():
    # Five missing adjacencies in K5,5, up to permutations on each side.
    changes = [
        tuple(sum(1 << perm[i] for i in range(5) if mask >> i & 1) for mask in range(32))
        for perm in permutations(range(5))
    ]

    def cols(prefix, start, weight):
        if len(prefix) == 5:
            if weight == 0:
                yield tuple(prefix)
            return
        for mask in range(start, 32):
            if mask.bit_count() <= weight:
                yield from cols(prefix + [mask], mask, weight - mask.bit_count())

    return {min(tuple(sorted(p[c] for c in columns)) for p in changes) for columns in cols([], 0, 5)}


def cover_test():
    stats = Counter()
    for masks in sorted(deficit_patterns()):
        p = [(a, 5 + b) for a in range(5) for b, mask in enumerate(masks) if not mask >> a & 1]
        witness = strong_witness(10, p)
        assert witness is not None
        if len(witness) == 10:
            assert sorted(masks) == [1, 2, 4, 8, 16]
            assert boundary_counts(10, p).min() == 18
        stats[len(witness)] += 1
    assert stats == {8: 33, 10: 1}
    print(
        "K5,5 minus five edges, strong induced certificate sizes by isomorphism type",
        dict(stats),
        flush=True,
    )
    q = edges(nx.complete_bipartite_graph(4, 4))
    assert int(boundary_counts(8, q).min()) == 16
    # Saturation of the reduced twelve-vertex JLPT graph by any added edge.
    p = jlpt()
    tab = boundary_counts(12, p)
    holes = {tuple(map(int, b)) for b in zip(*np.nonzero(tab == 0))}
    assert holes == {(1,) * 11, (2,) * 11}
    assert strong_witness(12, p) is None
    g = nx.Graph(p)
    for a, b in nx.non_edges(g):
        delta = [0] * 12
        delta[a], delta[b] = 1, -1
        assert not (holes & {tuple((x + 2 * d) % 3 for x, d in zip(h, delta)) for h in holes})
    assert test_reduced_core(12, p) == (0, 0)
    print(
        "JLPT core: reduced; all",
        len(list(nx.non_edges(g))),
        "simple one-edge extensions group-connected",
    )


def dense_reduced_substitutions():
    # A strong subgraph would project to one in the old graph or lie entirely in the new fibre.
    g = nx.Graph(jlpt())
    for step in range(1, 15):
        n, m = len(g), g.number_of_edges()
        u, d = max(g.degree(), key=lambda item: item[1])
        old = list(g.neighbors(u))
        new = max(g) + 1
        g.remove_node(u)
        g.add_edges_from((new + a, new + b) for a, b in core("three hubs", d + 3))
        g.add_edges_from((v, new + 3 + i) for i, v in enumerate(old))
        assert len(g) == n + d + 2 and g.number_of_edges() == m + 3 * d + 1
        assert min(dict(g.degree()).values()) == 4
        assert sum(max(5 - q, 0) for _, q in g.degree()) > 5
        if 5 * len(g) - 2 * g.number_of_edges() <= 5:
            print(
                "reduced substitution, min degree four and high average",
                step,
                len(g),
                g.number_of_edges(),
                "five-spoke deficit",
                sum(max(5 - q, 0) for _, q in g.degree()),
            )
            break
    else:
        raise AssertionError("density threshold not reached")
    # Cover the small inserted fibres below the order-ten start of the family loop.
    for n in (7, 8, 9):
        p = core("three hubs", n)
        assert strong_witness(n, p) is None and count(n, p, [0] * n) == 0
        assert all(count(n, p, [0] * n, [i]) for i in range(len(p)))
    # Two spokes to v may leave degree three, even when every nontrivial cut has size >= 6.
    p = edges(nx.complete_graph(7)) + [(7, i) for i in range(3)] + [(8, i) for i in (7, 7, 3, 4, 5)]
    assert mincut(9, p) == 5 and nontrivial_five_cut(9, p, 8) is None
    for i in range(5):
        assert solve_checked(LocalOrientations(9, p), [0] * 9, port_pins(p, 8, i))
    print("double-spoke example: free degree three; all five pins extend")
    # All choices of centre/incident leaves give a W4 inside an augmented K3,t.
    for t in (6, 12, 37):
        g = nx.complete_bipartite_graph(3, t)
        g.add_edges_from((3 + i, 3 + (i + 1) % t) for i in range(t))
        for i in range(t):
            a, b = 3 + (i - 1) % t, 3 + (i + 1) % t
            vertices = [3 + i, 0, a, 1, b]
            assert all(g.has_edge(vertices[u], vertices[v]) for u, v in nx.wheel_graph(5).edges())


if __name__ == "__main__":
    certified_families()
    cover_test()
    dense_reduced_substitutions()
