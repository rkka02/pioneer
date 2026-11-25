"""Affine chord polynomials, permanent certificates, and cancellation in connected terminal sums."""

from collections import Counter
from itertools import combinations, product, permutations
from math import comb

import networkx as nx
import numpy as np

from flow_lab import boundary_counts, edges, divergence, mincut
from round1_ports import port_pins, LocalOrientations, solve_checked


def chord_forms(n, p, tree, beta):
    """On tree edge a->b, solve the equation on the a-side of T-ab."""
    chords = [i for i in range(len(p)) if i not in tree]
    g = nx.Graph()
    g.add_nodes_from(range(n))
    g.add_edges_from(p[i] for i in tree)
    assert nx.is_tree(g)
    forms = []
    for i in tree:
        a, b = p[i]
        g.remove_edge(a, b)
        s = nx.node_connected_component(g, a)
        g.add_edge(a, b)
        forms.append(
            (sum(beta[v] for v in s), [int(v in s) - int(u in s) for u, v in (p[e] for e in chords)])
        )
    return chords, forms


def walsh(values):
    ans = values.copy() % 3
    size = len(ans)
    for j in range(size.bit_length() - 1):
        pairs = ans.reshape(-1, 2, 1 << j)
        a, b = pairs[:, 0].copy(), pairs[:, 1].copy()
        pairs[:, 0], pairs[:, 1] = (a + b) % 3, (a - b) % 3
    return ans * pow(size, -1, 3) % 3


def polynomial(n, p, tree, beta):
    chords, forms = chord_forms(n, p, tree, beta)
    masks = np.arange(1 << len(chords))
    values = np.ones(len(masks), dtype=np.int16)
    unsquared = np.zeros_like(values)
    unsquared[0] = 1
    for constant, row in forms:
        vals = np.full_like(values, constant)
        changed = constant * unsquared
        for j, a in enumerate(row):
            if a:
                vals += a * (1 - 2 * ((masks >> j) & 1)).astype(np.int16)
                changed += a * unsquared[masks ^ (1 << j)]
        values *= vals % 3 != 0
        unsquared = changed % 3
    indicator = walsh(values)
    assert np.array_equal(walsh(unsquared) ** 2 % 3, values)  # inverse scale has square one
    return chords, forms, indicator, unsquared, int(values.sum())


def permanent(matrix):
    n = len(matrix)
    return (
        sum(
            np.prod([int(row[j]) for row, j in zip(matrix, perm)], dtype=np.int64)
            for perm in permutations(range(n))
        )
        % 3
    )


def tree_list(n, p):
    ids = {tuple(sorted(e)): i for i, e in enumerate(p)}
    for tree in nx.SpanningTreeIterator(nx.Graph(p)):
        yield sorted(ids[tuple(sorted(e))] for e in tree.edges())


def polynomial_tests():
    # An integral 4-flow and two disjoint trees coexist with a missing zero boundary on K4.
    p = edges(nx.complete_graph(4))
    assert not any(divergence(4, p, [-3, 1, 2, -2, -1, -1]))
    for tree in ((1, 2, 3), (0, 4, 5)):
        assert nx.is_tree(nx.Graph([p[i] for i in tree]))
    assert boundary_counts(4, p)[(0, 0, 0)] == 0
    for name, g in [
        ("K4", nx.complete_graph(4)),
        ("W4", nx.wheel_graph(5)),
        ("K3,3+", nx.complete_bipartite_graph(3, 3)),
        ("K5-e", nx.complete_graph(5)),
    ]:
        if name == "K3,3+":
            g.add_edge(0, 1)
        if name == "K5-e":
            g.remove_edge(0, 1)
        n = len(g)
        p = edges(g)
        table = boundary_counts(n, p)
        certified, attempts = 0, 0
        for tree in tree_list(n, p):
            _, forms, _, _, _ = polynomial(n, p, tree, [0] * n)
            # The permanent of any full-degree minor is independent of the boundary.
            for subset in combinations(range(len(p) - n + 1), n - 1):
                matrix = [[row[j] for j in subset] for _, row in forms]
                if permanent(matrix):
                    certified += 1
                attempts += 1
        tree = next(tree_list(n, p))
        # Independent direct sign enumeration for all Walsh moments of two small examples.
        if name in ("K4", "W4"):
            by_boundary = {}
            chords = [i for i in range(len(p)) if i not in tree]
            for f in product((-1, 1), repeat=len(p)):
                beta = tuple(v % 3 for v in divergence(n, p, f))
                mask = sum(1 << j for j, e in enumerate(chords) if f[e] == -1)
                by_boundary.setdefault(beta, []).append(mask)
        for beta in product(range(3), repeat=n - 1):
            full = (*beta, (-sum(beta)) % 3)
            _, forms, q, u, total = polynomial(n, p, tree, full)
            assert total == int(table[beta]) and (total > 0) == bool(np.any(q))
            if name in ("K4", "W4"):
                vals = by_boundary.get(full, [])
                for i, coef in enumerate(q):
                    moment = sum((-1) ** ((i & mask).bit_count()) for mask in vals)
                    assert (moment * pow(len(q), -1, 3)) % 3 == coef
            for subset in combinations(range(len(p) - n + 1), n - 1):
                assert u[sum(1 << i for i in subset)] == permanent(
                    [[row[j] for j in subset] for _, row in forms]
                )
        assert not certified or table.min() > 0
        print("top-degree permanents, nonzero/all", name, certified, attempts, flush=True)
    g = nx.complete_graph(7)
    p = edges(g)
    index = {e: i for i, e in enumerate(p)}
    summary = Counter()
    for tree in nx.nonisomorphic_trees(7):
        ids = sorted(index[tuple(sorted(e))] for e in tree.edges())
        _, _, q, _, total = polynomial(7, p, ids, [0] * 7)
        degree = min(int(mask).bit_count() for mask in np.flatnonzero(q))
        summary[degree] += 1
        assert total == 3648 and q[0] == 0
    print("K7, minimum nonzero degree across all tree shapes", dict(summary), flush=True)
    tree = [i for i, (a, b) in enumerate(p) if a == 0]
    c, _, q, _, _ = polynomial(7, p, tree, [0] * 7)
    target = {(1, 2), (1, 4), (1, 5), (2, 3)}
    assert q[sum(1 << i for i, e in enumerate(c) if p[e] in target)] == 2


def terminal_block(k):
    inside = tuple(range(k, k + 3))
    return [(a, b) for a in range(k) for b in inside] + [
        (inside[j], inside[(j + 1) % 3]) for j in range(3)
    ]


def terminal_counts(k):
    p = terminal_block(k)
    table = boundary_counts(k + 3, p)
    out = Counter()
    for beta in product(range(3), repeat=k - 1):
        target = (*beta, (-sum(beta)) % 3, 0, 0)
        n = int(table[target])
        out[n % 3] += 1
        if any(target):
            assert n % 3 == 0
        else:
            fixed = 2 * sum(comb(k, j) for j in range(k + 1) if (2 * j - k) % 3 == 0)
            assert n % 3 == fixed % 3
    return out


def degree_barrier():
    for k in (3, 4, 5, 6, 7, 8, 10):
        counts = terminal_counts(k)
        assert (len(counts) == 1 and 0 in counts) == (k % 3 == 1)
        print("terminal residues, k and conditional table mod 3", k, dict(counts), flush=True)
    for k, t in ((7, 1), (7, 3), (7, 10), (10, 4)):
        p = edges(nx.complete_graph(k))
        for i in range(t):
            p.extend((a if a < k else a + 3 * i, b if b < k else b + 3 * i) for a, b in terminal_block(k))
        z = k + 3 * t
        p.extend((z, i) for i in range(5))
        assert nx.node_connectivity(nx.Graph([e for e in p if z not in e])) >= k
        assert mincut(z + 1, p) == 5
        for minority in range(5):
            sol = solve_checked(LocalOrientations(z + 1, p), [0] * (z + 1), port_pins(p, z, minority))
            assert sol is not None and not any(d % 3 for d in divergence(z + 1, p, sol))
        print("positive rooted witness, ports/blocks/order/lower bound on Fourier degree", k, t, z + 1, t)


if __name__ == "__main__":
    polynomial_tests()
    degree_barrier()
