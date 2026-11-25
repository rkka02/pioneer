"""Transfer-set invariance, local pair/triple splittings, irreducibility and high-girth tests."""

from collections import Counter
from itertools import product
import json
from pathlib import Path

import networkx as nx

from flow_lab import divergence, edges, mincut
from round1_repair import nontrivial_five_cut
from round1_ports import port_pins
from round2_transfers import TransferSearch, shortest_with_one_branch


def subset_div(n, arcs, mask):
    return tuple(d % 3 for d in divergence(n, arcs, [(mask >> i) & 1 for i in range(len(arcs))]))


def changes_and_atoms():
    checks = 0
    for n, p in [
        (4, [(0, 1), (0, 1), (2, 0), (1, 2), (1, 3), (2, 3), (3, 0)]),
        (4, edges(nx.complete_graph(4))),
        (3, [(0, 0), (0, 1), (1, 2), (2, 0)]),
    ]:
        for t in range(1 << len(p)):
            rev = [edge[::-1] if t >> i & 1 else edge for i, edge in enumerate(p)]
            shift = subset_div(n, p, t)
            old = [subset_div(n, p, m) for m in range(1 << len(p))]
            hist = Counter()
            for m in range(1 << len(p)):
                new = subset_div(n, rev, m)
                assert new == tuple((a - b) % 3 for a, b in zip(old[m ^ t], shift))
                hist[new] += 1
                checks += 1
            if not any(shift):
                assert hist == Counter(old)
    print("exact symmetric-difference transports", checks, flush=True)

    # For each contracted irreducible component, check the criterion for *both* signs.
    n, p = 4, [(0, 1), (0, 1), (1, 2), (1, 3), (2, 3), (2, 3), (3, 0)]
    total = 0
    for direction in range(1 << len(p)):
        arcs = [e[::-1] if direction >> i & 1 else e for i, e in enumerate(p)]
        x, y = 0, 2
        divs = [subset_div(n, arcs, m) for m in range(1 << len(p))]
        projected = [((a[x] + a[y]) % 3, a[1], a[3]) for a in divs]
        valid = [m for m, d in enumerate(divs) if d[x] and projected[m] == (0, 0, 0)]
        optimum = min(map(int.bit_count, valid), default=None)
        witness = TransferSearch(n, arcs).shortest(x, y)
        assert (None if witness is None else len(witness)) == optimum
        one_branch = []
        for m in valid:
            d = divergence(n, arcs, [(m >> i) & 1 for i in range(len(arcs))])
            if sum(bool(d[v]) for v in range(n) if v not in (x, y)) == 1:
                one_branch.append(m.bit_count())
        constrained = shortest_with_one_branch(n, arcs, x, y, optimum or 0)
        assert (None if constrained is None else len(constrained)) == min(one_branch, default=None)
        for m in valid:
            atom = all(z == 0 or z == m or z & m != z or any(projected[z]) for z in range(1 << len(p)))
            minimal = not any(s != m and s & m == s for s in valid)
            assert minimal == atom
            if minimal:
                active = set(v for i, e in enumerate(arcs) if m >> i & 1 for v in e)
                assert m.bit_count() <= 2 * len(active) - 3
            total += 1
    print("two-sign contracted-subset criterion, transfers checked", total, flush=True)

    # Equality in the size bound for general supports. Split the source of a doubled path.
    for r in range(1, 7):
        x, y = 0, r + 1
        arcs = [(x, 1), (y, 1)] + [(i, i + 1) for i in range(1, r) for _ in range(2)] + [(y, r)]
        chosen = TransferSearch(r + 2, arcs).shortest(x, y)
        assert chosen == list(range(2 * r + 1))

    # Directed cycle reversals keep every directed cut count and reachability relation.
    for t in range(1 << len(p)):
        if any(divergence(n, p, [(t >> i) & 1 for i in range(len(p))])):
            continue
        old = nx.DiGraph(p)
        new = nx.DiGraph([e[::-1] if t >> i & 1 else e for i, e in enumerate(p)])
        assert all(nx.descendants(old, v) == nx.descendants(new, v) for v in range(n))


def local_components():
    data = json.loads(Path(__file__).with_name("round2_witnesses.json").read_text())
    for row in data:
        p = row["edges"]
        z, drop = row["root"], row["missing"]
        x, y = p[drop]
        used = set(row["transfer"])
        reversed_ids = set(row["partial_reversed"])
        arcs = {i: tuple(e[::-1] if i in reversed_ids else e) for i, e in enumerate(p) if i != drop}
        groups = nx.utils.UnionFind(arcs)
        for v in range(row["n"]):
            if v in (x, y, z):
                continue
            for selected in (True, False):
                outgoing = [i for i, (a, b) in arcs.items() if a == v and (i in used) == selected]
                incoming = [i for i, (a, b) in arcs.items() if b == v and (i in used) == selected]
                while outgoing and incoming:
                    groups.union(outgoing.pop(), incoming.pop())
                rest = outgoing + incoming
                assert len(rest) % 3 == 0
                for pos in range(0, len(rest), 3):
                    groups.union(*rest[pos : pos + 3])
        parts = groups.to_sets()
        assert sum(s == used for s in parts) == 1
        assert not any(z in p[i] for i in used)
        assert len(used) <= 2 * len(set(v for i in used for v in p[i])) - 3
    print("29 shortest supports recovered as single pair/triple components", flush=True)


def gf4_times(a, b):
    p = (a if b & 1 else 0) ^ ((a << 1) if b & 2 else 0)
    return p ^ 7 if p & 4 else p


def normalized(v):
    lead = next(x for x in v if x)
    inverse = next(y for y in (1, 2, 3) if gf4_times(lead, y) == 1)
    return tuple(gf4_times(x, inverse) for x in v)


def incidence(dim):
    points = sorted({normalized(v) for v in product(range(4), repeat=dim) if any(v)})
    if dim == 3:
        return 42, [
            (i, 21 + j)
            for i, u in enumerate(points)
            for j, v in enumerate(points)
            if gf4_times(u[0], v[0]) ^ gf4_times(u[1], v[1]) ^ gf4_times(u[2], v[2]) == 0
        ]
    lines = set()
    for i, u in enumerate(points):
        for v in points[i + 1 :]:
            form = (
                gf4_times(u[0], v[1])
                ^ gf4_times(u[1], v[0])
                ^ gf4_times(u[2], v[3])
                ^ gf4_times(u[3], v[2])
            )
            if form == 0:
                line = [
                    normalized(tuple(a ^ gf4_times(t, b) for a, b in zip(u, v))) for t in range(4)
                ] + [v]
                lines.add(tuple(sorted(line)))
    assert len(points) == len(lines) == 85
    return 170, [(points.index(v), 85 + j) for j, line in enumerate(sorted(lines)) for v in line]


def girth_path(n, p, z, minority):
    g = nx.Graph(p)
    left = {v for v, c in nx.bipartite.color(g).items() if c == 0}
    star = [e for e in p if z in e]
    a, b = star[minority]
    remainder = g.copy()
    remainder.remove_nodes_from([a, b])
    match = nx.bipartite.maximum_matching(remainder, top_nodes=left - {a, b})
    match[a], match[b] = b, a
    assert len(match) == n
    # Every nonmatching arc goes from the left end of a pair to the right end of another.
    compressed = nx.DiGraph()
    compressed.add_nodes_from(left)
    for a in left:
        for b in g[a]:
            if match[a] != b:
                compressed.add_edge(a, match[b], wire=(a, b))
    compressed.remove_node(z if z in left else match[z])
    assert all(compressed.out_degree(v) >= 3 for v in compressed)
    for component in nx.strongly_connected_components(compressed):
        if any(v not in component for u in component for v in compressed.successors(u)):
            continue
        core = compressed.subgraph(component).copy()
        for u, v in list(core.edges):
            core.remove_edge(u, v)
            if nx.has_path(core, u, v):
                path = nx.shortest_path(core, u, v)
                route = []
                for i, (a, b) in enumerate(zip(path, path[1:])):
                    if i:
                        route.append((match[a], a))
                    route.append((a, match[b]))
                edge = (u, match[v])
                is_matching = lambda a, b: match[a] == b
                full = [1 if (a in left) != is_matching(a, b) else -1 for a, b in p]
                assert all(t % 3 == 0 for t in divergence(n, p, full))
                assert all(z not in arc for arc in route)
                pins = port_pins(p, z, minority)
                if any(full[i] != s for i, s in pins.items()):
                    full = [-s for s in full]
                assert all(full[i] == s for i, s in pins.items())
                signs = full.copy()
                for i, arc in enumerate(p):
                    if frozenset(arc) == frozenset(edge):
                        signs[i] = 0
                    elif arc in route or arc[::-1] in route:
                        signs[i] *= -1
                assert all(t % 3 == 0 for t in divergence(n, p, signs))
                assert all(signs[i] == s for i, s in pins.items())
                return len(route)
            core.add_edge(u, v)
    raise AssertionError("dense sink SCC had no redundant arc")


def girth_tests():
    # Finite involutions on reduced-word balls used in the arbitrary-girth proof.
    for limit in (2, 3, 4, 5):
        words = [()]
        for length in range(limit):
            words.extend(
                w + (c,) for w in list(words) if len(w) == length for c in range(5) if not w or w[-1] != c
            )

        def step(w, c):
            if w and w[-1] == c:
                return w[:-1]
            return w + (c,) if len(w) < limit else w

        assert all(step(step(w, c), c) == w for w in words for c in range(5))
        for word in words[1:]:
            w = ()
            for c in word:
                w = step(w, c)
            assert w == word
    for g, (n, p) in zip(
        (4, 6, 8), [(10, edges(nx.complete_bipartite_graph(5, 5))), incidence(3), incidence(4)]
    ):
        graph = nx.Graph(p)
        assert nx.girth(graph) == g and set(dict(graph.degree()).values()) == {5}
        assert mincut(n, p) == 5 and nontrivial_five_cut(n, p) is None
        lengths = [girth_path(n, p, 0, i) for i in range(5)]
        assert min(lengths) >= g - 1
        print("girth barrier", n, g, "good-edge bypass lengths for five positions", lengths, flush=True)


if __name__ == "__main__":
    changes_and_atoms()
    local_components()
    girth_tests()
