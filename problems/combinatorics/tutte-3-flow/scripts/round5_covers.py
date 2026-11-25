"""Exact two-sheet lifts of a root-star obstruction and cyclic bipartite 5-factors."""

from collections import Counter
import argparse
import json
from itertools import combinations, product
from math import comb, gcd
import networkx as nx

from flow_lab import boundary_counts, divergence, mincut
from round1_ports import LocalOrientations, port_pins
from round1_repair import nontrivial_five_cut
from round3_reduced import strong_witness
from round4_lifts import cover


def half_edges():
    return [e for e in combinations(range(5), 2) if e != (0, 1)] + [(1, 2), (3, 4)]


def signings():
    pairs = half_edges()
    # The tree fixes all vertex switches up to a simultaneous switch.
    tree = {(1, 2), (2, 3), (3, 4), (0, 2)}
    fixed = {pairs.index(e): 0 for e in tree}
    fixed.update({9: 1, 10: 1})  # opposite voltages on the two parallel pairs
    free = [e for e in range(len(pairs)) if e not in fixed]
    for bits in product((0, 1), repeat=len(free)):
        volts = fixed | dict(zip(free, bits))
        yield cover(5, pairs, {i for i, b in volts.items() if b})


def cut_table(pairs):
    # Keep exact terminal membership and a truncated count on both shores.
    table = {}
    ports = (0, 5, 1, 6)
    for mask in range(1024):
        a = mask.bit_count()
        key = (sum(((mask >> x) & 1) << i for i, x in enumerate(ports)), min(a, 2), min(10 - a, 2))
        bound = sum(((mask >> x) ^ (mask >> y)) & 1 for x, y in pairs)
        table[key] = min(bound, table.get(key, 100))
    return table


def spectra(pairs, pinned, vertex=0):
    # Return an exact 64-bit orientation mask on the six exposed strands.
    endpoints = (0, 5, 0, 5, 1, 6)
    zstar = [e for e, edge in enumerate(pairs) if vertex in edge]
    external = [j for j, x in enumerate(endpoints) if x == vertex]
    assert len(zstar) + len(external) == 5
    remaining = [edge for e, edge in enumerate(pairs) if not pinned or e not in zstar]
    arrays = boundary_counts(10, remaining)
    result = []
    for minority in (range(5) if pinned else [None]):
        mask = 0
        for state in range(64):
            signs = [1 if (state >> j) & 1 else -1 for j in range(6)]
            if pinned and any(
                signs[t] != (1 if j + len(zstar) == minority else -1)
                for j, t in enumerate(external)
            ):
                continue
            rhs = [0] * 10
            for x, val in zip(endpoints, signs):
                rhs[x] -= val
            if pinned:
                for j, edge in enumerate(zstar):
                    a, b = pairs[edge]
                    val = (1 if j == minority else -1) * (1 if a == vertex else -1)
                    rhs[a] -= val
                    rhs[b] += val
            if sum(rhs) % 3 == 0 and arrays[tuple(x % 3 for x in rhs[:-1])] > 0:
                mask |= 1 << state
        result.append(mask)
    return result


def crossing_permutation(a, b):
    # Interface uses (0,0),(0,1),(1,0); fix voltage zero on its first edge.
    return (0, 1, 4 + a, 5 - a, 2 + b, 3 - b)


def cut_values(left, right, perm):
    # The table indices of the six strands repeat the two copies of vertex 0.
    terminal = (0, 1, 0, 1, 2, 3)
    cost = [
        [
            sum(((x >> terminal[j]) ^ (y >> terminal[perm[j]])) & 1 for j in range(6))
            for y in range(16)
        ]
        for x in range(16)
    ]
    small = large = 100
    for (x, a, b), cx in left.items():
        for (y, c, d), cy in right.items():
            if not (a + c and b + d):
                continue
            val = cx + cy + cost[x][y]
            if min(a + c, b + d) == 1:
                small = min(small, val)
            else:
                large = min(large, val)
    return small, large


def voltage_search():
    h = half_edges()
    base = h + [(a + 5, b + 5) for a, b in h] + [(0, 5), (0, 6), (1, 5)]
    solver = LocalOrientations(10, base)
    observed = tuple(solver.solve([0] * 10, port_pins(base, 0, i)) is not None for i in range(5))
    assert observed == (True, True, True, False, False) and mincut(10, base) == 3
    halves = list(signings())
    witnesses = [strong_witness(10, p) for p in halves]
    rights = [spectra(p, False)[0] for p in halves]
    pinned = [[spectra(p, True, v) for v in range(5)] for p in halves]
    # Internals related by local isomorphism often share the same cut table.
    tables = [tuple(sorted(cut_table(p).items())) for p in halves]
    distinct = sorted(set(tables))
    idx = [distinct.index(t) for t in tables]
    cuts = Counter()
    survivors = failures = checked = 0
    strong_halves = sum(int(boundary_counts(10, p).min() > 0) for p in halves)
    for a, b in product((0, 1), repeat=2):
        perm = crossing_permutation(a, b)
        exact = {
            (i, j): cut_values(dict(t), dict(u), perm)
            for i, t in enumerate(distinct)
            for j, u in enumerate(distinct)
        }

        def transport(right):
            states = 0
            for s in range(64):
                target = sum((1 - ((s >> j) & 1)) << k for j, k in enumerate(perm))
                states |= ((right >> target) & 1) << s
            return states

        translated = {
            m: transport(m) for m in set(rights) | {m for h in pinned for v in h for m in v}
        }
        for i, left_by_root in enumerate(pinned):
            for j, other in enumerate(rights):
                right = translated[other]
                small, large = exact[idx[i], idx[j]]
                cuts[min(small, large), large] += 1
                if small < 5 or large < 6:
                    continue
                survivors += witnesses[j] is None
                for v in range(5):
                    failures += 2 * sum(not (state & right) for state in left_by_root[v])
                    failures += 2 * sum(
                        not (rights[i] & translated[state]) for state in pinned[j][v]
                    )
                    checked += 20  # both halves, both sheets, five minorities
                # Direct whole-graph solver, independent of the tensor contraction.
                if i in (0, 7, 31) and j in (0, 17, 31):
                    ports = (0, 5, 0, 5, 1, 6)
                    full = (
                        halves[i]
                        + [(u + 10, v + 10) for u, v in halves[j]]
                        + [(ports[k], 10 + ports[perm[k]]) for k in range(6)]
                    )
                    assert len(set(tuple(sorted(e)) for e in full)) == 50
                    assert mincut(20, full) == 5 and nontrivial_five_cut(20, full) is None
                    check = LocalOrientations(20, full)
                    for v in (0, 1, 4, 10, 11, 14):
                        for k in range(5):
                            assert check.solve([0] * 20, port_pins(full, v, k)) is not None
    print("cover switching classes, (minimum cut, minimum nonsingleton cut)", sorted(cuts.items()))
    print(
        "whole strong halves",
        strong_halves,
        "half witness orders",
        Counter(len(w) if w else 0 for w in witnesses),
    )
    print(
        "essential completions lacking an opposite-half witness, stars, failures",
        survivors,
        checked,
        failures,
    )
    assert cuts == {(5, 6): 4096} and not survivors and not failures and checked == 409600
    assert strong_halves == 32
    return survivors


def cyclic_panel():
    # Exhaust the shift sets up to rotation of shifts. Choose a minimum-square
    # representative at each order, then test its rooted free core for a strong witness.
    for r in range(9, 19):

        def score(shifts):
            counts = Counter((s - t) % r for s in shifts for t in shifts if s != t)
            return sum(comb(k, 2) for k in counts.values())

        sets = [(0,) + s for s in combinations(range(1, r), 4)]
        shifts = min(sets, key=lambda s: (score(s), s))
        p = [(i, r + (i + s) % r) for i in range(r) for s in shifts]
        assert mincut(2 * r, p) == 5 and nontrivial_five_cut(2 * r, p) is None
        for k in range(5):
            witness = [1 if j % 5 == k else -1 for j in range(len(p))]
            assert all(x % 3 == 0 for x in divergence(2 * r, p, witness))
        w = splitting_certificate(2 * r, p)
        assert w is not None
        print(
            "cyclic",
            2 * r,
            shifts,
            "squares",
            r * score(shifts) // 2,
            "reduction moves",
            dict(Counter(step[0] for step in w)),
            flush=True,
        )


def affine_classes(r):
    seen = set()
    units = [u for u in range(1, r) if gcd(u, r) == 1]
    for tail in combinations(range(1, r), 4):
        s = (0,) + tail
        if s in seen:
            continue
        orbit = {tuple(sorted((u * (x - c)) % r for x in s)) for u in units for c in s}
        seen.update(orbit)
        yield s, len(orbit)
    assert len(seen) == comb(r - 1, 4)


def all_cyclic(emit=False):
    for r in range(9, 19):
        size = orbits = success = disconnected = 0
        for s, k in affine_classes(r):
            size += k
            if gcd(r, *s) > 1:
                disconnected += 1
                continue
            orbits += 1
            p = [(i, r + (i + t) % r) for i in range(r) for t in s]
            cert = splitting_certificate(2 * r, p)
            if cert is None:
                print("unresolved whole-core certificate", r, s, flush=True)
            else:
                success += 1
                if emit:
                    print(json.dumps({"r": r, "shifts": s, "moves": cert}), flush=True)
        print("all cyclic", 2 * r, size, disconnected, orbits, success, flush=True)
        assert size == comb(r - 1, 4) and success == orbits


def splitting_certificate(n, p):
    """Search for a positive certificate for the *whole* core. Replay each operation."""
    from random import Random

    def merge(g, u, v):
        for w in list(g[v]):
            if w != u:
                g.add_edges_from([(u, w)] * g.number_of_edges(v, w))
        g.remove_node(v)

    def split(g, v, a, b):
        g.remove_edge(v, a)
        g.remove_edge(v, b)
        g.add_edge(a, b)

    base = nx.MultiGraph(p)
    base.remove_node(0)
    for attempt in range(96):
        rng = Random(attempt)
        g = base.copy()
        trace = []
        while len(g) > 1:
            if len(g) <= 11:
                vs = list(g)
                sub = [(vs.index(a), vs.index(b)) for a, b in g.edges()]
                if boundary_counts(len(g), sub).min() > 0:
                    break
            doubles = [(u, v) for u in g for v in g[u] if u < v and g.number_of_edges(u, v) >= 2]
            if doubles:
                u, v = rng.choice(doubles)
                trace.append(("contract", u, v))
                merge(g, u, v)
                continue
            small = [v for v, d in g.degree() if d == 2]
            if small:
                v = rng.choice(small)
                trace.append(("delete", v))
                g.remove_node(v)
                continue
            if any(d < 2 for v, d in g.degree()):
                break
            moves = []
            for v, d in g.degree():
                if d < 4:
                    continue
                for a, b in combinations(g[v], 2):
                    common = len(set(g[a]) & set(g[b])) - 1
                    score = (int(g.has_edge(a, b)), common + (d == 4) * rng.randrange(2))
                    if score != (0, 0):
                        moves.append((score, rng.random(), v, a, b))
            if not moves:
                break
            _, _, v, a, b = max(moves)
            trace.append(("split", v, a, b))
            split(g, v, a, b)
        if len(g) > 11:
            continue
        vs = list(g)
        sub = [(vs.index(a), vs.index(b)) for a, b in g.edges()]
        if boundary_counts(len(g), sub).min() == 0:
            continue
        verify_moves(n, p, trace)
        return trace
    return None


def verify_moves(n, p, trace):
    """Replay a certificate on a multiset of edges, independently of the search graph."""
    vertices = set(range(1, n))

    def edge(a, b):
        return tuple(sorted((a, b)))

    counts = Counter(edge(a, b) for a, b in p if a in vertices and b in vertices)
    for kind, *args in trace:
        if kind == "split":
            v, a, b = args
            assert len({a, b, v}) == 3 and counts[edge(v, a)] and counts[edge(v, b)]
            counts[edge(v, a)] -= 1
            counts[edge(v, b)] -= 1
            counts[edge(a, b)] += 1
        elif kind == "contract":
            u, v = args
            assert counts[edge(u, v)] >= 2
            mapped = Counter()
            for (a, b), multiplicity in counts.items():
                a = u if a == v else a
                b = u if b == v else b
                if a != b:
                    mapped[edge(a, b)] += multiplicity
            counts = mapped
            vertices.remove(v)
        elif kind == "delete":
            (v,) = args
            assert sum(value for key, value in counts.items() if v in key) >= 2
            counts = Counter({key: value for key, value in counts.items() if v not in key})
            vertices.remove(v)
        else:
            raise ValueError(kind)
    labels = {v: i for i, v in enumerate(sorted(vertices))}
    final = [(labels[a], labels[b]) for (a, b), k in counts.items() for _ in range(k)]
    assert len(labels) <= 11 and boundary_counts(len(labels), final).min() > 0
    return len(labels)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--emit-moves", action="store_true", help="also print the 262 reproducible cyclic proofs"
    )
    args = parser.parse_args()
    voltage_search()
    cyclic_panel()
    all_cyclic(args.emit_moves)
