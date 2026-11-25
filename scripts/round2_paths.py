"""Change the deleted edge or partial orientation via path deletion. Adversarial rooted search."""

from collections import Counter, defaultdict
from itertools import combinations, product
import json
from pathlib import Path
import random

import networkx as nx

from flow_lab import divergence, edges, flower, mincut
from round1_ports import LocalOrientations, cubic_derivative, port_pins, solve_checked
from round1_repair import join_lobes, nontrivial_five_cut


def path_candidates(p, z, drop):
    arc_ids = defaultdict(list)
    g = nx.Graph()
    x, y = p[drop]
    g.add_nodes_from((x, y))
    for i, (a, b) in enumerate(p):
        if i != drop and z not in (a, b):
            g.add_edge(a, b)
            arc_ids[frozenset((a, b))].append(i)
    if not nx.has_path(g, x, y):
        return
    for vertices in nx.shortest_simple_paths(g, x, y):
        consecutive = list(zip(vertices, vertices[1:]))
        for ids in product(*(arc_ids[frozenset(e)] for e in consecutive)):
            yield consecutive, ids


def try_path(n, p, z, pins, drop, steps, ids):
    # Orient G-P, substitute the directed path for the surviving distinguished edge.
    keep = [i for i in range(len(p)) if i not in ids]
    assigned = {j: pins[i] for j, i in enumerate(keep) if i in pins}
    signs = solve_checked(LocalOrientations(n, [p[i] for i in keep]), [0] * n, assigned)
    if signs is None:
        return None
    old = {i: s for i, s in zip(keep, signs)}
    e_sign = old[drop]
    old[drop] = 0
    for step, i in zip(steps, ids):
        old[i] = e_sign if tuple(p[i]) == step else -e_sign
    assert all(d % 3 == 0 for d in divergence(n, p, [old[i] for i in range(len(p))]))
    assert all(old[i] == s for i, s in pins.items()) and all(z not in p[i] for i in ids)
    full = [old[i] for i in range(len(p))]
    full[drop] = -e_sign
    for i in ids:
        full[i] *= -1
    assert all(s in (-1, 1) for s in full) and all(d % 3 == 0 for d in divergence(n, p, full))
    return [i for i in range(len(p)) if old[i] < 0]


def best_path(n, p, z, minority, drop, limit=None):
    pins = port_pins(p, z, minority)
    lower = None
    for attempt, (steps, ids) in enumerate(path_candidates(p, z, drop), 1):
        if lower is None:
            lower = len(ids)
        witness = try_path(n, p, z, pins, drop, steps, ids)
        if witness is not None:
            return lower, list(ids), witness, attempt
        if limit is not None and attempt >= limit:
            break
    return lower, None, None, None


def old_panel():
    rows = json.loads(Path(__file__).with_name("round2_witnesses.json").read_text())
    hist = Counter()
    for row in rows:
        n, p, z, minority, drop = (row[k] for k in ("n", "edges", "root", "minority", "missing"))
        lower, ids, rev, trials = best_path(n, p, z, minority, drop)
        assert ids is not None
        hist[(lower, len(ids))] += 1
        print(
            "reoriented",
            row["family"],
            row["instance"],
            drop,
            "distance/path",
            lower,
            len(ids),
            "trials",
            trials,
            "path edges",
            ids,
            flush=True,
        )
    print("fixed edge, free partial orientation", dict(sorted(hist.items())), flush=True)


def square_cycle(n):
    return [(a, (a + s) % n) for a in range(n) for s in (1, 2)]


def pocket(kind):
    if kind == "double four-cut":
        n, z = 22, 21
        p = [(u + j, v + j) for j in (0, 6) for u, v in combinations(range(6), 2) if (u + 3) % 6 != v]
        p += [(12 + u, 12 + v) for u, v in square_cycle(9)]
        p += [(z, v) for v in (0, 1, 6, 7, 12)]
        p += [(i + 2, 13 + i) for i in range(4)] + [(i + 8, 17 + i) for i in range(4)]
        return n, p, z
    n, z = 16, 15
    p = square_cycle(7) + [(7 + u, 7 + v) for u, v in square_cycle(8)]
    p += [(z, v) for v in (0, 1, 7, 8, 9)] + [(2 + i, 10 + i) for i in range(5)]
    return n, p, z


def adversaries():
    rng = random.Random(3552607)
    for kind in ("double four-cut", "mixed five-cut"):
        yield (kind, *pocket(kind))
    for k in (1, 3, 5, 7):
        n, arcs, _ = join_lobes(k)
        base = arcs + [(6, 15)]
        yield "seven-cut chain", n, base, 24
        for j in range(3):
            # Keep a bottleneck in the chain but perturb ports on its six wires.
            p = base.copy()
            cap_edges = [i for i, (a, b) in enumerate(p) if a < 6 and b >= 18]
            dest = [p[i][1] for i in cap_edges]
            rng.shuffle(dest)
            for i, b in zip(cap_edges, dest):
                p[i] = (p[i][0], b)
            if j == 1:
                p += [tuple(rng.sample([v for v in range(n) if v != 24], 2)) for _ in range(n // 5)]
            yield "perturbed seven-cut chain", n, p, 24
    for t in (6, 7, 8, 10, 12, 16, 22):
        # K_{3,t} plus a hub edge is obstructed before we raise the cubic vertices to five.
        for j in range(3):
            leaves = list(range(3, 3 + t))
            rng.shuffle(leaves)
            p = [(i, v) for v in leaves for i in range(3)] + [(0, 1)]
            blocks = [leaves] if j == 0 else [leaves[:3], leaves[3:]]
            if j == 2 and t % 2 == 0:
                blocks = [leaves[i : i + 2] for i in range(0, t, 2)]
            for vs in blocks:
                p += list(zip(vs, vs[1:] + vs[:1]))
            yield "augmented critical bipartite core", 3 + t, p, leaves[0]
    for k in (5, 7, 9):
        for j in range(3):
            p = cubic_derivative(flower(k), 222 + j)
            if j == 0:
                # Rewire the added 2-factor through a different cyclic order on all vertices.
                order = rng.sample(range(4 * k), 4 * k)
                p = flower(k) + list(zip(order, order[1:] + order[:1]))
            else:
                p = [
                    (2 * u + i, 2 * v + ((i + w) % 2))
                    for u, v in p
                    for w in [rng.randrange(2)]
                    for i in range(2)
                ]
            yield "flower perturbation or cover", (4 if j == 0 else 8) * k, p, 0
    for j in range(9):
        p = cubic_derivative(edges(nx.petersen_graph()), 7731 + j)
        t = 3 + j % 3
        p = [
            (t * u + i, t * v + v2)
            for u, v in p
            for perm in [rng.sample(range(t), t)]
            for i, v2 in enumerate(perm)
        ]
        if j % 2:
            p += [tuple(rng.sample(range(1, 10 * t), 2)) for _ in range(t + 1)]
        yield "Petersen covers", 10 * t, p, 0


def chosen_edge_panel():
    stats = defaultdict(Counter)
    for family, n, p, z in adversaries():
        s = stats[family]
        if mincut(n, p) != 5 or nontrivial_five_cut(n, p, z) is not None:
            s["excluded"] += 1
            continue
        s["eligible"] += 1
        for minority in range(5):
            pins = port_pins(p, z, minority)
            assert solve_checked(LocalOrientations(n, p), [0] * n, pins) is not None
            s["root prescriptions"] += 1
            neighbors = {a if a != z else b for a, b in p if z in (a, b)}
            candidates = [i for i, e in enumerate(p) if z not in e]
            # Prefer an edge among neighbors, then an edge at a high-degree vertex.
            degree = [sum(v in e for e in p) for v in range(n)]
            candidates.sort(key=lambda i: (-len(set(p[i]) & neighbors), -max(degree[v] for v in p[i]), i))
            for drop in candidates:
                _, ids, _, _ = best_path(n, p, z, minority, drop, limit=3)
                if ids is not None:
                    s["chosen-edge path"] += 1
                    s["longest found"] = max(len(ids), s["longest found"])
                    break
    for family, s in stats.items():
        print("new adversaries", family, dict(s), flush=True)


if __name__ == "__main__":
    old_panel()
    chosen_edge_panel()
