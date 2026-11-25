"""Reconstruct Round 1's 29 incomparable pairs and prove minimum transfer sizes by integer search."""

import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import random

import networkx as nx
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp

from flow_lab import divergence, mincut
from round1_ports import LocalOrientations, fixtures, port_pins, solve_checked
from round1_repair import comparability, nontrivial_five_cut
from round2_paths import best_path


def partial_witnesses():
    rng = random.Random(3552605)
    counts = Counter()
    for group, n, p in fixtures():
        if group not in ("random simple", "irregular added edges", "flower", "Petersen cover"):
            continue
        counts[group] += 1
        if mincut(n, p) < 5 or nontrivial_five_cut(n, p) is not None:
            continue
        z = next(v for v in range(n) if sum(v in e for e in p) == 5)
        for drop in rng.sample([i for i, e in enumerate(p) if z not in e], 3):
            residual = p[:drop] + p[drop + 1 :]
            minority = rng.randrange(5)
            pins = port_pins(residual, z, minority)
            signs = solve_checked(LocalOrientations(n, residual), [0] * n, pins)
            assert signs is not None
            if not comparability(n, residual, signs, *p[drop], z):
                yield group, counts[group], n, p, z, minority, drop, signs


class TransferSearch:
    """Cost-bounded exact search. Resolve all remaining incident edges at a wrong-residue vertex."""

    def __init__(self, n, arcs):
        self.n, self.arcs = n, arcs
        self.incident = [[] for _ in range(n)]
        for i, (a, b) in enumerate(arcs):
            self.incident[a].append((i, 1))
            self.incident[b].append((i, -1))
        self.calls = 0

    def bounded(self, x, y, sign, budget):
        wanted = [0] * self.n
        wanted[x], wanted[y] = sign % 3, (-sign) % 3
        failed = set()

        def visit(available, remainder, slots):
            self.calls += 1
            wrong = [v for v, d in enumerate(remainder) if d]
            if not wrong:
                return ()
            if len(wrong) > 2 * slots:
                return None
            key = (available, tuple(remainder), slots)
            if key in failed:
                return None
            bound = 0
            pivot, priority = None, None
            for v in wrong:
                local = [(i, s) for i, s in self.incident[v] if available >> i & 1]
                if any(s % 3 == remainder[v] for i, s in local):
                    least = 1
                elif len(local) >= 2:
                    least = 2
                else:
                    return None
                bound += least
                rank = (len(local) - least, len(local), v)
                if priority is None or rank < priority:
                    pivot, priority = (v, local, least), rank
            if bound > 2 * slots:
                return None
            v, local, least = pivot
            rest = available ^ sum(1 << i for i, s in local)
            for k in range(least, min(slots, len(local)) + 1):
                for chosen in combinations(local, k):
                    if sum(s for i, s in chosen) % 3 != remainder[v]:
                        continue
                    demand = remainder.copy()
                    for i, _ in chosen:
                        a, b = self.arcs[i]
                        demand[a] = (demand[a] - 1) % 3
                        demand[b] = (demand[b] + 1) % 3
                    tail = visit(rest, demand, slots - k)
                    if tail is not None:
                        return tuple(i for i, s in chosen) + tail
            failed.add(key)
            return None

        return visit((1 << len(self.arcs)) - 1, wanted, budget)

    def shortest(self, x, y):
        underlying = nx.Graph()
        underlying.add_nodes_from(range(self.n))
        underlying.add_edges_from(self.arcs)
        if not nx.has_path(underlying, x, y):
            return None
        for budget in range(nx.shortest_path_length(underlying, x, y), len(self.arcs) + 1):
            for sign in (1, -1):
                witness = self.bounded(x, y, sign, budget)
                if witness is not None:
                    assert len(witness) == budget
                    return sorted(witness)
        return None


def directed_arcs(p, drop, signs, z):
    old = [i for i in range(len(p)) if i != drop]
    arcs, ids, reverse = [], [], []
    for i, sign in zip(old, signs, strict=True):
        if sign < 0:
            reverse.append(i)
        if z not in p[i]:
            arcs.append(p[i] if sign == 1 else p[i][::-1])
            ids.append(i)
    return arcs, ids, reverse


def verify_irreducible(n, arcs, selected, x, y):
    """Check every subset on the contracted graph; also count full orientations there."""
    p = [tuple(x if v == y else v for v in arcs[i]) for i in selected]
    zero_sets = []
    for mask in range(1 << len(p)):
        d = divergence(n, p, [(mask >> i) & 1 for i in range(len(p))])
        if all(t % 3 == 0 for t in d):
            zero_sets.append(mask)
    assert zero_sets == [0, (1 << len(p)) - 1]


def milp_minimum(n, arcs, x, y):
    """Independent cross-check. The last bit chooses the sign of the terminal demand."""
    m = len(arcs)
    incidence = np.zeros((n, m), dtype=int)
    for i, (a, b) in enumerate(arcs):
        incidence[a, i] += 1
        incidence[b, i] -= 1
    demand = np.zeros(n, dtype=int)
    demand[x], demand[y] = 1, -1
    matrix = np.column_stack((incidence, -3 * np.eye(n, dtype=int), -2 * demand))
    limit = (np.sum(np.abs(incidence), axis=1) + 1) // 3
    result = milp(
        np.r_[np.ones(m), np.zeros(n + 1)],
        integrality=np.ones(m + n + 1),
        bounds=Bounds(np.r_[np.zeros(m), -limit, 0], np.r_[np.ones(m), limit, 1]),
        constraints=LinearConstraint(matrix, -demand, -demand),
        options={"mip_rel_gap": 0.0},
    )
    assert result.success and result.mip_gap == 0
    values = np.rint(result.x).astype(int)
    assert np.array_equal(matrix @ values, -demand) and set(values[:m]) <= {0, 1}
    return int(values[:m].sum())


def shortest_with_one_branch(n, arcs, x, y, lower):
    """Exhaust the integer imbalances at the terminals and one ordinary branch vertex."""
    graph = nx.MultiDiGraph()
    graph.add_nodes_from(range(n), demand=0)
    for i, (a, b) in enumerate(arcs):
        graph.add_edge(a, b, key=i, weight=1, capacity=1)

    def possible(v):
        return range(-graph.in_degree(v), graph.out_degree(v) + 1)

    best = None
    for dx in possible(x):
        for dy in possible(y):
            branch = -(dx + dy)
            if dx % 3 == 0 or branch == 0 or branch % 3 != 0:
                continue
            graph.nodes[x]["demand"], graph.nodes[y]["demand"] = -dx, -dy
            for v in range(n):
                if v in (x, y) or branch not in possible(v):
                    continue
                graph.nodes[v]["demand"] = -branch
                try:
                    cost, flow = nx.network_simplex(graph)
                except nx.NetworkXUnfeasible:
                    continue
                finally:
                    graph.nodes[v]["demand"] = 0
                if best is None or cost < len(best):
                    best = [i for i, (a, b) in enumerate(arcs) if flow[a][b][i]]
                    assert len(best) == cost
                    div = divergence(n, arcs, [int(i in best) for i in range(len(arcs))])
                    assert div[x] == dx and div[y] == dy and div[v] == branch
                    assert all(t == 0 for u, t in enumerate(div) if u not in (x, y, v))
                    if cost == lower:
                        return best
    return best


def witness_panel(cross_check=False):
    panel = []
    for group, instance, n, p, z, minority, drop, signs in partial_witnesses():
        x, y = p[drop]
        arcs, ids, reversed_ids = directed_arcs(p, drop, signs, z)
        search = TransferSearch(n, arcs)
        selected = search.shortest(x, y)
        assert selected is not None
        if cross_check:
            assert milp_minimum(n, arcs, x, y) == len(selected)
        val = [int(i in selected) for i in range(len(arcs))]
        d = divergence(n, arcs, val)
        assert (
            d[x] % 3
            and (d[x] + d[y]) % 3 == 0
            and all(d[v] % 3 == 0 for v in range(n) if v not in (x, y))
        )
        branch = {v: d[v] for v in range(n) if v not in (x, y) and d[v]}
        single = shortest_with_one_branch(n, arcs, x, y, len(selected))
        lower, path, alternative, _ = best_path(n, p, z, minority, drop)
        assert path is not None and len(path) == lower
        verify_irreducible(n, arcs, selected, x, y)
        used = sorted(ids[i] for i in selected)
        f = [(-1 if i in reversed_ids else 1) * (-1 if i in used else 1) for i in range(len(p))]
        f[drop] = -1 if d[x] % 3 == 1 else 1
        assert all(t % 3 == 0 for t in divergence(n, p, f))
        assert all(f[i] == s for i, s in port_pins(p, z, minority).items())
        panel.append(
            dict(
                family=group,
                instance=instance,
                n=n,
                edges=p,
                root=z,
                minority=minority,
                missing=drop,
                partial_reversed=reversed_ids,
                transfer=used,
                terminal_divergences=[d[x], d[y]],
                internal_divergences=branch,
                shortest_one_branch=None if single is None else sorted(ids[i] for i in single),
                geodesic=path,
                geodesic_partial_reversed=alternative,
            )
        )
        print(group, instance, n, drop, len(used), [d[x], d[y]], branch, search.calls, flush=True)
    assert len(panel) == 29
    return panel


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--save", type=Path, help="write the exact reconstructed witnesses")
    parser.add_argument(
        "--milp", action="store_true", help="independently minimize both terminal signs with HiGHS"
    )
    args = parser.parse_args()
    panel = witness_panel(args.milp)
    encoded = "[\n" + ",\n".join(json.dumps(row, separators=(",", ":")) for row in panel) + "\n]\n"
    if args.save:
        args.save.write_text(encoded)
    else:
        reference = Path(__file__).with_name("round2_witnesses.json")
        assert json.loads(encoded) == json.loads(reference.read_text())
    print("minimum supports", dict(sorted(Counter(len(w["transfer"]) for w in panel).items())))
    print(
        "internal branch counts",
        dict(sorted(Counter(len(w["internal_divergences"]) for w in panel).items())),
    )
    branch_costs = Counter(
        (
            "impossible"
            if w["shortest_one_branch"] is None
            else len(w["shortest_one_branch"]) - len(w["transfer"])
        )
        for w in panel
    )
    print("one internal branch: excess cost above minimum, or impossible", dict(branch_costs))
