"""Cut arithmetic after root deletion, tame augmentations and partition-density tests."""

from collections import Counter
from itertools import combinations
import random

import networkx as nx
import numpy as np

from flow_lab import boundary_counts, divergence, edges, mincut
from round1_ports import LocalOrientations, port_pins, solve_checked
from round1_repair import nontrivial_five_cut
from round2_paths import adversaries, best_path, pocket
from round2_transfers import TransferSearch


def absolute_tau(degree, beta):
    return np.where(degree % 2, np.where(beta % 3 == 0, 3, 1), np.where(beta % 3 == 0, 0, 2))


def deleted_cuts(n, p, z):
    vertices = [v for v in range(n) if v != z]
    label = {v: i for i, v in enumerate(vertices)}
    bits = np.arange(1 << (n - 1), dtype=np.int32)
    size = np.bitwise_count(bits)
    star = [a if b == z else b for a, b in p if z in (a, b)]
    k = sum((bits >> label[v]) & 1 for v in star)
    cut = sum(((bits >> label[a]) ^ (bits >> label[b])) & 1 for a, b in p if z not in (a, b))
    assert mincut(n, p) == 5 and nontrivial_five_cut(n, p, z) is None
    eligible = (size >= 2) & (size <= n - 3) & (k <= 2)
    failures = []
    for i, v in enumerate(star):
        minority = (bits >> label[v]) & 1
        beta = k - 2 * minority
        fails = eligible & (cut < 4 + absolute_tau(cut, beta))
        type_a = eligible & (k == 2) & (cut == 4) & (minority == 0)
        type_b = eligible & (k == 2) & (cut == 5) & (minority == 1)
        assert np.array_equal(fails, type_a | type_b)
        failures.append((int(type_a.sum()), int(type_b.sum())))
    return failures


def fixed_edge_counterexample():
    # root 0 receives from 1 and 2 on all four parallel spokes, sends to 3.
    p = [(1, 0)] * 2 + [(2, 0)] * 2 + [(0, 3), (1, 2)] + [(3, 1)] * 2 + [(3, 2)] * 2
    n, z, drop, minority = 4, 0, 5, 4
    pins = port_pins(p, z, minority)
    assert mincut(n, p) == 5 and nontrivial_five_cut(n, p, z) is None
    assert all(v == 1 for v in pins.values())
    p0 = p[:drop] + p[drop + 1 :]
    assert all(r % 3 == 0 for r in divergence(n, p0, [1] * len(p0)))
    assert best_path(n, p, z, minority, drop)[1] is None
    free = [e for e in p0 if z not in e]
    selected = TransferSearch(n, free).shortest(1, 2)
    assert len(selected) == 3
    assert solve_checked(LocalOrientations(n, p), [0] * n, pins) is not None
    other = best_path(n, p, z, minority, 6)
    assert len(other[1]) == 1
    return p


def augmentation_tests():
    rng = random.Random(3552608)
    counts = Counter()
    for group, n, p, z in adversaries():
        if n > 45 or mincut(n, p) != 5 or nontrivial_five_cut(n, p, z) is not None:
            continue
        degree = [sum(v in edge for edge in p) for v in range(n)]
        degree5 = [i for i in range(n) if i != z and degree[i] == 5]
        for k in range(4):
            if len(degree5) < k:
                continue
            bad = rng.sample(degree5, k)
            # Sample a prescribed star and residual boundary with exactly k (5,0) nonroot vertices.
            for _ in range(100):
                beta = [rng.randrange(3) if v not in degree5 else rng.choice((1, 2)) for v in range(n)]
                for v in bad:
                    beta[v] = 0
                pins = {i: rng.choice((-1, 1)) for i, e in enumerate(p) if z in e}
                beta[z] = divergence(n, p, [pins.get(i, 0) for i in range(len(p))])[z] % 3
                if sum(beta) % 3 == 0:
                    break
            else:
                continue
            witness = solve_checked(LocalOrientations(n, p), beta, pins)
            assert witness is not None
            augmented = p.copy()
            fixed = pins.copy()
            target = beta.copy()
            # For three faults leave one distinguished vertex exposed. Both new spokes miss it.
            ends = bad[:2]
            for j, v in enumerate(ends):
                if k == 1:
                    s = 1 if (target[z] + 1) % 3 else -1
                elif k == 2:
                    s = next(
                        a[j] for a in ((1, 1), (1, -1), (-1, 1), (-1, -1)) if (beta[z] + sum(a)) % 3 == 0
                    )
                else:
                    s = (1, -1)[j]
                fixed[len(augmented)] = s
                augmented.append((z, v))
                target[z] = (target[z] + s) % 3
                target[v] = (target[v] - s) % 3
            deg = [sum(v in e for e in augmented) for v in range(n)]
            if k <= 2:
                assert deg[z] <= 4 + absolute_tau(deg[z], target[z])
            for v in range(n):
                if v != z and not (k == 3 and v == bad[-1]):
                    assert deg[v] >= 4 + absolute_tau(deg[v], target[v])
            extended = solve_checked(LocalOrientations(n, augmented), target, fixed)
            assert extended is not None
            old = extended[: len(p)]
            assert all((t - b) % 3 == 0 for t, b in zip(divergence(n, p, old), beta))
            counts[k] += 1
    print("tame augmentation cases by original singleton faults", dict(counts), flush=True)


def density_tests():
    rng = random.Random(3552609)
    checked, entries = 0, 0
    for n in (8, 10, 12):
        for want in range(min(8, n - 1) + 1):
            p = edges(nx.random_regular_graph(5, n, seed=rng.randrange(1 << 30)))
            if mincut(n, p) < 5 or nontrivial_five_cut(n, p) is not None:
                continue
            nonroot = list(range(1, n))
            rng.shuffle(nonroot)
            raise_degree = nonroot[want:]
            if len(raise_degree) == 1:
                continue
            for a, b in zip(raise_degree[::2], raise_degree[1::2]):
                p.append((a, b))
            if len(raise_degree) % 2:
                p.append((raise_degree[-1], raise_degree[0]))
            b = sum(sum(v in e for e in p) == 5 for v in nonroot)
            assert b == want
            h = [(u - 1, v - 1) for u, v in p if 0 not in (u, v)]
            table = boundary_counts(n - 1, h)
            assert table.min() > 0
            checked += 1
            entries += table.size
    print(
        "at most eight nonroot vertices of degree five, graphs/all residual boundary entries",
        checked,
        entries,
        flush=True,
    )

    checked = 0
    for t in (3, 4, 5):
        p = [(a, b) for a in range(3) for b in range(3, t + 3)] + [(0, 1)]
        for s in range(2, t + 4):
            for vertices in combinations(range(t + 3), s):
                label = {v: i for i, v in enumerate(vertices)}
                h = [(label[a], label[b]) for a, b in p if a in label and b in label]
                assert boundary_counts(s, h).min() == 0
                if s >= 5:
                    assert len(h) <= 3 * s - 7
                checked += 1
    print("reduced induced subgraphs checked on three critical bipartite cores", checked, flush=True)


def check_lift(p, z):
    # In the mixed pocket the two spokes into the C7-square form an admissible opposite pair.
    s = set(range(7))
    cut = lambda pairs: sum((a in s) != (b in s) for a, b in pairs)
    assert cut(p) == 7
    lifted = [e for e in p if e not in ((z, 0), (z, 1))] + [(0, 1)]
    assert cut(lifted) == 5
    pins = port_pins(p, z, 0)
    assert pins[p.index((z, 0))] != pins[p.index((z, 1))]


if __name__ == "__main__":
    p = fixed_edge_counterexample()
    assert deleted_cuts(4, p, 0) == [(0, 0)] * 5
    for kind in ("double four-cut", "mixed five-cut"):
        n, p, z = pocket(kind)
        counts = deleted_cuts(n, p, z)
        assert any(b for a, b in counts) if kind == "mixed five-cut" else all(a for a, b in counts)
        if kind == "mixed five-cut":
            check_lift(p, z)
        print(kind, "nontrivial residual LTWZ violations by minority label", counts, flush=True)
        for i in range(5):
            assert solve_checked(LocalOrientations(n, p), [0] * n, port_pins(p, z, i)) is not None
    augmentation_tests()
    density_tests()
