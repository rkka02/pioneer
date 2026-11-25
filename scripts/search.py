"""Boundary census, five-port transfer, algebraic checks and adversarial witness search."""
from collections import Counter
import itertools
import random

import networkx as nx
import numpy as np

from flow_lab import (boundary_counts, divergence, edges, flower, fourier, jlpt, lift, mincut,
                      orient, regular_census, splice)
from obstructions import seven_cut_graph


def delete_root(n, pairs, z):
    reindex = {v: i for i, v in enumerate(v for v in range(n) if v != z)}
    ports = [reindex[b if a == z else a] for a, b in pairs if z in (a, b)]
    inside = [(reindex[a], reindex[b]) for a, b in pairs if z not in (a, b)]
    return ports, boundary_counts(n-1, inside)


def profile(ports, counts):
    values = []
    for i in range(len(ports)):
        beta = [0]*(counts.ndim+1)
        for j, v in enumerate(ports):
            beta[v] += 1 if j == i else -1
        assert sum(beta) % 3 == 0
        values.append(int(counts[tuple(b % 3 for b in beta[:-1])]))
    return values


def census():
    summary = {}
    for n in (5, 6, 7):
        eligible = [edges(g) for g in nx.graph_atlas_g() if len(g) == n and mincut(n, edges(g)) >= 4]
        for pairs in eligible:
            assert boundary_counts(n, pairs).min() > 0
        summary[n] = len(eligible)
    print("all simple connected atlas graphs, lambda>=4", summary)
    for n in (6, 8, 10):
        all_graphs = list(regular_census(n))
        valid = [g for g in all_graphs if mincut(n, g) == 5]
        min_boundary, min_root, zeros, residues, partial = [], [], [], Counter(), []
        for i, pairs in enumerate(valid):
            counts = boundary_counts(n, pairs)
            min_boundary.append(int(counts.min()))
            zeros.append(int(counts.flat[0]))
            residues[zeros[-1] % 3] += 1
            for z in range(n):
                ports, c = delete_root(n, pairs, z)
                min_root.append(int(c.min()))
                p = profile(ports, c)
                assert sum(p)*2 == zeros[-1]
                if len(set(p)) > 1 and not partial:
                    partial.append((i, z, p))
            if zeros[-1] % 3 == 0 and residues[0] == 1:
                assert fourier(n, pairs)[0] == zeros[-1]
                print("first mod-3 cancellation", n, zeros[-1], pairs)
        print("regular census n, generated, lambda5, beta min, root min, zero range, residues, profile",
              n, len(all_graphs), len(valid), min(min_boundary), min(min_root),
              (min(zeros), max(zeros)), dict(residues), partial)


def named_cases():
    pet = edges(nx.petersen_graph())
    pet5 = [e for e in pet for _ in range(1 if e[1]-e[0] == 5 else 2)]
    # Split K5 vertex 0 into 0 and 5, then augment the other four degrees.
    split = ([(a, b) for a, b in itertools.combinations(range(1, 5), 2)] +
             [(0, 1), (0, 2), (5, 3), (5, 4)] + [(0, 5)]*3 + [(1, 2), (3, 4)])
    # The two split vertices form a four-cut. Add a second crossing matching.
    repaired = split + [(0, 3), (5, 1)]
    k6 = edges(nx.complete_graph(6))
    yield "K6", 6, k6
    yield "Petersen cubic", 10, pet
    yield "Petersen triple spokes", 10, pet + 2*[(i, i+5) for i in range(5)]
    yield "Petersen doubled 2-factor", 10, pet5
    yield "split K5", 6, split
    yield "augmented split K5", 6, repaired
    yield "K6 splice K6", 10, splice(6, k6, 0, 6, k6, 0, range(5))
    yield "K6 splice Petersen", 14, splice(6, k6, 0, 10, pet5, 0, range(5))
    yield "JLPT ring", 12, jlpt()
    yield "JLPT doubled links", 12, jlpt() + jlpt()[-6:]
    # Signed two-sheet lift of the five-regular Petersen multigraph.
    rng = random.Random(355)
    cover = []
    for a, b in pet5:
        twist = rng.randrange(2)
        cover.extend([(2*a, 2*b+twist), (2*a+1, 2*b+1-twist)])
    yield "Petersen two-lift", 20, cover
    for k in (5, 7):
        raw = flower(k)
        yield "flower J"+str(k), 4*k, raw
        matching = nx.max_weight_matching(nx.Graph(raw), maxcardinality=True)
        factor = {frozenset(e) for e in matching}
        assert len(factor)*2 == 4*k
        multi = raw + [e for e in raw if frozenset(e) not in factor]
        yield "flower doubled 2-factor J"+str(k), 4*k, multi
    yield "seven-cut maximum-bisection obstruction", 18, seven_cut_graph()
    pairs, n = k6, 6
    for _ in range(6):
        perm = rng.sample(range(5), 5)
        pairs = splice(n, pairs, n-1, 10, pet5, 0, perm)
        n += 8
    yield "six successive splices", n, pairs
    for n in (16, 24, 36):
        for seed in range(3):
            yield f"regular random {n}.{seed}", n, edges(nx.random_regular_graph(5, n, seed=seed))


def witnesses():
    rng = random.Random(355)
    for name, n, pairs in named_cases():
        conn = mincut(n, pairs)
        zero = [0]*n
        signs = orient(n, pairs, zero)
        if signs is not None:
            lift(n, pairs, signs)
        exact = None
        if n <= 12:
            counts = boundary_counts(n, pairs)
            exact = (int(counts.min()), int(counts.flat[0]), int(np.count_nonzero(counts == 0)))
            assert (signs is None) == (exact[1] == 0)
            if name == "JLPT ring":
                assert exact[2] == 2 and counts[(1,)*(n-1)] == counts[(2,)*(n-1)] == 0
                assert orient(n, pairs, [1]*n) is None
        if conn >= 4:
            assert signs is not None
        else:
            # The named connectivity-three controls are nonbipartite cubic graphs.
            assert set(dict(nx.Graph(pairs).degree()).values()) == {3}
            assert not nx.is_bipartite(nx.Graph(pairs)) and signs is None
        sampled = 0
        if conn >= 5:
            for _ in range(12):
                beta = [rng.randrange(3) for _ in range(n-1)]
                beta.append(-sum(beta) % 3)
                assert orient(n, pairs, beta) is not None
                sampled += 1
        print(name, "n,m,lambda", (n, len(pairs), conn), "zero", signs is not None,
              "exact(min,zero,missing)", exact, "sampled beta", sampled)


def transfer():
    # Use unequal port counts to make the permutation visible.
    g = list(regular_census(8))[0]
    ports, c = delete_root(8, g, 3)
    p = profile(ports, c)
    if len(set(p)) == 1:
        raise AssertionError("need an asymmetric port profile")
    tally = Counter()
    for perm in itertools.permutations(range(5)):
        tally[2*sum(a*p[j] for a, j in zip(p, perm))] += 1
    for perm in (tuple(range(5)), tuple(reversed(range(5)))):
        pairs = splice(8, g, 3, 8, g, 3, perm)
        # The independent full-graph DP has 3^13 entries.
        count = int(boundary_counts(14, pairs).flat[0])
        assert count == 2*sum(a*p[j] for a, j in zip(p, perm))
    print("all 120 gluings", p, sorted(tally.items()))
    # For beta != 0 reversal changes beta. Retain all signed cut assignments.
    rng = random.Random(355)
    for turn in range(24):
        beta = [rng.randrange(3) for _ in range(13)]
        beta.append(-sum(beta) % 3)
        total = 0
        for signs in itertools.product((-1, 1), repeat=5):
            left, right = beta[:7], beta[7:]
            for i, s in enumerate(signs):
                left[ports[i]] -= s
                right[ports[perm[i]]] += s
            if sum(left) % 3 == 0:
                assert sum(right) % 3 == 0
                total += int(c[tuple(b % 3 for b in left[:-1])])*int(c[tuple(b % 3 for b in right[:-1])])
        if turn == 0:
            glued = boundary_counts(14, pairs)
        assert total == int(glued[tuple(beta[:-1])])
    print("24 signed gluing checks, arbitrary valid boundaries")


def arithmetic():
    for d, b in itertools.product(range(4, 13), range(3)):
        reps = [x for x in range(-3, 4) if (d-x) % 2 == 0 and x % 3 == b]
        tau = min(map(abs, reps))
        if d >= 5:
            assert (d < 4+tau) == (d == 5 and b == 0)
        if d in (5, 6, 7):
            print("cut, beta, abs(tau), slack above LTWZ", d, b, tau, d-4-tau)
    cubic = edges(nx.complete_bipartite_graph(3, 3))
    slacks = []
    for mask in range(1, (1 << 6)-1):
        d = sum(((mask >> a) ^ (mask >> b)) & 1 for a, b in cubic)
        b = mask.bit_count() % 3
        tau = min(abs(x) for x in range(-3, 4) if (d-x) % 2 == 0 and x % 3 == b)
        slacks.append(d-tau)
    assert min(slacks) == 2 and boundary_counts(6, cubic)[(1,)*5] == 0
    k6 = edges(nx.complete_graph(6))
    assert fourier(6, k6)[0] == int(boundary_counts(6, k6).flat[0]) == 80
    # Character triangle inequality fails already on a five-parallel path.
    assert 17**12 > 2*16**12
    path = [(i, i+1) for i in range(12) for _ in range(5)]
    assert int(boundary_counts(13, path).flat[0]) == 10**12
    # Exhaustive lifting on all orientations of a small multigraph with loops,
    # parallel edges, an isolated vertex, and a reversed reference edge.
    pairs = [(0, 0), (0, 1), (1, 0), (1, 2), (1, 2), (2, 0), (2, 2)]
    good = 0
    brute_counts = np.zeros((3,)*3, dtype=np.int64)
    realized_degrees = set()
    for signs in itertools.product((-1, 1), repeat=len(pairs)):
        div = divergence(4, pairs, signs)
        brute_counts[tuple(b % 3 for b in div[:-1])] += 1
        tails = [0]*4
        for (a, b), s in zip(pairs, signs):
            tails[a if s == 1 else b] += 1
        realized_degrees.add(tuple(tails))
        if all(v % 3 == 0 for v in div):
            lift(4, pairs, signs)
            good += 1
    assert good > 0 and np.array_equal(brute_counts, boundary_counts(4, pairs))
    inside = [sum((mask >> a) & (mask >> b) & 1 for a, b in pairs) for mask in range(16)]
    for quota in itertools.product(range(len(pairs)+1), repeat=4):
        allowed = sum(quota) == len(pairs) and all(
            e <= sum(q for v, q in enumerate(quota) if mask & (1 << v))
            for mask, e in enumerate(inside))
        assert allowed == (quota in realized_degrees)
    print("loop/parallel lift witnesses", good)


if __name__ == "__main__":
    arithmetic()
    census()
    transfer()
    witnesses()
