"""Evaluate every bisection and every single exchange by a separable max-plus transform."""
from collections import Counter, deque
import itertools
import random

import networkx as nx
import numpy as np

from flow_lab import edges, mincut, regular_census, splice
from obstructions import seven_cut_graph
from bisections import component_defect
from search import named_cases


def landscape(n, pairs, low=None):
    masks = np.arange(1 << n, dtype=np.int32)
    sizes = np.bitwise_count(masks).astype(np.int16)
    internal = sum(((masks >> a) & (masks >> b) & 1).astype(np.int16) for a, b in pairs)
    base = sizes if low is None else sum(a*((masks >> i) & 1).astype(np.int16)
                                        for i, a in enumerate(low))
    defect = internal - base
    # Process coordinates S_i -> H_i. Max over S_i=0,1, with penalty 3 H_i S_i.
    for i in range(n):
        lanes = defect.reshape(-1, 2, 1 << i)
        zero = lanes[:, 0, :].copy()
        one = lanes[:, 1, :].copy()
        np.maximum(zero, one, out=lanes[:, 0, :])
        np.maximum(zero, one-3, out=lanes[:, 1, :])
    return masks, sizes, internal - base, defect


def plateau_escape(n, h, defect):
    """Shortest number of neutral swaps before a strict decrease. None means a closed level."""
    bfs, seen = deque([(h, 0)]), {h}
    while bfs:
        u, steps = bfs.popleft()
        ins = [i for i in range(n) if (u >> i) & 1]
        outs = [i for i in range(n) if not (u >> i) & 1]
        for i, j in itertools.product(ins, outs):
            v = u ^ (1 << i) ^ (1 << j)
            if defect[v] < defect[h]:
                return steps
            if defect[v] == defect[h] and v not in seen:
                bfs.append((v, steps+1))
                seen.add(v)
    return None


def scan(n, pairs, detail=False, beta=None):
    low = None if beta is None else [(2*(b+5)) % 3 for b in beta]
    quota = n//2 if low is None else (len(pairs) - sum(low))//3
    assert low is None or 3*quota + sum(low) == len(pairs)
    masks, sizes, base, defect = landscape(n, pairs, low)
    high = masks[(sizes == quota) & (defect > 0)]
    feasible = int((sizes == quota).sum()) - len(high)
    assert feasible > 0
    best = np.full(len(high), 1000, dtype=np.int16)
    for a, b in itertools.combinations(range(n), 2):
        change = ((high >> a) ^ (high >> b)) & 1
        other = defect[high ^ (1 << a) ^ (1 << b)]
        np.minimum(best, other, where=(change != 0), out=best)
    stalled = high[best >= defect[high]]
    if detail:
        d = defect[high]
        if low is None:
            assert np.array_equal(d, defect[((1 << n)-1) ^ high])
        print("bisections", n, feasible, len(high), "stalled", len(stalled),
              "deficiencies", {int(k): int(v) for k, v in zip(*np.unique(d, return_counts=True))})
    if len(stalled):
        h = int(stalled[0])
        direct = base - 3*np.bitwise_count(masks & h).astype(np.int16)
        assert direct.max() == defect[h]
        escapes = Counter(plateau_escape(n, int(hh), defect) for hh in stalled)
        if detail or None in escapes:
            print("exchange obstruction", n, "mask", h, "D", int(defect[h]),
                  "best adjacent", int(best[high == h][0]), "worst shore", int(np.argmax(direct)),
                  "neutral steps histogram", dict(escapes), "beta", beta)
        if None in escapes:
            print("closed level graph", pairs, "state", next(int(u) for u in stalled
                  if plateau_escape(n, int(u), defect) is None))
    return feasible, len(high), len(stalled)


def audit_defects():
    # This mixed cyclic/tree partition has deficiency two.
    shore = [(i, (i+1) % 5) for i in range(5)] + list(itertools.product(range(5), (5, 6)))
    pairs = shore + [(a+7, b+7) for a, b in shore] + [(i, i+7) for i in range(5)]
    h = set(range(5)) | {12, 13}
    assert mincut(14, pairs) == 5 and component_defect(nx.MultiGraph(pairs), h) == 2
    masks, _, base, d = landscape(14, pairs)
    bits = sum(1 << v for v in h)
    assert d[bits] == (base-3*np.bitwise_count(masks & bits).astype(np.int16)).max() == 2
    # Independent worst-shore sweep for every neighbor of the 18-vertex stalled state.
    pairs = seven_cut_graph()
    masks, _, base, d = landscape(18, pairs)
    stalled = 42858
    for i in range(18):
        for j in range(18):
            if ((stalled >> i) & 1) and not ((stalled >> j) & 1):
                h2 = stalled ^ (1 << i) ^ (1 << j)
                direct = (base-3*np.bitwise_count(masks & h2).astype(np.int16)).max()
                assert direct == d[h2] and direct >= 1
    assert (d[42858], d[42860], d[107884]) == (1, 1, 0)
    print("mixed cyclic/tree deficiency 2; direct 81-swap audit passed")


def main():
    audit_defects()
    summary = Counter()
    for n in (6, 8, 10, 12):
        # Degree-five graph on 12 vertices can have a nontrivial cut of size <5.
        for g in regular_census(n):
            if mincut(n, g) < 5:
                continue
            summary[n, "graphs"] += 1
            good, bad, stalled = scan(n, g)
            summary[n, "realizable"] += good
            summary[n, "deficient"] += bad
            summary[n, "stalled"] += stalled
        print(n, {k: summary[n, k] for k in ("graphs", "realizable", "deficient", "stalled")})
    for name, n, pairs in named_cases():
        if n <= 20 and mincut(n, pairs) == 5 and len(pairs)*2 == 5*n:
            print(name)
            scan(n, pairs, detail=True)
    # Arbitrary beta replaces low degree 1 by a beta-dependent low degree 0, 1 or 2.
    k6 = edges(nx.complete_graph(6))
    boundary_stats = Counter()
    for prefix in itertools.product(range(3), repeat=5):
        beta = [*prefix, -sum(prefix) % 3]
        good, bad, stalled = scan(6, k6, beta=beta)
        boundary_stats.update(dict(realizable=good, deficient=bad, stalled=stalled))
    print("K6 all beta exchanges", boundary_stats)
    rng = random.Random(355)
    for name, n, pairs in named_cases():
        if n <= 20 and mincut(n, pairs) == 5 and 2*len(pairs) == 5*n and n >= 10:
            beta = [rng.randrange(3) for _ in range(n-1)]
            beta.append(-sum(beta) % 3)
            print("beta exchange probe", name, beta)
            scan(n, pairs, detail=True, beta=beta)
    # Small cuts between denser shores, often missed by uniform regular sampling.
    k6 = edges(nx.complete_graph(6))
    for seed in range(6):
        large = edges(nx.random_regular_graph(5, 12, seed=seed))
        combined = splice(12, large, 0, 6, k6, 0, range(5))
        scan(16, combined, detail=True)


if __name__ == "__main__":
    main()
