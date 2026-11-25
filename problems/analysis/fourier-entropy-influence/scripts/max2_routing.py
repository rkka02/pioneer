"""Exact joint spectra of a gate routed through correlated linear addresses."""

from collections import Counter
from fractions import Fraction as Q
import random
import numpy as np

from certificate import enclose_text
from max1_pool import logloss
from walsh import degrees, quadratic, signs, wht


def bits(u):
    while u:
        bit = u & -u
        yield bit
        u -= bit


def statistics(rows, den):
    kinds = Counter()
    I = Q(0)
    mass = 0
    for private, a in rows.items():
        for t in np.flatnonzero(a).tolist():
            c = abs(int(a[t]))
            w = c * c
            mass += w
            neighbors = [abs(int(a[t ^ j])) for j in bits(t)]
            neighbors.extend(
                abs(int(rows[private ^ i][t])) if private ^ i in rows else 0 for i in bits(private)
            )
            k = len(neighbors)
            I += Q(k * w, den * den)
            if k:
                kinds[c, k, tuple(sorted(z for z in neighbors if z))] += w
    assert mass == den * den
    P = [Q(0), Q(0)]
    A = [Q(0), Q(0)]
    X = [Q(0), Q(0)]
    for (c, k, neighbors), w in kinds.items():
        L = [logloss(Q(v * v, c * c)) for v in neighbors]
        for side in (0, 1):
            total = pairs = Q(0)
            for l in L:
                pairs += 2 * total * l[side]
                total += l[side]
            P[side] += Q(w, den * den * k) * total * total
            A[side] += Q(w, den * den) * total
            X[side] += Q(w, den * den * k) * pairs
    return I, A, P, X


def route(g, m, maps, h, dense=False):
    # For each private tuple compute the signed address fiber by an integer WHT.
    ds = degrees(m)
    N = 1 << m
    t = len(maps)
    offsets = [sum(1 << len(c) for c in maps[:j]) for j in range(t)]
    p = sum(1 << len(c) for c in maps)
    assert len(g) == 1 << t and len(h) == N
    labels = [
        [
            offset + sum((int(ds[x & v]) % 2) << k for k, v in enumerate(c))
            for c, offset in zip(maps, offsets)
        ]
        for x in range(N)
    ]
    a = wht(g)
    rows = {}
    origins = {}
    codims = {}
    for U in np.flatnonzero(a).tolist():
        groups = {}
        for x, lab in enumerate(labels):
            u = sum(1 << lab[j] for j in range(t) if U & (1 << j))
            if u not in groups:
                groups[u] = np.zeros(N, dtype=np.int64)
            groups[u][x] = h[x]
        codims[U] = len(groups).bit_length() - 1
        assert len(groups) == 1 << codims[U]
        for u, cell in groups.items():
            assert u not in rows
            row = wht(cell) * a[U]
            assert len(set(np.abs(row[row != 0]).tolist())) == 1
            rows[u] = row
            origins[u] = U
    # Check the pointwise rank-increment inequality before summing any losses.
    for u, row in rows.items():
        U = origins[u]
        if not U:
            continue
        nonzero = row != 0
        for bit in bits(u):
            parent = rows.get(u ^ bit)
            if parent is not None:
                V = origins[u ^ bit]
                loss_rank = codims[U] - codims[V]
                assert np.all(
                    np.abs(parent[nonzero]) * abs(int(a[U]))
                    <= np.abs(row[nonzero]) * abs(int(a[V])) * (1 << loss_rank)
                )
    H = statistics(rows, N * len(g))
    base = statistics({0: a}, len(g))
    cost = H[0] - base[0]
    assert cost >= 0
    assert H[2][0] <= base[2][1] + 74 * cost and H[1][0] <= base[1][1] + 5 * cost
    if cost:
        assert H[2][1] <= base[2][0] + 74 * cost and H[1][1] <= base[1][0] + 5 * cost
    if dense:
        assert p + m <= 19
        f = np.empty((1 << p, N), dtype=np.int64)
        y = np.arange(1 << p)
        for x, l in enumerate(labels):
            addr = sum(((y >> j) & 1) << k for k, j in enumerate(l))
            f[:, x] = h[x] * g[addr]
        full = wht(f.ravel()).reshape(-1, N)
        for u, r in enumerate(full):
            assert np.array_equal(
                r * (N * len(g)), rows.get(u, np.zeros(N, dtype=np.int64)) * len(f.ravel())
            )
    return base, H, cost


def main():
    rng = random.Random(412233)
    peak = [Q(0), Q(0)]
    for m, t in ((2, 3), (3, 4), (4, 5), (5, 6)):
        for trial in range(12):
            g = signs(rng.choices([0, 1], k=1 << t))
            if trial % 3 == 0:
                g = signs(degrees(t) >= t // 2)
            maps = [rng.sample(range(1, 1 << m), rng.choice((1, 1, 2))) for _ in range(t)]
            h = np.ones(1 << m, dtype=np.int64)
            x = np.arange(len(h))
            for _ in range(2 * m):
                i, j = rng.sample(range(m), 2)
                h *= signs(((x >> i) & (x >> j)) & 1)
            base, new, cost = route(
                g, m, maps, h, dense=m + sum(1 << len(r) for r in maps) <= 18 and trial == 0
            )
            if cost:
                for side in (0, 1):
                    peak[side] = max(peak[side], (new[2][side] - base[2][1 - side]) / cost)
    print(
        "48 fixed-quadratic routed gates; maximum pooled increment per added influence",
        enclose_text(peak, 8),
    )
    # A zero-address coded data permutation: start with a four-bit bent function
    # times a mandatory sign, then conjugate so the support is an odd hyperplane.
    n = 5
    x = np.arange(1 << n)
    results = []
    for weight in (5, 2):
        # The last physical coordinate, added to the first weight-1 input bits,
        # induces the required parity check on the Fourier support.
        s = (x >> 4) & 1
        y = (x % 16) ^ (s * ((1 << (weight - 1)) - 1))
        f = signs(s) * quadratic(4)[y]
        a = wht(f)
        ids = np.flatnonzero(a)
        check = 16 + ((1 << (weight - 1)) - 1)
        assert all(int(degrees(n)[int(j) & check]) % 2 == 1 for j in ids)
        results.append(statistics({0: a}, 32))
    orig, new = results
    assert orig[0] == new[0] == Q(5, 2) and orig[3] == [0, 0]
    assert new[3][0] <= Q(7, 16) <= new[3][1]
    assert sum(Q(c * b * (b - 1), 8 * (1 + b)) for b, c in enumerate((1, 3, 3, 1))) == Q(7, 16)
    print("coded data, identical I", new[0], "old X 0, new X", Q(7, 16))


if __name__ == "__main__":
    main()
