"""Exact WHT tests for peeling a disjoint union of affine cells by codimension."""

from fractions import Fraction as Q
import random

import numpy as np

from certificate import enclose_text
from max1_pool import logloss
from max2_routing import statistics
from max3_codes import linear_values, scramble
from walsh import checked, degrees, signs, wht


def leaves(ids, depth, n, rng):
    if depth == n or (depth and rng.randrange(5) == 0):
        return [(depth, ids)]
    deg = degrees(n)
    while True:
        v = rng.randrange(1, 1 << n)
        lo = (deg[ids & v] % 2) == 0
        if lo.any() and not lo.all():
            break
    assert lo.sum() * 2 == len(ids)
    return leaves(ids[lo], depth + 1, n, rng) + leaves(ids[~lo], depth + 1, n, rng)


def test(cells, n):
    N = 1 << n
    f = np.zeros(N, dtype=np.int64)
    ds = degrees(n)
    for d, idx in cells:
        assert len(idx) == N >> d and not np.any(f[idx])
        f[idx] = 1
    mu = Q(int(f.sum()), N)
    assert 0 < mu <= Q(1, 2)
    a = wht(f)
    true = checked(signs(f))
    I, _, pooled, _ = statistics({0: true}, N)
    sur = Q(0)
    for s in np.flatnonzero(true[1:]) + 1:
        p = Q(int(true[s]) ** 2, N * N)
        sur += p * logloss(1 / p - 1)[1] ** 2 / int(ds[s])
    upper = Q(0)
    for m in range(n + 1):
        tail = np.zeros_like(f)
        for d, idx in cells:
            if d > m:
                tail[idx] = 1
        b = wht(tail)
        assert np.all((a - b) % (N >> m) == 0)
        mask = (a != 0) & (abs(a) * (2 << m) <= N) & (ds > 0)
        assert np.all(abs(a[mask]) <= abs(b[mask]))
        tau = Q(int(tail.sum()), N)
        if tau:
            dl, du = logloss(1 / tau - 1)
            inv = sum(Q(int(b[s]) ** 2, int(ds[s]) * N * N) for s in range(1, N) if b[s])
            assert inv * du <= 10 * tau
            upper += Q(2 * m + 1) * tau / (1 + dl)
    assert sur <= 1280 * upper
    return mu, I, tuple(v / I for v in pooled), upper


def main():
    rng = random.Random(412309)
    for n in (5, 7, 9, 11):
        cells = leaves(np.arange(1 << n), 0, n, rng)
        rng.shuffle(cells)
        chosen = []
        size = 0
        for c in cells:
            if size + len(c[1]) <= 1 << (n - 1) and rng.randrange(3) == 0:
                chosen.append(c)
                size += len(c[1])
        if not chosen:
            chosen = [min(cells, key=lambda c: len(c[1]))]
        mu, I, p, u = test(chosen, n)
        print("affine union, bits,cells,mu,I,P2/I", n, len(chosen), mu, I, enclose_text(p, 8))
    # Varying orientations and lengths can also have a dimension-free
    # exponential tail. One nested leaf per depth gives tau_m <= 2^-m.
    n = 15
    ids = np.arange(1 << n)
    remaining = ids
    chosen = []
    for d in range(1, n + 1):
        lo = ((remaining >> (d - 1)) & 1) == 0
        if d % 2 == 0:
            chosen.append((d, remaining[lo]))
        remaining = remaining[~lo]
    # Apply a common reversible triangular binary linear map.
    chosen = [(d, z ^ (z >> 1)) for d, z in chosen]
    mu, I, p, u = test(chosen, n)
    print("sheared nested leaves, bits,mu,I,P2/I", n, mu, I, enclose_text(p, 8))
    for n in (3, 5, 7, 13):
        # The extremal weight obstruction holds for every affine cell. Check
        # both signs and noncoordinate cosets well below the minimum codimension.
        d = n // 2 + 1
        for _ in range(48):
            flat = linear_values(scramble(d, n, rng)) ^ rng.randrange(1 << n)
            weights = degrees(n)[flat]
            assert weights.min() <= n - d and weights.max() >= d
        m = checked(signs(degrees(n) > n // 2))
        assert int(np.dot(m * m, degrees(n))) == n * len(m) * abs(m[1])


if __name__ == "__main__":
    main()
