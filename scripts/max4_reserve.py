"""Block entropy transfer, guarded lookup occupation times and marginal reserves."""

from collections import Counter
from fractions import Fraction as Q
from math import comb, isqrt
import random

import numpy as np
from certificate import enclose_text
from max1_pool import logloss
from max3_carries import distance, edge_cost, node
from max3_selectors import coarse_height, endpoint_cost
from walsh import checked, degrees, signs, wht


def entropy_counts(weights):
    counts = Counter(Q(z) for z in weights if z)
    lo = hi = Q(0)
    for w, m in counts.items():
        a, b = logloss(1 / w - 1)
        lo += m * w * a
        hi += m * w * b
    return lo, hi


def bent_reserve(n):
    N = 1 << n
    M = N // 2
    # The n coordinate influences are conditional means of edge indicators.
    # Each independent edge is counted twice on the core cube.
    variance = Q(n + 1, 4 * N)
    if n <= 4:
        y = np.arange(N)
        b = np.ones_like(y)
        for i in range(0, n, 2):
            b *= signs((y >> i) & (y >> (i + 1)) & 1)
        x = np.arange(1 << M)[:, None]
        f = np.where(y & 1, b, signs((x >> (y // 2)) & 1))
        a = wht(f)
        costs = []
        for j in range(n):
            per_x = ((a[:, (y & (1 << j)) != 0] ** 2).sum(axis=1)).tolist()
            costs.append(
                Q(sum(z * z for z in per_x), len(per_x) * N**4)
                - Q(sum(per_x), len(per_x) * N**2) ** 2
            )
        assert costs == [Q(1, 2 * N)] + [Q(1, 4 * N)] * (n - 1)
        assert sum(costs) == variance
    R = endpoint_cost(n)
    print(
        "bent prefix",
        n,
        "R",
        enclose_text((R, R), 6),
        "I_X",
        Q(1, 2),
        "future quadratic reserve spent",
        variance,
    )


def walk_cost(n, r):
    N, q = 1 << n, 1 << (n - r)
    total = Q(0)
    heights = [1 << j for j in range(3, n + 1)]
    residuals = dict.fromkeys(heights, 0)
    count = 1
    for t in range(q + 1):
        for h in heights:
            residuals[h] += count * distance(2 * t - q, h) ** 2
        count = count * (q - t) // (t + 1)
    for h in heights:
        er = Q(residuals[h], 1 << q)
        cost = 1 - er / q
        assert 0 <= cost <= 1
        if h * h <= q:
            assert cost >= 1 - Q(h * h, 4 * q)
        else:
            assert cost <= Q(12 * q, h * h)
        total += cost
    if q <= 64:
        direct = sum(
            Q(sum(comb(j, k) * coarse_height(2 * k - j, N) for k in range(j + 1)), q * (1 << j))
            for j in range(q)
        )
        assert total == direct
    assert Q(n - r, 2) - 4 <= total <= Q(n - r, 2) + 16
    return total


def guard_test(n, columns, d, dense=False):
    N = 1 << n
    r = max(columns).bit_length()
    Z = 1 << r
    labels = [0]
    for c in columns:
        labels += [v ^ c for v in labels]
    assert len(labels) == N and len(set(labels)) == Z
    assert all(labels[v] for v in range(1, N) if bin(v).count("1") <= d)
    y = np.arange(N)
    core = np.arange(N * Z)
    labels = np.array(labels)
    phase = signs(degrees(r)[(core >> n) & labels[core % N]] % 2)
    rng = random.Random(40621 + n)
    # A physical assignment of data signs leaves a Boolean future truth table.
    # A prefix is an average of full conditional squared laws (Parseval).
    for _ in range(10):
        values = signs(rng.choices((0, 1), k=N))
        f = phase * values[core % N]
        a = checked(f)
        correlations = wht(a * a)
        assert all(correlations[v] == 0 for v in range(1, len(f)) if bin(v).count("1") <= d)
        rows = wht((phase * values[core % N]).reshape(Z, N).T)
        predictions = np.zeros((Z, N), dtype=np.int64)
        for t in range(Z):
            predictions[t] = Z * wht(np.where(labels == t, values, 0))
        assert np.array_equal(a, predictions.ravel())
        assert np.count_nonzero(rows) == N
    R = walk_cost(n, r)
    if dense:
        truth = (
            phase[:, None] * signs((np.arange(1 << N)[None, :] >> (core % N)[:, None]) & 1)
        ).ravel()
        a = checked(truth)
        # The independent balancing character just shifts all these frequencies.
        assert set(abs(a)) == {0, len(a) // N}
        assert np.count_nonzero(a) == N * N
        _, actual = prefix_cost(truth, N)
        assert actual == R
    print(
        "guard n,r,d",
        n,
        r,
        d,
        "coarse / prefix I",
        enclose_text((R, R), 6),
        "conditional spectral label entropy",
        n - r,
    )


def prefix_cost(f, k):
    if not k:
        return Q(0), Q(0)
    _, r, alpha = node(wht(f), 0)
    a, b = (prefix_cost(f[j::2], k - 1) for j in range(2))
    return alpha + (a[0] + b[0]) / 2, r + (a[1] + b[1]) / 2


def plus(a, b):
    return a[0] + b[0], a[1] + b[1]


def minus(a, b):
    return a[0] - b[1], a[1] - b[0]


def overlap(a, b):
    return a[0] <= b[1] and b[0] <= a[1]


def block_test(f, k):
    N = len(f)
    x, y = 1 << k, N >> k
    f = f.reshape(y, x)
    a = checked(f.ravel()).reshape(y, x)
    # w(x,T), w(U,y), p(U,T) all have exactly the indicated denominators.
    hybrid_xt = wht(f.T).T ** 2
    hybrid_uy = wht(f) ** 2
    p = a * a
    rows = [Q(int(s), N * N) for s in p.sum(axis=1)]
    cols = [Q(int(s), N * N) for s in p.sum(axis=0)]
    assert np.array_equal(hybrid_xt.sum(axis=1) * x, p.sum(axis=1))
    assert np.array_equal(hybrid_uy.sum(axis=0) * y, p.sum(axis=0))
    Hp = entropy_counts(Q(int(v), N * N) for v in p.flat)
    HT, HU = entropy_counts(rows), entropy_counts(cols)
    Ht_x = entropy_counts(Q(int(v), y * y * x) for v in hybrid_xt.flat)
    Ht_x = tuple(v - k for v in Ht_x)
    Hu_y = entropy_counts(Q(int(v), x * x * y) for v in hybrid_uy.flat)
    Hu_y = tuple(v - (y.bit_length() - 1) for v in Hu_y)
    cond = minus(Hp, HT)
    ix_t = minus(HT, Ht_x)
    iu_y = minus(HU, Hu_y)
    iu_t = minus(plus(HU, HT), Hp)
    defect = minus(minus(Hp, Ht_x), Hu_y)
    assert overlap(minus(plus(ix_t, iu_y), iu_t), defect)
    I, R = prefix_cost(f.ravel(), k)
    assert ix_t[0] <= 3 * I  # underlying theorem uses 2/ln(2)
    mixed = sum(Q(int(sum(p[t, 1:])), N * N) * bin(t).count("1") for t in range(y))
    delta = 1 - cols[0]
    assert iu_y[0] <= 3 * mixed + Q(3, 2) * delta
    # Certified upper bound on sum |u| sqrt(e), integer rounding at 2^-36.
    gamma = sum(
        Q(abs(int(a[t, 0])) * (isqrt(int(sum(p[t, 1:])) << 72) + 1), N * N * (1 << 36))
        for t in range(y)
        if any(p[t, 1:])
    )
    assert max(R - cond[0] / 2, cond[1] / 2 - R) <= 18 * I + 8 * gamma
    return defect


def absorbing_walk(B, steps, dense=False):
    """One fixed terminal singleton; counts include all stopped paths."""
    power = B.bit_length() - 1
    counts = {0: 1}
    spent = visiting = Q(0)
    for j in range(steps):
        live = sum(c for x, c in counts.items() if abs(x) < B)
        spent += Q(live, 1 << j)
        visiting += Q(
            sum(c * coarse_height(x, B) for x, c in counts.items() if abs(x) < B), (1 << j) * B * B
        )
        nxt = Counter()
        for x, c in counts.items():
            if abs(x) == B:
                nxt[x] += 2 * c
            else:
                nxt[x - 1] += c
                nxt[x + 1] += c
        counts = nxt
    endpoint = Q(0)
    for t in range(3, power + 1):
        h = 1 << t
        err = Q(sum(c * distance(x, h) ** 2 for x, c in counts.items()), 1 << steps)
        endpoint += (spent - err) / (B * B)
    assert endpoint == visiting
    assert spent == Q(sum(c * x * x for x, c in counts.items()), 1 << steps)
    if steps >= 2 * B * B:
        assert spent >= Q(B * B, 2) and visiting >= Q(power - 2, 2) - Q(1, 3)
    if dense:
        size = 1 << (steps + power + 1)
        x = np.arange(size)
        w = np.zeros_like(x)
        for j in range(steps):
            w += (abs(w) < B) * signs((x >> j) & 1)
        truth = signs((x >> steps) >= B + w)
        a = checked(np.concatenate((truth, -truth)))
        assert not a[0] and sum(truth) == 0
        direct = Q(0)
        for j in range(steps):
            # The tag coefficient after fixing j steps is the mean of the untagged sign.
            restricted = wht(truth.reshape(-1, 1 << j).T)
            child = wht(truth.reshape(-1, 2 << j).T)[:, 0]
            m = restricted[:, 0] * B // (size >> j)
            assert np.array_equal(m * (size >> j), restricted[:, 0] * B)
            u = (child[: 1 << j] + child[1 << j :]) * B
            v = (child[: 1 << j] - child[1 << j :]) * B
            assert np.array_equal(u, m * (size >> j))
            assert np.all(abs(v) == (abs(m) < B) * (size >> j))
            direct += Q(sum(coarse_height(int(t), B) for t in m if abs(t) < B), B * B * (1 << j))
        assert direct == visiting
    # Finish the same singleton martingale through every rounding bit.
    variation = spent / B
    quadratic = spent / (B * B)
    complete = visiting
    for pos, count in counts.items():
        terminal = signs(np.arange(2 * B) >= B + pos)
        for j in range(power + 1):
            child = wht(terminal.reshape(-1, 2 << j).T)[:, 0] * (1 << j)
            for m in range(1 << j):
                u = int(child[m] + child[m + (1 << j)])
                v = int(child[m] - child[m + (1 << j)])
                w = Q(count, 1 << (steps + j))
                variation += w * Q(abs(v), 2 * B)
                quadratic += w * Q(v * v, 4 * B * B)
                complete += w * edge_cost(u, v, 2 * B)[1]
    assert quadratic == 1 and complete >= visiting
    assert complete <= 2 + logloss(variation - 1)[0]
    print(
        "terminal singleton walk B,steps",
        B,
        steps,
        "prefix cost",
        enclose_text((visiting, visiting), 8),
        "full R",
        enclose_text((complete, complete), 8),
        "full V",
        enclose_text((variation, variation), 6),
        "full Q",
        quadratic,
    )


def single_switch_credit(n):
    N = 1 << n
    y = np.arange(N)
    bent = np.ones_like(y)
    for i in range(0, n, 2):
        bent *= signs((y >> i) & (y >> (i + 1)) & 1)
    sides = np.tile(bent, (2, 1))
    sides[0, 0] *= -1
    sides[1, 1] *= -1
    a = checked(sides.ravel())
    _, R, I = node(a, n)
    assert I == Q(2, N) and R == Q(2, 1 << (n // 2))
    # Tagging simply translates the future frequencies.
    h = entropy_counts((I, 1 - I))
    assert R > h[1] / 2
    print(
        "single switch, n",
        n,
        "R",
        R,
        "half conditional label entropy at most",
        enclose_text((h[1] / 2, h[1] / 2), 8),
    )


def scalar_and_blocks():
    rng = random.Random(40622)
    for n in range(1, 10):
        N = 1 << n
        last = (Q(0), Q(0))
        for j in range(1, N + 1):
            w = Q(j * j, N * N)
            h = tuple(w * t for t in logloss(Q(N, j) - 1))
            if not j & (j - 1):
                h = (w * (n - j.bit_length() + 1),) * 2
            grid = Q(sum(distance(j, 1 << m) ** 2 for m in range(1, n + 1)), N * N)
            gap = (h[0] - grid, h[1] - grid)
            assert 0 <= gap[0] and gap[1] <= w
            # Gap upper bound for adjacent rational arguments in both directions.
            assert max(gap[1] - last[0], last[1] - gap[0]) <= 4 * Q(2 * j - 1, N * N)
            last = gap
    for n in (3, 4, 5, 7):
        for k in range(1, n):
            for _ in range(3):
                block_test(signs(rng.choices((0, 1), k=1 << n)), k)
    h = np.array([1, 1, 1, -1], dtype=np.int64)
    xor = np.bitwise_xor.outer(np.arange(4), np.arange(4))
    z = block_test(h[xor].ravel(), 2)
    assert overlap(z, (Q(-2), Q(-2)))
    print(
        "scalar grids, local-time comparison, log-Sobolev and two mixed laws passed; XOR defect -2"
    )


def main():
    for n in (4, 6, 8, 12):
        bent_reserve(n)
    for n, cols, d in (
        (2, [1, 1], 1),
        (3, [1, 2, 3], 2),
        (7, list(range(1, 8)), 2),
        (10, [1] * 10, 1),
        (14, [1] * 14, 1),
    ):
        # Large data cubes admit exact factored Walsh and walk calculations.
        if n <= 10:
            guard_test(n, cols, d, dense=(n == 2))
        else:
            R = walk_cost(n, 1)
            print("guard n=14, r=1, factored exact coarse / prefix I", enclose_text((R, R), 8))
    for B, steps in ((8, 9), (8, 128), (16, 512), (32, 2048), (32, 5120)):
        absorbing_walk(B, steps, dense=(steps == 9))
    single_switch_credit(12)
    scalar_and_blocks()


if __name__ == "__main__":
    main()
