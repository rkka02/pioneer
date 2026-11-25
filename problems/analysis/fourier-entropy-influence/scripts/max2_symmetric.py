"""Integer radial Walsh transforms and branching losses for symmetric signs."""

from fractions import Fraction as Q
from functools import lru_cache
from math import comb, isqrt
import random

import numpy as np

from certificate import enclose_text
from max1_pool import ln_integer_bounds, logloss
from walsh import degrees, signs, wht


@lru_cache(None)
def kernels(n):
    rows = []
    for k in range(n + 1):
        row = [1]
        lag = 0
        for j in range(n):
            value = (n - 2 * k) * row[-1] - (n - j + 1) * lag
            assert value % (j + 1) == 0
            lag = row[-1]
            row.append(value // (j + 1))
        rows.append(row)
    return rows


def radial(values):
    n = len(values) - 1
    a = [sum(x * y for x, y in zip(row, values)) for row in kernels(n)]
    N = 1 << n
    W = [Q(comb(n, k) * v * v, N * N) for k, v in enumerate(a)]
    assert sum(W) == 1
    I = sum(k * w for k, w in enumerate(W))
    if not I:
        return Q(0), Q(0), (Q(0), Q(0)), (Q(0), Q(0))
    # A radial boundary is pivotal on every edge between successive layers.
    assert I == Q(
        n * sum(comb(n - 1, j) for j in range(n) if values[j] != values[j + 1]), 1 << (n - 1)
    )
    assert n * (W[1] / I) ** 2 <= 1
    vals = [Q(0), Q(0)]
    mixed = [Q(0), Q(0)]
    for k in range(2, n + 1):
        if W[k]:
            for j, l in enumerate(logloss(Q(a[k - 1] ** 2, a[k] ** 2))):
                vals[j] += k * W[k] * l
                mixed[j] += (k - 1) * W[k] * l * l
    assert mixed[1] <= 78 * I
    # Test a finite grid of genuine noise multipliers with exact powers.
    for rho in (Q(0), Q(1, 2), Q(7, 8), Q(31, 32)):
        stability = sum(k * w * rho ** (k - 1) for k, w in enumerate(W) if k)
        assert n * (1 - rho) * stability**2 <= I**2
    running = Q(0)
    for k in range(1, n + 1):
        running += k * W[k]
        assert n * running**2 <= Q(739, 100) * k * I**2  # 7.39 > e^2
    if n <= 18:
        full = np.asarray(values, dtype=np.int64)[degrees(n)]
        assert np.array_equal(wht(full), np.asarray(a, dtype=np.int64)[degrees(n)])
    db = I - W[1]
    return (
        I,
        W[2] if n >= 2 else Q(0),
        tuple(v / db if db else Q(0) for v in vals),
        tuple(v / I for v in mixed),
    )


def split_threshold(n):
    # At selector 0 read h(x); at selector 1 read -h(y), using disjoint groups.
    t = (n + isqrt(n)) // 2
    N = 1 << n
    c = Q(comb(n - 1, t - 1), 1 << (n - 1))
    c2 = c * Q(n + 1 - 2 * t, n - 1)
    mu = 1 - 2 * Q(sum(comb(n, j) for j in range(t, n + 1)), N)
    I = n * c + (1 + mu * mu) / 2
    w1 = mu * mu + n * c * c / 2
    mass = Q(comb(n, 2), 2) * c2 * c2
    ell = logloss((c / c2) ** 2)
    b = tuple(2 * mass * v / (I - w1) for v in ell)
    x = tuple(mass * v * v / I for v in ell)
    if n <= 8:
        inputs = np.arange(1 << (2 * n + 1))
        hx = signs(degrees(n)[inputs % N] >= t)
        hy = signs(degrees(n)[(inputs >> n) % N] >= t)
        f = np.where(inputs >> (2 * n), -hy, hx)
        a = wht(f)
        assert not a[0] and Q(int(a[1]), len(f)) == c / 2 and Q(int(a[3]), len(f)) == c2 / 2
        assert I == Q(int(np.sum(a * a * degrees(2 * n + 1))), len(f) ** 2)
    return mass, b, x


def block_test(sizes, rng):
    """Compute the multidegree law and noise estimate on each separate block."""
    from max2_routing import statistics

    n = sum(sizes)
    ids = np.arange(1 << n)
    offset = 0
    counts = []
    for s in sizes:
        counts.append(degrees(s)[(ids >> offset) % (1 << s)])
        offset += s
    table = {}
    f = []
    for pattern in zip(*counts):
        key = tuple(map(int, pattern))
        if key not in table:
            table[key] = rng.choice((-1, 1))
        f.append(table[key])
    a = wht(np.asarray(f))
    levels = {}
    for pattern, v in zip(zip(*counts), a):
        key = tuple(map(int, pattern))
        assert levels.setdefault(key, int(v)) == v
    from math import prod

    W = {
        key: Q(v * v * prod(comb(s, k) for s, k in zip(sizes, key)), 1 << (2 * n))
        for key, v in levels.items()
    }
    I, _, _, mixed = statistics({0: a}, 1 << n)
    assert I == sum(sum(key) * w for key, w in W.items())
    ratio_sum = Q(0)
    for j, s in enumerate(sizes):
        Ij = sum(key[j] * w for key, w in W.items())
        for rho in (Q(0), Q(3, 5), Q(7, 8)):
            smooth = sum(key[j] * w * rho ** (key[j] - 1) for key, w in W.items() if key[j])
            assert s * (1 - rho) * smooth**2 <= Ij**2
        for key, w in W.items():
            if w and key[j] and sum(key) >= 2:
                parent = list(key)
                parent[j] -= 1
                ratio_sum += key[j] * W[tuple(parent)]
    assert ratio_sum <= (1 + len(sizes)) * I
    assert mixed[1] <= (9 + (len(sizes) + 2).bit_length()) ** 2 * I


def main():
    rng = random.Random(4122)
    for sizes in ((2, 3, 4), (4, 6), (2, 2, 2, 3)):
        for _ in range(8):
            block_test(sizes, rng)
    rng = random.Random(4122)
    for n in (8, 13, 18, 32, 64, 128):
        t = (n + isqrt(n)) // 2
        for name, values in [
            ("shifted threshold", [1 if j < t else -1 for j in range(n + 1)]),
            ("band", [1 if abs(2 * j - n) <= isqrt(n) else -1 for j in range(n + 1)]),
            ("scrambled layers", rng.choices([-1, 1], k=n + 1)),
        ]:
            i, w2, b, x = radial(values)
            print(
                name,
                n,
                "W2,B,X/I",
                enclose_text((w2, w2), 6),
                enclose_text(b, 6),
                enclose_text(x, 6),
            )
    for n in (6, 8, 16, 64, 256, 1024, 4096):
        w, b, x = split_threshold(n)
        print(
            "balanced two-branch threshold",
            n,
            "private W2,B2,X2/I",
            enclose_text((w, w), 6),
            enclose_text(b, 6),
            enclose_text(x, 6),
        )
    for n in (6, 8, 10, 12):
        weights = [comb(n, j) for j in range(n + 1)]
        best_b = [Q(0), Q(0)]
        best_x = [Q(0), Q(0)]
        count = 0
        for mask in range(1 << (n + 1)):
            v = [1 - 2 * ((mask >> j) & 1) for j in range(n + 1)]
            if sum(x * y for x, y in zip(v, weights)):
                continue
            count += 1
            _, _, b, x = radial(v)
            best_b = [max(a, c) for a, c in zip(best_b, b)]
            best_x = [max(a, c) for a, c in zip(best_x, x)]
        print(
            "all balanced radial",
            n,
            count,
            "B, X/I maxima",
            enclose_text(best_b, 6),
            enclose_text(best_x, 6),
        )
    l = ln_integer_bounds(2)[0]
    assert (Q(467, 100) + Q(142, 100)) ** 2 / l**2 < 78


if __name__ == "__main__":
    main()
