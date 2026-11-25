"""Test the two-sided degree budget under arbitrary binary linear input recoding."""

from collections import Counter
from fractions import Fraction as Q
from math import comb
import random

import numpy as np

from certificate import enclose_text
from max1_pool import logloss
from max2_routing import statistics
from max3_codes import linear_values, scramble, verify_recode
from walsh import degrees, signs, wht


def profiles(sizes):
    n = sum(sizes)
    ids = np.arange(1 << n)
    offset = 0
    groups = []
    for b in sizes:
        groups.append(degrees(b)[(ids >> offset) % (1 << b)])
        offset += b
    return list(zip(*(z.tolist() for z in groups)))


def profile_test(f, sizes, rows, out_n, tag):
    n = sum(sizes)
    a = wht(f)
    final = verify_recode(f, rows, out_n, tag=tag)
    I, A, P, X = statistics({0: final}, len(final))
    if not I:
        return I, (Q(0), Q(0))
    ds = degrees(out_n)[linear_values(rows) ^ tag]
    profile = profiles(sizes)
    values = {}
    counts = Counter()
    reciprocals = Counter()
    projected_degrees = Counter()
    for t, key in enumerate(profile):
        assert values.setdefault(key, int(a[t]) ** 2) == int(a[t]) ** 2
        counts[key] += 1
        K = int(ds[t])
        projected_degrees[key] += K
        if K:
            reciprocals[key] += Q(1, K)
    W = {key: Q(counts[key] * v, len(a) ** 2) for key, v in values.items()}
    for key, count in counts.items():
        minor_sum = sum(min(k, b - k) for k, b in zip(key, sizes))
        assert count * minor_sum <= 128 * projected_degrees[key]
    Js = Q(0)
    for col, b in enumerate(sizes):
        jdeg = {key: min(key[col], b - key[col]) for key in W}
        J = sum(W[key] * j for key, j in jdeg.items())
        Js += J
        if not J:
            continue
        pair_sum = sum(key[col] * (b - key[col]) * w for key, w in W.items())
        for rho in (Q(0), Q(1, 2), Q(7, 8)):
            for reflected in (False, True):
                moment = Q(0)
                for key, w in W.items():
                    k = key[col] if not reflected else b - key[col]
                    if 0 < k < b:
                        moment += k * (b - k) * w * rho ** (k - 1)
                assert (b - 1) * (1 - rho) * moment**2 <= 4 * pair_sum**2
        for d in range(1, b // 2 + 1):
            mass = sum(W[key] * j for key, j in jdeg.items() if j <= d)
            assert b * mass**2 <= 1024 * d * J**2
        for key, j in jdeg.items():
            if j:
                assert reciprocals[key] * j <= 34 * counts[key]
        # Replace e by 4 in the logarithm for a strictly larger test value.
        norm = sum(
            w * jdeg[key] * logloss(Q(4 * b, jdeg[key]) - 1)[1] ** 2
            for key, w in W.items()
            if jdeg[key]
        )
        assert norm <= 24**2 * J
    assert Js <= 128 * I
    raw = Q(0)
    for key, c in values.items():
        if c:
            l = logloss(Q(len(a) ** 2, c) - 1)[1]
            raw += Q(c, len(a) ** 2) * reciprocals[key] * l * l
    r = len(sizes)
    # Integer safe relaxation of the displayed constant in the report.
    assert raw <= (1700 * r + 7) ** 2 * I and P[1] <= (1700 * r + 10) ** 2 * I
    return I, tuple(v / I for v in X)


def redundant_threshold(m, t, rng):
    # Systematic generator [Id | P]. Column types of P are symmetry blocks.
    dependent = [rng.randrange(1, 1 << m) for _ in range(t)]
    types = [tuple((v >> i) & 1 for v in dependent) for i in range(m)]
    order = sorted(range(m), key=types.__getitem__)
    groups = [types[i] for i in order]
    counts = Counter(groups)
    sizes = list(counts.values())
    rows = [1 << j for j in range(m)]
    for v in dependent:
        rows.append(sum(((v >> old) & 1) << j for j, old in enumerate(order)))
    idx = linear_values([sum(((v >> i) & 1) << j for j, v in enumerate(rows)) for i in range(m)])
    # Arbitrary radial sign; coset shift only at the dependent positions.
    shift = rng.randrange(1 << t) << m
    f = signs(degrees(m + t)[idx ^ shift] >= (m + t) // 2 + 1)
    I, x = profile_test(f, sizes, scramble(m, m + 1, rng), m + 1, rng.randrange(1 << (m + 1)))
    return len(sizes), I, x


def main():
    rng = random.Random(412307)
    for sizes in ([6], [12], [3, 5], [2, 3, 4], [1, 3, 6]):
        n = sum(sizes)
        keys = profiles(sizes)
        for trial in range(3):
            labels = {key: rng.choice((-1, 1)) for key in sorted(set(keys))}
            if trial == 0:
                labels = {key: 1 - 2 * (sum(key) > n // 2) for key in labels}
            f = np.array([labels[k] for k in keys])
            I, x = profile_test(
                f, sizes, scramble(n, n + 1, rng), n + 1, rng.randrange(1 << (n + 1))
            )
            print("recoded block sizes, I, X/I", sizes, I, enclose_text(x, 7))
    for n, t in ((8, 1), (8, 2), (10, 3), (12, 4)):
        r, I, x = redundant_threshold(n, t, rng)
        assert r <= 1 << t
        print(
            "coded majority with dependent parities, m,t,blocks,I,X/I",
            n,
            t,
            r,
            I,
            enclose_text(x, 7),
        )
    # Exact volume bound used in the proof, independent of coordinate positions.
    for n in (16, 65, 128, 513, 1024):
        for j in range(1, n // 2 + 1):
            small = sum(comb(n, h) for h in range(1 + j // 32))
            assert small**2 * (1 << j) <= comb(n, j) ** 2


if __name__ == "__main__":
    main()
