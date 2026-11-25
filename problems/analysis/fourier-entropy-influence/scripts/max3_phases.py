"""Dual Walsh divisibility obstruction to a plateaued signing of the odd floor."""

from fractions import Fraction as Q
from math import comb
import random

import numpy as np

from certificate import enclose_text
from max3_codes import scramble, pullback
from max3_grids import odd_shell
from max1_pool import logloss
from walsh import checked, degrees, signs, wht


def metrics(a):
    # Balancing by an independent tag adds one to each degree. Losing the
    # tag has cost zero. All private-data deletions of nonempty core sets
    # enter B, including deletions whose core parent is empty.
    from collections import Counter

    n = len(a).bit_length() - 1
    N = len(a)
    d = degrees(n)
    I = Q(int(np.dot(a * a, d + 1)), N * N)
    db = I - Q(int(a[0]) ** 2, N * N)
    pairs = Counter()
    for i in range(n):
        child = np.arange(N)[(np.arange(N) & (1 << i)) != 0]
        v, counts = np.unique(
            np.stack((a[child] ** 2, a[child ^ (1 << i)] ** 2), axis=1), axis=0, return_counts=True
        )
        for (c, b), m in zip(v.tolist(), counts.tolist()):
            if c and b:
                pairs[c, b] += m
    edges = [Q(0), Q(0)]
    for (c, b), m in pairs.items():
        for side, cost in enumerate(logloss(Q(b, c))):
            edges[side] += Q(m * c, N * N) * cost
    return I, enclose_text([x / db for x in edges], 7) if db else "character"


def slice_budget(f, r):
    # Parseval on the outside cube is unnecessary: the triangle inequality
    # against each outside character already gives this stronger fiber bound.
    N = len(f)
    restricted = wht(f.reshape(-1, 1 << r))
    a = checked(f).reshape(-1, 1 << r)
    spectrum = int(np.max(abs(a), axis=0).sum())
    cosets = int(abs(restricted).sum())
    assert spectrum <= cosets
    return Q(spectrum, N), Q(cosets, N)


def affine_fiber_test():
    rng = random.Random(412312)
    m = 6
    for r in (2, 4, 6):
        labels = np.array(rng.choices(range(1 << r), k=1 << m))
        parities = degrees(r)[np.arange(1 << r)[None, :] & labels[:, None]] % 2
        f = (signs(parities) * signs(rng.choices([0, 1], k=1 << m))[:, None]).ravel()
        cost, budget = slice_budget(f, r)
        assert budget == 1
        rows = scramble(m + r, m + r, rng)
        slice_budget(pullback(f, rows, m + r), r)
    for k in (4, 16, 64, 256):
        n = k * k
        s = k.bit_length() - 1
        d = (n + s) // 2
        M = comb(n, k)
        target = ((1 << (2 * d)) - (1 << n)) // 2
        low = 1 << (((target // M).bit_length() - 1) // 2)
        # Every upper-shell amplitude is at least (low-1)/2^d, for any signing.
        left, right = k - 1, n + 1
        while right - left > 1:
            r = (left + right) // 2
            if comb(r, k) * (low - 1) <= 1 << d:
                left = r
            else:
                right = r
        print(
            "shell k, core n, largest possible dimension affine on every parallel slice",
            k,
            n,
            left,
        )


def main():
    k, n = 4, 16
    original, d, t = odd_shell(k, full=True, return_core=True)
    N = len(original)
    X = np.arange(N)
    sizes = degrees(n)
    upper = np.flatnonzero(sizes == k)
    u = min(abs(int(original[s]) - 1) for s in upper)
    limit = k + u.bit_length() - 1
    assert t <= limit < n // 2
    rng = random.Random(412311)
    for rank in (0, 2, 6, 12, 16):
        phase = np.ones_like(X)
        for j in range(0, rank, 2):
            phase *= signs((X >> j) & (X >> (j + 1)) & 1)
        phase = pullback(phase, scramble(n, n, rng), n, tag=rng.randrange(N))
        dual = checked(phase)
        divisor = int(np.gcd.reduce(abs(dual)))
        assert divisor >= 1 << (n // 2)
        a = original * phase
        inv = wht(a)
        assert np.dot(inv, inv) == N * (1 << (2 * d))
        assert np.any(abs(inv) != (1 << d))
        # Each alternating k-face sum of the degree-k correction is fixed
        # across outside assignments. A Boolean inverse would make the
        # alternating sum of dual residues equal its negative mod 2^(d+1).
        for s in rng.sample(upper.tolist(), 8):
            sub = np.flatnonzero((X & s) == X)
            outside = np.flatnonzero((X & s) == 0)
            par = signs(sizes[sub] % 2)
            idx = outside[:, None] | sub
            correction = (inv - dual)[idx] @ par
            assert np.all(correction == (1 << k) * int(a[s] - phase[s]))
            assert np.all((dual[idx] @ par + correction) % (2 << d) != 0)
        print(
            "floor at k=4, plateaued phase rank, Walsh gcd, forbidden when valuation exceeds",
            rank,
            divisor,
            limit,
        )
    # Search genuine Boolean spectra by alternating integer WHT projections.
    # Every per-run metric is recomputed from a Boolean truth table.
    for name, phase in (
        ("bent", phase),
        (
            "cubic",
            signs(((X & 1) * ((X >> 1) & 1) * ((X >> 2) & 1)) ^ (sizes[(X & 255) & (X >> 8)] % 2)),
        ),
    ):
        weights = abs(original)
        spectrum = phase * original
        best_dot = -1
        for step in range(9):
            truth = signs(wht(spectrum) < 0)
            a = checked(truth)
            overlap = int(np.dot(abs(a), weights))
            assert overlap >= best_dot
            best_dot = overlap
            spectrum = weights * signs(a < 0)
        dist = 2 - 2 * Q(best_dot, N * (1 << d))
        assert dist > 0
        I, B = metrics(a)
        print(
            "Boolean projection, phase, squared spectral distance, balanced I,B", name, dist, I, B
        )
    affine_fiber_test()


if __name__ == "__main__":
    main()
