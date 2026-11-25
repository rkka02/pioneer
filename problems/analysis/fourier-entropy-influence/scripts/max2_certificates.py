"""Quantized Walsh slices, information after revealing bits, and relaxed shell laws."""

from fractions import Fraction as Q
from itertools import combinations
from math import comb
import random

import numpy as np

from certificate import enclose_text
from max1_pool import logloss
from max2_levels import tied_majority
from walsh import degrees, record_seed, signs, splits, wht


def subspaces(n):
    spaces = {frozenset([0])}
    for j in range(1, 1 << n):
        for s in list(spaces):
            if j not in s:
                spaces.add(s | frozenset(x ^ j for x in s))
    return spaces


def verify_bits(f, spaces=()):
    a = wht(f)
    N = len(f)
    n = N.bit_length() - 1
    p = a * a
    odd_unit = min(abs(int(v)) & -abs(int(v)) for v in a if v)
    grid_depth = (N // odd_unit).bit_length() - 1
    for i in range(n):
        u, v = splits(a, i)
        A = int(np.dot(v, v))
        # Independence uses the whole signed-row magnitude, including its zeros.
        if all(int(z) ** 2 * N * N == A * (int(y) ** 2 + int(z) ** 2) for y, z in zip(u, v)):
            assert A in (0, N * N // 2, N * N)
    for s in spaces:
        r = n - (len(s).bit_length() - 1)
        if not r:
            continue
        unseen = set(range(N))
        while unseen:
            pivot = next(iter(unseen))
            C = [pivot ^ j for j in s]
            unseen.difference_update(C)
            assert int(p[C].sum()) * (1 << (r - 1)) >= N * max(abs(int(a[j])) for j in C)
            if r <= grid_depth:
                assert sum((int(a[j]) // odd_unit) % 2 for j in C) % 2 == 0
    # Highest-degree nonzero superset at each vertex (max-zeta transform).
    top = np.where(a, degrees(n), 0)
    for j in range(n):
        pair = top.reshape(-1, 2, 1 << j)
        pair[:, 0, :] = np.maximum(pair[:, 0, :], pair[:, 1, :])
    for s in np.flatnonzero(a).tolist():
        if top[s]:
            assert (int(a[s]) * (1 << (int(top[s]) - 1))) % N == 0

    # Prefix odds, full odds and their exact present-incidence likelihood ratio.
    for i in range(n):
        row = p.reshape(-1, 2, 1 << i)
        pre = row.sum(axis=0)
        value = Q(0)
        for j in range(1 << i):
            if pre[1, j]:
                prob = Q(int(pre[1, j]), int(pre[0, j] + pre[1, j]))
                keep = row[:, 1, j] != 0
                value += prob * int(row[keep, :, j].sum())
        assert value <= int(pre[1].sum())
    # Verify the moment bound for the local highest-degree region.
    influence = int(np.dot(p, degrees(n)))
    if not influence:
        return
    high = Q(0)
    for s in np.flatnonzero(a).tolist():
        k = int(degrees(n)[s])
        if not k or 2 * k < top[s]:
            continue
        v = int(a[s]) ** 2
        loss = sum(logloss(Q(int(a[s ^ (1 << j)]) ** 2, v))[1] for j in range(n) if (s >> j) & 1)
        high += v * loss**2 / k
    assert high <= (4 + Q(205, 100)) ** 2 * influence


def fake(n, k, delta, dense=False):
    b = delta / (1 << n)
    parent = b + (1 - delta) / (2 * comb(n, k - 1))
    child = b + (1 - delta) / (2 * comb(n, k))
    assert max(parent, child, b) * 4 <= delta**2
    # Mandatory sign makes the law balanced. Its deletion odds vanish.
    I = 1 + (1 - delta) * Q(2 * k - 1, 2) + delta * Q(n, 2)
    w = comb(n, k) * child
    L = logloss(parent / child)
    # Lower endpoints from the single weight-k cohort (ignore all other cohorts).
    B = w * k * L[0] / I
    X = w * Q(k * (k - 1), k + 1) * L[0] ** 2 / I
    if dense:
        # Inverse WHT in the symbolic basis of the three distinct square roots.
        masks = [(degrees(n) == k - 1), (degrees(n) == k)]
        masks.append(~(masks[0] | masks[1]))
        masses = [parent, child, b]
        assert sum(Q(np.count_nonzero(m)) * p for m, p in zip(masks, masses)) == 1
        for mask in masks:
            coeffs = np.concatenate((np.zeros(1 << n, dtype=np.int64), mask.astype(np.int64)))
            assert np.array_equal(wht(wht(coeffs)), len(coeffs) * coeffs)
    return B, X


def dyadic_shell(k, dense=False):
    """A unit vector on the exact Walsh grid satisfying every affine mass bound.

    An odd count on one affine flat excludes every Boolean choice of signs.
    All amplitude counts below are in units of the smallest amplitude, 2^-d.
    """
    n = k * k
    logk = k.bit_length() - 1
    assert k == 1 << logk and logk % 2 == 0 and k >= 4
    d = n // 2 + logk // 2
    norm = 1 << (2 * d)
    base = 1 << n
    left = norm - base
    moment = n * (base // 2)
    amps = {}
    for j in (k - 1, k):
        count = comb(n, j)
        exp = ((8 * count - 1).bit_length() + 1) // 2
        u = 1 << (d - exp)
        assert 1 < u <= Q(1, 2 * k) * (1 << d)
        amps[j] = u
        increment = count * (u * u - 1)
        left -= increment
        moment += j * increment
    fill = {}
    while left:
        step = min(d - logk - 1, ((left + 1).bit_length() - 1) // 2)
        assert step >= 1
        m, left = divmod(left, (1 << (2 * step)) - 1)
        fill[1 << step] = m
        moment += 2 * m * ((1 << (2 * step)) - 1)
    assert sum(fill.values()) <= comb(n, 2)
    used = base + sum(comb(n, j) * (u * u - 1) for j, u in amps.items())
    assert used + sum(m * (u * u - 1) for u, m in fill.items()) == norm
    I = 1 + Q(moment, norm)
    w = Q(comb(n, k) * amps[k] ** 2, norm)
    odds = Q(amps[k - 1], amps[k]) ** 2
    L = logloss(odds)[0]
    # Codimension k in the balanced (n+1)-variable law; z-absent masses are zero.
    assert k <= d and ((1 << (n - k)) - 1) % 2
    if dense:
        deg = degrees(n)
        coeff = np.ones(base, dtype=np.int64)
        for j, u in amps.items():
            coeff[deg == j] = u
        pairs = np.flatnonzero(deg == 2)
        start = 0
        for u, m in fill.items():
            coeff[pairs[start : start + m]] = u
            start += m
        coface = (np.arange(base) & ((1 << k) - 1)) == ((1 << k) - 1)
        assert int(np.sum(coeff[coface] % 2)) % 2 == 1
        coeff = np.concatenate((np.zeros_like(coeff), coeff))
        assert int(np.dot(coeff, coeff)) == norm
        assert np.array_equal(wht(wht(coeff)), len(coeff) * coeff)
        assert max(coeff) * (2 * k) <= 1 << d and wht(coeff)[0] > 1 << d
    return k * w * L / I, Q(k * (k - 1), k + 1) * w * L * L / I, odds


def loss_moments(f):
    a = wht(f)
    n = len(f).bit_length() - 1
    d = len(f) ** 2
    K = Q(int(np.sum(a * a * degrees(n))), d)
    A = [Q(0), Q(0)]
    A2 = [Q(0), Q(0)]
    for s in np.flatnonzero(a).tolist():
        v = int(a[s]) ** 2
        L = [logloss(Q(int(a[s ^ (1 << i)]) ** 2, v)) for i in range(n) if (s >> i) & 1]
        for j in (0, 1):
            x = sum(l[j] for l in L)
            A[j] += Q(v, d) * x
            A2[j] += Q(v, d) * x * x
    return K, A, A2


def tensor_check():
    g = signs([0, 1, 1, 1])  # biased two-bit gate
    i, a, v = loss_moments(g)
    f = np.array([1, -1], dtype=np.int64)
    for t in range(1, 6):
        f = np.kron(f, g)
        j, b, w = loss_moments(f)
        assert j == 1 + t * i and b[0] <= t * a[1] and t * a[0] <= b[1]
        lower = t * v[0] + t * (t - 1) * a[0] ** 2
        upper = t * v[1] + t * (t - 1) * a[1] ** 2
        assert w[0] <= upper and lower <= w[1]
    # Padding by mandatory parities can suppress the fraction of costly incidences.
    h = np.kron(signs(degrees(4) % 2), g)
    j, b, _ = loss_moments(h)
    assert j == 4 + i and b[0] <= a[1] and a[0] <= b[1]


def signed_hyperplane_test():
    # At unit norm, integer sums on all negative character hyperplanes and
    # an odd total characterize Boolean signs exactly.
    rng = random.Random(412237)
    n = 4
    N = 1 << n
    ids = np.arange(N)
    neg = [degrees(n)[ids & x] % 2 == 1 for x in range(1, N)]
    trials = [wht(signs(rng.choices((0, 1), k=N))) for _ in range(24)]
    even = np.zeros(N, dtype=np.int64)
    even[: N // 4] = 2
    trials.append(wht(even))
    for original in trials:
        for _ in range(12):
            a = original * signs(rng.choices((0, 1), k=N))
            assert int(np.dot(a, a)) == N * N
            integer = all(int(a[h].sum()) % N == 0 for h in neg)
            odd = int(a.sum()) % (2 * N) == N
            assert (integer and odd) == bool(np.all(np.abs(wht(a)) == N))


def main():
    rng = random.Random(412215)
    spaces = subspaces(4)
    for _ in range(40):
        verify_bits(signs(rng.choices([0, 1], k=16)), spaces)
    for code in range(256):
        verify_bits(signs((code >> np.arange(8)) & 1))
    for f in (record_seed(), tied_majority(12, "random")):
        verify_bits(f)
    fake(16, 4, Q(1, 3), True)
    for k in (9, 17, 33, 65, 129):
        b, x = fake(k * k, k, Q(1, k))
        print(
            "balanced real relaxation k,n, lower bounds B and X/I",
            k,
            k * k,
            enclose_text((b, b), 6),
            enclose_text((x, x), 6),
        )
    for k in (4, 16, 64, 256):
        b, x, r = dyadic_shell(k, dense=k == 4)
        print(
            "dyadic shell k,odds, lower bounds B and X/I",
            k,
            r,
            enclose_text((b, b), 6),
            enclose_text((x, x), 6),
        )
    tensor_check()
    signed_hyperplane_test()
    print(
        "all 4D affine flats on 40 tables, independence, local granularity and tensor moments passed"
    )


if __name__ == "__main__":
    main()
