"""Certify the mean squared spectrum of Gaussian signs and the mixture loss bound."""

from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, isqrt

import numpy as np

from certificate import enclose_text
from max1_pool import ln_integer_bounds, logloss
from max2_routing import statistics
from walsh import degrees, record_seed, signs, wht


def atan_reciprocal(d):
    lo = sum(Q((-1) ** j, (2 * j + 1) * d ** (2 * j + 1)) for j in range(32))
    return lo, lo + Q(1, 65 * d**65)


l5, u5 = atan_reciprocal(5)
l239, u239 = atan_reciprocal(239)
PI = 16 * l5 - 4 * u239, 16 * u5 - 4 * l239  # Machin's identity
UNIT = 1 << 42


def sqrt_bounds(q):
    scale = 1 << 65
    j = isqrt((q.numerator * scale**2) // q.denominator)
    return Q(j, scale), Q(j + (j * j * q.denominator != q.numerator * scale**2), scale)


def asin_small(x):
    assert 0 <= x <= Q(1, 2)
    term = x
    lo = Q(0)
    for j in range(33):
        lo += term
        term *= x * x * Q((2 * j + 1) ** 2, (2 * j + 2) * (2 * j + 3))
    return lo, lo + 4 * term / 3


@lru_cache(None)
def sign_kernel(x):
    if x < 0:
        lo, hi = sign_kernel(-x)
        return -hi, -lo
    if x == 1:
        return UNIT, UNIT
    if x <= Q(1, 2):
        a, b = asin_small(x)
        lo, hi = 2 * a / PI[1], 2 * b / PI[0]
    else:
        l, u = sqrt_bounds((1 - x) / 2)
        lo, hi = 1 - 4 * asin_small(u)[1] / PI[0], 1 - 4 * asin_small(l)[0] / PI[1]
    return (lo * UNIT).__floor__(), (hi * UNIT).__ceil__()


def gaussian_law(counts, radial_k=None):
    """WHT the arcsine kernel with a pointwise certified error before inversion."""
    n = len(counts).bit_length() - 1
    size = len(counts)
    scale = int(counts.sum())
    deg = degrees(n)
    corr = wht(counts)
    values, inv = np.unique(corr, return_inverse=True)
    bounds = [sign_kernel(Q(int(c), scale)) for c in values]
    err = max(u - l for l, u in bounds)
    transformed = wht(np.array([l for l, _ in bounds], dtype=np.int64)[inv])
    den = size * UNIT
    assert den <= 1 << 61
    hist = Counter(map(int, transformed))
    entropy = [Q(0), Q(0)]
    for value, count in hist.items():
        lo, hi = max(Q(0), Q(value, den) - Q(err, UNIT)), min(Q(1), Q(value, den) + Q(err, UNIT))
        assert lo <= hi
        if not hi:
            continue
        density_log = logloss(1 / hi - 1)
        entropy[0] += count * lo * density_log[0]
        upper = Q(1)
        if hi <= Q(1, 4):
            upper = hi * density_log[1]
        elif lo:
            upper = hi * logloss(1 / lo - 1)[1]
        entropy[1] += count * upper
    inf = [Q(0), Q(0)]
    for i in range(n):
        l, u = sign_kernel(Q(int(corr[1 << i]), scale))
        inf[0] += Q(UNIT - u, 2 * UNIT)
        inf[1] += Q(UNIT - l, 2 * UNIT)
    assert entropy[1] < 24 * (1 + inf[0])
    if radial_k is not None:
        assert inf[0] * PI[0] / 2 >= sqrt_bounds(Q(n) * (radial_k - Q(1, 2)))[1]
        # On a radial law P2 is the incidence second moment of its common loss.
        pooled_hi = Q(0)
        last_hi = Q(0)
        mass_upper = Q(0)
        for k in range(n + 1):
            rows = transformed[deg == k]
            assert rows.min() == rows.max()
            mid = Q(int(rows[0]), den)
            hi = min(Q(1), mid + Q(err, UNIT))
            lo = max(Q(0), mid - Q(err, UNIT))
            if k and lo:
                ell = logloss(last_hi / lo)[1]
                pooled_hi += k * comb(n, k) * hi * ell**2
            elif k and hi:
                # For x <= hi < 1/16 and y <= 1, x log^2(1+y/x)
                # is at most hi log^2(2/hi), by monotonicity of x ln^2(2/x).
                assert hi <= Q(1, 16)
                pooled_hi += k * comb(n, k) * hi * logloss(2 / hi - 1)[1] ** 2
            mass_upper += k * comb(n, k) * hi
            assert n * mass_upper**2 <= 100 * max(1, k) * inf[0] ** 2
            last_hi = hi
        assert pooled_hi < 224 * inf[0]
    return tuple(inf), tuple(entropy)


def mixture_check():
    # The posterior ratio tail is exact for a finite mixture, including
    # spectra with disjoint supports and zero rows.
    rng = np.random.default_rng(412282)
    for n in (3, 5, 7):
        size = 1 << n
        rows = [wht(signs(rng.integers(0, 2, size))) for _ in range(8)]
        weight = sum(row * row for row in rows)
        total = 8 * size**2
        pmix = [Q(0), Q(0)]
        for s in np.flatnonzero(weight).tolist():
            k = int(degrees(n)[s])
            if not k:
                continue
            L = [Q(0), Q(0)]
            for j in range(n):
                if s & (1 << j):
                    v = s ^ (1 << j)
                    odds = Q(int(weight[v]), int(weight[s]))
                    lo, hi = logloss(odds)
                    L[0] += lo
                    L[1] += hi
                    if weight[v]:
                        used = sum(int(row[v]) ** 2 for row in rows if row[s])
                        assert used <= weight[v]
            for side, x in enumerate(L):
                pmix[side] += Q(int(weight[s]), k * total) * x * x
        actual = [statistics({0: row}, size) for row in rows]
        I = sum(item[0] for item in actual) / len(rows)
        pool = sum(item[2][1] for item in actual) / len(rows)
        # sqrt(E P2) <= sqrt(P2(mean p)) + sqrt(2I)/ln 2.
        budget = sqrt_bounds(pmix[0])[0] + sqrt_bounds(2 * I)[0] / ln_integer_bounds(2)[1]
        assert pool <= budget**2


def profile_check(a):
    """Compare an individual asymmetric sign to its averaged level profile."""
    n = len(a).bit_length() - 1
    p = a * a
    deg = degrees(n)
    W = [Q(int(p[deg == k].sum()), len(a) ** 2) for k in range(n + 1)]
    I, _, _, mixed = statistics({0: a}, len(a))
    if not I:
        return
    radial = Q(0)
    for k in range(2, n + 1):
        if W[k]:
            ell = logloss((n - k + 1) * W[k - 1] / (k * W[k]))[0]
            radial += k * W[k] * ell**2 / I
    correction = sqrt_bounds(Q(2))[0] / ln_integer_bounds(2)[1]
    assert mixed[1] <= I * (sqrt_bounds(radial)[0] + correction) ** 2


def main():
    assert PI[0] > 3 and PI[1] < Q(22, 7)
    assert sign_kernel(Q(1, 2))[0] <= Q(UNIT, 3) <= sign_kernel(Q(1, 2))[1]
    mixture_check()
    for n, k in ((6, 2), (8, 3), (12, 3), (16, 4), (18, 4)):
        d = degrees(n)
        counts = np.where(d == k - 1, comb(n, k), np.where(d == k, comb(n, k - 1), 0))
        I, H = gaussian_law(counts, k)
        print(
            "Gaussian shells",
            n,
            k,
            "mean influence and entropy of the mean law",
            enclose_text(I, 8),
            enclose_text(H, 8),
        )
        if (n, k) == (6, 2):
            assert I[0] <= 2 <= I[1]
    seed = wht(record_seed())
    profile_check(seed)
    rng = np.random.default_rng(412283)
    for n in (6, 8, 10):
        profile_check(wht(signs(rng.integers(0, 2, 1 << n))))
    I, H = gaussian_law(seed * seed)
    print(
        "Gaussian Numaro variances, mean influence and entropy of the mean law",
        enclose_text(I, 8),
        enclose_text(H, 8),
    )
    counts = np.ones(64, dtype=np.int64)
    counts[0] = 1 << 26
    gaussian_law(counts)
    assert (6 / Q(69, 100) + Q(283, 100)) * PI[1] / 2 < 24
    assert (sqrt_bounds(Q(80))[1] + 2 * sqrt_bounds(Q(2))[1]) ** 2 < 290 * ln_integer_bounds(2)[
        0
    ] ** 2


if __name__ == "__main__":
    main()
