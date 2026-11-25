"""Frequency-side affine certificates for nonplateaued phase signings."""

from fractions import Fraction as Q
from math import comb
import random

import numpy as np
from certificate import enclose_text
from max3_codes import entropy
from max3_phases import metrics
from walsh import checked, degrees, signs, wht


def floor_vector(k=4):
    n = k * k
    N = 1 << n
    d = (n + k.bit_length() - 1) // 2
    goal = ((1 << (2 * d)) - N) // 2
    left = 2 * goal
    A = np.ones(N, dtype=np.int64)
    for j in (k - 1, k):
        idx = np.flatnonzero(degrees(n) == j)
        u = 1 << (((goal // len(idx)).bit_length() - 1) // 2)
        more = (goal - len(idx) * u * u) // (6 * u * u)
        p = 0
        for v, num in ((u, len(idx) // 2 - more), (2 * u, more)):
            A[idx[p : p + num]] += v
            A[idx[p + num : p + 2 * num]] -= v
            left -= 2 * num * v * v
            p += 2 * num
    idx = np.flatnonzero(degrees(n) == 2)
    p = 0
    while left:
        v = 1 << (((left // 2).bit_length() - 1) // 2)
        num, left = divmod(left, 2 * v * v)
        A[idx[p : p + num]] += v
        A[idx[p + num : p + 2 * num]] -= v
        p += 2 * num
    assert np.dot(A, A) == 1 << (2 * d)
    return A, d


def test_phase(A, d, k, a, kind, rng):
    n = len(A).bit_length() - 1
    b = n - a
    v = np.arange(1 << b)
    z = np.arange(1 << a)
    parity = degrees(b) % 2
    component = parity[v & int("10110", 2)]
    labels = np.array(rng.choices(range(1 << a), k=len(v)), dtype=np.int64)
    checks = []
    if kind == "linear component":
        labels = (labels & ~1) | component
        checks = [int("10110", 2)]
    elif kind == "nonlinear component":
        forms = [int("10110", 2), int("100101", 2)]
        labels = (labels & ~1) | (parity[v & forms[0]] * parity[v & forms[1]])
        checks = forms
    # One odd fiber suffices for Walsh gcd exactly 2^a, regardless of h.
    assert any(sum(labels == j) % 2 for j in z)
    hv = signs(rng.choices((0, 1), k=len(v)))
    phase = (hv[None, :] * signs(degrees(a)[z[:, None] & labels[None, :]] % 2)).ravel()
    dual = checked(phase)
    val = int(np.gcd.reduce(abs(dual)))
    expected = 1 << a
    assert val == expected
    signed = phase * A
    inv = wht(signed)
    assert sum(int(x) ** 2 for x in inv) == len(A) * (1 << (2 * d))
    assert min(abs(dual[dual != 0])) != max(abs(dual))  # genuinely nonplateaued
    # For fixed physical x_a, partial WHT of the bare floor.
    partial = wht(phase.reshape(1 << a, -1).T).T
    for j in z:
        assert np.array_equal(partial[j], np.where(labels == j, (1 << a) * hv, 0))
    upper = np.flatnonzero(degrees(b) == k)
    if checks:
        R = int(upper[0])
        region = np.ones(len(v), dtype=bool)
        for mask in checks:
            region &= parity[v & mask] == parity[R & mask]
        target = int((labels[R] & 1) ^ 1)
        assert np.all((labels[region] & 1) != target)
        residual = wht(((A - 1) * phase).reshape(1 << a, -1).T).T[target]
        assert abs(int(residual[R])) == abs(int(A[R]) - 1)
        small = abs(Q(int(residual[R]), 1 << d))
        assert 0 < small < Q(1, 1 << (k + len(checks) - 1))
        # Filter in b-frequency, then sum the R derivative on each physical face.
        partial_true = wht(signed.reshape(1 << a, -1).T).T[target]
        filtered = np.where(region, partial_true, 0)
        assert not np.any(filtered[((v & R) == R) & (v != R)])
        assert int(filtered[R]) == int(residual[R])
    assert max(abs(inv)) > 1 << d
    fourth = Q(sum((int(x) ** 2 - (1 << (2 * d))) ** 2 for x in inv), len(inv) * (1 << (4 * d)))
    # Project once to a genuine sign and measure its entropy in the tagged presentation.
    boolean = checked(signs(inv < 0))
    I, B = metrics(boolean)
    h = tuple(t / I for t in entropy(boolean))
    print(
        "phase",
        a,
        kind,
        "gcd valuation",
        a,
        "relative fourth-moment defect",
        enclose_text((fourth, fourth), 6),
        "projected tagged H/I",
        enclose_text(h, 7),
        "B",
        B,
    )


def main():
    A, d = floor_vector()
    rng = random.Random(412413)
    for a in (3, 4, 5, 6):
        for kind in ("linear component", "nonlinear component", "unconstrained"):
            test_phase(A, d, 4, a, kind, rng)
    for k in (4, 16, 64, 256):
        n = k * k
        d = (n + k.bit_length() - 1) // 2
        goal = ((1 << (2 * d)) - (1 << n)) // 2
        unit_log = ((goal // comb(n, k)).bit_length() - 1) // 2
        print(
            "k, forbidden affine certificate codimension (uniform for upper corrections)",
            k,
            d - k - unit_log - 1,
        )


if __name__ == "__main__":
    main()
