"""Branching-normalized low-degree and shifted-character tests (integer WHT)."""

from collections import Counter
from fractions import Fraction as Q
from math import comb, isqrt

import numpy as np

from certificate import enclose_text
from experiments import block_comp, tribes
from max1_pool import ln_integer_bounds, logloss, switch
from walsh import degrees, record_seed, signs, splits, wht


def fourth_root_up(num, den):
    scaled = num << 256
    a = isqrt(isqrt(scaled // den))
    return a + (a**4 * den != scaled)


def level_test(f, verify_shifts=True):
    a = wht(f)
    n = len(a).bit_length() - 1
    size = len(a)
    scale = size**2
    assert not a[0]
    deg = degrees(n)
    p = a * a
    I = Q(int(np.sum(p * deg)), scale)
    W1 = Q(int(p[deg == 1].sum()), scale)
    W2 = Q(int(p[deg == 2].sum()), scale)
    db = I - W1
    epsilon = 1 - W1
    pmax = Q(int(p[deg == 1].max()), scale)
    delta = Q(size - int(np.abs(a[deg == 1]).max()), 2 * size)
    cross = (W1**2 - sum(Q(int(z), scale) ** 2 for z in p[deg == 1])) / 2
    assert 4 * cross <= 39 * epsilon
    if W1 >= Q(1, 2):
        assert pmax >= 1 - 40 * epsilon and delta <= 20 * epsilon
    assert W2**3 <= 32**3 * delta**4
    dsum = heavy_num = Q(0)
    first2 = [Q(0), Q(0)]
    low_deg = degrees(n - 1)
    for i in range(n):
        u, v = splits(a, i)
        u, v = u[1:], v[1:]  # T is nonempty
        delta = Q(int(np.dot(v, v)), scale)
        dsum += delta
        assert Q(int(np.max(np.abs(v), initial=0)), size) <= 2 * delta
        down = low_deg[1:]
        energy = Q(int(np.sum(v * v * np.left_shift(1, n - 1 - down))), scale * (1 << (n - 1)))
        assert energy**3 <= (2 * delta) ** 4
        # Fourth-root form of tilted Holder, with the empty child removed.
        nz = np.flatnonzero(v)
        types = Counter(zip(map(int, np.abs(v[nz])), map(int, np.abs(u[nz])), map(int, down[nz])))
        total = 0
        for (b, c, k), mult in types.items():
            total += mult * fourth_root_up(b**6 * (b * b + c * c), 1 << (3 * k))
            if k == 1 or 4 * c > size:
                lo, hi = logloss(Q(c * c, b * b))
                if k == 1:
                    first2[0] += Q(mult * b * b, scale) * lo
                    first2[1] += Q(mult * b * b, scale) * hi
                if 4 * c > size:
                    heavy_num += Q(mult * b * b, scale) * hi
        assert Q(total, scale * (1 << 64)) <= 2 * delta
    assert dsum == db
    if db:
        assert first2[1] <= (7 + 4 / ln_integer_bounds(2)[1]) * db
        assert heavy_num <= 8 * db / ln_integer_bounds(2)[1]
    if verify_shifts:
        neigh = np.zeros_like(p)
        ids = np.arange(size)
        for t in (1, size // 3, size - 1):
            shifted = wht(f * signs(deg[ids & t] % 2))
            assert np.array_equal(shifted, a[ids ^ t])
            for i in range(n):
                present = (ids & (1 << i)) != 0
                weight = int(p[present].sum())
                shifted_weight = int(np.dot(shifted[present], shifted[present]))
                assert shifted_weight == (scale - weight if t & (1 << i) else weight)
        for i in range(n):
            neigh += p[ids ^ (1 << i)]
        maxima = {}
        for c, v in zip(np.abs(a), neigh):
            c = int(c)
            maxima[c] = max(maxima.get(c, 0), int(v))
        for c, v in maxima.items():
            delta = Q(size - c, 2 * size)
            if not delta:
                assert not v
                continue
            ln = ln_integer_bounds(delta.denominator)[0] - ln_integer_bounds(delta.numerator)[1]
            assert Q(v, scale) <= 8 * delta**2 * ln
    if not db:
        return I, W1, W2, (Q(0), Q(0))
    return I, W1, W2, tuple(v / db for v in first2)


def near_dictator(n):
    # Flip both signs of a dictator at the same address of every other bit.
    x = np.arange(1 << n)
    return signs(x & 1) * np.where((x >> 1) == 0, -1, 1)


def tied_majority(n, kind):
    # Balanced perturbation of the zero slice of even majority. Pairing antipodes
    # would make every even coefficient vanish; use a balanced slice cut instead.
    assert n % 2 == 0
    x = np.arange(1 << n)
    f = signs(degrees(n) > n // 2)
    tie = np.flatnonzero(degrees(n) == n // 2)
    if kind == "lex":
        # Order by a nonlinear, reproducible involution-free permutation key.
        tie = tie[np.argsort((tie * 137 + 19) % (1 << n))]
    else:
        tie = np.random.default_rng(n + 412).permutation(tie)
    f[tie[: len(tie) // 2]] = -1
    return f


def balanced_biased_majority(n):
    # Two permutation-symmetric signal gates of opposite bias, deliberately
    # non-antipodal after a sign change in one branch.
    d = degrees(n)
    f = signs(d >= n // 2 + 1)
    x = np.arange(1 << n)
    return np.concatenate((f, -f[x ^ 1]))


def shell_model(n, k):
    # Two adjacent flat levels. It is a non-Boolean probability law, with a
    # positive WHT square root as explicit normalized real function coefficients.
    p = {j: Q(1, 2 * comb(n, j)) for j in (k - 1, k)}
    D = Q(2 * k - 1, 2)
    incidence = Q(2 * k - 1, 2 * n)
    b = tuple(Q(k, 2) * v / D for v in logloss(p[k - 1] / p[k]))
    x = tuple(Q(k - 1, 2) * v * v / D for v in logloss(p[k - 1] / p[k]))
    # All shifts have a vacuous Chang bound, even though adjacent loss grows.
    assert max(p.values()) <= Q(1, 16) and max(p.values()) <= (2 * incidence) ** 2
    # Exact row test of the centered derivative HC at the origin.
    e = sum(Q(j, 2 * n * 2 ** (j - 1)) for j in (k - 1, k))
    assert e**3 <= (2 * incidence) ** 4
    return b, x


def shell_rounding(n, k, mode):
    deg = degrees(n)
    size = 1 << n
    parents, children = comb(n, k - 1), comb(n, k)
    # The exact covariance kernel of the equal-energy Gaussian ensemble.
    variances = np.where(deg == k - 1, children, np.where(deg == k, parents, 0))
    cov = wht(variances)
    tau = Q(2 * k - 1, 2 * n)
    assert int(cov[0]) == 2 * parents * children
    assert all(Q(int(v), int(cov[0])) == 1 - 2 * tau for v in cov[deg == 1])

    rng = np.random.default_rng(41235 + n + k)
    # Integer amplitudes approximate the ideal shell ratio before sign rounding.
    h = np.where(deg == k - 1, isqrt(64**2 * children // parents), np.where(deg == k, 64, 0))
    if mode == "independent":
        h = h * rng.choice([-1, 1], size=size)
    elif mode == "quadratic":
        idx = np.arange(size)
        for i, j in zip(range(0, n - 1, 2), range(1, n, 2)):
            h = h * signs((idx >> i) & (idx >> j) & 1)
    rounded = signs(wht(h) < 0)
    a = wht(rounded)
    p = a * a
    if n <= 12:
        # Balancing by a fresh sign preserves all data losses.
        whole = wht(np.concatenate((rounded, -rounded)))
        assert not np.any(whole[:size]) and np.array_equal(whole[size:], 2 * a)
    I = 1 + Q(int(np.dot(deg, p)), size**2)
    db = I - Q(int(p[0]), size**2)
    wk = Q(int(p[deg == k].sum()), size**2)
    wparent = Q(int(p[deg == k - 1].sum()), size**2)
    pairs = Counter()
    for s in np.flatnonzero((deg == k) & (p > 0)).tolist():
        for j in range(n):
            if s & (1 << j):
                pairs[int(p[s]), int(p[s ^ (1 << j)])] += 1
    raw = [Q(0), Q(0)]
    for (child, parent), count in pairs.items():
        for side, loss in enumerate(logloss(Q(parent, child))):
            raw[side] += Q(count * child, size**2) * loss
    if wk:
        mean_odds = (n - k + 1) * wparent / (k * wk)
        if raw[1] > k * wk * logloss(mean_odds)[0]:
            assert all(Q(parent, child) == mean_odds for child, parent in pairs)
    print(
        "rounded shells, n,k,phases,I,original k-level B contribution",
        n,
        k,
        mode,
        I,
        enclose_text(tuple(v / db for v in raw), 6),
    )


def exact_rounding_mean(n, k):
    # Independent random phases in an integer two-shell polynomial. Enumerate
    # all rounded Boolean tables, then compute the same mean from one edge.
    deg = degrees(n)
    modes = np.flatnonzero((deg == k - 1) | (deg == k))
    num = len(modes)
    weights = np.where(deg[modes] == k - 1, 2, 1)
    ids = np.arange(1 << num)
    phases = signs((ids[:, None] >> np.arange(num)) & 1)
    poly = np.zeros((len(ids), 1 << n), dtype=np.int64)
    poly[:, modes] = phases * weights
    a = wht(signs(wht(poly) < 0))
    exact = Q(int(np.sum(a * a * deg)), len(ids) * (1 << (2 * n)))

    def sum_law(weights):
        law = Counter({0: 1})
        for value in weights:
            nxt = Counter()
            for x, mass in law.items():
                nxt[x - int(value)] += mass
                nxt[x + int(value)] += mass
            law = nxt
        return law

    common = sum_law(weights[(modes & 1) == 0])
    reversed_terms = sum_law(weights[(modes & 1) == 1])
    changes = sum(
        cx * cy
        for x, cx in common.items()
        for y, cy in reversed_terms.items()
        if (x + y < 0) != (x - y < 0)
    )
    assert exact == Q(n * changes, len(ids))
    print("all integer sign roundings, n,k,count, mean original influence", n, k, len(ids), exact)


def main():
    for n in (6, 10, 14, 18):
        for label, f in [
            ("one-address flip", near_dictator(n)),
            ("tie cut", tied_majority(n, "lex")),
            ("random tie cut", tied_majority(n, "random")),
        ]:
            i, w1, w2, b2 = level_test(f)
            print(
                label,
                n,
                "I, W2, 2W2/db, B2",
                i,
                w2,
                enclose_text((2 * w2 / (i - w1),) * 2, 6),
                enclose_text(b2, 6),
            )
    for f in (
        record_seed(),
        switch(6),
        balanced_biased_majority(13),
        np.kron([-1, 1], block_comp(tribes([1, 2]), tribes([2, 2]))),
    ):
        level_test(f)
    for n in (8, 16, 32, 64, 128):
        N = 1 << n
        # Use k=n in ambient dimension 2^n. No truth-table materialization.
        b, x = shell_model(N, n)
        print(
            "non-Boolean two-shell log2(n),k,B,X/I", n, n, enclose_text(b, 6), enclose_text(x, 6)
        )
    for n, k in ((3, 2), (4, 2), (4, 3)):
        exact_rounding_mean(n, k)
    for n, k in ((8, 2), (12, 3), (16, 4), (18, 2), (18, 4)):
        for mode in ("constant", "quadratic", "independent"):
            shell_rounding(n, k, mode)


if __name__ == "__main__":
    main()
