"""Dyadic projection, signed coface matchings, and an odd-numerator two-shell law."""

from collections import Counter
from fractions import Fraction as Q
from math import comb
import random

import numpy as np

from certificate import enclose_text
from max1_pool import logloss
from max3_codes import linear_values, scramble
from walsh import checked, degrees, record_seed, signs, wht


def projection(a):
    N = len(a)
    n = N.bit_length() - 1
    count = Counter(abs(int(x)) for x in a[1:] if x)
    residual = Q(0)
    entropy_half = [Q(0), Q(0)]
    var = Q(0)
    for c, mult in count.items():
        weight = Q(mult * c * c, N * N)
        var += weight
        for side, x in enumerate(logloss(Q(N, c) - 1)):
            entropy_half[side] += weight * x
        for m in range(n):
            step = N >> m
            r = c % step
            residual += Q(mult * min(r, step - r) ** 2, N * N)
    assert entropy_half[1] - var <= residual <= entropy_half[0] + 4 * var / 3
    return residual


def coface_sum(a):
    out = a.copy()
    for j in range(len(a).bit_length() - 1):
        b = out.reshape(-1, 2, 1 << j)
        b[:, 0, :] += b[:, 1, :]
    return out


def has_matching(vertices, adjacency, capacities):
    # Expand integral capacities. Test both ordinary Hall and its length version.
    copies = [s for s in vertices for _ in range(capacities[s])]
    targets = {s: [] for s in vertices}
    for j, s in enumerate(copies):
        targets[s].append(j)
    edges = {s: [j for v in adjacency[s] for j in targets[v]] for s in vertices}
    owner = [None] * len(copies)

    def augment(s, seen):
        for j in edges[s]:
            if j in seen:
                continue
            seen.add(j)
            if owner[j] is None or augment(owner[j], seen):
                owner[j] = s
                return True
        return False

    return all(augment(s, set()) for s in copies)


def signed_test(a):
    N = len(a)
    n = N.bit_length() - 1
    zeta = coface_sum(a)
    depth = {s: n - (abs(int(c)) & -abs(int(c))).bit_length() + 1 for s, c in enumerate(a) if c}
    deg = degrees(n)
    for m in range(n):
        mod = N >> m
        active = [s for s in depth if depth[s] > m]
        neighbors = {s: [v for v in active if int(zeta[s | v]) % mod] for s in active}
        assert all(int(deg[s | v]) >= m + 2 for s in active for v in neighbors[s])
        for cap in ({s: 1 for s in active}, {s: depth[s] - m for s in active}):
            assert has_matching(active, neighbors, cap)
        # Every coordinate flat gives a conditional-variance grid certificate.
        for mask in range(1, N):
            r = int(deg[mask])
            if r != m + 1:
                continue
            cells = Counter()
            for s, z in enumerate(a):
                cells[s & mask] += int(z) ** 2
            for s, z in enumerate(a):
                c = int(z) % mod
                assert cells[s & mask] - int(z) ** 2 >= c * (mod - c)


def odd_shell(k, thin=False, full=False, return_core=False):
    """Choose a signed vector on the balancing-bit slice. Replace pairs of ones
    by 1+b,1-b, changing the squared norm by exactly 2b^2."""
    n = k * k
    sizes = {j: comb(n, j) for j in (k - 1, k)}
    s = 2 * ((sizes[k - 1].bit_length() - 1) // 8) if thin else k.bit_length() - 1
    assert s % 2 == 0 and 0 < s < n - 4
    d = (n + s) // 2
    N = 1 << n
    scale = 1 << d
    target = (scale**2 - N) // 2
    steps = {}
    remaining = 2 * target
    # Start all pairs on the lower power and upgrade as many as fit.
    for j, cnt in sizes.items():
        low = ((target // cnt).bit_length() - 1) // 2
        unit = 1 << low
        highpairs, unused = divmod(target - cnt * unit**2, 6 * unit**2)
        steps[j] = [(unit, cnt // 2 - highpairs), (2 * unit, highpairs)]
        assert cnt % 2 == 0 and unused >= 0
        remaining -= sum(2 * b * b * pairs for b, pairs in steps[j])
    t = min((n - 1) // 2, min(b.bit_length() - 1 for v in steps.values() for b, m in v if m))
    steps[2] = []
    while remaining:
        e = ((remaining // 2).bit_length() - 1) // 2
        assert e >= t
        m, remaining = divmod(remaining, 2 * (1 << (2 * e)))
        steps[2].append((1 << e, m))
    assert 2 * sum(m for _, m in steps[2]) <= comb(n, 2)
    norm = N + sum(2 * m * b * b for v in steps.values() for b, m in v)
    assert norm == scale**2
    mass = {j: Q(comb(n, j) + sum(2 * m * b * b for b, m in v), norm) for j, v in steps.items()}
    beta = Q(N, norm)
    I = (
        1
        + beta * Q(n, 2)
        + sum(j * Q(2 * m * b * b, norm) for j, v in steps.items() for b, m in v)
    )
    parents = min(abs(1 - b) for b, m in steps[k - 1] if m)
    children = max(1 + b for b, m in steps[k] if m)
    min_odds = Q(parents, children) ** 2
    assert min_odds >= Q(n - k + 1, 144 * k)
    max_amp = max(1 + b for v in steps.values() for b, m in v if m)
    assert Q(max_amp, scale) <= beta / 2
    ell = logloss(min_odds)[0]
    B = k * mass[k] * ell / I
    X = Q(k * (k - 1), k + 1) * mass[k] * ell**2 / I
    if full:
        a = np.ones(N, dtype=np.int64)
        for j, v in steps.items():
            places = np.flatnonzero(degrees(n) == j)
            ptr = 0
            for b, m in v:
                a[places[ptr : ptr + m]] += b
                a[places[ptr + m : ptr + 2 * m]] -= b
                ptr += 2 * m
        assert np.all((a - 1) % (1 << t) == 0) and np.dot(a, a) == norm
        # Check every standard coface in the advertised signed range.
        z = coface_sum(a)
        for r in range(d - t + 1, d + 1):
            assert np.all(z[degrees(n) == r] % (1 << (d + 1 - r)) == 0)
        rng = random.Random(412314)
        for r in range(1, d + 1):
            for codim in (r, r - 1):  # rank on the tagged support
                for trial in range(2):
                    coordinates = scramble(n, n, rng)
                    labels = linear_values(coordinates) % (1 << codim)
                    sums = np.zeros(1 << codim, dtype=np.int64)
                    energies = sums.copy()
                    np.add.at(sums, labels, a)
                    np.add.at(energies, labels, a * a)
                    step = 1 << (d + 1 - r)
                    residue = a % step
                    assert np.all(energies[labels] - a * a >= residue * (step - residue))
                    if r >= d - t + 1:
                        assert np.all(sums % step == 0)
        idx = np.arange(N)
        assert np.all((idx | (idx ^ (N - 1))) == N - 1) and int(a[-1]) % 2
        assert z[-1] == 1 and int(a.sum()) == N
        real = wht(a)
        assert np.array_equal(wht(real), N * a) and not np.all(abs(real) == scale)
        # WHT-calculated per-edge lower bounds in the true probability laws.
        for v in np.flatnonzero(degrees(n) == k):
            for j in range(n):
                if int(v) & (1 << j):
                    assert Q(int(a[int(v) ^ (1 << j)]), int(a[v])) ** 2 >= min_odds
        if return_core:
            return a, d, t
    return s, d - t + 1, B, X


def majority_obstruction(n):
    b = (n - 1) // 2
    c = Q(comb(2 * b, b), 1 << (2 * b))
    m = 0
    while c <= Q(1, 1 << (m + 2)):
        m += 1
    assert c <= Q(1, 1 << (m + 1)) and n * c * c > Q(1, 2)
    if n <= 15:
        sign = signs(degrees(n) > b)
        a = checked(np.concatenate((sign, -sign)))
        assert max(map(abs, a)) == len(a) * c
        assert Q(int((a[degrees(n + 1) == 2] ** 2).sum()), len(a) ** 2) == n * c * c
    return m, n * c * c


def main():
    rng = np.random.default_rng(412302)
    for code in range(256):
        a = checked(signs((code >> np.arange(8)) & 1))
        signed_test(a)
        projection(a)
    for n, count in ((4, 30), (5, 12), (6, 4)):
        for _ in range(count):
            a = checked(signs(rng.integers(0, 2, 1 << n)))
            signed_test(a)
            projection(a)
    print(
        "Numaro nonconstant squared grid residual sum",
        enclose_text((projection(wht(record_seed())),) * 2, 10),
    )
    for n in (7, 15, 255, 4095):
        m, mass = majority_obstruction(n)
        print("tagged majority, n, scale, degree-two mass", n, m, enclose_text((mass, mass), 8))
    for k in (4, 16, 64, 256):
        for thin in (False, True):
            if thin and k == 4:
                continue
            s, r, b, x = odd_shell(k, thin, full=k == 4)
            print(
                "odd shell, k, floor exponent, first automatic codimension, lower B,X/I",
                k,
                s,
                r,
                enclose_text((b, b), 6),
                enclose_text((x, x), 6),
            )


if __name__ == "__main__":
    main()
