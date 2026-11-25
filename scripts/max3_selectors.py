"""Sparse exact Walsh transform of a bent sign with one selector per even row."""

from fractions import Fraction as Q
from math import comb

import numpy as np

from certificate import enclose_text
from max3_carries import distance, edge_cost, total_grid
from walsh import checked, degrees, signs, wht


def coarse_height(s, N):
    # For a signed parent numerator s and child numerator of magnitude one,
    # strict coarse crossings occur only when s is exactly a grid midpoint.
    h = 2 * (abs(s) & -abs(s))
    return h if 4 < h <= N else 0


def endpoint_cost(n):
    N = 1 << n
    M = N // 2
    root = 1 << (n // 2)
    steps = [1 << j for j in range(3, n + 1)]
    moment = [0] * len(steps)
    weight = 1
    for j in range(M + 1):
        x = 2 * j - M
        for i, step in enumerate(steps):
            moment[i] += weight * (distance(x, step) ** 2 + distance(x + root, step) ** 2)
        weight = weight * (M - j) // (j + 1)
    result = Q(0)
    for step, m in zip(steps, moment):
        cost = Q(M, N) + Q(distance(root, step) ** 2, 2 * N) - Q(m, 2 * N * (1 << M))
        assert cost >= 0
        if step <= root:
            assert Q(1, 2) - Q(step * step, 4 * N) <= cost <= Q(1, 2)
        else:
            assert cost * step**2 <= 11 * N
        result += cost
    assert Q(n, 4) - Q(4, 3) <= result <= Q(n, 4) + Q(8, 3)
    return result


def example(n):
    N = 1 << n
    M = N // 2
    x = np.arange(N)
    b = np.ones(N, dtype=np.int64)
    for i in range(0, n, 2):
        b *= signs((x >> i) & (x >> (i + 1)) & 1)
    outside = wht(b * (x & 1))
    assert np.count_nonzero(outside) == M
    assert set(abs(outside)) == {0, 1 << (n // 2)}
    # Each other nonempty row of the spectrum is a signed point transform.
    point = wht((x == 0).astype(np.int64))
    assert np.all(point == 1)
    data_root = sum(edge_cost(int(s), 1, N)[1] for s in outside)
    assert data_root == Q(1, 1 << (n // 2))
    address = Q(int(np.dot(outside**2, degrees(n))), N * N) + Q(M * n, 2 * N)
    I = 1 + address + Q(M, N)
    assert I == Q(2 * n + 7, 4)
    potential = total_grid(outside) + M * total_grid(point)
    assert potential == Q(3 * n, 4)

    if n <= 4:
        labels = np.arange(1 << M)[:, None]
        tables = np.where(x & 1, b, signs((labels >> (x // 2)) & 1))
        untagged = tables.ravel()
        a = checked(np.concatenate((untagged, -untagged)))
        rows = a[len(untagged) :].reshape(-1, N)
        assert np.array_equal(rows[0], outside * (2 << M))
        for j in range(M):
            assert np.array_equal(rows[1 << j], (2 << M) * wht((x == 2 * j).astype(np.int64)))
        assert total_grid(a) == potential
    if n <= 8:
        # After revealing j selectors in any fixed order, each old Walsh
        # numerator has gained j independent Rademachers. Integrate exactly.
        visiting = Q(0)
        for j in range(M):
            numer = 0
            for k in range(j + 1):
                w = 2 * k - j
                heights = coarse_height(w, N) + coarse_height((1 << (n // 2)) + w, N)
                numer += comb(j, k) * heights
            visiting += Q(numer, 2 * N * (1 << j))
        assert visiting <= potential
        print("all selectors queried in order, n, exact aggregate coarse cost", n, visiting)
    if n <= 12:
        total = endpoint_cost(n)
        if n <= 8:
            assert total == visiting
        print(
            "selector-prefix cost and queried influence",
            n,
            enclose_text((total, total), 8),
            Q(M, N),
        )
    print("core size, I, G, sum of selector coarse costs at root", n, I, potential, M * data_root)


if __name__ == "__main__":
    for n in (4, 6, 8, 12, 16):
        example(n)
