"""Exhaust the 65535 nonempty events on a 4-by-4 Boolean cube.

For each exact normalized Gram spectrum only the smallest boundary can
maximize the event surplus. Descartes isolation and rational logs enclose
every retained spectrum. This enumeration is for the seed, before guards.
"""

from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product

import numpy as np
from certificate import enclose_text, log2_int
from max4_rank import eig_entropy, eig_intervals
from max4_reserve import entropy_counts
from walsh import degrees, wht


def main():
    grouped = {}
    for start in range(1, 65536, 512):
        ids = np.arange(start, min(start + 512, 65536))
        events = ((ids[:, None] >> np.arange(16)) & 1).reshape(-1, 4, 4)
        grams = events @ events.transpose(0, 2, 1)
        norms = events.sum(axis=(1, 2))
        boundary = np.zeros_like(norms)
        for i in (1, 2):
            boundary += (events != events[:, np.arange(4) ^ i, :]).sum(axis=(1, 2))
            boundary += (events != events[:, :, np.arange(4) ^ i]).sum(axis=(1, 2))
        a = wht((1 - 2 * events).reshape(-1, 16))
        assert np.array_equal((a * a) @ degrees(4), 16 * boundary)
        p = grams
        traces = []
        for j in range(4):
            traces.append(p.trace(axis1=1, axis2=2))
            if j < 3:
                p = p @ grams
        for pos, signature in enumerate(zip(*traces)):
            key = tuple(int(z) for z in signature)
            cost = int(boundary[pos])
            if key not in grouped or cost < grouped[key][0]:
                grouped[key] = cost, int(ids[pos]), grams[pos].copy()
    maxima = {}
    multiplicities = Counter()
    for key, (boundary, mask, gram) in grouped.items():
        mass = key[0]
        mu = Q(mass, 16)
        boxes = eig_intervals(gram, mass, 65)
        rank = len(boxes)
        H = eig_entropy(boxes)
        correction = entropy_counts([mu])
        out = tuple(H[j] + correction[j] / mu - Q(boundary, 2 * mass) for j in (0, 1))
        old = maxima.get(rank, ((-20, -20), None))
        maxima[rank] = (max(old[0][0], out[0]), max(old[0][1], out[1])), (
            mask if out[0] > old[0][0] else old[1]
        )
        multiplicities[rank] += 1
    print("nonempty event tables", 65535, "spectral signatures", len(grouped))
    for rank, (bounds, mask) in sorted(maxima.items()):
        print(
            "event rank",
            rank,
            "signatures",
            multiplicities[rank],
            "maximum surplus",
            enclose_text(bounds, 10),
            "witness",
            mask,
        )
    assert maxima[3][0][1] < Q(500001, 1000000) and maxima[4][0][0] > Q(5968, 10000)


@lru_cache(None)
def rare_entropy(x):
    u = min(x, 1 - x)
    return entropy_counts([u]) if u else (Q(0), Q(0))


def weighted_entropy(m):
    # The Schmidt entropy of the event and its classical coordinate information.
    event = m.sum()
    row = m.sum(axis=1)
    col = m.sum(axis=0)
    S = eig_entropy(eig_intervals(m @ m.T, int(event), 68))
    Hrow = entropy_counts(Q(int(v), int(event)) for v in row)
    Hcol = entropy_counts(Q(int(v), int(event)) for v in col)
    Hjoint = log2_int(int(event))
    return (S[0] - Hrow[1] - Hcol[1] + Hjoint[0], S[1] - Hrow[0] - Hcol[0] + Hjoint[1])


def two_label_gap():
    # Two five-point slices with three common points realize z=3/5 exactly.
    m = np.array(
        [[int(i < 5) for i in range(8)], [int(2 <= i < 7) for i in range(8)]], dtype=np.int64
    )
    for masks in product(range(1, 16), repeat=2):
        E = np.array([[(z >> j) & 1 for j in range(4)] for z in masks])
        bounds = weighted_entropy(E)
        assert bounds[1] < log2_int(5)[0] - 2
    w = weighted_entropy(m)
    assert max(w[0], log2_int(5)[0] - 2) <= min(w[1], log2_int(5)[1] - 2)
    print("sharp two-label information gap", enclose_text(w, 12))


def rank_three_grid(D=8):
    # The canonical four projective row types against three column labels.
    A = np.ones((4, 3), dtype=object)
    for i in range(3):
        A[i + 1, i] = -1
    best = Q(0)
    count = 0
    for p0, p1, p2 in product(range(D + 1), repeat=3):
        p3 = D - p0 - p1 - p2
        # Change the reference row type and simultaneously permute the three labels.
        if not p0 >= p1 >= p2 >= p3 >= 0:
            continue
        p = np.array([p0, p1, p2, p3], dtype=object)
        u = [Q(D - p0 - v, D) for v in (p1, p2, p3)]
        d = [min(w, 1 - w) for w in u]
        beta = [sum(d) / 2 - v for v in d]
        for q0, q1 in product(range(D + 1), repeat=2):
            q2 = D - q0 - q1
            if q2 < 0:
                continue
            qs = np.array([q0, q1, q2], dtype=object)
            q = [Q(v, D) for v in (q0, q1, q2)]
            c = [min(v, 1 - v) for v in q]
            alpha = [sum(c) / 2 - v for v in c]
            assert min(alpha + beta) >= 0
            lower = 2 * sum(
                a * rare_entropy(v)[0] + b * rare_entropy(w)[0]
                for a, b, v, w in zip(alpha, beta, u, q)
            )
            gram = ((A.T * p) @ A) * qs
            boxes = eig_intervals(gram, D * D, 60)
            if len(boxes) <= 1:
                continue
            S = eig_entropy(boxes)
            assert S[1] < 2 * lower
            best = max(best, S[1] / lower)
            count += 1
    print(
        "three-column scalar test, denominator",
        D,
        "nontrivial oriented models",
        count,
        "upper bound for this mesh",
        enclose_text((best, best), 8),
    )


def subcube_rows(n):
    """Rank-three 4 by 2^n indicators all of whose row supports are subcubes."""
    size = 1 << n
    cubes = [0]
    for pattern in product((-1, 0, 1), repeat=n):
        cubes.append(
            sum(
                1 << v
                for v in range(size)
                if all(bit == -1 or (v >> j) & 1 == bit for j, bit in enumerate(pattern))
            )
        )
    pop = lambda z: bin(z).count("1")
    candidates = len(cubes)
    sizes = np.array([pop(r) for r in cubes])
    overlaps = np.array([[pop(r & s) for s in cubes] for r in cubes])
    yboundary = np.array(
        [0 if m == 0 else 2 * int(m) * (n - int(m).bit_length() + 1) for m in sizes]
    )
    best_by_spectrum = {}
    count = 0
    # Put an independent triple in rows 0,1,2 by an X translation, then
    # normalize row 0 by isometries of Y. Both operations preserve boundary.
    for k in range(n + 1):
        ia = cubes.index((1 << (1 << k)) - 1)
        for ib, ic in product(range(candidates), repeat=2):
            ids = [ia, ib, ic]
            triple = overlaps[np.ix_(ids, ids)]
            p, q, r = triple[0]
            _, s, t = triple[1]
            _, _, u = triple[2]
            adj = np.array(
                [
                    [s * u - t * t, r * t - q * u, q * t - r * s],
                    [r * t - q * u, p * u - r * r, q * r - p * t],
                    [q * t - r * s, q * r - p * t, p * s - q * q],
                ]
            )
            det = int(triple[0] @ adj[:, 0])
            if det == 0:
                continue
            rows = overlaps[:, ids]
            ds = np.flatnonzero(np.sum((rows @ adj) * rows, axis=1) == sizes * det)
            matrices = np.zeros((len(ds), 4, 4), dtype=np.int64)
            matrices[:, :3, :3] = triple
            matrices[:, 3, 3] = sizes[ds]
            matrices[:, 3, :3] = rows[ds]
            matrices[:, :3, 3] = rows[ds]
            norms = sizes[ids].sum() + sizes[ds]
            squares = matrices @ matrices
            sig2 = squares.trace(axis1=1, axis2=2)
            sig3 = (squares @ matrices).trace(axis1=1, axis2=2)
            # At rank three the first three traces determine the spectrum.
            shellcost = yboundary[ids].sum() + yboundary[ds]
            native = 4 * norms - 4 * (
                overlaps[ia, ib] + overlaps[ia, ic] + overlaps[ib, ds] + overlaps[ic, ds]
            )
            for j, (key, bd) in enumerate(zip(zip(norms, sig2, sig3), native + shellcost)):
                if key not in best_by_spectrum or bd < best_by_spectrum[key][0]:
                    best_by_spectrum[key] = (int(bd), matrices[j].copy())
            count += len(ds)
    maximum = Q(-1)
    for (mass, _, _), (bd, gram) in best_by_spectrum.items():
        mu = Q(int(mass), 4 * size)
        S = eig_entropy(eig_intervals(gram, int(mass), 55))
        upper = S[1] + entropy_counts([mu])[1] / mu - Q(bd, 2 * int(mass))
        maximum = max(upper, maximum)
    assert maximum < Q(500001, 1000000)
    print(
        "subcube rows, Y bits",
        n,
        "tested",
        count,
        "surplus upper",
        enclose_text((maximum, maximum), 9),
    )


if __name__ == "__main__":
    main()
    two_label_gap()
    rank_three_grid()
    subcube_rows(3)
    subcube_rows(4)
