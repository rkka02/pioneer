"""Fixed-error Frobenius rank, common measurement bases, and coded phase features."""

from collections import Counter
from fractions import Fraction as Q
from math import comb
import random
import numpy as np
from certificate import enclose_text
from max1_pool import logloss
from max4_reserve import entropy_counts
from walsh import checked, degrees, record_seed, signs, wht


def eig_intervals(gram, den, bits=48):
    # Faddeev--LeVerrier on the exact integer Gram matrix, then Descartes'
    # rule on its translated real-rooted polynomial. All multiplicities count.
    G = gram.astype(object)
    dim = len(G)
    ident = np.eye(dim, dtype=object)
    A = ident.copy()
    descending = [1]
    for j in range(1, dim + 1):
        A = G @ A
        neg = -int(A.trace())
        assert neg % j == 0
        c = neg // j
        descending.append(c)
        A += c * ident
    assert not A.any()
    coeff = descending[::-1]
    precision = 1 << bits

    def above(point):
        if point == 0:
            poly = coeff
        else:
            # Coefficients of P((point*den/precision)+X), multiplied by
            # positive denominators per coefficient so signs are exact.
            p = point * den
            poly = [
                sum(
                    coeff[j] * comb(j, i) * p ** (j - i) * precision ** (dim - j)
                    for j in range(i, dim + 1)
                )
                for i in range(dim + 1)
            ]
        vals = [1 if c > 0 else -1 for c in poly if c]
        return sum(z != w for z, w in zip(vals, vals[1:]))

    boxes = []
    for j in range(1, above(0) + 1):
        lo, hi = 0, precision
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if above(mid) >= j:
                lo = mid
            else:
                hi = mid
        boxes.append((Q(lo, precision), Q(hi, precision)))
    assert sum(a for a, b in boxes) <= 1 <= sum(b for a, b in boxes)
    return boxes


def eig_entropy(boxes):
    lo = hi = Q(0)
    for a, b in boxes:
        assert a > 0
        lo += a * logloss(1 / b - 1)[0]
        hi += b * logloss(1 / a - 1)[1]
    return lo, hi


def rank_examples():
    h = signs(np.arange(8) == 7)
    a = checked(h)
    xor = h[np.bitwise_xor.outer(np.arange(8), np.arange(8))]
    transformed = wht(wht(xor).T).T
    assert np.array_equal(transformed, np.diag(len(a) * a))
    for m in (1, 8, 64, 256):
        threshold = 3 * 16**m // 4
        left = threshold
        rank = 0
        for k in range(m + 1):
            mass = 9 ** (m - k)
            count = comb(m, k) * 7**k
            take = min(count, (left + mass - 1) // mass)
            rank += take
            left -= take * mass
            if left <= 0:
                break
        rate = tuple(v / m for v in logloss(Q(rank - 1)))
        print("XOR tensor", m, "log2 r_1/4 per copy", enclose_text(rate, 8))
    print("limit", enclose_text(entropy_counts(Q(int(x * x), 64) for x in a), 8))


def extremal_seed_split():
    # New quantities on the published 18-bit seed: simultaneous grid and Schmidt checks.
    # Four core bits index columns in this split. Integer Gram entries and the Walsh
    # spectrum are obtained independently from the physical truth table.
    f = record_seed()
    table = f.reshape(-1, 16)
    gram = table.T @ table
    boxes = eig_intervals(gram, f.size)
    ev = eig_entropy(boxes)
    a = checked(f)
    hist = Counter(abs(int(x)) for x in a)
    H = entropy_counts(Q(int(z * z), len(a) ** 2) for z in a)
    g = Q(0)
    for c, m in hist.items():
        for j in range(1, 19):
            h = 1 << j
            r = min(c % h, (-c) % h)
            g += Q(m * r * r, len(a) ** 2)
    I = Q(int(np.dot(degrees(18), a * a)), len(a) ** 2)
    assert H[1] / 2 - 2 * I <= g <= H[0] / 2 and ev[1] <= H[0]
    captured = Q(0)
    for i, (l, u) in enumerate(boxes):
        if captured + l >= Q(3, 4):
            assert sum(v for _, v in boxes[:i]) < Q(3, 4)
            print(
                "18-bit seed, four core bits, rank at 1/4",
                i + 1,
                "Schmidt entropy",
                enclose_text(ev, 8),
                "G",
                g,
            )
            break
        captured += l
    else:
        raise AssertionError("missing rank bracket")


def arbitrary_basis():
    rng = random.Random(412420)
    for _ in range(8):
        X = Y = 8
        f = signs(rng.choices((0, 1), k=X * Y)).reshape(Y, X)
        a = checked(f.ravel())
        gram = f @ f.T
        se = eig_entropy(eig_intervals(gram, f.size))
        assert se[0] <= entropy_counts(Q(int(z * z), f.size**2) for z in a)[1]
        direction = np.array(rng.choices((1, 2, -1), k=X))
        den = int(direction @ direction)
        transform = den * np.eye(X, dtype=np.int64) - 2 * np.outer(direction, direction)
        assert np.array_equal(transform @ transform, den**2 * np.eye(X, dtype=np.int64))
        numer = (f @ transform) ** 2
        cond = sum(entropy_counts(Q(int(z), X * den**2) for z in row)[1] for row in numer) / Y
        H = entropy_counts(Q(int(z), X * Y * den**2) for z in numer.sum(axis=0))
        iy = Q(0)
        for j in range(3):
            d = np.count_nonzero(f != f[np.arange(Y) ^ (1 << j)], axis=1)
            iy += Q(int(np.minimum(d, X - d).sum()), X * Y)
        assert se[1] <= H[0] and H[1] <= cond + 3 * iy
    print("arbitrary rational orthogonal measurement, projective edge estimate passed")


def coded_features():
    rng = random.Random(412416)
    for case in range(8):
        widths = (2, 3, 1)
        E = [np.array(rng.sample(range(1 << b), m)) for b, m in zip(widths, (1, 2 + case % 2, 1))]
        x = np.arange(1 << sum(widths))
        feat = [np.isin((x >> sum(widths[:i])) % (1 << b), E[i]) for i, b in enumerate(widths)]
        bits = np.arange(8)
        words = (
            np.array([0, 7, 3, 0, 5, 6, 0, 7])
            if case == 0
            else np.array(rng.choices(range(8), k=len(bits)))
        )
        if case == 0:
            words = np.array([0, 0, 0, 0, 7, 7, 7, 7])  # simultaneous changes in all features
        # Orient each B_j to density at most 1/2; absorb complements into row phase.
        for j in range(len(widths)):
            if np.count_nonzero(words & (1 << j)) > len(words) // 2:
                words ^= 1 << j
        sx = signs(rng.choices((0, 1), k=len(x))) if case % 3 == 1 else np.ones_like(x)
        sy = signs(rng.choices((0, 1), k=len(bits)))
        f = np.tile(sx, (len(bits), 1)) * sy[:, None]
        mark = np.zeros((len(bits), len(widths)), dtype=bool)
        for j, B in enumerate(feat):
            mark[:, j] = (words & (1 << j)) != 0
            f *= signs(mark[:, j, None] & B[None, :])
        a = checked(f.ravel()).reshape(f.shape)
        Ix = Q(int((a * a @ degrees(sum(widths))).sum()), a.size**2)
        Iy = Q(int((degrees(3) @ (a * a)).sum()), a.size**2)
        iy_proj = Q(0)
        for j in range(3):
            d = np.count_nonzero(f != f[bits ^ (1 << j)], axis=1)
            iy_proj += Q(int(np.minimum(d, len(x) - d).sum()), f.size)
        assert iy_proj <= Iy
        gram = f @ f.T
        boxes = eig_intervals(gram, f.size)
        sh = eig_entropy(boxes)
        # Compressed column Gram has the same nonzero spectrum. Computing
        # it also tests phases and all correlations in the shared label map.
        mu = [Q(len(s), 1 << b) for s, b in zip(E, widths)]
        theta = [4 * u * (1 - u) for u in mu]
        for y in bits:
            for z in bits:
                prod = Q(int(sy[y] * sy[z]))
                for j in range(len(mu)):
                    if mark[y, j] != mark[z, j]:
                        prod *= 1 - 2 * mu[j]
                assert prod == Q(int(gram[y, z]), len(x))
        law = Counter()
        cond = Q(0)
        for y in bits:
            row = []
            for mask in range(1 << len(mu)):
                prob = Q(1)
                for j, t in enumerate(theta):
                    p = t if mark[y, j] else 0
                    prob *= p if (mask >> j) & 1 else 1 - p
                law[mask] += prob / len(bits)
                row.append(prob)
            cond += entropy_counts(row)[1] / len(bits)
        measurement = entropy_counts(law.values())
        assert sh[0] <= measurement[1]
        assert cond <= 2 * Ix + Q(1, 10**20)
        assert measurement[0] - cond <= 3 * iy_proj
        assert sh[1] <= 2 * Ix + 3 * iy_proj
        if case in (0, 3):
            print(
                "coded phase",
                case,
                "I_X,I_Y,I_Y projective",
                Ix,
                Iy,
                iy_proj,
                "Schmidt entropy",
                enclose_text(sh, 7),
            )
    for w in (3, 6, 12, 30):
        # 1-2 times the point indicator on a 2w-bit cube. Reduced Gram is
        # two-dimensional with trace one and explicitly known determinant.
        N = 1 << w
        gram = np.array([[(N - 1) * N, (N - 2) * (N - 1)], [N - 2, N]], dtype=object)
        # Similar by diagonal conjugation to the positive grouped Gram.
        boxes = eig_intervals(gram, N * N, bits=4 * w + 30)
        I = Q(4 * w, N * N)
        print(
            "rank 2, w",
            w,
            "Schmidt entropy / I",
            enclose_text(tuple(t / I for t in eig_entropy(boxes)), 8),
        )
        assert eig_entropy(boxes)[1] <= 2 * I
        if w <= 6:
            f = np.ones((N, N), dtype=np.int64)
            f[-1, -1] = -1
            a = checked(f.ravel())
            assert int((degrees(2 * w) @ (a * a))) == I * f.size**2
            assert int(np.trace((f @ f.T) @ (f @ f.T))) == int(np.trace(gram @ gram))
    print("guarded lookup rank at error 1/4 is 3*2^(n-2), bent prefix 1+2^(n-2)")


if __name__ == "__main__":
    rank_examples()
    coded_features()
    extremal_seed_split()
    arbitrary_basis()
