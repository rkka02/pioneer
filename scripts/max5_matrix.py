"""Exact Walsh, Gram and rational checks for the final-round matrix constructions."""

from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, product
from math import prod
import numpy as np

from certificate import enclose_text, ln_mantissa, log2_int
from max4_rank import eig_entropy, eig_intervals
from max4_reserve import entropy_counts
from walsh import checked, degrees, signs, wht


def influence(table):
    f = table.ravel()
    a = checked(f)
    return Q(int(degrees(len(f).bit_length() - 1) @ (a * a)), len(f) ** 2)


def dense_lift(h):
    n = len(h).bit_length() - 1
    x = np.arange(4**n)
    address = np.zeros((len(x), len(x)), dtype=np.int64)
    for j in range(n):
        a, b = (x >> (2 * j)) & 1, (x >> (2 * j + 1)) & 1
        # For a given column, equal signs select the first row bit.
        out = np.where((a == b)[None, :], a[:, None], b[:, None]) ^ a[None, :]
        address += out << j
    f = h[address]
    I = influence(f)
    a = checked(h)
    Ih = Q(int(degrees(n) @ (a * a)), len(h) ** 2)
    transformed = wht(wht(f).T).T
    gram = transformed @ transformed.T
    # In the Walsh bases, all rows are orthogonal; for n<=3 these products fit int64.
    assert np.array_equal(gram, np.diag(np.diag(gram)))
    predicted = Counter()
    for s, c in enumerate(a):
        if c:
            m = 1 << bin(s).count("1")
            predicted[Q(int(c * c), len(h) ** 2 * m)] += m
    actual = Counter(Q(int(z), f.size**2) for z in gram.diagonal() if z)
    assert actual == predicted and I == 2 * Ih
    H = entropy_counts(Q(int(c * c), len(h) ** 2) for c in a)
    S = entropy_counts(p for p, k in actual.items() for _ in range(k))
    assert max(H[0] + Ih, S[0]) <= min(H[1] + Ih, S[1])


def lift_tests():
    for n in (1, 2):
        for z in range(1 << (1 << n)):
            dense_lift(signs([(z >> j) & 1 for j in range(1 << n)]))
    for z in (1, 23, 113, 177, 220, 254):
        dense_lift(signs([(z >> j) & 1 for j in range(8)]))
    # All 4x4 sign matrices whose rows and columns are signed dictators.
    rows = [np.array(a) for a in ((1, -1, 1, -1), (1, 1, -1, -1), (-1, 1, -1, 1), (-1, -1, 1, 1))]
    profiles = Counter()
    for ids in product(range(4), repeat=4):
        m = np.array([rows[j] for j in ids])
        if all(any(np.array_equal(c, r) for r in rows) for c in m.T):
            nums = wht(wht(m).T).T
            gram = nums @ nums.T
            assert np.array_equal(gram, np.diag(np.diag(gram)))
            law = tuple(sorted(Q(int(v), 256) for v in gram.diagonal() if v))
            assert influence(m) == 2 and law in ((Q(1),), (Q(1, 2), Q(1, 2)))
            profiles[law] += 1
    print("bidictator profiles", profiles)


def sampling():
    gamma = Q(3, 4)
    for n in (2, 3, 4, 8, 16):
        D = 1 << n

        def residual(m):
            return (1 - Q(m, D)) * (1 - gamma) * (1 + m * gamma) / (1 + (m - 1) * gamma)

        need = next(m for m in range(1, D + 1) if residual(m) <= Q(1, 4))
        assert 4 * need + 3 * need**2 >= 3 * D and 4 * (need - 1) + 3 * (need - 1) ** 2 < 3 * D
        if n <= 4:
            u = np.arange(D)
            phase = signs(degrees(n)[u[:, None] & u[None, :]] % 2)
            f = np.vstack([np.ones((3 * D, D), dtype=np.int64), phase])
            a = checked(f.ravel())
            assert sum(int(x) ** 2 for x in a) == f.size**2
            gram = f.T @ f
            assert np.array_equal(gram, D * (np.eye(D, dtype=np.int64) + 3 * np.ones_like(gram)))
            for m in range(1, D + 1):
                # Adjacent columns outside a selected set have identical regressions.
                k = Q(3, 1 + 3 * m)
                for j in range(m):
                    assert sum(int(gram[j, l]) * k for l in range(m)) == 3 * D
                assert residual(m) == (1 - Q(m, D)) * (1 - m * gamma * k)
        print("column population", D, "optimal rank 1; distinct columns required", need)


def tribes():
    for k in (1, 2, 3, 5, 8, 12):
        m = 1 << k
        u = Q(1, m)
        a = (1 - u) ** m
        bias = 2 * a - 1
        ij = 2 * u * (1 - u) ** (m - 1)
        I = m * k * ij
        rho = 1 - Q(1, 2 * k)
        z = rho**2
        # Grouped absolute Walsh generating function, and squared-norm generating function.
        # For large k evaluate only the finite rational base, avoiding gigantic powers.
        if k <= 8:
            base = 1 - 2 * u + u * (1 + z) ** k
            nuclear = abs(bias) + 2 * (base**m - a)
            squared = bias**2 + 4 * (((1 - u) ** 2 + u * u * ((1 + z * z) ** k - 1)) ** m - a * a)
            if k <= 2:
                x = np.arange(1 << (k * m))
                hit = np.array([((x >> (j * k)) % (1 << k)) == m - 1 for j in range(m)]).any(axis=0)
                f = signs(hit)
                c = checked(f)
                assert squared == sum(
                    Q(int(t * t), len(f) ** 2) * z ** (2 * int(d))
                    for t, d in zip(c, degrees(k * m))
                )
                assert nuclear == sum(
                    Q(abs(int(t)), len(f)) * z ** int(d) for t, d in zip(c, degrees(k * m))
                )
            print(
                "Tribes",
                k,
                "noise trace norm >= 2^",
                nuclear.numerator.bit_length() - nuclear.denominator.bit_length() - 1,
                "clustering requires mean depth >=",
                int((Q(3, 4) - bias * bias) / ij),
            )
        if k <= 12:
            full = 4 * (1 - u) ** m
            # Number of occupied tribes, restricted to nonempty masks, has this
            # multiple of Bin(m,u). Markov bounds the entire mass with J>=17.
            assert full / 17 <= Q(1, 4) and I < 2 * k


def rare_kernel(mask, w):
    table = np.array([[(mask >> (4 * i + j)) & 1 for j in range(4)] for i in range(4)])
    event = Q(int(table.sum()), 16)
    S_event = eig_entropy(eig_intervals(table @ table.T, int(table.sum()), 80))
    native = signs(table)
    I0 = influence(native)
    surpr = entropy_counts([event])
    excess = tuple(I0 / (2 * event) - s / event for s in surpr[::-1])
    gap = S_event[0] - excess[1], S_event[1] - excess[0]
    norm = 4 * (1 << w)
    weights = np.array([norm - 4, 1, 1, 1, 1], dtype=object)
    F = np.ones((5, 5), dtype=object)
    F[1:, 1:] = native
    G = (F * weights) @ F.T * weights
    spectrum = eig_intervals(G, norm**2, 2 * w + 70)
    S = eig_entropy(spectrum)
    I = (I0 + 4 * w * event) / 4**w
    if w == 1:
        data = np.ones((norm, norm), dtype=np.int64)
        data[:4, :4] = native
        assert influence(data) == I
    return len(spectrum), gap, (S[0] / I, S[1] / I)


def rare_examples():
    for mask in (58, 13740, 13050):
        for w in (1, 12, 32):
            rank, gap, ratio = rare_kernel(mask, w)
            print(
                "rare mask",
                mask,
                "guard width",
                w,
                "rank",
                rank,
                "event surplus",
                enclose_text(gap, 9),
                "Schmidt ratio",
                enclose_text(ratio, 10),
            )
            if mask == 13050 and w == 12:
                assert rank == 5 and ratio[0] > 2


def overlap():
    # Independent physical blocks, with intrinsically overlapping predicates
    # within each block and shared, correlated column labels.
    x, y = np.arange(64), np.arange(8)
    for mode in range(6):
        vals = np.ones((len(x), len(y)), dtype=np.int64)
        for j in range(2):
            s = (x >> (3 * j)) & 7
            first = (s & 3) == 1
            second = (s & 6) == 4
            third = (s & 5) == 4
            words = (y * (2 * j + 1) + mode) % 8
            exponent = (
                first[:, None] * (words[None, :] & 1)
                + second[:, None] * ((words[None, :] >> 1) & 1)
                + third[:, None] * ((words[None, :] >> 2) & 1)
            )
            vals *= signs(exponent % 2)
        if mode % 2:
            vals *= signs(((x & 9) == 1))[:, None]
        a = checked(vals.ravel())
        assert sum(int(t) ** 2 for t in a) == vals.size**2
        S = eig_entropy(eig_intervals(vals.T @ vals, vals.size))
        ix = Q(sum(np.count_nonzero(vals != vals[x ^ (1 << j)]) for j in range(6)), vals.size)
        iy = Q(0)
        for j in range(3):
            ds = np.count_nonzero(vals != vals[:, y ^ (1 << j)], axis=0)
            iy += Q(int(np.minimum(ds, len(x) - ds).sum()), vals.size)
        pix = Q(0)
        for j in range(6):
            ds = np.count_nonzero(vals != vals[x ^ (1 << j)], axis=1)
            pix += Q(int(np.minimum(ds, len(y) - ds).sum()), vals.size)
        assert pix <= ix
        assert S[1] <= (4 + 2 * log2_int(7)[0]) * pix + 2 * iy / ln_mantissa(Q(2))[1]
    print("six overlapping-feature kernels, integer WHT and Gram checks passed")


def column_span_loss(gram, sample):
    # Schur complement for a Gram matrix with unit diagonal, in Fractions.
    # Skip dependent sampled vectors using a rank-one projection update.
    g = [[Q(int(z), int(gram[0, 0])) for z in row] for row in gram]
    for j in sample:
        diag = g[j][j]
        if diag:
            v = g[j].copy()
            g = [[g[a][b] - v[a] * v[b] / diag for b in range(len(g))] for a in range(len(g))]
    return sum(g[i][i] for i in range(len(g))) / len(g)


def sample_bound():
    for mask in (0x32FA, 0x35AC, 0x1374, 0xAA55):
        f = signs([(mask >> j) & 1 for j in range(16)]).reshape(4, 4)
        checked(f.ravel())
        gram = f.T @ f
        spec = eig_intervals(gram, 16, 60)
        for m in (1, 2, 4):
            loss = sum(column_span_loss(gram, seq) for seq in product(range(4), repeat=m)) / 4**m
            # Upper bound using each eigenvalue: min(lambda,(1-lambda)/m).
            upper = sum(min(b, (1 - a) / m) for a, b in spec)
            assert loss <= upper
    print("exact expected sample-span residual, 4 sign matrices, m=1,2,4")


def encoders():
    rng = np.random.default_rng(412505)
    bits = np.arange(8)
    event = (bits & 1).astype(bool) | ((bits & 6) == 6)
    h = signs(event)
    a = checked(h)
    weights = [Q(abs(int(a[1 << j])), 8) for j in range(3)]
    for s in range(1, 8):
        disagreement = Q(np.count_nonzero(h != h[bits ^ s]), 8)
        assert disagreement >= max(weights[j] for j in range(3) if (s >> j) & 1)
    for _ in range(8):
        pi = rng.permutation(np.tile(bits, 2))
        sigma = rng.permutation(bits)
        f = h[pi[:, None] ^ sigma[None, :]]
        assert influence(f) >= 2 * sum(weights)
        # Row features overlap under the nonlinear balanced map pi.
        labels = rng.integers(8, size=8)
        sign = signs(degrees(3)[pi[:, None] & labels[None, :]] % 2)
        sign *= signs((np.arange(16) % 3) == 0)[:, None]
        checked(sign.ravel())
        gram = sign.T @ sign
        S = eig_entropy(eig_intervals(gram, sign.size))
        counts = Counter(int(z) for z in labels)
        H = entropy_counts(Q(v, 8) for v in counts.values())
        assert max(S[0], H[0]) <= min(S[1], H[1])
        cuts = sum(np.count_nonzero(labels != labels[bits ^ (1 << j)]) for j in range(3))
        assert 8**8 <= 2 ** int(cuts) * prod(v**v for v in counts.values())
    print("overlapping nonlinear encodings and projectively orthogonal dictionaries verified")


if __name__ == "__main__":
    lift_tests()
    sampling()
    sample_bound()
    encoders()
    tribes()
    rare_examples()
    overlap()
