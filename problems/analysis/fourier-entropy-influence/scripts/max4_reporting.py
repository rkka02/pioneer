"""Finite reporting rules of #192, switched balanced gates, and block refresh."""

from collections import Counter, defaultdict
from fractions import Fraction as Q
from math import comb
from itertools import product
from max1_pool import logloss
import random
import numpy as np
from certificate import enclose_text
from max3_carries import tree
from max3_code_odds import scores
from max3_codes import entropy
from max4_reserve import entropy_counts
from walsh import checked, degrees, signs, wht


def influence(a):
    return Q(int(np.dot(a * a, degrees(len(a).bit_length() - 1))), len(a) ** 2)


def report(m, width, windows, coarse=False, weighted=False):
    q = m + 1
    n = q * width
    blocks = [
        (width - 2 * degrees(width)[(np.arange(1 << n) >> (j * width)) % (1 << width)]).tolist()
        for j in range(q)
    ]
    tags = []
    totals = defaultdict(int)
    counts = Counter()
    raw = []
    for values in zip(*blocks):
        u, *z = values
        # Integer score units have variance width. Both schedules fix the tie convention.
        if weighted:
            i = min(m - 1, (u + width) * m // (2 * width + 1))
        else:
            i = min(range(m), key=lambda j: abs(1 + u - Q(sum(windows[j]), 2)))
        hits = [lo <= v <= hi for v, (lo, hi) in zip(z, windows)]
        if all(hits):
            key = ("B",) if coarse else ("B", *z)
        elif all(hits[j] for j in range(m) if j != i):
            key = ("A",)
        else:
            key = ("O", u, i, *z[:i], *z[i + 1 :])
        total = sum(values)
        raw.append(total)
        counts[key] += 1
        totals[key] += total
        tags.append(key)
    score = [Q(totals[key], counts[key]) for key in tags]
    exceptional = np.array([key[0] == "A" for key in tags], dtype=np.int64)
    variance = sum((Q(v * v, counts[key]) for key, v in totals.items()), Q()) / (1 << n)
    # Every label indicator has no mask meeting all q blocks.
    needed = np.ones(1 << n, dtype=bool)
    for j in range(q):
        needed &= ((np.arange(1 << n) >> (j * width)) % (1 << width)) != 0
    for label in counts:
        a = wht(np.array([key == label for key in tags], dtype=np.int64))
        assert not np.any(a[needed])
    return score, exceptional, variance / width


def scored(f):
    a = checked(f)
    hi = entropy(a)
    I = influence(a)
    return I, tuple(v / I for v in hi), scores(a)


def block_occupation(f, b, m):
    a = checked(f)
    I = influence(a)
    if not I:
        return
    J = [sum(bool((s >> (j * b)) % (1 << b)) for j in range(m)) for s in range(len(a))]
    W = Counter()
    for s, c in enumerate(a.tolist()):
        W[J[s]] += Q(bin(s).count("1") * c * c, len(a) ** 2)
    for rho in (Q(0), Q(1, 4), Q(1, 2), Q(7, 8)):
        value = sum(w * rho ** (j - 1) for j, w in W.items() if j)
        assert value**2 * (1 - rho) * m <= 2 ** (b - 1) * I * I
    for j in range(1, m + 1):
        total = sum(w for i, w in W.items() if i <= j)
        # e < 3 in the conversion rho=1-1/j.
        assert m * total**2 <= 9 * (2 ** (b - 1)) * j * I**2


def symmetric_checks():
    rng = random.Random(192412)
    for b, m in ((1, 8), (2, 5), (2, 7), (3, 4)):
        alphabet = 1 << b
        orbit = [
            tuple(sorted((s >> (j * b)) % alphabet for j in range(m))) for s in range(1 << (b * m))
        ]
        distinct = sorted(set(orbit))
        for style in ("random", "singleton", "parity", "density"):
            bits = {
                t: (
                    rng.randrange(2)
                    if style == "random"
                    else (
                        t == distinct[-1]
                        if style == "singleton"
                        else (
                            sum(x == 0 for x in t) % 2
                            if style == "parity"
                            else sum(t) > m * alphabet // 3
                        )
                    )
                )
                for t in distinct
            }
            block_occupation(signs([bits[t] for t in orbit]), b, m)
    print("block refresh moment passed on simultaneous permutation orbits")


def amplifying_example():
    # Four singleton leaf intervals and an exact finite cut-point selector.
    b = 4
    centers = (2, 0, -2, -4)
    support = (4, 2, 0, -2, -4)
    selected = (0, 1, 2, 3, 2)
    q = {u: Q(comb(b, j), 1 << b) for j, u in enumerate(support)}
    pp = Q(1)
    for a in centers:
        pp *= q[a]
    mass = moment = second = Q(0)
    for u, i in zip(support, selected):
        a = centers[i]
        weight = q[u] * pp * (1 - q[a]) / q[a]
        average = u + sum(centers) - a / (1 - q[a])
        variance = b / (1 - q[a]) - a * a * q[a] / (1 - q[a]) ** 2
        mass += weight
        moment += weight * average
        second += weight * (variance + average**2)
    prediction = moment / mass
    variance_given = second / mass - prediction**2
    retained = 4 + mass * (1 - variance_given / b)
    assert retained > 4
    # Direct readout and squared prediction error, on every one of the 2^20 inputs.
    x = np.arange(1 << 20)
    z = np.array([4 - 2 * degrees(4)[(x >> (4 * j)) & 15] for j in range(5)])
    index = np.array(selected)[(4 - z[0]) // 2]
    good = z[1:] == np.array(centers)[:, None]
    all_good = good.all(axis=0)
    A = (good.sum(axis=0) == 3) & ~good[index, x]
    score = np.where(all_good, z[1:].sum(axis=0), z.sum(axis=0) - z[1 + index, x])
    numer = score * prediction.denominator
    numer[A] = prediction.numerator
    assert Q(int(A.sum()), len(x)) == mass
    assert Q(int(np.dot(numer, numer)), len(x) * prediction.denominator**2 * b) == retained
    truth = signs(numer < 0)
    a = checked(truth)
    I = influence(a)
    H = tuple(v / I for v in entropy(a))
    # Exploit exact orbit multiplicities on the five blocks to price all deletion edges.
    B = X = Q(0)
    BU = XU = Q(0)
    db = I - Q(int((a[degrees(20) == 1] ** 2).sum()), len(a) ** 2)
    for ks in product(range(5), repeat=5):
        k = sum(ks)
        s = sum(((1 << j) - 1) << (4 * i) for i, j in enumerate(ks))
        c = int(a[s]) ** 2
        if not c or k < 2:
            continue
        mult = 1
        for j in ks:
            mult *= comb(4, j)
        weight = Q(c * mult, len(a) ** 2)
        logs = [
            logloss(Q(int(a[s ^ (1 << (4 * i))]) ** 2, c))
            for i, j in enumerate(ks)
            if j
            for _ in range(j)
        ]
        for side in (0, 1):
            vals = [v[side] for v in logs]
            slope = sum(vals)
            bc = weight * slope / db
            xc = weight * (slope * slope - sum(t * t for t in vals)) / (k * I)
            if side:
                BU += bc
                XU += xc
            else:
                B += bc
                X += xc
    print(
        "variance-amplifying 20-bit refined report, m=4, v/4",
        retained,
        "Pr(A)",
        mass,
        "Var(L|A)",
        variance_given,
        "I",
        I,
        "H/I",
        enclose_text(H, 8),
        "B",
        enclose_text((B, BU), 8),
        "X/I",
        enclose_text((X, XU), 8),
    )


def main():
    for width, windows in (
        (1, [(-1, -1), (-1, 1), (1, 1)]),
        (2, [(-2, 0), (0, 0), (2, 2)]),
        (3, [(-3, -1), (1, 1), (3, 3)]),
    ):
        for weighted, coarse in ((False, False), (False, True), (True, False), (True, True)):
            score, A, v = report(3, width, windows, coarse, weighted)
            sign = signs([t < 0 for t in score])
            I, hi, (B, X) = scored(sign)
            print(
                "report",
                width,
                "weighted",
                weighted,
                "coarse",
                coarse,
                "variance",
                v,
                "H/I",
                enclose_text(hi, 6),
                "B",
                enclose_text(B, 6),
                "X/I",
                enclose_text(X, 6),
            )
            if width == 1 and not weighted and not coarse:
                pair = signs([x + y < 0 for x in score for y in score])
                block_occupation(pair, 4, 2)
                R = tree(pair, random.Random(4), "fixed")[1]
                print("two reports readout H/I", enclose_text(scored(pair)[1], 8), "R", R)
            if weighted or coarse:
                continue
            # On A return the private gate; off A return the old score sign times a fresh tag.
            # First test dense substitution of majority on three bits.
            u = (1 - A) * sign
            u = np.concatenate((u, -u))
            mask = np.tile(A, 2)
            h = signs(degrees(3) >= 2)
            expanded = (u[None, :] + h[:, None] * mask).ravel()
            native = np.concatenate((u + mask, u - mask))
            w, c = checked(native), checked(expanded)
            mu = Q(int(sum(A)), len(A))
            assert influence(c) == influence(w) + mu * (influence(checked(h)) - 1)
            direct, base, hg = entropy(c), entropy(w), entropy(checked(h))
            assert direct[0] <= base[1] + mu * hg[1] and base[0] + mu * hg[0] <= direct[1]
            amp = tuple(v / (influence(w) - 1) for v in base)
            print("balanced switch host H/(I-1)", enclose_text(amp, 8), "active probability", mu)
            assert amp[1] < 6
    amplifying_example()
    symmetric_checks()


if __name__ == "__main__":
    main()
