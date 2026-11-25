"""Exact affine Fourier recoding, optimal influence bases and code-shell search."""

from collections import Counter
from fractions import Fraction as Q
from itertools import permutations
import random

import numpy as np

from certificate import enclose_text
from max1_pool import logloss
from max2_routing import statistics
from walsh import checked, degrees, record_seed, signs, wht


def linear_values(images):
    """Extend the images of binary basis vectors to the full linear map."""
    out = np.zeros(1, dtype=np.int64)
    for v in images:
        out = np.concatenate((out, out ^ v))
    return out


def independent_add(basis, v):
    while v:
        j = v.bit_length() - 1
        if j not in basis:
            basis[j] = v
            return True
        v ^= basis[j]
    return False


def scramble(n, out_n, rng):
    rows = [1 << j for j in range(out_n)]
    for _ in range(6 * out_n):
        i, j = rng.sample(range(out_n), 2)
        rows[i] ^= rows[j]
    rng.shuffle(rows)
    return rows[:n]


def pullback(table, rows, n, shift=0, tag=0):
    idx = np.arange(1 << n)
    deg = degrees(n)
    active = np.zeros_like(idx)
    for j, row in enumerate(rows):
        active |= (deg[idx & row] % 2) << j
    return table[active ^ shift] * signs(deg[idx & tag] % 2)


def verify_recode(table, rows, n, shift=0, tag=0):
    f = pullback(table, rows, n, shift, tag)
    a = checked(f)
    old = wht(table)
    native = np.arange(len(table))
    destinations = linear_values(rows) ^ tag
    signed = old * signs(degrees(len(rows))[native & shift] % 2)
    predicted = np.zeros_like(a)
    np.add.at(predicted, destinations, signed)
    assert np.array_equal(len(table) * a, len(a) * predicted)
    return a


def entropy(a):
    lo = hi = Q(0)
    for c, m in Counter(abs(int(x)) for x in a if x).items():
        p = Q(c * c, len(a) ** 2)
        l, u = logloss(1 / p - 1)
        lo += m * p * l
        hi += m * p * u
    return lo, hi


def greedy(cost):
    basis = {}
    selected = []
    for j in np.argsort(cost, kind="stable").tolist():
        if independent_add(basis, j):
            selected.append(j)
            if len(selected) == len(cost).bit_length() - 1:
                break
    return sum(int(cost[j]) for j in selected), selected


def directional(a):
    N = len(a)
    # 2N^2 times each directional influence, including zero direction.
    return N * N - wht(a * a)


def orbit_min(a, tag=0, allow_output_shift=False):
    n = len(a).bit_length() - 1
    raw = directional(a)
    twice = 2 * len(a) ** 2
    flip = (degrees(n)[np.arange(len(a)) & tag] % 2) != 0
    raw = np.where(flip, twice - raw, raw)
    if allow_output_shift:
        raw = np.minimum(raw, twice - raw)
    val, chosen = greedy(raw)
    return Q(val, twice), chosen


def directional_test():
    rng = random.Random(412305)
    for n in (3, 4, 6, 8):
        for _ in range(5):
            f = signs(rng.choices((0, 1), k=1 << n))
            a = wht(f)
            cost, rows = orbit_min(a)
            x = np.arange(len(f))
            basis_table = f[linear_values(rows)]
            actual = checked(basis_table)
            assert Q(int(np.dot(actual * actual, degrees(n))), len(a) ** 2) == cost
            for v in range(len(f)):
                assert directional(a)[v] == 2 * len(a) * np.count_nonzero(f != f[x ^ v])
            if n == 3:
                vals = [
                    sum(int(directional(a)[v]) for v in P)
                    for P in permutations(range(1, 8), 3)
                    if len(set(linear_values(P))) == 8
                ]
                assert cost == Q(min(vals), 2 * len(a) ** 2)
        f = signs(degrees(n) > n // 2)
        a = wht(f)
        assert orbit_min(a)[0] == sum(Q(abs(int(a[1 << i])), len(a)) for i in range(n))
    a = wht(record_seed())
    assert orbit_min(a)[0] == Q(261, 128)
    print("directional minimum for the monotone 18-bit seed", orbit_min(a)[0])


def code_words(label):
    if label in ("Hamming(7,4)", "BCH(15,7)"):
        m, poly, n, d = (
            (4, 0b1011, 7, 3) if label.startswith("Hamming") else (7, 0b111010001, 15, 5)
        )
        values = linear_values([poly << j for j in range(m)])
    else:
        m = 4
        queries = [(1 << i) for i in range(m)]
        if label == "RM(2,4)":
            queries += [(1 << i) | (1 << j) for i in range(m) for j in range(i)]
        queries = [0] + queries
        n = 1 << m
        values = linear_values([sum((1 << x) for x in range(n) if (x & t) == t) for t in queries])
        d = 4 if label == "RM(2,4)" else 8
    weights = degrees(n)[values]
    assert weights[1:].min() == d
    return weights


def search_code_shells():
    best = [Q(0), Q(0)]
    witness = None
    for label in ("Hamming(7,4)", "BCH(15,7)", "RM(1,4)", "RM(2,4)"):
        weights = code_words(label)
        layers, ids = np.unique(weights, return_inverse=True)
        tested = 0
        for pattern in range(2, 1 << len(layers), 2):  # quotient by output negation
            f = signs((pattern >> ids) & 1)
            a = wht(f)
            # Look for a macro jump in the amplified score of a balanced
            # character shift. The absolute directional optimum prunes safely.
            lower, _ = orbit_min(a, allow_output_shift=True)
            h = entropy(a)
            if lower > 1 and h[1] <= best[0] * (lower - 1):
                continue
            for tag in np.flatnonzero(a == 0).tolist():
                I, _ = orbit_min(a, tag=tag)
                tested += 1
                if I <= 1:
                    continue
                score = tuple(v / (I - 1) for v in h)
                if score[0] > best[0]:
                    witness = (label, pattern, tag, I)
                best = [max(b, c) for b, c in zip(best, score)]
        print("code and weight layers", label, layers.tolist(), "unpruned balanced shifts", tested)
    print(
        "maximum amplified score across these four code-shell searches",
        witness,
        enclose_text(best, 12),
    )


def program():
    # A reversible address program acts repeatedly on the SAME data block.
    # Compare the attainable-state law and physical directional costs directly.
    rng = random.Random(412306)
    x = np.arange(32)
    bent = signs(((x & 1) * ((x >> 1) & 1)) ^ (((x >> 2) & 1) * ((x >> 3) & 1)) ^ ((x >> 4) & 1))
    for depth in (2, 5, 9):
        states = [bent.copy()]
        for stage in range(depth):
            i, j = (0, 4) if stage % 3 == 0 else rng.sample(range(5), 2)
            perm = x ^ ((((x >> i) & 1)) << j)
            states = states + [row[perm] for row in states]
        table = np.concatenate(states)
        a = checked(table)
        I, A, P, X = statistics({0: a}, len(a))
        w = len({tuple(row) for row in states})
        dmin = min(
            (
                Q(int(np.count_nonzero(s != t)), 32)
                for s in states
                for t in states
                if not np.array_equal(s, t)
            ),
            default=Q(1),
        )
        assert dmin >= Q(1, 4)
        bound = Q(1, 1 << min(w - 1, depth)) * Q(1, 4)
        assert P[1] <= (w + 4) ** 2 * I
        counts = Counter(row.tobytes() for row in states)
        assert min(counts.values()) * Q(1, len(states)) >= Q(1, 1 << (w - 1))
        for i in range(5 + depth):
            marginal = Q(int((a[(np.arange(len(a)) & (1 << i)) != 0] ** 2).sum()), len(a) ** 2)
            assert not marginal or marginal >= bound
        print(
            "controlled shears depth, states, I,X/I",
            depth,
            w,
            I,
            enclose_text(tuple(v / I for v in X), 8),
        )


if __name__ == "__main__":
    directional_test()
    search_code_shells()
    program()
