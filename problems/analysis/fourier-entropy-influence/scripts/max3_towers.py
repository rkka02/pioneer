"""Exact spectral branching with an invertible shear across bottom data blocks."""

from collections import Counter
from fractions import Fraction as Q
import random

import numpy as np

from certificate import enclose_text
from max2_routing import statistics
from max3_codes import linear_values, scramble, verify_recode
from walsh import checked, degrees, signs, wht


def flat_gate(n):
    x = np.arange(1 << n)
    if n == 3:
        return signs(np.where(x & 1, (x >> 1) & 1, (x >> 2) & 1))
    tag = (x >> 4) & 1
    y = (x % 16) ^ tag
    return signs(tag ^ ((y & 1) * ((y >> 1) & 1)) ^ (((y >> 2) & 1) * ((y >> 3) & 1)))


def depth_two(top, bottom):
    outer, inner = flat_gate(top), flat_gate(bottom)
    upper, lower = checked(outer), checked(inner)
    roots, choices = np.flatnonzero(upper).tolist(), np.flatnonzero(lower).tolist()
    assert (
        0 not in roots + choices
        and len(set(abs(upper[roots]))) == len(set(abs(lower[choices]))) == 1
    )
    counts = Counter((int(degrees(bottom)[v]), v & 1) for v in choices)
    joint = Counter()
    for u in roots:
        occupied = int(degrees(top)[u])
        point_weight = Q(1, len(roots) * len(choices) ** occupied)
        paths = Counter({(0, 0, 0): 1})
        for j in range(top):
            if u & (1 << j):
                children = Counter()
                for (k, target, parity), m in paths.items():
                    for (d, v), c in counts.items():
                        children[k + d, v if j == 0 else target, parity ^ (v if j else 0)] += m * c
                paths = children
        for (k, t, v), multiplicity in paths.items():
            new_k = k + (t ^ v) - t
            joint[point_weight, new_k] += multiplicity
        assert sum(paths.values()) == len(choices) ** occupied
    assert sum(p * c for (p, k), c in joint.items()) == 1
    I = sum(p * c * k for (p, k), c in joint.items())
    surprise = sum(
        p * c * (p.denominator.bit_length() - 1) ** 2 / k for (p, k), c in joint.items() if k
    )
    if top * bottom <= 15:
        N = 1 << (top * bottom)
        ids = np.arange(N)
        phys = np.zeros_like(ids)
        for j in range(top):
            phys |= ((1 - inner[(ids >> (bottom * j)) % len(inner)]) // 2) << j
        table = outer[phys]
        wiring = [1 << j for j in range(top * bottom)]
        for j in range(1, top):
            wiring[j * bottom] ^= 1
        a = verify_recode(table, wiring, top * bottom)
        got = Counter(
            (Q(int(a[s]) ** 2, N**2), int(degrees(top * bottom)[s])) for s in np.flatnonzero(a)
        )
        assert got == joint
        i, _, p2, mixed = statistics({0: a}, N)
        assert i == I
        print(
            "dense depth-two rule, top,bottom,X/I",
            top,
            bottom,
            enclose_text(tuple(v / I for v in mixed), 8),
        )
    print(
        "coded depth-two, top,bottom,I,squared inverse-degree surprise/I",
        top,
        bottom,
        I,
        enclose_text((surprise / I, surprise / I), 8),
    )


def deeper():
    # The reciprocal-size step of the tree proof for the true five-bit WHT.
    # Check the pivot-ball estimate exactly for up to 192 active bottom gates.
    from math import comb

    for n in (3, 5):
        a = checked(flat_gate(n))
        p = Q(int(max(abs(a))) ** 2, len(a) ** 2)
        mean = Q(int(np.dot(a * a, degrees(n))), len(a) ** 2)
        assert p <= Q(1, 4) and mean > 1
        total = Q(0)
        for M in range(1, 193):
            ball = sum(comb(n * M, j) for j in range(M // 16 + 1))
            assert ball * ball * p**M <= 1
        for depth in (3, 9, 25, 80):
            # M>=Z_l pathwise, and E Z_l is the exact branching mean^l.
            total = sum(mean**j for j in range(depth))
            assert total * (mean - 1) == mean**depth - 1
        print("bottom gate, largest atom, exact expansion", n, p, mean)


def affine_lookup():
    """Distinct shared characters, nonparallel address cells, quadratic leaves,
    and a final affine permutation mixing both address and data frequencies."""
    rng = random.Random(412313)
    for m in (4, 6, 8):
        X = np.arange(1 << m)
        cells = [X]
        while len(cells) < 7:
            j = max(range(len(cells)), key=lambda h: len(cells[h]))
            old = cells.pop(j)
            while True:
                bit = (degrees(m)[old & rng.randrange(1, 1 << m)] % 2) != 0
                if bit.any() and not bit.all():
                    break
            cells.extend((old[bit], old[~bit]))
        labels = rng.sample(range(8), len(cells))
        data = np.arange(8)
        table = np.empty((8, len(X)), dtype=np.int64)
        pieces = []
        for ids, label in zip(cells, labels):
            phase = np.ones_like(X)
            for _ in range(2 * m):
                i, j = rng.sample(range(m), 2)
                phase *= signs((X >> i) & (X >> j) & 1)
            table[:, ids] = signs(degrees(3)[data & label] % 2)[:, None] * phase[ids]
            row = np.zeros_like(X)
            row[ids] = phase[ids]
            a = wht(row)
            freq = np.flatnonzero(a)
            dim = len(freq).bit_length() - 1
            r = m - (len(ids).bit_length() - 1)
            assert 1 << dim == len(freq) and dim >= r
            assert len(set(abs(a[freq]))) == 1
            pieces.append((freq | (label << m), r, dim))
        n = m + 3
        maps = scramble(n, n, rng)
        shift = rng.randrange(1 << n)
        final = verify_recode(table.ravel(), maps, n, tag=shift)
        dst = linear_values(maps) ^ shift
        I, _, P, _ = statistics({0: final}, len(final))
        U = Q(0)
        for freq, r, d in pieces:
            mass = Q(1, 1 << (r + d))
            for idx in dst[freq]:
                assert Q(int(final[idx]) ** 2, len(final) ** 2) == mass
                k = int(degrees(n)[idx])
                if k:
                    U += mass * (r + d) ** 2 / k
        assert U <= 32 * I and P[1] < 60 * I
        print(
            "fully recoded shared-character lookup, bits,I,P2/I",
            n,
            I,
            enclose_text(tuple(v / I for v in P), 8),
        )


if __name__ == "__main__":
    for sizes in ((3, 3), (3, 5), (5, 3), (5, 5)):
        depth_two(*sizes)
    deeper()
    affine_lookup()
