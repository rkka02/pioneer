"""Exact Walsh slices of f(x,y)=h(x) chi_{Phi(x)}(y) and pooled label losses."""

from collections import Counter
from fractions import Fraction as Q
from math import comb
import random

import numpy as np

from certificate import enclose_text
from max1_pool import logloss
from walsh import degrees, signs, wht


def set_bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask -= bit


def analyze(phi, h, private_bits, affine=False, dense=False):
    N = len(h)
    n = N.bit_length() - 1
    cells = Counter(phi)
    vals = {u: wht(np.where(np.asarray([v == u for v in phi]), h, 0)) for u in cells}
    if dense:
        assert n + private_bits <= 18
        y = np.arange(1 << private_bits)[:, None]
        f = h[None, :] * signs(degrees(private_bits)[y & np.asarray(phi, dtype=np.int64)] % 2)
        a = wht(f.reshape(-1)).reshape(-1, N)
        for u, row in enumerate(a):
            assert np.all(row == vals.get(u, 0) * (1 << private_bits))
    prefixes = Counter()
    for u, count in cells.items():
        for i in range(private_bits + 1):
            prefixes[i, u % (1 << i)] += count
    # Exact likelihood-ratio contraction for present-bit conditionals.
    for i in range(private_bits):
        bit = 1 << i
        mass = Q(0)
        excess = Q(0)
        for u, c in cells.items():
            if u & bit:
                prior = Q(prefixes[i + 1, u % (2 * bit)], prefixes[i, u % bit])
                excess += Q(c + cells[u ^ bit], N) * prior
                mass += Q(c, N)
        assert excess <= mass
    score_types = Counter()
    i_out = i_priv = Q(0)
    for u, a in vals.items():
        c = cells[u]
        energy = sum(int(b) ** 2 * (1 << (n - int(k))) for b, k in zip(a, degrees(n)))
        assert Q(energy, N * N * N) ** 3 <= Q(c, N) ** 4
        assert sum(int(b) ** 2 for b in a) == c * N
        nonzero = np.flatnonzero(a).tolist()
        if affine:
            assert len({abs(int(a[t])) for t in nonzero}) == 1
            assert c & (c - 1) == 0
        tags = list(set_bits(u))
        for bit in tags:
            pred = vals.get(u ^ bit)
            if pred is not None:
                used = sum(int(pred[t]) ** 2 for t in nonzero)
                assert used <= N * cells[u ^ bit]
        for t in nonzero:
            v = abs(int(a[t]))
            weight = Q(v * v, N * N)
            addresses = tuple(sorted(abs(int(a[t ^ j])) for j in set_bits(t)))
            labels = tuple(sorted(abs(int(vals[u ^ j][t])) if u ^ j in vals else 0 for j in tags))
            k = len(addresses) + len(labels)
            i_priv += len(labels) * weight
            i_out += len(addresses) * weight
            if k:
                score_types[v, addresses, labels] += weight / k
    x = [Q(0), Q(0)]
    priv = [Q(0), Q(0)]
    pooled = [Q(0), Q(0)]
    for (v, ad, lab), factor in score_types.items():
        l = [logloss(Q(b * b, v * v)) for b in lab]
        r = [logloss(Q(b * b, v * v)) for b in ad]
        for s in (0, 1):
            a = sum(z[s] for z in l)
            ps = pair = Q(0)
            for z in l + r:
                pair += 2 * ps * z[s]
                ps += z[s]
            priv[s] += factor * a * a
            pooled[s] += factor * ps * ps
            x[s] += factor * pair
    I = i_out + i_priv
    assert priv[1] <= 47 * I
    if affine:
        assert pooled[1] <= 31 * I
    return len(vals), I, tuple(v / I for v in priv), tuple(v / I for v in x)


def routing(m, maps):
    t = len(maps)
    ds = degrees(m)
    xrow = []
    phi = []
    offset = [sum(1 << len(a) for a in maps[:j]) for j in range(t)]
    for z in range(1 << (m + t)):
        x = z % (1 << m)
        controls = z >> m
        u = phase = 0
        for j, rows in enumerate(maps):
            addr = sum((int(ds[x & r]) % 2) << i for i, r in enumerate(rows))
            if (controls >> j) & 1:
                u |= 1 << (offset[j] + addr)
            else:
                # On each fiber this is a quadratic sign, with the form allowed
                # to change when any one of the occupied labels is removed.
                phase ^= (addr & 1) & ((addr >> 1) & 1)
                phase ^= (x & 1) & ((x >> (m - 1)) & 1)
        phi.append(u)
        xrow.append(1 - 2 * phase)
    return phi, np.asarray(xrow), sum(1 << len(a) for a in maps)


def independent(m, t):
    """Balanced by one mandatory sign. Group all the simultaneously costly deletions."""
    L = logloss(Q(1 << m))
    A = t * (m + 1)
    c0 = c1 = c2 = Q(0)
    for b in range(A + 1):
        for u in range(t + 1):
            p = Q(comb(A, b) * comb(t, u), (1 << (A + t)) * (b + u + 1))
            c0 += p * b * (b - 1)
            c1 += p * 2 * b * u
            c2 += p * u * (u - 1)
    I = 1 + Q(t * (m + 2), 2)
    return tuple((c0 + c1 * l + c2 * l * l) / I for l in L)


def main():
    rng = random.Random(4122201)
    for m, maps in [
        (2, [(1, 2), (1, 2)]),
        (3, [(1,), (2, 4), (3, 5)]),
        (5, [(1, 2), (4, 8), (6, 16)]),
        (6, [(1, 2), (4, 8), (16, 32), (5, 17)]),
    ]:
        phi, h, p = routing(m, maps)
        cells, I, pr, x = analyze(phi, h, p, True, m + len(maps) + p <= 18)
        print(
            "linear lookups m,t,cells,I,private square/I,X/I",
            m,
            len(maps),
            cells,
            I,
            enclose_text(pr, 6),
            enclose_text(x, 6),
        )
    for n, p in [(5, 4), (7, 6), (8, 10)]:
        # Arbitrary nonlinear labels, unstructured signs and unequal fiber sizes.
        phi = [
            rng.randrange(1 << p) if rng.random() < 0.6 else rng.choice([0, 1, 3, 7])
            for _ in range(1 << n)
        ]
        h = np.asarray(rng.choices([-1, 1], k=1 << n), dtype=np.int64)
        cells, I, pr, x = analyze(phi, h, p, False, n + p <= 18)
        print(
            "nonlinear cells",
            n,
            p,
            cells,
            I,
            "private square/I,X/I",
            enclose_text(pr, 6),
            enclose_text(x, 6),
        )
    # Compare the simultaneous-deletion formula to a dense signed WHT at t=2.
    m, t = 2, 2
    phi = []
    phases = []
    for z in range(1 << (t * (m + 1))):
        u = phase = 0
        for j in range(t):
            code = (z >> (j * (m + 1))) % 8
            addr = code % 4
            if code >= 4:
                u |= 1 << (4 * j + addr)
            else:
                phase ^= (addr & 1) & (addr >> 1)
        phi.append(u | (1 << 8))  # multiply by an independent balancing sign
        phases.append(1 - 2 * phase)
    *_, x = analyze(phi, np.array(phases), 9, True, True)
    b = independent(2, 2)
    assert x[0] <= b[1] and b[0] <= x[1]
    for m, t in [(2, 2), (4, 4), (8, 8), (16, 12), (32, 16), (64, 16), (128, 8)]:
        print("independent bent tables, m,t,X/I", m, t, enclose_text(independent(m, t), 7))


if __name__ == "__main__":
    main()
