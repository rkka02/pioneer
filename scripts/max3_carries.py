"""Exact same-grid restriction identity and the isolated coarse rounding error."""

from fractions import Fraction as Q
import random

import numpy as np

from max3_codes import entropy
from walsh import checked, degrees, record_seed, signs, splits, wht


def distance(z, h):
    t = z % h
    return min(t, h - t)


def total_grid(a):
    N = len(a)
    return Q(
        sum(distance(int(v), N >> m) ** 2 for v in a for m in range(N.bit_length() - 1)), N * N
    )


def edge_cost(u, v, N, verify=True):
    # Arguments are signed integer Walsh numerators with common denominator N.
    total = large = 0
    hits = 0
    for m in range(N.bit_length() - 1):
        h = N >> m
        a, b = u + v, u - v
        direct = (
            2 * (distance(u, h) ** 2 + distance(v, h) ** 2)
            - distance(a, h) ** 2
            - distance(b, h) ** 2
        )
        if verify:
            ia, ib = (2 * a + h) // (2 * h), (2 * b + h) // (2 * h)
            parity = 0 if (ia - ib) % 2 == 0 else h * (h - 2 * max(distance(a, h), distance(b, h)))
            assert direct == parity >= 0
        if h > 4 * abs(v):
            predicted = h * max(0, abs(v) - abs(u % h - h // 2))
            assert direct == 2 * predicted
            if direct:
                hits += 1
                large += direct
        total += direct
    assert hits <= 1 and 0 <= 3 * (total - large) <= 64 * v * v
    return Q(total, 2 * N * N), Q(large, 2 * N * N)


def node(a, i):
    N = len(a)
    u, v = splits(a, i)
    cost = coarse = Q(0)
    from collections import Counter

    for (x, y), multiplicity in Counter(zip(map(int, u), map(int, v))).items():
        c, l = edge_cost(x, y, N)
        cost += multiplicity * c
        coarse += multiplicity * l
    alpha = Q(int(np.dot(v, v)), N * N)
    return cost, coarse, alpha


def tree(f, rng, order):
    n = len(f).bit_length() - 1
    if not n:
        return (Q(0),) * 3
    a = wht(f)
    if len(np.flatnonzero(a)) == 1:
        return Q(0), Q(0), Q(int(degrees(n)[np.flatnonzero(a)[0]]))
    if order == "random":
        i = rng.randrange(n)
    elif order == "greedy":

        def ratio(b):
            c, _, alpha = node(a, b)
            return c / alpha if alpha else Q(0)

        i = min(range(n), key=ratio)
    else:
        i = 0
    children = splits(f, i)
    c, l, w = node(a, i)
    assert c == total_grid(a) - sum(total_grid(wht(g)) for g in children) / 2
    nodes = [tree(g, rng, order) for g in children]
    return tuple(v + sum(x[j] for x in nodes) / 2 for j, v in enumerate((c, l, w)))


def bent_switch(n):
    x = np.arange(1 << n)
    f = np.ones_like(x)
    for j in range(0, n, 2):
        f *= signs((x >> j) & (x >> (j + 1)) & 1)
    left, right = f.copy(), f.copy()
    left[0] *= -1
    right[1] *= -1
    tagged = np.concatenate((left, right, -left, -right))
    a = checked(tagged)
    c, l, alpha = node(a, n)
    assert not a[0] and alpha == Q(2, 1 << n)
    assert l == Q(2, 1 << (n // 2)) and l / alpha == 1 << (n // 2)
    return l / alpha


def main():
    rng = random.Random(412304)
    for n in range(2, 7):
        N = 1 << n
        for u in range(-N, N + 1, 2):
            for v in range(-N, N + 1, 2):
                if abs(u) + abs(v) <= N:
                    edge_cost(u, v, N)
    for n in (4, 7, 10):
        f = signs(rng.choices((0, 1), k=1 << n))
        a = checked(f)
        I = Q(int(np.dot(degrees(n), a * a)), len(f) ** 2)
        h = entropy(a)
        for label in ("fixed", "random", "greedy"):
            g, l, w = tree(f, rng, label)
            assert g == total_grid(a) and w == I and 0 <= 3 * (g - l) <= 32 * I
            assert h[1] / 2 - 2 * I <= g <= h[0] / 2 + 10 * I / 3
            assert l - 10 * I / 3 <= h[0] / 2 <= h[1] / 2 <= l + 38 * I / 3
            print("tree", n, label, "G,coarse,I", g, l, I)
    for n in (6, 8, 12, 16):
        print("balanced bent switch", n, "distinguished cost/I_i", bent_switch(n))
    a = wht(record_seed())
    for i in (0, 9, 17):
        c, l, w = node(a, i)
        print("Numaro carry, coarse, I_i", i, c, l, w)


if __name__ == "__main__":
    main()
