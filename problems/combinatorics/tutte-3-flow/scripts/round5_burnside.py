"""Count all isomorphism classes in the raw degree slices by vertex-cycle Burnside enumeration."""

from collections import Counter
from functools import cache
from itertools import groupby
from math import comb, factorial, gcd, prod
import sys


def partitions(n, least=1):
    if n == 0:
        yield ()
    for first in range(least, n + 1):
        for tail in partitions(n - first, first):
            yield (first,) + tail


@cache
def group_options(a, b, degree, number, budget):
    """Independent intercycle edge orbits for labelled cycles of the same length and quota."""
    g = gcd(a, b)
    left, right = b // g, a // g
    cap = min(g, degree // right, budget // left)
    options = []

    def distribute(k, remaining, spent, coefficient, quotas):
        if k == 0:
            options.append((spent, coefficient, quotas + ((b, degree),) * remaining))
            return
        for used in range(min(remaining, (budget - spent) // (k * left)) + 1):
            distribute(
                k - 1,
                remaining - used,
                spent + used * k * left,
                coefficient * comb(remaining, used) * comb(g, k) ** used,
                quotas + ((b, degree - k * right),) * used,
            )

    distribute(cap, number, 0, 1, ())
    return options


@cache
def fixed_quota(cycles):
    if not cycles:
        return 1
    total_vertices = sum(a for a, _ in cycles)
    if any(d >= total_vertices for a, d in cycles) or sum(a * d for a, d in cycles) % 2:
        return 0
    a, quota = cycles[-1]
    rest = cycles[:-1]
    groups = [(length, degree, len(list(items))) for (length, degree), items in groupby(rest)]
    result = 0

    def incident(i, remaining, factor, tail):
        nonlocal result
        if i == len(groups):
            if remaining == 0:
                result += factor * fixed_quota(tuple(sorted((b, d) for b, d in tail if d)))
            return
        b, degree, number = groups[i]
        for cost, ways, residual in group_options(a, b, degree, number, remaining):
            incident(i + 1, remaining - cost, factor * ways, tail + residual)

    # A cycle has floor((a-1)/2) distance-two-degree orbits, and an antipodal
    # matching of degree one exactly when the cycle has even length.
    for j in range(int(a % 2 == 0) + 1):
        for k in range(min((a - 1) // 2, (quota - j) // 2) + 1):
            incident(0, quota - j - 2 * k, comb((a - 1) // 2, k), ())
    return result


def assignments(lengths, threes, fours):
    groups = sorted(Counter(lengths).items())

    def go(i, x, y, coefficient, data):
        if i == len(groups):
            if x == y == 0:
                yield coefficient, data
            return
        length, n = groups[i]
        for s in range(min(n, x // length) + 1):
            for t in range(min(n - s, y // length) + 1):
                w = comb(n, s) * comb(n - s, t)
                yield from go(
                    i + 1,
                    x - s * length,
                    y - t * length,
                    coefficient * w,
                    data + ((length, 3),) * s + ((length, 4),) * t + ((length, 5),) * (n - s - t),
                )

    return go(0, threes, fours, 1, ())


def raw_counts(n):
    totals = [0, 0, 0]
    for lengths in partitions(n):
        centralizer = prod(a**c * factorial(c) for a, c in Counter(lengths).items())
        perms = factorial(n) // centralizer
        for x in range(3):
            totals[x] += perms * sum(
                mult * fixed_quota(data) for mult, data in assignments(lengths, x, 5 - 2 * x)
            )
    assert all(t % factorial(n) == 0 for t in totals)
    return tuple(t // factorial(n) for t in totals)


if __name__ == "__main__":
    for n in map(int, sys.argv[1:] or [7, 9, 11, 13, 15]):
        print(n, raw_counts(n), flush=True)
