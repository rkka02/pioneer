#!/usr/bin/env python3
"""Exact modular and lattice enumeration checks for the four-square count."""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import isqrt


def obstructed(n):
    while n % 4 == 0:
        n //= 4
    return n % 8 == 7


def modular_count(level):
    modulus = 2 ** (2 * level + 1)
    squares = Counter((v * v) % modulus for v in range(modulus))
    pair_sums = Counter()
    for (a, ca), (b, cb) in product(squares.items(), repeat=2):
        pair_sums[(a + b) % modulus] += ca * cb
    wanted = {
        residue for residue in range(modulus)
        if any(residue % (8 * 4**a) == 7 * 4**a for a in range(level))
    }
    count = sum(
        ca * cb for (a, ca), (b, cb) in product(pair_sums.items(), repeat=2)
        if (a + b) % modulus in wanted
    )
    return Fraction(count, modulus**4)


def tuple_counts(limit):
    count_four = count_optimal_four = 0
    for a in range(1, isqrt(limit) + 1):
        after_a = min(2 * a, limit - a * a)
        for b in range(1, isqrt(after_a) + 1):
            after_b = min(2 * b, after_a - b * b)
            for c in range(1, isqrt(after_b) + 1):
                after_c = min(2 * c, after_b - c * c)
                partial = a * a + b * b + c * c
                for d in range(1, isqrt(after_c) + 1):
                    count_four += 1
                    count_optimal_four += obstructed(partial + d * d)
    return count_four, count_optimal_four


def direct_counts(limit):
    squares = [a * a for a in range(1, isqrt(limit) + 1)]
    square_set = set(squares)
    two_square_set = set()
    for i, a in enumerate(squares):
        for b in squares[i:]:
            if a + b > limit:
                break
            two_square_set.add(a + b)

    lengths = bytearray(limit + 1)
    count_four = count_optimal_four = count_all_optimal = 0
    for n in range(1, limit + 1):
        count = 1 + lengths[n - isqrt(n)**2]
        lengths[n] = count
        if count > 4:
            continue
        if count == 1:
            count_all_optimal += 1
        elif count == 2:
            count_all_optimal += n not in square_set
        elif count == 3:
            count_all_optimal += n not in square_set and n not in two_square_set
        else:
            count_four += 1
            requires_four = obstructed(n)
            count_optimal_four += requires_four
            count_all_optimal += requires_four
    return count_four, count_optimal_four, count_all_optimal


def main():
    for level in range(1, 5):
        density = modular_count(level)
        predicted = Fraction(3, 20) - Fraction(1, 40 * 16 ** (level - 1))
        assert density == predicted, (level, density)
        print(f"M={level}: truncated congruence density {density}")

    print("limit, four greedy roots, four required, all optimal")
    oeis_totals = {10_000: 3560, 100_000: 26394, 1_000_000: 202012}
    for limit, expected in oeis_totals.items():
        direct = direct_counts(limit)
        assert direct[:2] == tuple_counts(limit), (limit, direct)
        assert direct[2] == expected, (limit, direct)
        print(limit, *direct, sep=", ")


if __name__ == "__main__":
    main()
