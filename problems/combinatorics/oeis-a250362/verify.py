#!/usr/bin/env python3
"""Compare the formula with direct enumeration and check the claimed series."""

from itertools import product
from math import comb


def count_arrays(n):
    choices = [range(i, i + n + 1) for i in range(1, 5)]
    return sum(len(set(word)) > 1 for word in product(*choices))


def main():
    values = [0] + [(n + 1) ** 4 - max(n - 2, 0) for n in range(1, 101)]
    for n in range(1, 17):
        assert count_arrays(n) == values[n], n
    numerator = [0, 16, 1, 10, -2, -2, 1]
    for n in range(len(values)):
        coefficient = sum(
            (-1) ** j * comb(5, j) * values[n - j]
            for j in range(min(n, 5) + 1)
        )
        assert coefficient == (numerator[n] if n < len(numerator) else 0), n
    print("Checked 16 direct counts and 101 coefficients.")
    print("First terms:", values[1:9])


if __name__ == "__main__":
    main()
