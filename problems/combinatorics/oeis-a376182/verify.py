#!/usr/bin/env python3
"""Compare the parity decomposition and inverse with Schulte's definition."""

from math import isqrt


def entry(row, column):
    constant = (2 * row**2 + 4 * row + 1 - (-1) ** row) // 4
    return constant - column - (1 + (-1) ** column) * (row - column)


def odd_count(rows):
    m, odd = divmod(rows, 2)
    return (m + 1) ** 2 if odd else m * (m + 1)


def even_count(rows):
    m, odd = divmod(rows, 2)
    return m * (m + 1) if odd else m**2


def inverse(value):
    q = (value + 1) // 2
    m = isqrt(q - 1)
    odd_row = 2 * m + (q > m * (m + 1))
    if value % 2:
        return odd_row, 2 * (odd_count(odd_row) - q) + 1
    row = odd_row + 1
    return row, 2 * (q - even_count(row - 1))


def main():
    for row in range(1, 401):
        for column in range(1, row + 1):
            value = entry(row, column)
            assert inverse(value) == (row, column), (row, column, value)
            index = row * (row - 1) // 2 + column
            offset = row + (row + 1) // 2 - 2 * column if column % 2 else -(row // 2)
            assert value - index == offset
    for value in range(1, 100_001):
        row, column = inverse(value)
        assert 1 <= column <= row and entry(row, column) == value
    print("Checked both inverse identities and the displacement formula.")


if __name__ == "__main__":
    main()
