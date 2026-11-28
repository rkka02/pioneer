#!/usr/bin/env python3
"""Check the recurrence against the decimal chunks read from the raw word."""

from itertools import cycle


def direct_chunks(limit):
    digits = cycle([1, 2, 3, 2, 1])
    chunks = [0]
    for n in range(1, limit + 1):
        digit_sum = value = 0
        while digit_sum < n:
            digit = next(digits)
            value = 10 * value + digit
            digit_sum += digit
        assert digit_sum == n, n
        chunks.append(value)
    return chunks


def main():
    chunks = direct_chunks(180)
    numerator = [
        0, 1, 2, 3, 211, 23, 2112, 3211, 2321, 12321,
        23210, 32110, 21120, 23000, 21100, 30000, 20000, 10000,
    ]
    for n, chunk in enumerate(chunks):
        prev9 = chunks[n - 9] if n >= 9 else 0
        prev18 = chunks[n - 18] if n >= 18 else 0
        assert chunk - 100001 * prev9 + 100000 * prev18 == (
            numerator[n] if n < len(numerator) else 0
        ), n
    print("Checked 180 directly read chunks and 181 coefficients.")
    print("First terms:", chunks[1:11])


if __name__ == "__main__":
    main()
