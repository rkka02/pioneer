#!/usr/bin/env python3
"""Check small bases against the sharp gap and fixed-point formulas."""

from itertools import product


def integer(digits, base):
    value = 0
    for digit in digits:
        value = base * value + digit
    return value


def predicted_gap(base, length):
    if length % 2 == 0:
        return base ** ((length - 2) // 2) * (base - 1)
    return base ** ((length - 3) // 2) * (base**2 - 1)


def main():
    for base in range(2, 13):
        fixed = {0}
        for length in range(1, 6):
            least_gap = None
            for digits in product(range(base), repeat=length):
                if not digits[0]:
                    continue
                value = integer(digits, base)
                reverse = integer(reversed(digits), base)
                if reverse - max(digits) == value:
                    fixed.add(value)
                gap = abs(reverse - value)
                if gap == 0:
                    continue
                least_gap = gap if least_gap is None else min(least_gap, gap)
                mismatches = [
                    i for i in range(length // 2)
                    if digits[i] != digits[length - 1 - i]
                ]
                inner = length // 2 - 1
                expected_equality = (
                    mismatches == [inner]
                    and abs(digits[inner] - digits[length - 1 - inner]) == 1
                )
                assert (gap == predicted_gap(base, length)) == expected_equality
            if length >= 2:
                assert least_gap == predicted_gap(base, length), (base, length)
        expected = {0} if base == 2 else {0, base**2 - base - 1}
        assert fixed == expected, (base, fixed)
    print("Checked sharp gaps, their equality cases, and fixed points in bases 2–12, lengths 1–5.")


if __name__ == "__main__":
    main()
