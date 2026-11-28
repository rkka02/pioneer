#!/usr/bin/env python3
"""Multiply the generating series obtained directly from the q-polynomial recurrence."""


def add(p, q):
    result = p + [0] * max(0, len(q) - len(p))
    for i, value in enumerate(q):
        result[i] += value
    return result


def multiply(p, q):
    result = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            result[i + j] += x * y
    return result


def main():
    nu = [[1], [2]]
    for n in range(79):
        nu.append(add(multiply([2], nu[-1]), multiply([2] * (n + 1), nu[-2])))
    cubic = [p[3] if len(p) > 3 else 0 for p in nu]

    denominator = [1]
    for _ in range(4):
        denominator = multiply(denominator, [1, -2, -2])
    numerator = multiply(multiply([0] * 5 + [8], [1, 1]), [5, -16, -2, 24, 12])
    cleared = multiply(denominator, cubic)[: len(cubic)]
    assert cleared == numerator + [0] * (len(cubic) - len(numerator))
    print(f"Checked {len(cubic)} coefficients using the full polynomial recurrence.")
    print("First nonzero terms:", cubic[5:10])


if __name__ == "__main__":
    main()
