"""Compare the rational generating function with direct enumeration of four-part partitions."""


def partition_weight(n):
    total = 0
    for smallest in range(1, n // 4 + 1):
        for second in range(smallest, (n - smallest) // 3 + 1):
            for third in range(second, (n - smallest - second) // 2 + 1):
                total += second
    return total


def main():
    last = 100
    terms = [partition_weight(n) for n in range(last + 1)]
    denominator = {0: 1, 2: -1, 3: -2, 4: -2, 5: 2, 6: 3, 7: 4,
                   9: -4, 10: -3, 11: -2, 12: 2, 13: 2, 14: 1, 16: -1}
    for n in range(last + 1):
        product = sum(c * terms[n - j] for j, c in denominator.items() if j <= n)
        assert product == int(4 <= n <= 10), (n, product)
    print(f"Checked all coefficients through degree {last} against direct partition enumeration.")


if __name__ == "__main__":
    main()
