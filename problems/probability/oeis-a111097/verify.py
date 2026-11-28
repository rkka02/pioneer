"""Check the exact adjacent-likelihood inequalities and the polynomial identity."""
from math import comb


def ratio_sign(n, population):
    # Positive when the population+1 likelihood exceeds the population likelihood.
    return (population + 1) * population ** (n + 1) - (
        population + 1 - n) * (population + 1) ** (n + 1)


def main():
    limit = 236
    sizes = [0, 1] + [
        n * (n + 1) // 2 - 1 - (n - 1) // 3 for n in range(2, limit + 1)
    ]
    for n in range(1, limit + 1):
        chosen = sizes[n]
        assert chosen >= n
        if chosen > n:
            assert ratio_sign(n, chosen - 1) > 0
        assert ratio_sign(n, chosen) < 0
    # (1-x)^3 (1+x+x²) times the generating function.
    denominator = [sum((-1) ** j * comb(3, j) for j in range(4) if 0 <= i - j <= 2)
                   for i in range(6)]
    numerator = {1: 1, 3: 2, 4: -1, 5: 2, 6: -1}
    for n in range(limit + 1):
        coefficient = sum(d * sizes[n-i] for i, d in enumerate(denominator) if i <= n)
        assert coefficient == numerator.get(n, 0), n
    print(f"Verified both neighboring likelihoods and all coefficients through index {limit}.")


if __name__ == "__main__":
    main()
