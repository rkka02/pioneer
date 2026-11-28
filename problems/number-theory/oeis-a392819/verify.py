from math import isqrt


def prime_powers(number):
    divisor = 2
    while divisor <= isqrt(number):
        power = 0
        while number % divisor == 0:
            number //= divisor
            power += 1
        if power:
            yield divisor, power
        divisor += 1
    if number > 1:
        yield number, 1


def is_term(number):
    return all(number % (prime + exponent) == 0
               for prime, exponent in prime_powers(number))


def check():
    assert list(prime_powers(5625)) == [(3, 2), (5, 4)]
    assert is_term(5625)
    cutoffs = [100, 1000, 10000, 50000]
    counts = []
    total = 0
    for number in range(1, max(cutoffs) + 1):
        total += is_term(number)
        if number in cutoffs:
            counts.append(total)
    for cutoff, count in zip(cutoffs, counts):
        print(f"{cutoff:>6} {count:>5} {count / cutoff:.6f}")


if __name__ == "__main__":
    check()
