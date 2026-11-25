"""Integer-numerator replay of the fixed-coordinate Lean restriction tree."""

from fractions import Fraction as Q
from functools import lru_cache
from random import Random

from walsh import wht


def grid(x, h):
    return min(x % h, (-x) % h)


@lru_cache(None)
def verify(truth):
    size = len(truth)
    n = size.bit_length() - 1
    a = list(map(int, wht(truth)))
    I = Q(sum(bin(s).count("1") * v * v for s, v in enumerate(a)), size**2)
    G = Q(sum(grid(v, 1 << j) ** 2 for v in a for j in range(1, n + 1)), size**2)
    if n == 0:
        assert G == I == 0
        return G, Q(0), I
    all_loss = coarse = 0
    children = [truth[b::2] for b in (0, 1)]
    transforms = [wht(child) for child in children]
    for s, (u, v) in enumerate(zip(a[::2], a[1::2])):
        assert u + v == 2 * transforms[0][s] and u - v == 2 * transforms[1][s]
        fine = count = 0
        for j in range(1, n + 1):
            h = 1 << j
            loss = (
                2 * (grid(u, h) ** 2 + grid(v, h) ** 2) - grid(u + v, h) ** 2 - grid(u - v, h) ** 2
            )
            assert loss >= 0
            all_loss += loss
            if 4 * abs(v) < h:
                price = h * max(0, 2 * abs(v) - h + 2 * grid(u, h))
                assert loss == price
                count += price > 0
                coarse += price
            else:
                fine += loss
        assert count <= 1 and 3 * fine <= 64 * v * v
    results = [verify(child) for child in children]
    avg = lambda j: sum(row[j] for row in results) / 2
    alpha = Q(sum(v * v for v in a[1::2]), size**2)
    assert I == alpha + avg(2) and G == Q(all_loss, 2 * size**2) + avg(0)
    R = Q(coarse, 2 * size**2) + avg(1)
    assert 0 <= R <= G and G - R <= Q(32, 3) * I
    return G, R, I


def main():
    for table in range(256):
        verify(tuple(1 - 2 * ((table >> j) & 1) for j in range(8)))
    rng = Random(412555)
    for n in range(4, 9):
        for _ in range(12):
            verify(tuple(rng.choice((-1, 1)) for _ in range(1 << n)))
    print(
        "all 256 three-bit signs and 60 further tables; distinct restriction nodes",
        verify.cache_info().currsize,
    )


if __name__ == "__main__":
    main()
