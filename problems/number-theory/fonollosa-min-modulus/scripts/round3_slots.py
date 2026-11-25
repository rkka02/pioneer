"""Exact primal and dual certificates for the two-by-two signature-box relaxation."""

from fractions import Fraction as F
from math import comb, lcm
from scipy.optimize import linprog


def certificate(slots, layers=2, slope=1):
    sig = [
        (p, q)
        for p in range(2, slots)
        for q in range(2, slots)
        if (layers - slope) * p + slope * q < slots
    ]
    squares = sorted({(p - i, q - j) for p, q in sig for i in (0, 1) for j in (0, 1)})
    incidence = [[int(i <= p <= i + 1 and j <= q <= j + 1) for p, q in sig] for i, j in squares]

    def density(p, q):
        g = abs(p - q)
        if not g:
            return F(3, 8) if p == 2 else F(1, 2)
        return max(F(comb(h, (h - g) // 2), 2**h) for h in range(g, g * g + 1, 2))

    w = [(slots - (layers - slope) * p - slope * q) * density(p, q) for p, q in sig]
    solution = linprog(
        [-float(v) for v in w],
        A_ub=incidence,
        b_ub=[1] * len(squares),
        bounds=(0, None),
        method="highs",
    )
    assert solution.success
    x = [F(y).limit_denominator(64) for y in solution.x]
    denom = lcm(*(v.denominator for v in w))
    y = [F(round(-v * denom), denom) for v in solution.ineqlin.marginals]
    assert all(s >= 0 for s in x + y)
    assert all(sum(a * b for a, b in zip(row, x)) <= 1 for row in incidence)
    assert all(sum(a * b for a, b in zip(col, y)) >= cost for col, cost in zip(zip(*incidence), w))
    loss = sum(a * b for a, b in zip(w, x))
    assert loss == sum(y)
    return loss, (slots - loss) / (4 * layers)


if __name__ == "__main__":
    for layers, slope, slots in [(2, 1, L) for L in range(5, 11)] + [
        (3, 1, 11),
        (4, 1, 14),
        (5, 2, 18),
    ]:
        loss, ratio = certificate(slots, layers, slope)
        print(layers, slope, slots, loss, ratio)
