"""Standalone finite FEI lower-bound certificate. Python 3 standard library only.

Every endpoint is an integer multiple of 2**-192. A Walsh butterfly and
range-reduced atanh bounds are the only numerical primitives.
"""

from collections import Counter
from functools import lru_cache

UNIT = 1 << 192
BASE = int(
    "fefefeeefefafc00feaafeaafeaafc00fefeccccfefacc00eeaacc00eeaacc00"
    "fefefeeef0f0f000faaafaaaf000f000fcfcccccf0f000000000000000000000",
    16,
)
EDGES = [
    (78, 79),
    (113, 121),
    (228, 484),
    (170, 186),
    (149, 151),
    (338, 466),
    (284, 316),
    (291, 295),
    (393, 457),
]


def wht(values):
    a = list(values)
    h = 1
    while h < len(a):
        for k in range(0, len(a), 2 * h):
            for j in range(k, k + h):
                a[j], a[j + h] = a[j] + a[j + h], a[j] - a[j + h]
        h *= 2
    return a


def point(n, d=1):
    return n * UNIT // d, -(-n * UNIT // d)


def add(*xs):
    return sum(x[0] for x in xs), sum(x[1] for x in xs)


def sub(x, y):
    return x[0] - y[1], x[1] - y[0]


def mul(x, y):
    products = [a * b for a in x for b in y]
    return min(products) // UNIT, -(-max(products) // UNIT)


def div(x, y):
    assert y[0] > 0
    return mul(x, (UNIT**2 // y[1], -(-(UNIT**2) // y[0])))


def square(x):
    smallest = 0 if x[0] <= 0 <= x[1] else min(abs(a) for a in x)
    return smallest**2 // UNIT, -(-max(a * a for a in x) // UNIT)


def power(x, n):
    result = ONE
    while n:
        if n % 2:
            result = mul(result, x)
        x = square(x)
        n //= 2
    return result


ZERO, ONE = point(0), point(1)
RATE, Q, I0 = point(1, 256), point(57, 256), point(261, 128)


@lru_cache(None)
def ln_mantissa(n, d):
    assert d <= n <= 2 * d
    z = point(n - d, n + d)
    z2 = square(z)
    term = z
    result = ZERO
    for j in range(65):
        result = add(result, mul(term, point(2, 2 * j + 1)))
        term = mul(term, z2)
    # z <= 1/3, so 2 z^131 / [131(1-z^2)] <= 3 z^131/131.
    return result[0], add(result, mul(term, point(3, 131)))[1]


@lru_cache(None)
def surprise(n):
    assert 0 < n <= UNIT
    exponent = n.bit_length() - 1
    mantissa = div(ln_mantissa(n, 1 << exponent), ln_mantissa(2, 1))
    return sub(point(192 - exponent), mantissa)


def eta(x):
    assert 0 <= x[0] <= x[1] <= UNIT
    if x[1] == 0:
        return ZERO
    if x[0] == 0:
        assert x[1] < UNIT // 4  # eta is increasing here
        return 0, mul(x, surprise(x[1]))[1]
    return mul(x, (max(0, surprise(x[1])[0]), surprise(x[0])[1]))


def text(box, digits):
    def fmt(v):
        whole, rem = divmod(abs(v), 10**digits)
        return ("-" if v < 0 else "") + f"{whole}.{rem:0{digits}d}"

    scale = 10**digits
    return "[" + fmt(box[0] * scale // UNIT) + ", " + fmt(-(-box[1] * scale // UNIT)) + "]"


def core():
    values = [1 - 2 * ((BASE >> i) & 1) for i in range(512)]
    rows = []
    for a, b in EDGES:
        assert b - a == a ^ b and (b - a) & (b - a - 1) == 0
        values[a] = values[b] = 0
        row = [0] * 512
        row[a], row[b] = 1, -1
        rows.append(wht(row))
    assert sum(values) == 0
    return values, wht(values), rows


TABLE, U, V = core()


def core_entropy(amplitudes):
    # Group the equal interval weights before transforming. All row entries
    # stored here are exact integer Walsh numerators on the nine-bit cube.
    groups = sorted(set(amplitudes))
    terms = [
        [sum(V[j][s] for j, t in enumerate(amplitudes) if t == group) for s in range(512)]
        for group in groups
    ]
    bins = Counter(zip(U, *terms))
    out = ZERO
    for (a, *weights), count in bins.items():
        coefficient = add(point(a), *(mul(point(w), g) for w, g in zip(weights, groups)))
        out = add(out, mul(point(count), eta(square(mul(point(1, 512), coefficient)))))
    return out


def seed_check():
    truth = []
    index = {endpoint: j for j, pair in enumerate(EDGES) for endpoint in pair}
    for x in range(1 << 18):
        addr = x & 511
        truth.append(TABLE[addr] if addr not in index else 1 - 2 * ((x >> (9 + index[addr])) & 1))
    assert all(truth[x] >= truth[x | (1 << i)] for x in range(len(truth)) for i in range(9))
    a = wht(truth)
    assert a[0] == 0 and a[1] * 256 == 57 * len(a)
    counts = Counter(abs(c) for c in a)
    assert sum(m * c * c for c, m in counts.items()) == len(a) ** 2
    assert sum(bin(s).count("1") * c * c for s, c in enumerate(a)) * 128 == 261 * len(a) ** 2
    entropy = add(*(mul(point(m), eta(point(c * c, len(a) ** 2))) for c, m in counts.items()))
    assert all(U[1 << j] == 114 for j in range(9))
    assert {a ^ b for a, b in EDGES} == {1 << j for j in range(9)}
    predicted = add(core_entropy([ZERO] * 9), point(9 * 16, 256))
    assert max(entropy[0], predicted[0]) <= min(entropy[1], predicted[1])
    return entropy


# State is (entropy, influence, distinguished singleton, arity).
def spine(g, depth):
    h, i, x, n = g
    factor = add(*(power(x, j) for j in range(depth)))
    return mul(factor, h), add(ONE, mul(factor, sub(i, ONE))), power(x, depth), 1 + depth * (n - 1)


def host(gates):
    ts = [g[2] for g in gates]
    h = core_entropy(ts)
    i = I0
    arity = 9
    for gh, gi, t, gn in gates:
        mass = square(t)
        h = add(h, mul(RATE, add(sub(gh, eta(mass)), mul(point(16), sub(ONE, mass)))))
        i = add(i, mul(RATE, sub(gi, ONE)))
        arity += gn - 1
    assert EDGES[0][0] ^ EDGES[0][1] == 1
    return h, i, add(Q, mul(RATE, ts[0])), arity


def score(g):
    return div(g[0], sub(g[1], ONE))


def ordinary(g, depth):
    return mul(score(g), sub(ONE, power(div(ONE, g[1]), depth)))


def asymmetric_fork(g, first_depth, side_depth):
    """Eight tuned edges. At the ninth, route two paths through one shared bit."""
    path = spine(g, 4)
    j = host([(ZERO, ONE, ZERO, 2)] + [path] * 8)
    # Zero marked amplitude is an independent private dictator; the two-bit
    # representation includes an unused distinguished core input.
    ah, ai, a, an = spine(g, first_depth)
    bh, bi, b, bn = spine(g, side_depth)
    t = path[2]
    fixed = [1 - 2 * (bin(s & (EDGES[0][0] >> 1)).count("1") % 2) for s in range(256)]
    bins = Counter(
        (U[(s << 1) | 1], sum(v[(s << 1) | 1] for v in V[1:]), fixed[s]) for s in range(256)
    )
    change = ZERO
    for (u, v, parity), m in bins.items():
        row = mul(a, mul(point(1, 512), add(point(u), mul(point(v), t))))
        side = mul(b, point(parity, 256))
        diff = sub(eta(square(add(row, side))), add(eta(square(row)), eta(square(side))))
        change = add(change, mul(point(m), diff))
    return (
        add(j[0], mul(Q, ah), mul(RATE, bh), change),
        add(j[1], mul(Q, sub(ai, ONE)), mul(RATE, sub(bi, ONE))),
        add(mul(Q, a), mul(RATE, b)),
        j[3] - 2 + an + bn - 1,
    )


def compose_marked(parent, child):
    """Put child into the parent's marked input; retain the child's mark."""
    h, i, x, n = parent
    h2, i2, x2, n2 = child
    return add(h, mul(x, h2)), add(i, mul(x, sub(i2, ONE))), mul(x, x2), n + n2 - 1


def retuned(g, check_shorter=False):
    """Two successive last-copy replacements. Only the parallel edge transmits the mark."""
    path = spine(g, 4)
    prefix = spine(g, 3)
    untouched = (ZERO, ONE, ZERO, 2)
    special = host([untouched] + [path] * 8)
    # Mark the untouched private dictator, whose singleton is its edge probability.
    marked = special[0], special[1], RATE, special[3]
    lower = host([marked] + [path] * 8)
    if check_shorter:
        shorter = ordinary(host([compose_marked(prefix, lower)] * 9), 140)
        assert shorter[1] < ordinary(g, 140)[0]
        print("one fewer marked host", text(shorter, 30))
    upper = host([compose_marked(prefix, lower)] + [path] * 8)
    return host([compose_marked(prefix, upper)] * 9)


def dense_perturbations(seed_h):
    # Split one edge or use Maj_3 and its first input on two exclusive ports.
    # Both are literal 19-bit truth tables.
    index = {endpoint: j for j, e in enumerate(EDGES) for endpoint in e}
    for fork in (False, True):
        values = []
        for raw in range(1 << 19):
            if fork:
                z, p, q = raw & 1, (raw >> 9) & 1, (raw >> 18) & 1
                u = int(z + p + q >= 2)
                addr = (raw & 510) | u
            else:
                addr = raw & 511
            if addr not in index:
                v = TABLE[addr]
            else:
                j = index[addr]
                if fork and j == 0:
                    selector = z
                elif not fork and addr == EDGES[0][1]:
                    selector = (raw >> 18) & 1
                else:
                    selector = (raw >> (9 + j)) & 1
                v = 1 - 2 * selector
            values.append(v)
        a = wht(values)
        assert a[0] == 0
        hist = Counter(abs(t) for t in a)
        den = len(a) ** 2
        h = add(*(mul(point(m), eta(point(c * c, den))) for c, m in hist.items()))
        I = point(sum(bin(t).count("1") * v * v for t, v in enumerate(a)), den)
        if fork:
            delta = ZERO
            for s in range(256):
                r = point(U[2 * s + 1], 1024)  # singleton of majority is 1/2
                v = point((-1) ** (bin(s & (EDGES[0][0] >> 1)).count("1")), 256)
                delta = add(delta, sub(eta(square(add(r, v))), add(eta(square(r)), eta(square(v)))))
            target = add(seed_h, mul(Q, point(2)), delta)
            assert I == add(I0, mul(Q, point(1, 2))) and point(a[1], len(a)) == add(
                mul(Q, point(1, 2)), RATE
            )
        else:
            target = add(seed_h, point(2, 256))
            assert I == add(I0, point(1, 512))
        assert max(target[0], h[0]) <= min(target[1], h[1])
    print("two dense 19-bit perturbations verified")


def main():
    h = seed_check()
    dense_perturbations(h)
    g = h, I0, Q, 18
    for k in range(1, 19):
        g = host([spine(g, 4)] * 9)
        if k in (10, 14, 18):
            print(
                "shared stages",
                k,
                "base arity",
                g[3],
                "ordinary depth 120",
                text(ordinary(g, 120), 36),
            )
    result = ordinary(g, 120)
    assert result[0] * 10**22 > 65218511673478223969023 * UNIT
    # Splitting m original matched edges into independent endpoint selectors
    # adds two entropy bits per unit edge mass and one half unit of influence.
    for m in range(1, 7):
        split = add(h, point(2 * m, 256)), add(I0, point(m, 512)), Q, 18 + m
        assert score(split)[1] < score(g)[0]
    for depths in [(3,) + (4,) * 8, (5,) + (4,) * 8, (3, 5) + (4,) * 7, (5, 3, 5) + (4,) * 6]:
        other = host([spine(g, d) for d in depths])
        print("unequal spine", depths, "amplified", text(score(other), 13))
    for side in (2, 3, 4, 5, 6, 7):
        fork = asymmetric_fork(g, 3, side)
        out = host([fork] * 9)
        print("fork side depth", side, "amplified", text(score(out), 15))
    for k in range(1, 15):
        g = retuned(g, check_shorter=(k == 1))
        if k in (1, 5, 10, 14):
            print(
                "asymmetric rounds", k, "base arity", g[3], "ordinary", text(ordinary(g, 140), 36)
            )
    result = ordinary(g, 140)
    low = 6521851167347822949109657013506222645
    assert low * UNIT < result[0] * 10**36 <= result[1] * 10**36 < (low + 1) * UNIT
    print("certified ordinary depth 140", text(result, 36))


if __name__ == "__main__":
    main()
