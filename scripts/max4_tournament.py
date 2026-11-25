"""Target-only witness polynomial for the labelled-tournament gates of #132."""

from collections import Counter
from fractions import Fraction as Q
from math import comb, isqrt
import random
import numpy as np
from certificate import enclose_text
from max3_carries import tree
from max3_code_odds import scores
from max3_codes import entropy
from max4_reserve import entropy_counts
from max1_pool import logloss
from walsh import checked, degrees, signs, wht


def mean(x):
    return Q(sum(int(v) for v in x), len(x))


def dirichlet(x):
    a = wht(x)
    return Q(int(np.dot(a * a, degrees(len(x).bit_length() - 1))), len(x) ** 2)


def show(f, name, full_tree):
    a = checked(signs(f))
    I = dirichlet(signs(f))
    h = entropy(a)
    b, mixed = scores(a)
    values = [enclose_text(tuple(v / I for v in h), 8), enclose_text(b, 8), enclose_text(mixed, 8)]
    if full_tree:
        _, R, actual = tree(signs(f), random.Random(1324), "fixed")
        assert actual == I
        values += [str(R / I)]
    print(name, "H/I, incident loss B (formula also on biased gates), X/I, [fixed R/I]", *values)


def literal(L, centers, k, r):
    # Scaled versions use the true target/gate rule, with (k-1)/2 outgoing gates.
    b = L * centers
    n = b * k * r
    assert n <= 19
    x = np.arange(1 << n)
    balls = [(2**L - 1) << (L * j) for j in range(centers)]
    dist = np.min([degrees(b)[np.arange(1 << b) ^ z] for z in balls], axis=0)
    base, weak = (dist == 0).astype(np.int64), (dist <= 1).astype(np.int64)
    accept = np.zeros_like(x)
    W = np.zeros_like(x)
    for i in range(k):
        product = np.ones_like(x)
        for c in range(r):
            child = (x >> (b * (i * r + c))) % (1 << b)
            product *= base[child]
        W += product
        for offset in range(1, 1 + k // 2):
            j = (i + offset) % k
            c = (i + j) % r
            product *= 1 - weak[(x >> (b * (j * r + c))) % (1 << b)]
        accept += product
    assert max(accept) <= 1 and min(W - accept) >= 0
    a, mu = mean(base), mean(accept)
    assert mean(W) == k * a**r
    assert mu == k * a**r * (1 - mean(weak)) ** (k // 2)
    assert mean(W**2) / mean(W) == 1 + (k - 1) * a**r
    assert dirichlet(W) / mean(W) == Q(b * r, 2)
    assert mean((W - accept) ** 2) <= mean(W**2) - mu
    assert all(int(c) % (1 << (n - b * r)) == 0 for c in wht(W))
    if n == 9:
        composition(accept)
    show(accept, "scaled L,M,k,r=" + str((L, centers, k, r)), n <= 10)


def outer_law(event, p):
    n = len(event).bit_length() - 1
    vals = np.array([Q(int(v)) for v in event], dtype=object)
    for i in range(n):
        t = vals.reshape(-1, 2, 1 << i)
        lo, hi = t[:, 0, :].copy(), t[:, 1, :].copy()
        t[:, 0, :] = (1 - p) * lo + p * hi
        t[:, 1, :] = hi - lo
    mu = vals[0]
    weights = [(p * (1 - p)) ** int(j) * v * v for j, v in zip(degrees(n), vals)]
    assert sum(weights) == mu
    q = [w / (mu * (1 - mu)) for w in weights[1:]]
    assert sum(q) == 1
    b = sum(w * int(j) for w, j in zip(q, degrees(n)[1:]))
    return mu, b, entropy_counts(q)


def composition(event):
    p = Q(1, 2)
    Ibar = Q(1)
    Hbar = (Q(0), Q(0))
    for j in range(1, 4):
        p, b, h = outer_law(event, p)
        Ibar *= b
        Hbar = tuple(s + b * old for s, old in zip(h, Hbar))
        v = 4 * p * (1 - p)
        bias = entropy_counts([v, 1 - v])
        ratio = tuple((s * v + t) / (v * Ibar) for s, t in zip(Hbar, bias))
        if j == 1:
            a = checked(signs(event))
            direct = entropy(a)
            assert ratio[0] * dirichlet(signs(event)) <= direct[1]
            assert ratio[1] * dirichlet(signs(event)) >= direct[0]
        print("biased tournament tower scaled 9-bit seed, depth", j, "H/I", enclose_text(ratio, 8))
    # Independent 2-level integer WHT versus the general biased recursion.
    g = np.array([0, 1, 0, 0], dtype=np.int64)
    raw = np.arange(16)
    two = g[g[raw % 4] + 2 * g[raw // 4]]
    p, b, h = outer_law(g, Q(1, 2))
    p, b2, h2 = outer_law(g, p)
    v = 4 * p * (1 - p)
    assert dirichlet(signs(two)) == v * b * b2
    hh = entropy_counts([v, 1 - v])
    check = tuple(c + v * (t + b2 * s) for c, t, s in zip(hh, h2, h))
    direct = entropy(checked(signs(two)))
    assert check[0] <= direct[1] and check[1] >= direct[0]


def sqrt_upper(x, bits=64):
    return Q(isqrt((x.numerator << (2 * bits)) // x.denominator) + 1, 1 << bits)


def base_surprise(M, L=3):
    # Symbolic integer WHT of the M-center indicator, indexed by total degree
    # and the number of odd block parities. Repeated binomial convolution.
    counts = {(0, 0): 1}
    for _ in range(M):
        dest = {}
        for (k, o), cnt in counts.items():
            for j in range(L + 1):
                key = k + j, o + (j % 2)
                dest[key] = dest.get(key, 0) + cnt * comb(L, j)
        counts = dest
    b = L * M
    N = 1 << b
    hist = {}
    I = Q(0)
    U = [Q(0), Q(0)]
    for (k, o), cnt in counts.items():
        c = N - 2 * M if not k else 2 * abs(M - 2 * o)
        key = c, k
        hist[key] = hist.get(key, 0) + cnt
        if c and k:
            p = Q(c * c, N * N)
            I += cnt * k * p
            for side, surprise in enumerate(logloss(1 / p - 1)):
                U[side] += cnt * p * surprise**2 / k
    if b <= 16:
        f = signs(np.isin(np.arange(N), [(2**L - 1) << (L * j) for j in range(M)]))
        assert Counter(zip(abs(wht(f)).tolist(), degrees(b).tolist())) == hist
    print("exact center base M", M, "U/I", enclose_text(tuple(v / I for v in U), 8))


def actual_certificate(d, M):
    # No materialization of an n-bit truth table. Only the finite moment inequalities
    # in the report are used. Bounds avoid storing 2^m for the very large gates.
    L, b = d + 2, (d + 2) * M
    k, r = 2 * M * M + 1, isqrt(M - 1) + 1
    g = (r**d - 1) // (r - 1)
    m, n = b * r**d, b * M * (k * r) ** d
    base = Q(M, 1 << b)
    beta = base * sum(comb(b, j) for j in range(d + 1))
    assert k * base ** (r - 1) <= 1 and M * base < Q(1, 2)
    # EW = A.  mu/A >= 1-loss. EW^2/A <= (1+M*a0)(1+a0)^g.
    loss = M * M * g * beta + M * base
    x = (g + M) * base
    assert x < Q(1, 2) and loss < Q(1, 2)
    # e^x <= 1+2x for 0<=x<=1/2.
    err = (2 * x + loss) / (1 - loss)
    # err bounds both squared relative difference and the spectral mass outside supp W.
    # Bound h_2(err) <= err(log2(1/err)+log2 e) and log2(A/mu) <= 3*loss.
    logceil = max(0, err.denominator.bit_length() - err.numerator.bit_length() + 1)
    extra = err * (n + logceil + 2) + 3 * loss
    # (sqrt(m/2)-sqrt(n*err))^2 >= m/2 - sqrt(2*m*n*err).
    floor = Q(m, 2) - sqrt_upper(2 * m * n * err)
    assert floor > 0
    # 2-log2(e)>1/2 and mu <= M*base.
    upper = (2 * m - (1 - M * base) / 2 + extra) / floor
    assert upper < 4
    print(
        "actual d,M",
        d,
        M,
        "n,m",
        n,
        m,
        "relative-error less than 2^-",
        max(0, logceil - 2),
        "proved H/I <",
        enclose_text((upper, upper), 8),
    )


if __name__ == "__main__":
    for params in [(3, 1, 3, 1), (2, 1, 3, 2), (3, 2, 3, 1)]:
        literal(*params)
    for M in (3, 5):
        b = 3 * M
        x = np.arange(1 << b)
        base = np.isin(x, [7 << (3 * j) for j in range(M)]).astype(np.int64)
        show(base, "actual base M=" + str(M), M == 3)
    for M in (3, 5, 20, 81):
        base_surprise(M)
    for pair in ((1, 81), (2, 729), (3, 6561)):
        actual_certificate(*pair)
