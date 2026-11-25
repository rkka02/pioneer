"""Check rare activation, tensor dilution, and the local tests at a dictator."""

from fractions import Fraction as Q

import numpy as np

from certificate import enclose_text
from max1_pool import logloss, spine_mean, switch
from max2_routing import statistics
from walsh import degrees, record_seed, signs, wht


def summary(f):
    return statistics({0: wht(f)}, len(f))


def mask(f, w, with_sign=True):
    # The address and the mandatory sign are independent of all data.
    block = np.tile(np.ones_like(f), 1 << w)
    block[: len(f)] = f
    return np.concatenate((block, -block)) if with_sign else block


def interval_meets(a, b):
    return a[0] <= b[1] and b[0] <= a[1]


def mask_example(seed, w, t):
    I, A, _, _ = summary(seed)
    assert not np.sum(seed) and t >= 2
    delta = Q(1, 1 << w)
    boundary_log = logloss(((1 - delta) / delta) ** 2)
    Db = delta * (t * I + w + 2 - delta)
    expected = tuple(delta * (t * A[j] + w + w * delta * (boundary_log[j] - 1)) for j in (0, 1))
    tensor = np.array([1])
    for _ in range(t):
        tensor = np.kron(tensor, seed)
    f = mask(tensor, w)
    true_i, actual, _, actual_x = summary(f)
    assert true_i == 1 + delta * (t * I + w)
    assert true_i - (1 - delta) ** 2 == Db and interval_meets(expected, actual)
    h = mask(tensor, w, False)
    h_i, h_a, _, h_x = summary(h)
    assert h_i == true_i - 1 and interval_meets(h_a, actual) and actual_x[0] <= h_x[1]
    ah = wht(h)
    singles = [int(ah[1 << j]) for j in range(len(h).bit_length() - 1)]
    assert sum(bool(v) for v in singles) == w
    assert all(abs(v) == len(h) * delta for v in singles if v)
    rare_branch = tuple(delta * (t * A[j] + w * (1 - delta)) for j in (0, 1))
    observed = (h_a[0] - w * delta**2 * boundary_log[1], h_a[1] - w * delta**2 * boundary_log[0])
    assert interval_meets(rare_branch, observed)
    return tuple(x / Db for x in actual)


def transfer_x(f, w, with_sign=True):
    I, _, _, _ = summary(f)
    delta = Q(1, 1 << w)
    a = wht(f)
    n = len(a).bit_length() - 1
    lower = Q(0)
    slow = Q(0)
    for s in np.flatnonzero(a).tolist():
        k = int(degrees(n)[s])
        if k < 2:
            continue
        v = int(a[s]) ** 2
        pre = pair = Q(0)
        for i in range(n):
            if (s >> i) & 1:
                l = logloss(Q(int(a[s ^ (1 << i)]) ** 2, v))[0]
                pair += 2 * pre * l
                pre += l
        if k >= w + 1:
            lower += Q(v, len(f) ** 2 * k) * pair
        else:
            slow += Q(v, len(f) ** 2 * k) * pair
    assert slow <= 18 * w**3 + 150 * I
    *_, x = summary(mask(f, w, with_sign))
    assert x[1] >= delta * lower / 2


def diluted(f, t):
    inp = wht(f)
    var = 1 - Q(int(inp[0]) ** 2, len(f) ** 2)
    I, _, _, X = summary(f)
    A = np.array([1, -1])
    for _ in range(t):
        A = np.kron(A, f)
    j, _, _, Y = summary(A)
    assert j == 1 + t * I and Y[1] >= Q(2, 3) * t * (1 - var) ** (t - 1) * X[0]


def outer_mask(g, w, r, t):
    core = np.ones(1, dtype=np.int64)
    for _ in range(t):
        core = np.kron(core, g)
    G = mask(core, w)
    h = mask(G, r, False)
    eta = Q(1, 1 << r)
    mu = eta / 2
    delta = Q(1, 1 << w)
    I, N, _, _ = summary(G)
    ih, nh, _, _ = summary(h)
    C = np.zeros(len(h), dtype=bool)
    C[len(G) // 2 : len(G)] = True
    assert Q(np.count_nonzero(h < 0), len(h)) == mu
    assert Q(np.count_nonzero((h < 0) ^ C), len(h)) == eta * delta / 2
    assert ih - 2 * mu * (r + 1) == eta * (I - 1)
    a = wht(h)
    origin = int(a[0])
    singles = [int(a[1 << i]) for i in range(len(h).bit_length() - 1)]
    singleton = sum(Q(v * v, len(h) ** 2) * logloss(Q(origin**2, v * v))[1] for v in singles if v)
    assert nh[0] - singleton >= eta * N[1]
    # One Walsh slice of the signed exchange: only z present among the r+1
    # subcube coordinates. Count only deletions leaving a nonempty free parent.
    length = len(G) // 2
    defect = (h < 0).astype(np.int64) - C.astype(np.int64)
    row = wht(defect)[length : 2 * length]
    inner = mask(core, w, False)
    assert np.array_equal(row[1:], -wht(inner)[1:])
    assert int(np.max(np.abs(row[1:]), initial=0)) <= np.count_nonzero(defect)
    actual = [Q(0), Q(0)]
    for v in np.flatnonzero(row).tolist():
        if v == 0 or v & (v - 1) == 0:
            continue
        p = int(row[v]) ** 2
        for j in range(length.bit_length() - 1):
            if v & (1 << j):
                odds = Q(int(row[v ^ (1 << j)]) ** 2, p)
                for side, ell in enumerate(logloss(odds)):
                    actual[side] += Q(4 * p, len(h) ** 2) * ell
    _, old, _, _ = summary(g)
    expected = tuple(eta**2 * delta * (t * v + w * (1 - delta)) for v in old)
    assert interval_meets(actual, expected)
    transfer_x(G, r, False)


def main():
    g = switch(1)
    for w, t in ((1, 2), (3, 2), (4, 3), (5, 3)):
        print(
            "exact near-dictator B, mask width, block count",
            w,
            t,
            enclose_text(mask_example(g, w, t), 8),
        )
    for f in (g, signs(degrees(4) >= 3), switch(2)):
        for w in (1, 2, 4):
            transfer_x(f, w)
        diluted(f, 3)
    for w, r, t in ((2, 2, 2), (3, 2, 2), (4, 3, 2)):
        outer_mask(g, w, r, t)
    # A non-enumerated near-dictator built from the certified high-ratio seed.
    f = record_seed()
    I, A, _, _ = summary(f)
    for w in (8, 16, 32, 64):
        t = w * w
        delta = Q(1, 1 << w)
        L = logloss(((1 - delta) / delta) ** 2)
        B = tuple(
            (t * A[j] + w + w * delta * (L[j] - 1)) / (t * I + w + 2 - delta) for j in (0, 1)
        )
        print(
            "Numaro data, w,t,I-1,B",
            w,
            t,
            enclose_text((delta * (t * I + w),) * 2, 12),
            enclose_text(B, 9),
        )
    # A two-copy rare cut of the genuine depth-20 gate, via its exact
    # marked-leaf mean. This tests the transfer on a high-H/I balanced input.
    depth = 20
    mean, _ = spine_mean(f, depth)
    J = I**depth
    w = 32
    delta = Q(1, 1 << w)
    branch = tuple(delta * (2 * J * v + w * (1 - delta)) for v in mean)
    cost = delta * (2 * J + w)
    print(
        "two-copy depth-20 Numaro cut, I(h), raw branching loss",
        enclose_text((cost, cost), 12),
        enclose_text(branch, 12),
    )
    w, r = 38, 6
    delta, eta = Q(1, 1 << w), Q(1, 1 << r)
    mu = eta / 2
    gap = eta * delta * (2 * J + w)
    dist = eta * delta / 2
    assert gap < mu**3 and dist < mu**3
    raw = tuple(eta * delta * (2 * J * v + w * (1 - delta)) for v in mean)
    print(
        "nested depth-20 cut, volume, boundary excess, distance, raw loss lower endpoint",
        mu,
        enclose_text((gap, gap), 14),
        dist,
        enclose_text((raw[0], raw[0]), 14),
    )
    print(
        "nested cut, exactly one fixed frequency slice",
        enclose_text(tuple(eta * v for v in raw), 16),
    )


if __name__ == "__main__":
    main()
