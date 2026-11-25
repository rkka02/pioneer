"""Exact section, boundary and loss identities for exchanges with a subcube."""

from collections import Counter, deque
from fractions import Fraction as Q

import numpy as np

from certificate import enclose_text
from max1_pool import logloss
from walsh import checked, degrees, signs, wht


def influence(event):
    a = checked(signs(event))
    return Q(int(np.dot(a * a, degrees(len(a).bit_length() - 1))), len(a) ** 2)


def branching(coefficients, denominator):
    pairs = Counter()
    for s in np.flatnonzero(coefficients).tolist():
        if s & (s - 1) == 0:
            continue
        child = int(coefficients[s]) ** 2
        for j in range(len(coefficients).bit_length() - 1):
            if s & (1 << j):
                pairs[child, int(coefficients[s ^ (1 << j)]) ** 2] += 1
    result = [Q(0), Q(0)]
    for (child, parent), count in pairs.items():
        for side, loss in enumerate(logloss(Q(parent, child))):
            result[side] += Q(4 * count * child, denominator**2) * loss
    return tuple(result)


def connected(event):
    pts = set(map(int, np.flatnonzero(event)))
    if not pts:
        return False
    queue = deque([pts.pop()])
    while queue:
        x = queue.popleft()
        for j in range(len(event).bit_length() - 1):
            y = x ^ (1 << j)
            if y in pts:
                pts.remove(y)
                queue.append(y)
    return not pts


def compare_sections(A):
    count, size = A.shape
    d = count.bit_length() - 1
    mu = Q(1, count)
    assert A.sum() == size
    C = np.zeros_like(A)
    C[0] = True
    defect = A ^ C
    rho = Q(int(defect.sum()), count * size)
    eps = influence(A.ravel()) - 2 * d * mu
    defect_cost = influence(defect.ravel())
    overlap = sum(np.count_nonzero(defect[0] != defect[1 << i]) for i in range(d))
    assert eps == defect_cost - Q(4 * int(overlap), count * size)
    assert defect_cost <= eps + 2 * (d + 1) * rho
    if d >= 3 and rho <= mu**3:
        assert (2 * d - 1) * defect_cost <= 3 * d * eps
    return eps, rho


def exchange(event, d):
    mu = Q(1, 1 << d)
    A = np.zeros((1 << d, len(event)), dtype=bool)
    A[0], A[1] = ~event, event
    eps, rho = compare_sections(A)
    assert eps == 2 * mu * influence(event)
    assert rho == 2 * mu * Q(int(event.sum()), len(event))
    diff = A.astype(np.int64)
    diff[0] -= 1
    a = wht(diff.ravel()).reshape(A.shape)
    core = wht(event)
    assert np.array_equal(a[1], -2 * core)
    actual = branching(a[1], A.size)
    predicted = tuple(4 * mu**2 * x for x in branching(core, len(event)))
    assert actual == predicted
    return eps, rho, actual


def main():
    rng = np.random.default_rng(412301)
    for d, b in ((2, 2), (3, 4), (4, 5)):
        for _ in range(15):
            A = np.zeros((1 << d, 1 << b), dtype=bool)
            A[0] = True
            count = int(rng.integers(0, 1 << b))
            A[0, rng.choice(1 << b, count, False)] = False
            outside = rng.choice(((1 << d) - 1) * (1 << b), count, False)
            A.ravel()[(1 << b) + outside] = True
            compare_sections(A)
    for table in range(256):
        event = ((table >> np.arange(8)) & 1).astype(bool)
        exchange(event, 3)
    # A connected island with a complete lower face can carry an arbitrary
    # event on its upper face. All nonempty data pairs keep their odds.
    data = rng.integers(0, 2, 64).astype(bool)
    island = np.concatenate((np.ones_like(data), data))
    assert connected(island)
    original = branching(wht(data), len(data))
    joined = branching(wht(island), len(island))
    assert joined[0] >= original[1] / 2
    w, d = 9, 3
    thin = np.zeros(len(island) << w, dtype=bool)
    thin[: len(island)] = island
    assert connected(thin)
    eps, rho, e = exchange(thin, d)
    mu = Q(1, 1 << d)
    assert rho <= mu**3
    print(
        "connected exchange, width, density distance, deficit, slice",
        w,
        rho,
        eps,
        enclose_text(e, 10),
    )
    # Exact larger widths use the partial-WHT identity of a point indicator.
    # Multiplication by it adds w fresh edge influences 2*w*theta*2^-w.
    theta = Q(int(island.sum()), len(island))
    inner_i = influence(island)
    for w in (9, 14, 25, 48):
        delta = Q(1, 1 << w)
        gap = 2 * mu * delta * (inner_i + 2 * w * theta)
        dist = 2 * mu * delta * theta
        if w == 9:
            assert gap == eps and dist == rho
        if w >= 14:
            assert gap <= mu**3 and dist <= mu**3
        print("exact connected-island transfer", w, "gap,distance", gap, dist)


if __name__ == "__main__":
    main()
