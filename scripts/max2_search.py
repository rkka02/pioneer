"""Direct balanced search for B and X/I through 18 bits, including affine changes."""

from collections import Counter
from fractions import Fraction as Q
import numpy as np

from certificate import enclose_text
from max1_pool import logloss
from max2_levels import tied_majority
from walsh import PAIRS, degrees, record_seed, seed_parts, signs, splits, wht


def quick(a, n, need_mixed):
    p = (a / len(a)) ** 2
    ds = degrees(n)
    db = np.sum(p * np.where(ds >= 2, ds, 0))
    if not db:
        return 0.0
    if not need_mixed:
        mean = 0.0
        for i in range(n):
            u, v = splits(p, i)
            ids = np.flatnonzero(v)
            mean += np.sum(v[ids] * np.log2(1 + u[ids] / v[ids]))
        return float(mean / db)
    accum = np.zeros_like(p)
    cross = 0.0
    for i in range(n):
        # Store the prefix loss in the original spectral order.
        paired = p.reshape(-1, 2, 1 << i)
        loc = np.nonzero(paired[:, 1, :])
        u = paired[:, 0, :][loc]
        v = paired[:, 1, :][loc]
        loss = np.log2(1 + u / v)
        s = (loc[0] << (i + 1)) + (1 << i) + loc[1]
        cross += np.sum(v * loss * 2 * accum[s] / ds[s])
        accum[s] += loss
    return float(cross / np.sum(p * ds))


def exact(a, n):
    """Group pairs and ordered cross products of integer WHT magnitudes."""
    ds = degrees(n)
    p = a * a
    I = int(np.sum(p * ds))
    db = I - int(p[ds == 1].sum())
    assert a[0] == 0 and db
    patterns = Counter()
    for s in np.flatnonzero(a).tolist():
        k = int(ds[s])
        if k >= 2:
            v = abs(int(a[s]))
            parents = tuple(
                sorted(
                    abs(int(a[s ^ (1 << i)])) for i in range(n) if (s >> i) & 1 and a[s ^ (1 << i)]
                )
            )
            if parents:
                patterns[k, v, parents] += 1
    b = [Q(0), Q(0)]
    x = [Q(0), Q(0)]
    for (k, v, parents), m in patterns.items():
        l = [logloss(Q(u * u, v * v)) for u in parents]
        for side in (0, 1):
            pre = pair = Q(0)
            for bounds in l:
                pair += 2 * pre * bounds[side]
                pre += bounds[side]
            b[side] += Q(m * v * v, db) * pre
            x[side] += Q(m * v * v, k * I) * pair
    return b, x


def starting(n):
    idx = np.arange(1 << n)
    if n >= 10:
        core = idx % 512
        f = seed_parts()[core].copy()
        for j, (u, v) in enumerate(PAIRS):
            use = (core == u) | (core == v)
            f[use] = signs((idx[use] >> (9 + j % (n - 9))) & 1)
        return f
    if n % 2 == 0:
        return tied_majority(n, "random")
    z = idx % (1 << (n - 1))
    return signs((idx >> (n - 1)) ^ (degrees(n - 1)[z] > (n - 1) // 2))


def move(f, n, idx, rng, kind):
    if kind == 0:
        x = rng.choice(np.flatnonzero(f == 1))
        y = rng.choice(np.flatnonzero(f == -1))
        out = f.copy()
        out[x], out[y] = -1, 1
        return out
    target = int(rng.integers(n))
    other = [i for i in range(n) if i != target]
    if kind == 1:
        # Invertible linear map with an even-parity predicate on the other bits.
        v = sum(1 << int(i) for i in rng.choice(other, size=min(3, n - 1), replace=False))
        on = degrees(n)[idx & v] % 2
    else:
        width = int(rng.integers(1, min(n - 1, 7) + 1))
        cols = rng.choice(other, size=width, replace=False)
        fixed = sum(1 << int(i) for i in cols)
        value = int(rng.integers(1 << n)) & fixed
        on = (idx & fixed) == value
    return f[idx ^ (on.astype(np.int64) << target)]


def main():
    rng = np.random.default_rng(412202611)
    records = {}
    for n in range(8, 19):
        idx = np.arange(1 << n)
        start = starting(n)
        assert not np.sum(start)
        steps = 96 if n <= 12 else 56 if n <= 15 else 24
        for mixed in (False, True):
            f = start.copy()
            score = quick(wht(f), n, mixed)
            accepted = 0
            for step in range(steps):
                trial = move(f, n, idx, rng, step % 3)
                a = wht(trial)
                value = quick(a, n, mixed)
                if value > score + 1e-13:
                    f, score, accepted = trial, value, accepted + 1
            if mixed not in records or score > records[mixed][0]:
                records[mixed] = score, n, f
            print(n, ("B", "X/I")[mixed], steps, accepted, round(score, 8), flush=True)
    for mixed, (_, n, f) in records.items():
        b, x = exact(wht(f), n)
        print(
            "certified finalist",
            ("B", "X/I")[mixed],
            n,
            "B, X/I",
            enclose_text(b, 10),
            enclose_text(x, 10),
        )


if __name__ == "__main__":
    main()
