"""Optimize B and X directly on genuine code-shell gates and their affine spectra."""

from fractions import Fraction as Q
from itertools import combinations
import random

import numpy as np

from certificate import enclose_text
from max1_pool import logloss
from max3_codes import code_words, linear_values, orbit_min, scramble, verify_recode
from walsh import checked, degrees, signs


def scores(a):
    n = len(a).bit_length() - 1
    d = degrees(n)
    p = a * a
    I = int(np.dot(p, d))
    db = I - int(p[d == 1].sum())
    if db == 0:
        return ((Q(0), Q(0)),) * 2
    counts = {}
    for s in np.flatnonzero((p > 0) & (d >= 2)).tolist():
        k = int(d[s])
        child = int(p[s])
        parents = tuple(
            sorted(int(p[s ^ (1 << i)]) for i in range(n) if s & (1 << i) and p[s ^ (1 << i)])
        )
        if parents:
            key = k, child, parents
            counts[key] = counts.get(key, 0) + child
    B = [Q(0), Q(0)]
    X = [Q(0), Q(0)]
    for (k, c, parents), w in counts.items():
        terms = [logloss(Q(p, c)) for p in parents]
        for side in (0, 1):
            vals = [v[side] for v in terms]
            loss = sum(vals)
            B[side] += Q(w, db) * loss
            X[side] += Q(w, I * k) * (loss * loss - sum(x * x for x in vals))
    return tuple(B), tuple(X)


def main():
    rng = random.Random(412310)
    cache = {}
    for label in ("Hamming(7,4)", "BCH(15,7)", "RM(1,4)", "RM(2,4)"):
        weights = code_words(label)
        vals, layers = np.unique(weights, return_inverse=True)
        n = len(weights).bit_length() - 1
        exhaustive = n == 4
        peak = [[Q(0), Q(0)] for _ in range(2)]
        patterns = list(range(2, 1 << len(vals), 2))
        if not exhaustive:
            rng.shuffle(patterns)
            patterns = patterns[:8]
        bits = np.arange(1 << n)
        if exhaustive:
            # Coordinates of each output frequency are dot products with
            # an unordered physical basis. Quotient by coordinate permutations.
            maps = []
            for basis in combinations(range(1, 1 << n), n):
                if len(set(linear_values(basis))) == len(weights):
                    dst = np.zeros_like(bits)
                    for i, row in enumerate(basis):
                        dst |= (degrees(n)[bits & row] % 2) << i
                    maps.append(np.argsort(dst))
            assert len(maps) == 840
        tests = 0
        for pat in patterns:
            f = signs((pat >> layers) & 1)
            a = checked(f)
            tags = np.flatnonzero(a == 0).tolist()
            if not exhaustive:
                rng.shuffle(tags)
                tags = tags[:2]
            for tag in tags:
                if exhaustive:
                    spectra = (a[inverse ^ tag] for inverse in maps)
                else:
                    _, best = orbit_min(a, tag)
                    bases = [best, scramble(n, n, rng)]
                    # A physical basis maps frequency to the vector of its
                    # parities on the basis. verify_recode uses the transpose.
                    spectra = []
                    for basis in bases:
                        rows = [
                            sum(((v >> i) & 1) << j for j, v in enumerate(basis)) for i in range(n)
                        ]
                        offset = int(linear_values(rows)[tag])
                        spectra.append(verify_recode(f, rows, n, tag=offset))
                for rec in spectra:
                    key = tuple(map(abs, rec)) if exhaustive else None
                    if key is not None and key in cache:
                        result = cache[key]
                    else:
                        result = scores(rec)
                        if key is not None:
                            cache[key] = result
                    for hi, v in zip(peak, result):
                        hi[:] = [max(x, y) for x, y in zip(hi, v)]
                    tests += 1
        print(
            "balanced recodings, direct maxima B,X/I",
            label,
            tests,
            enclose_text(peak[0], 9),
            enclose_text(peak[1], 9),
        )


if __name__ == "__main__":
    main()
