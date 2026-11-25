"""Exact eight-coordinate exchange bounds, using integer permutation counts."""

from collections import Counter
from functools import lru_cache
from itertools import combinations, permutations, product
from math import comb, lcm
from sympy import Matrix

R = 8
P = lcm(*(comb(h, d) for h in range(R + 1) for d in range(h + 1)))
SIG = [(p, q) for p in range(2, 6) for q in range(2, 8 - p)]
BOX = [
    [s for s in SIG if max(s) <= 3],
    [s for s in SIG if s[0] >= 4],
    [s for s in SIG if s[1] >= 4],
]


def two_set_limit():
    """Test five two-by-two exchanges. Crossings fix the allowed destination edges."""
    edges = [1 << i | 1 << j for i, j in combinations(range(R), 2)]
    options = {d: [c for c in edges if not d & c] for d in edges}
    counts = Counter()
    for drops in combinations(edges, 5):
        choices = [[c for c in options[d] if all(d == f or c & f for f in drops)] for d in drops]
        if not all(choices):
            continue
        for takes in product(*choices):
            pairs = set(zip(drops, takes))
            if any((c, d) in pairs for d, c in pairs):
                counts["reverse"] += 1
                continue
            if all(
                sum(d >> i & 1 for d in drops) == sum(c >> i & 1 for c in takes) for i in range(R)
            ):
                counts["balanced-five"] += 1
                continue
            raise AssertionError((drops, takes))
    return counts


def four_edge_shapes():
    """Classify four two-by-two exchanges on eight named coordinates."""
    edges = [1 << i | 1 << j for i, j in combinations(range(R), 2)]
    # Relabel the first rule. A second rule cannot repeat either side (crossing)
    # or reverse an existing rule (twice the common displacement is nonzero).
    first = (3, 12)

    def compatible(u, v):
        d, c = u
        e, f = v
        return d != e and c != f and d & f and c & e and (d, c) != (f, e)

    candidates = [(d, c) for d in edges for c in edges if not d & c and compatible(first, (d, c))]
    matrices = set()
    for tail in combinations(candidates, 3):
        if all(compatible(u, v) for u, v in combinations(tail, 2)):
            rows = (first,) + tail
            cols = [tuple((d >> i & 1) - (c >> i & 1) for d, c in rows) for i in range(R)]
            matrices.add(tuple(sorted(cols)))

    def canonical(cols):
        return min(
            tuple(sorted(tuple(col[i] for i in perm) for col in cols))
            for perm in permutations(range(4))
        )

    shapes = {canonical(cols) for cols in matrices}
    counts = Counter()
    for cols in shapes:
        cols = [col for col in cols if any(col)]
        killed = False
        for t in product(range(-2, 3), repeat=4):
            if sum(t):
                continue
            c = [sum(x * y for x, y in zip(t, col)) for col in cols]
            if any(c) and min(c) >= -1:
                counts["signed relation"] += 1
                killed = True
                break
        if killed:
            continue
        mat = Matrix(cols).T
        for v in mat.T.nullspace():
            den = lcm(*(int(x.q) for x in v))
            t = den * v
            if sum(t):
                assert mat.T * t == Matrix.zeros(len(cols), 1) and 0 < 5 * abs(sum(t)) < 704
                counts["small torsion"] += 1
                killed = True
                break
        if killed:
            continue
        # Translate the first used coordinate to zero. Equal entries on the
        # adjugate right-hand side force equal determinant multiples.
        square = mat[:, 1:]
        assert square.shape == (4, 4)
        det = abs(int(square.det()))
        heights = [0, *list(square.adjugate() * Matrix.ones(4, 1))]
        repeat = max(Counter(heights).values())
        assert (det == 2 and repeat >= 2) or (det == 4 and repeat >= 3)
        counts["antipodal coset"] += 1
    return len(matrices), len(shapes), dict(counts)


def ordered_cross(u, v):
    return u[0] <= v[0] + 1 and v[1] <= u[1] + 1


def consistent(u, empty_shapes):
    for e in empty_shapes:
        if u == e:
            continue
        if (e[0] > e[1] and ordered_cross(e, u)) or (e[0] < e[1] and ordered_cross(u, e)):
            return False
    return True


@lru_cache(None)
def box_cost(box, empty_shapes, conditioned, allow_chain=True):
    # With a distinguished 2,2 singleton the other central exchanges all lose one
    # forced coordinate on either side. Their residual displacements increase by 2d.
    free = R - 2 * conditioned
    dp = [0] * (P + 1)
    for p, q in box:
        if not consistent((p, q), empty_shapes):
            continue
        for d in range(free + 1):
            c = d + p - q
            if c < 0 or d + c > free:
                continue
            if d + c == 0:
                continue  # equal signature and nonzero (p+2*conditioned) times the unit.
            if not conditioned and ((min(d, c) == 0) != ((p, q) in empty_shapes)):
                continue
            if (not conditioned or not allow_chain) and (p, q) == (2, 2) and d == c == 1:
                continue  # the unconditioned central case has no 2,2 singleton.
            weight = (8 - p - q) * 2 ** (free - d - c)
            debit = P // comb(d + c, d)
            multiplicity = P // debit
            if min(d, c) == 1:
                # Distinct singleton sides. If all other singleton centres exhaust
                # the opposite side, the centres have the same double.
                multiplicity = min(multiplicity, max(d, c))
            if d == c == 2:
                multiplicity = min(multiplicity, 3)
            for _ in range(multiplicity):
                for j in range(P, debit - 1, -1):
                    dp[j] = max(dp[j], dp[j - debit] + weight)
    return dp[-1]


def profiles(allow_chain=True):
    best = [(-1, None), (-1, None)]
    rows = []
    off = [s for s in SIG if s[0] != s[1]]
    for flags in product([False, True], repeat=len(off)):
        empties = tuple(s for s, v in zip(off, flags) if v)
        if not all(consistent(u, empties) for u in empties):
            continue
        for distinguished in (0, 1):
            if distinguished and not consistent((2, 2), empties):
                continue
            if distinguished and any(s in BOX[0] for s in empties):
                continue  # the original singleton crosses all other central exchanges.
            costs = [
                box_cost(tuple(box), empties, distinguished if i == 0 else 0, allow_chain)
                for i, box in enumerate(BOX)
            ]
            costs[0] += distinguished * (4 * 2 ** (R - 2))
            rows.append((distinguished, sum(costs), empties))
            if sum(costs) > best[distinguished][0]:
                best[distinguished] = sum(costs), (empties, costs)
    return best, rows


if __name__ == "__main__":
    print("five-edge families", dict(two_set_limit()))
    print("four-edge ordered types, shapes, obstructions", four_edge_shapes())
    print("permutation denominator", P)
    best, rows = profiles()
    for i, (loss, witness) in enumerate(best):
        print("distinguished singleton", i, "loss", loss, "relaxed profile", witness)
    loss = max(v for v, _ in best)
    print("minimum N from eight labels", (8 * 2**R - loss + 1) // 2)
    no_chain, rows = profiles(False)
    print("distinguished singleton without four-step residual", no_chain[1][0])
    print("empty signatures above loss 604 without a chain", [e for _, v, e in rows if v > 604])
    four_or_pair = {(4, 3), (3, 4), (4, 2), (2, 4)}
    print(
        "loss without chain and without the four one-sided outer signatures",
        max(v for _, v, e in rows if not four_or_pair.intersection(e)),
    )
