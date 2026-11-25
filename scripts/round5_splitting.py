"""Direct tests of uniform splitting, including low-degree intermediate auxiliary vertices."""

from collections import Counter
from itertools import combinations, product

import networkx as nx

from flow_lab import divergence, edges, flower, mincut
from round1_ports import LocalOrientations, cubic_derivative, port_pins


def small():
    n = 4
    ij = list(combinations(range(n), 2))
    shores = range(1, (1 << n) - 1)
    crossing = [tuple(i for i, (a, b) in enumerate(ij) if (s >> a ^ s >> b) & 1) for s in shores]
    ins = [tuple(i for i in range(n) if s >> i & 1) for s in shores]
    result = Counter()
    for stars in product(range(3), repeat=n):
        d = sum(stars)
        if d < 2 or d == 3:
            continue
        valid_pairs = [
            (u, v)
            for u in range(n)
            for v in range(u, n)
            if stars[u] and stars[v] and (u != v or stars[u] >= 2)
        ]
        spoke_cut = [sum(stars[i] for i in vs) for vs in ins]
        loss = [[2 * int(bool((s >> u) & (s >> v) & 1)) for s in shores] for u, v in valid_pairs]
        for mult in product(range(3), repeat=len(ij)):
            cuts = [a + sum(mult[j] for j in es) for a, es in zip(spoke_cut, crossing)]
            k = min(5, min(cuts))
            if k < 2:
                continue
            # Checking the largest applicable k certifies every smaller k as well.
            good = next(
                (i for i, v in enumerate(loss) if all(c - j >= k for c, j in zip(cuts, v))), None
            )
            assert good is not None, (stars, mult)
            u, v = valid_pairs[good]
            left = list(stars)
            left[u] -= 1
            left[v] -= 1
            new = list(mult)
            if u != v:
                new[ij.index((u, v))] += 1
            for inside, es in zip(ins, crossing):
                assert sum(left[i] for i in inside) + sum(new[j] for j in es) >= k
            result[k, d % 2] += 1
    print(
        "4 terminals, counts by maximal tested k and parity of split degree", sorted(result.items())
    )


def lifts():
    # Add an even vertex on two virtual edges, plus a closed two-edge walk.
    # A prescribed nonzero boundary tests lifting beyond the zero-boundary use.
    count = 0
    for n, raw, seed in [(10, edges(nx.petersen_graph()), 65), (20, flower(5), 74)]:
        p = cubic_derivative(raw, seed)
        assert mincut(n, p) == 5
        for beta in ([0] * n, [0, 1, 2] + [0] * (n - 3)):
            for minority in range(5):
                signs = LocalOrientations(n, p).solve(beta, port_pins(p, 0, minority))
                assert signs is not None
                picks = [i for i, arc in enumerate(p) if 0 not in arc][:2]
                new = [e for i, e in enumerate(p) if i not in picks]
                vals = [t for i, t in enumerate(signs) if i not in picks]
                for i in picks:
                    a, b = p[i]
                    new.extend([(a, n), (n, b)])
                    vals.extend([signs[i]] * 2)
                new.extend([(1, n), (n, 1)])
                vals.extend([1, 1])
                assert all(
                    (d - b) % 3 == 0 for d, b in zip(divergence(n + 1, new, vals), beta + [0])
                )
                count += 1
    print("lifted zero and nonzero pinned orientations", count)


def two_cuts():
    # Glue two realizable base graphs along an oriented virtual edge. Include
    # both possible coincidences of endpoints, parallel edges and reversed pins.
    small = edges(nx.complete_graph(6))
    large = cubic_derivative(edges(nx.petersen_graph()), 81)
    cases = checks = 0
    for lhs, rhs in [(small, small), (small, large)]:
        n = max(max(e) for e in lhs) + 1
        m = max(max(e) for e in rhs) + 1
        for loop_left, loop_right in product((False, True), repeat=2):

            def cut_block(k, p, loop):
                signs = LocalOrientations(k, p).solve([0] * k, {})
                assert signs
                if loop:
                    return list(p), signs, (0, 0)
                u, v = p[0]
                return p[1:], [s * signs[0] for s in signs[1:]], (u, v)

            l, lv, (a1, a2) = cut_block(n, lhs, loop_left)
            r, rv, (b2, b1) = cut_block(m, rhs, loop_right)
            whole = l + [(x + n, y + n) for x, y in r] + [(a1, n + b1), (n + b2, a2)]
            assert all(x % 3 == 0 for x in divergence(n + m, whole, lv + rv + [1, 1]))
            # Every nonempty proper single-block shore has an old cut of exactly its size.
            for order, base, pair, offset, other in [
                (n, l, (a1, a2), 0, range(n, n + m)),
                (m, r, (b1, b2), n, range(n)),
            ]:
                for mask in range(1, (1 << order) - 1):
                    inside = {v for v in range(order) if mask >> v & 1}
                    small_cut = sum((a in inside) != (b in inside) for a, b in base + [pair])
                    shore = {v + offset for v in inside}

                    def cut(vertices):
                        return sum((a in vertices) != (b in vertices) for a, b in whole)

                    assert min(cut(shore), cut(shore | set(other))) == small_cut
                    checks += 1
            if n + m == 12:
                for mask in range(1, 1 << (n + m - 1)):
                    assert sum(((mask >> a) ^ (mask >> b)) & 1 for a, b in whole) not in (1, 3)
            cases += 1
    print("two-cut assemblies, all single-block cut identities", cases, checks)


if __name__ == "__main__":
    small()
    lifts()
    two_cuts()
