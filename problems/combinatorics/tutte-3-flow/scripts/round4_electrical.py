"""Exact closest-lift and fractional-tree checks. All electrical arithmetic is integral after scaling."""

from collections import Counter
from itertools import combinations, product
from math import lcm

import networkx as nx
import sympy as sp

from flow_lab import boundary_counts, divergence, edges, flower, jlpt, mincut
from round1_ports import cubic_derivative, port_pins
from round1_repair import nontrivial_five_cut
from round3_descent import moves, pairs_of


class ElectricalLift:
    def __init__(self, n, pairs, weights):
        self.n, self.pairs, self.weights = n, pairs, weights
        incidence = sp.zeros(n - 1, len(pairs))
        for e, (a, b) in enumerate(pairs):
            if a < n - 1:
                incidence[a, e] += 1
            if b < n - 1:
                incidence[b, e] -= 1
        inv = (incidence * sp.diag(*weights) * incidence.T).inv()
        self.scale = lcm(*(int(x.q) for x in inv))
        integral = self.scale * inv
        self.rows = [[int(x) for x in row] for row in (incidence.T * integral).tolist()]
        self.resistance = [sum(row[v] * int(incidence[v, e]) for v in range(n - 1))
                           for e, row in enumerate(self.rows)]
        self.marginals = [w * r for w, r in zip(weights, self.resistance)]
        assert sum(self.marginals) == (n - 1) * self.scale
        self.degree = Counter(v for edge in pairs for v in edge)

    def solve(self, beta):
        eta = [next(x for x in range(-2, 4) if x % 2 == self.degree[v] % 2 and x % 3 == b)
               for v, b in enumerate(beta)]
        assert sum(eta) % 6 == 0
        eta[-1] -= sum(eta)
        while True:
            drops = [sum(c * x for c, x in zip(row, eta)) for row in self.rows]
            excess, e = max((abs(d) - 3 * r, e) for e, (d, r) in enumerate(zip(drops, self.resistance)))
            if excess <= 0:
                break
            a, b = self.pairs[e]
            shift = 6 if drops[e] > 0 else -6
            eta[a] -= shift
            eta[b] += shift
            assert 36 * self.resistance[e] - 12 * abs(drops[e]) < 0
        current = [d * w for d, w in zip(drops, self.weights)]
        assert divergence(self.n, self.pairs, current) == [x * self.scale for x in eta]
        assert all(abs(x) <= 3 * p for x, p in zip(current, self.marginals))
        assert all(x % 3 == b and x % 2 == self.degree[v] % 2 for v, (b, x) in enumerate(zip(beta, eta)))
        return eta


def cuts(n, pairs):
    g = nx.Graph()
    g.add_nodes_from(range(n))
    g.add_edges_from(pairs)
    rows = []
    for mask in range(1, 1 << (n - 1)):
        s = [v for v in range(n) if mask >> v & 1]
        t = [v for v in range(n) if not (mask >> v & 1)]
        cross = [e for e, (a, b) in enumerate(pairs) if (mask >> a ^ mask >> b) & 1]
        rows.append((s, len(cross), cross, nx.is_connected(g.subgraph(s)) and nx.is_connected(g.subgraph(t))))
    return rows


def check_tree_law(instance):
    n, pairs, weights = instance.n, instance.pairs, instance.weights
    totals = [0] * len(pairs)
    z = 0
    for tree in combinations(range(len(pairs)), n - 1):
        g = nx.Graph()
        g.add_nodes_from(range(n))
        g.add_edges_from(pairs[e] for e in tree)
        if nx.is_connected(g):
            weight = 1
            for e in tree:
                weight *= weights[e]
            for e in tree:
                totals[e] += weight
            z += weight
    assert [x * instance.scale for x in totals] == [z * x for x in instance.marginals]


def all_boundaries(n, pairs):
    table = boundary_counts(n, pairs)
    rows = cuts(n, pairs)
    stats = Counter()
    for weights in ([1] * len(pairs), [1 + (e * e + 3 * e) % 11 for e in range(len(pairs))]):
        electrical = ElectricalLift(n, pairs, weights)
        check_tree_law(electrical)
        for prefix in product(range(3), repeat=n - 1):
            beta = prefix + (-sum(prefix) % 3,)
            eta = electrical.solve(beta)
            bad = False
            bad_bond = False
            certified = True
            for shore, k, cross, bond in rows:
                value = abs(sum(eta[v] for v in shore))
                assert (value - k) % 2 == 0
                bad |= value > k
                if not bond:
                    continue
                bad_bond |= value > k
                residue = sum(beta[v] for v in shore) % 3
                first = next(k + 2 * i for i in range(1, 4) if (k + 2 * i) % 3 in (residue, -residue % 3))
                certified &= 3 * sum(electrical.marginals[e] for e in cross) < first * electrical.scale
            assert bad == bad_bond
            if certified:
                assert not bad
            if not bad:
                assert table[prefix] > 0
            stats['lifts'] += 1
            stats['bond certificates'] += certified
            stats['exact feasible demands'] += not bad
            stats['feasible boundary, bad demand'] += int(bad and table[prefix] > 0)
    return dict(stats)


def perturbation_checks():
    # The suspension of the pentagon is (3,6)-tight with zero-boundary degree-five hubs.
    n = 7
    pairs = [(i, (i + 1) % 5) for i in range(5)] + [(i, j) for i in range(5) for j in (5, 6)]
    m = len(pairs)
    for v in (5, 6):
        # t = 1 / (100m), common denominator 100m^2.
        numerators = [100 * m * (n - 1) + m * int(v in e) - 5 for e in pairs]
        den = 100 * m * m
        assert sum(numerators) == (n - 1) * den
        for mask in range(1, 1 << n):
            internal = [i for i, (a, b) in enumerate(pairs) if mask >> a & mask >> b & 1]
            assert sum(numerators[e] for e in internal) <= (mask.bit_count() - 1) * den
        tight = 0
        for s, d, cross, bond in cuts(n, pairs):
            if bond and d == 2 * n - 4:
                c = sum(v in pairs[e] for e in cross)
                if c <= 3:
                    assert 3 * sum(numerators[e] for e in cross) < (d + 2) * den
                else:
                    assert (2 * c - 5) * (n - 1) > 3 * (n - 2) and 5 * (n - 1) < 9 * (n - 2)
                tight += 1
        assert tight > 0
    print('pentagonal bipyramid maximal bonds', tight, 'per hub; exact perturbation passed')


def cube_obstruction():
    n = 32
    cube = [(v, v ^ (1 << j)) for v in range(n) for j in range(5) if not v >> j & 1]
    assert mincut(n, cube) == 5 and nontrivial_five_cut(n, cube, 0) is None
    for rooted in (False, True):
        vertices = set(range(int(rooted), n))
        p = [e for e in cube if set(e) <= vertices]
        g = nx.Graph(p)
        used = []
        for j in range(5):
            shore = {v for v in vertices if v >> j & 1}
            assert nx.is_connected(g.subgraph(shore)) and nx.is_connected(g.subgraph(vertices - shore))
            cut = [e for e in p if (e[0] in shore) != (e[1] in shore)]
            used += cut
            assert len(cut) == 16 - int(rooted)
            assert len([e for e in cube if 0 in e and any(v in shore for v in e)]) == 1
        assert sorted(used) == sorted(p)
        forbidden = 17 if rooted else 18
        assert 3 * (len(vertices) - 1) > 5 * forbidden
        print('cube pin, fractional-tree budget, sum of forbidden magnitudes',
              rooted, 3 * (len(vertices) - 1), 5 * forbidden)
    for minority in range(5):
        for reverse in (False, True):
            witness = [(-1 if a.bit_count() % 2 else 1) *
                       (1 if b ^ a == 1 << minority else -1) * (-1 if reverse else 1)
                       for a, b in cube]
            assert all(x % 3 == 0 for x in divergence(n, cube, witness))
            assert all(witness[e] == v for e, v in port_pins(cube, 0, minority, reverse).items())


def tight_splits():
    stats = Counter()
    for n in range(6, 11):
        rim = n - 2
        p = [(i, (i+1) % rim) for i in range(rim)] + [(i, h) for i in range(rim) for h in (rim, rim+1)]
        g = nx.Graph(p)
        assert len(p) == 3*n-6
        for u, d in g.degree():
            if d not in (4, 5):
                continue
            for residue in range(3):
                if d == 5 and residue == 0:
                    continue
                k, _ = moves(d, residue)
                small = g.copy()
                small.remove_node(u)
                assert nx.is_connected(small) and not list(nx.bridges(small))
                for pairs in pairs_of(sorted(g[u]), k):
                    raw = list(small.edges()) + list(pairs)
                    assert 3*(n-1)-len(raw) <= 6
                    for size in range(2, n):
                        for group in combinations(small, size):
                            sub = set(group)
                            assert 3*(size-1) - sum(a in sub and b in sub for a,b in raw) >= 1
                    stats['splits'] += 1
    # Rim signs give a nonzero spoke exactly when beta_i - x_i + x_{i-1} is nonzero.
    for rim in (4, 6, 8):
        table = boundary_counts(rim+1, edges(nx.wheel_graph(rim+1)))
        assert table.min() > 0
        for beta in product(range(3), repeat=rim):
            flip = {i for i,b in enumerate(beta) if b == 0}
            if len(flip) % 2:
                flip.add(next(i for i,b in enumerate(beta) if b))
            for start in (1,-1):
                v = start
                good = True
                for i,b in enumerate(beta):
                    w = -v if i in flip else v
                    good &= (b-w+v) % 3 != 0
                    v = w
                if good and start == v:
                    break
            else:
                raise AssertionError(beta)
            stats['wheel boundary assignments'] += 1
    print('density induction', dict(stats))


def main():
    fixtures = [('parallel', 3, [(0, 1)] * 3 + [(1, 2), (0, 2), (2, 2)]),
                ('K4', 4, edges(nx.complete_graph(4))), ('W4', 5, edges(nx.wheel_graph(5))),
                ('K6', 6, edges(nx.complete_graph(6)))]
    for name, n, p in fixtures:
        print(name, all_boundaries(n, p))
    for n, p in [(10, cubic_derivative(edges(nx.petersen_graph()), 0)),
                 (20, cubic_derivative(flower(5), 0)), (12, jlpt())]:
        solver = ElectricalLift(n, p, [1 + e % 7 for e in range(len(p))])
        for k in range(9):
            prefix = [(i * i + k * (i + 1) + k // 3) % 3 for i in range(n - 1)]
            solver.solve(prefix + [-sum(prefix) % 3])
        print('larger current certificates', (n, len(p)), 9)
    perturbation_checks()
    cube_obstruction()
    tight_splits()


if __name__ == '__main__':
    main()
