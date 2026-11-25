"""Shared matching states, exact missing boundaries on trees of fibres, and rooted K4 constructions."""

from collections import Counter
from itertools import combinations, permutations, product

import networkx as nx
import numpy as np

from flow_lab import boundary_counts, edges, mincut
from round1_ports import LocalOrientations, port_pins, solve_checked
from round1_repair import nontrivial_five_cut
from round3_reduced import core


def quartet(i):
    return list(combinations(range(4 * i, 4 * i + 4), 2))


def actual_holes(n, edges):
    counts = boundary_counts(n, edges)
    return {tuple(map(int, row)) + (-int(sum(row)) % 3,) for row in np.argwhere(counts == 0)}


def matching_tree(r, tree, seed):
    p = [e for i in range(r) for e in quartet(i)]
    links = []
    for j, (i, k) in enumerate(sorted(tree.edges())):
        la = [4 * i + (a + j + seed) % 4 for a in range(3)]
        ra = [4 * k + ((-1 if j % 2 else 1) * a + j * seed + 1) % 4 for a in range(3)]
        pairs = list(zip(la, ra))
        links.append(pairs)
        p += pairs
    return p, links


def predicted(r, links):
    result = set()
    for signs in product((1, -1), repeat=len(links)):
        b = [0] * (4 * r)
        for sign, link in zip(signs, links):
            for a, v in link:
                b[a] += sign
                b[v] += sign
        result.add(tuple(x % 3 for x in b))
    assert len(result) == 2 ** len(links)
    for i in range(r):
        assert len({b[:4*i] + b[4*i+4:] for b in result}) == len(result)
        assert all(sum(b[4*i:4*i+4]) % 3 == 0 for b in result)
    return result


STATES = list(product((-1, 1), repeat=3))


def tree_realizes(r, links, b, inside):
    # Independent bottom-up DP. 'inside' is enumerated directly on the six K4 edges.
    children = nx.Graph()
    children.add_nodes_from(range(r))
    for link in links:
        children.add_edge(link[0][0] // 4, link[0][1] // 4, link=link)
    parent = dict(nx.bfs_predecessors(children, 0))
    allowed = {}
    for i in reversed([0] + list(parent)):
        demands = {b[4*i:4*i+4]}
        for k in children[i]:
            if parent.get(k) != i:
                continue
            link = children[i][k]['link']
            inds = tuple((a if a // 4 == i else v) % 4 for a, v in link)
            demands = {adjust(d, inds, s, -1) for d in demands for s in allowed[k]}
        if i == 0:
            return any(d in inside for d in demands)
        link = children[i][parent[i]]['link']
        inds = tuple((a if a // 4 == i else v) % 4 for a, v in link)
        allowed[i] = [s for s in STATES if any(adjust(d, inds, s, 1) in inside for d in demands)]
    raise AssertionError('empty tree')


def adjust(d, inds, signs, coefficient):
    x = list(d)
    for v, s in zip(inds, signs):
        x[v] = (x[v] + coefficient * s) % 3
    return tuple(x)


def tree_tests():
    all4 = list(product(range(3), repeat=4))
    base = boundary_counts(4, quartet(0))
    inside = {b for b in all4 if sum(b) % 3 == 0 and base[b[:-1]] > 0}
    assert len(inside) == 26 and (0, 0, 0, 0) not in inside
    exact, compact, checked = 0, 0, 0
    for r in range(2, 11):
        for tree in nx.nonisomorphic_trees(r):
            for seed in range(2):
                p, links = matching_tree(r, tree, seed)
                holes = predicted(r, links)
                compact += 1
                if r <= 3:
                    assert actual_holes(4*r, p) == holes
                    for a, v in ((0, 4), (1, 4*r-1)):
                        assert not actual_holes(4*r, p + [(a, v)])
                    exact += 1
                if r <= 6 or tree.number_of_nodes() == nx.diameter(tree) + 1 or max(dict(tree.degree()).values()) == r - 1:
                    samples = sorted(holes)
                    for b in (samples if r <= 5 else samples[:2] + samples[-2:]):
                        assert not tree_realizes(r, links, b, inside)
                        for v in (4, 4*r-1):
                            for sign in (1, -1):
                                target = adjust(b, (0, v), (sign, -sign), 1)
                                assert tree_realizes(r, links, target, inside)
                        checked += 5
    print('tree attachments checked algebraically', compact, 'full boundary enumerations', exact,
          'independent tree DP queries', checked)


def other_fibres():
    four = (4, quartet(0))
    wheel = (6, edges(nx.wheel_graph(6)))
    book = (6, core('edge books', 6))
    for n, p in (four, wheel, book):
        assert actual_holes(n, p) == {(0,) * n}
    for (n, left), (m, right) in ((four, wheel), (book, four), (book, wheel)):
        ports = [(0, n + 2), (1, n), (n-1, n + m-1)]
        p = left + [(a+n,b+n) for a,b in right] + ports
        ends = {v for e in ports for v in e}
        expect = {tuple(s if i in ends else 0 for i in range(n+m)) for s in (1,2)}
        assert actual_holes(n+m, p) == expect
        for e in (ports[0], (2,n+1)):
            assert not actual_holes(n+m, p+[e])
    repeated = quartet(0) + quartet(1) + [(0,4)]*3
    holes = actual_holes(8, repeated)
    assert (0,)*8 in holes and len(holes) > 2
    print('three mixed one-hole fibre pairs; nonmatching repeated-port example has', len(holes), 'holes')


def two_blocks():
    states = list(product((-1, 1), repeat=4))
    table = boundary_counts(4, quartet(0))
    rel = {}
    for beta in product(range(3), repeat=4):
        rows = []
        for s in states:
            allowed = 0
            for j, t in enumerate(states):
                b = tuple((x + a - v) % 3 for x, a, v in zip(beta, s, t))
                if sum(b) % 3 == 0 and table[b[:3]] > 0:
                    allowed |= 1 << j
            rows.append(allowed)
        rel[beta] = rows
    stats = Counter()
    for x, a in rel.items():
        for y, b in rel.items():
            for s, row in zip(states, a):
                reach = 0
                for j in range(16):
                    if row >> j & 1:
                        reach |= b[j]
                expected = sum(1 << j for j, t in enumerate(states)
                               if (sum(t) - sum(s) - sum(x) - sum(y)) % 3 == 0)
                assert reach == expected
                stats['endpoint pairs'] += 16
    print('complete two-layer relation for arbitrary prescribed block boundaries', dict(stats))


def adversarial(q, twist):
    # Consecutive blocks exchange triples. Opposite blocks exchange two more edges.
    p = [e for i in range(q) for e in quartet(i)]
    perms = list(permutations((0, 1, 2)))
    for i in range(q):
        other = (i + 1) % q
        perm = perms[(twist * i + twist // 6) % 6]
        p.extend((4*i + 1+j, 4*other + perm[j]) for j in range(3))
        if i < q // 2:
            j = i + q // 2
            targets = (3, 0) if (i + twist) % 2 else (0, 3)
            p.extend(zip((4*i, 4*i + 3), (4*j + t for t in targets)))
    return p


def candidates():
    stats = Counter()
    for q in (4, 6, 8, 10):
        for twist in range(12):
            p = adversarial(q, twist)
            n = 4 * q
            assert mincut(n, p) == 5 and nontrivial_five_cut(n, p, 0) is None
            assert set(Counter(v for e in p for v in e).values()) == {5}
            solver = LocalOrientations(n, p)
            for i in range(5):
                assert solve_checked(solver, [0]*n, port_pins(p, 0, i)) is not None
                stats['zero-boundary stars'] += 1
            # A changing nonzero boundary with root-compatible labelled pins.
            b = [(v*v + twist*v + q) % 3 for v in range(n - 1)]
            b[0] = 0
            b.append(-sum(b) % 3)
            assert solve_checked(solver, b, port_pins(p, 0, twist % 5)) is not None
            stats['other boundaries'] += 1
            stats['inputs'] += 1
    print('matched K4 constructions, orders 16 to 40', dict(stats))


if __name__ == '__main__':
    tree_tests()
    other_fibres()
    two_blocks()
    candidates()
