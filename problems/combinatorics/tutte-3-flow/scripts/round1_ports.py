"""Pinned five-port search, exact local orientation constraints and five-sum compositions."""
from collections import Counter
from itertools import combinations, permutations, product
from math import comb
import random

import networkx as nx

from flow_lab import divergence, edges, flower, lift, mincut, orient, splice
from round1_exchange import chain


class SearchLimit(Exception):
    pass


def port_pins(pairs, z, minority, reverse=False):
    star = [e for e, endpoints in enumerate(pairs) if z in endpoints]
    assert len(star) == 5
    return {e: (1 if (pairs[e][0] == z) == ((i == minority) != reverse) else -1)
            for i, e in enumerate(star)}


class LocalOrientations:
    """Branch on a vertex's allowable signs. Each call either proves failure or returns signs."""
    def __init__(self, n, pairs):
        self.n, self.pairs = n, pairs
        self.stars = [0]*n
        self.forward = [0]*n
        for e, (u,v) in enumerate(pairs):
            assert u != v
            self.stars[u] |= 1 << e
            self.stars[v] |= 1 << e
            self.forward[u] |= 1 << e

    def solve(self, beta, pins, budget=None):
        calls = 0
        def visit(fixed, signs):
            nonlocal calls
            calls += 1
            if budget is not None and calls > budget:
                raise SearchLimit
            best, branch = None, None
            for v, star in enumerate(self.stars):
                pending = star & ~fixed
                t = pending.bit_count()
                fixed_out = (fixed & star & ~(signs ^ self.forward[v])).bit_count()
                residue = (2*(star.bit_count()+beta[v])-fixed_out) % 3
                if not t:
                    if residue:
                        return None
                    continue
                choices = range(residue, t+1, 3)
                count = sum(comb(t,k) for k in choices)
                if not count:
                    return None
                if best is None or count < best:
                    best, branch = count, (v, pending, choices)
            if branch is None:
                return signs
            v, pending, choices = branch
            if best > 100:
                bit = pending & -pending
                for extra in (0, bit):
                    result = visit(fixed | bit, signs | extra)
                    if result is not None:
                        return result
            else:
                bits = []
                rem = pending
                while rem:
                    bit = rem & -rem
                    bits.append(bit)
                    rem -= bit
                for k in choices:
                    for subset in combinations(bits, k):
                        # bits in subset point out at v. Reference heads reverse the sign.
                        plus = (sum(subset) ^ ~self.forward[v]) & pending
                        result = visit(fixed | pending, signs | plus)
                        if result is not None:
                            return result
            return None

        assert len(beta) == self.n and sum(beta) % 3 == 0
        fixed = sum(1 << e for e in pins)
        initial = sum(1 << e for e, s in pins.items() if s == 1)
        solution = visit(fixed, initial)
        if solution is None:
            return None
        signs = [1 if solution >> e & 1 else -1 for e in range(len(self.pairs))]
        assert all((a-b) % 3 == 0 for a, b in zip(divergence(self.n, self.pairs, signs), beta))
        assert all(signs[e] == s for e, s in pins.items())
        return signs


def solve_checked(solver, beta, pins):
    try:
        return solver.solve(beta, pins, budget=1500)
    except SearchLimit:
        witness = orient(solver.n, solver.pairs, beta, pins)
        if witness is not None:
            return witness
        return solver.solve(beta, pins)


def cubic_derivative(graph, seed):
    weighted = nx.Graph()
    rng = random.Random(seed)
    for a, b in graph:
        weighted.add_edge(a, b, weight=rng.randrange(10**7))
    matching = {frozenset(e) for e in nx.max_weight_matching(weighted, maxcardinality=True)}
    assert 2*len(matching) == len(weighted)
    return graph + [e for e in graph if frozenset(e) not in matching]


def fixtures():
    rng = random.Random(3552601)
    pet = edges(nx.petersen_graph())
    for k in (5, 7, 9):
        raw = flower(k)
        for j in range(4):
            yield 'flower', 4*k, cubic_derivative(raw, 91+j)
    for i in range(8):
        base = cubic_derivative(pet, 331+i)
        graph = []
        sheets = 2+i%3
        for a,b in base:
            perm = rng.sample(range(sheets), sheets)
            graph.extend((sheets*a+j, sheets*b+perm[j]) for j in range(sheets))
        yield 'Petersen cover', sheets*10, graph
    for n in range(20, 41, 2):
        for rep in range(2):
            p = edges(nx.random_regular_graph(5,n, seed=rng.randrange(1 << 30)))
            yield 'random simple', n, p
            p = p + [tuple(rng.sample(range(1,n), 2)) for _ in range(n//3)]
            yield 'irregular added edges', n, p
    for i in range(24):
        n, p, _, _ = chain(1, i%2 == 0)
        for j in range(2+i%5):
            m, h, _, _ = chain(1, rng.choice((True,False)))
            p = splice(n, p, rng.randrange(n), m, h, rng.randrange(m), rng.sample(range(5), 5))
            n += m-2
        yield 'permuted five-sums', n, p
    for k in (3,4,5,6):
        for simple in (False,True):
            n,p,_,_ = chain(k,simple,True)
            yield 'cut vertices', n, p
    # Random 5-splices of a sparse repaired split K5 and a Petersen derivative.
    split = list(combinations(range(1,5), 2)) + [(0,1),(0,2),(5,3),(5,4)] + [(0,5)]*3
    split += [(1,2),(3,4),(0,3),(5,1)]
    for j in range(8):
        n,p = 6,split
        for k in range(2+j%3):
            h = cubic_derivative(pet, 910+k+j)
            tips = [v for v in range(n) if sum(v in e for e in p) == 5]
            p = splice(n,p,rng.choice(tips),10,h,rng.randrange(10),rng.sample(range(5),5))
            n += 8
        yield 'split K5 five-sums', n,p


def exact_relations():
    blocks = []
    for simple in (False, True):
        n,p,_,_ = chain(1,simple)
        a,b = n-2,n-1
        inside = [e for e,(u,v) in enumerate(p) if a not in (u,v) and b not in (u,v)]
        solver = LocalOrientations(n,p)
        table = []
        for i, sense in product(range(5), (False,True)):
            row = []
            for j, other in product(range(5),(False,True)):
                pins = port_pins(p,a,i,sense) | port_pins(p,b,j,other)
                zero = [0]*n
                target = divergence(n,p,[pins.get(e,0) for e in range(len(p))])
                internal = [p[e] for e in inside]
                count = sum(all((x+y) % 3 == 0 for x,y in zip(divergence(n,internal,signs),target))
                            for signs in product((1,-1),repeat=len(inside)))
                assert (solver.solve(zero,pins) is not None) == bool(count)
                row.append(count)
            table.append(row)
        assert all(any(row) for row in table) and all(any(col) for col in zip(*table))
        assert min(sum(x>0 for x in line) for line in [*table,*zip(*table)]) >= 6
        blocks.append((n,p,table))
        print('two-root table',simple, 'positive',sum(x>0 for row in table for x in row),
              'row supports',[sum(x>0 for x in row) for row in table],
              'column supports',[sum(x>0 for x in col) for col in zip(*table)],
              'minimum positive count',min(x for row in table for x in row if x),flush=True)
    for (n,p,left),(m,q,right) in product(blocks,repeat=2):
        for perm in permutations(range(5)):
            wire = [2*perm[i]+(1-s) for i,s in product(range(5),range(2))]
            assert all(any(left[a][k]*right[wire[k]][b] for k in range(10))
                       for a,b in product(range(10),repeat=2))
            if perm not in ((0,1,2,3,4),(3,1,4,0,2)):
                continue
            pairs = splice(n,p,n-1,m,q,m-2,perm)
            solver = LocalOrientations(n+m-2,pairs)
            for a,b in product(range(10),repeat=2):
                pins = port_pins(pairs,n-2,a//2,bool(a%2))
                pins |= port_pins(pairs,n+m-3,b//2,bool(b%2))
                assert solver.solve([0]*(n+m-2),pins) is not None
    print('480 signed transfer products, 800 two-root whole-graph certificates',flush=True)


def amplifier_check():
    p = list(combinations(range(6),2))
    histogram = Counter()
    for signs in product((-1,1),repeat=len(p)):
        d = divergence(6,p,signs)
        if any(s%3 for s in d):
            continue
        # At rim i, a spoke with sign +1 is incoming; minority means d(i)=3 there.
        histogram[sum(signs[i-1]*d[i] == 3 for i in range(1,6))] += 1
    assert histogram == {1:80}
    print('K6 amplifier, number of minority spokes at rim endpoints',dict(histogram),flush=True)


def search():
    rng = random.Random(3552602)
    stats, skipped = {},Counter()
    for family,n,p in fixtures():
        if mincut(n,p) < 5:
            skipped[family] += 1
            continue
        s = stats.setdefault(family, Counter())
        s['graphs'] += 1
        s['min_order'] = min(n,s.get('min_order',n))
        s['max_order'] = max(n,s['max_order'])
        solver = LocalOrientations(n,p)
        candidates = [v for v in range(n) if solver.stars[v].bit_count() == 5]
        assert candidates
        # All roots on every sixth family instance. Otherwise sample four distinct roots.
        roots = candidates if s['graphs'] % 6 == 1 else rng.sample(candidates,min(4,len(candidates)))
        for z in roots:
            s['roots'] += 1
            support = []
            for i in range(5):
                pins = port_pins(p,z,i)
                witness = solve_checked(solver,[0]*n,pins)
                if witness is not None:
                    support.append(i)
                    if i == 0 and z == roots[0]:
                        lift(n,p,witness)
            if len(support) < 5:
                print('MISSING PORT',family,n,p,z,support,flush=True)
                # A missing port is already a conjecture-level finding. Verify independently.
                for i in set(range(5))-set(support):
                    assert orient(n,p,[0]*n,port_pins(p,z,i)) is None
                raise AssertionError('missing zero-boundary port')
            s['zero pins'] += len(support)
        # Also test an arbitrary valid boundary and a compatible arbitrary star prescription.
        z = roots[0]
        beta = [rng.randrange(3) for _ in range(n)]
        pins = {e:rng.choice((-1,1)) for e in range(len(p)) if z in p[e]}
        beta[z] = divergence(n,p,[pins.get(e,0) for e in range(len(p))])[z] % 3
        v = next(v for v in range(n) if v != z)
        beta[v] = (beta[v]-sum(beta)) % 3
        assert solve_checked(solver,beta,pins) is not None
        s['other boundary'] += 1
    for family,s in stats.items():
        print(family,dict(s),flush=True)
    print('excluded by measured connectivity',dict(skipped),flush=True)


if __name__ == '__main__':
    exact_relations()
    amplifier_check()
    search()
