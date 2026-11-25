"""Round 1. Exact deficit, saturated two-terminal blocks and modular exchange distances."""
import random

import networkx as nx
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import csr_array
from scipy.sparse.csgraph import maximum_flow

from flow_lab import divergence, mincut


class DeficitOracle:
    """D(q) from an integer min cut. Accepts signed quotas of the correct total."""
    def __init__(self, n, pairs):
        self.n, self.pairs = n, pairs
        self.capacity = np.zeros((n+2, n+2), dtype=np.int64)
        self.deg = np.zeros(n, dtype=np.int64)
        for u, v in pairs:
            assert u != v
            self.capacity[u, v] += 1
            self.capacity[v, u] += 1
            self.deg[[u, v]] += 1

    def result(self, quota, shores=False):
        n = self.n
        assert len(quota) == n and sum(quota) == len(self.pairs)
        w = self.deg - 2*np.asarray(quota)
        cap = self.capacity.copy()
        cap[n, :n] = np.maximum(w, 0)
        cap[:n, n+1] = np.maximum(-w, 0)
        graph = csr_array(cap)
        flow = maximum_flow(graph, n, n+1)
        double = int(cap[n].sum())-flow.flow_value
        assert double % 2 == 0
        if not shores:
            return int(double//2)
        residual = nx.from_numpy_array((cap-flow.flow.toarray()) > 0, create_using=nx.DiGraph)
        least = nx.descendants(residual, n)
        greatest = set(range(n))-nx.ancestors(residual, n+1)
        assert least <= greatest <= set(range(n))
        return int(double//2), least, greatest


def block(simple):
    """Labels s,t,h...,l...; all edge pairs below are directed to witness the defect."""
    if simple:
        high, low = (2, 3, 4), (5, 6, 7)
        core = [(2, 7), (3, 7), (4, 5), (4, 6)]
        from_high_s, from_high_t = high, (2, 3)
        to_low_s, to_low_t = (5, 6), low
    else:
        high, low = (2, 3), (4, 5)
        core = [(2, 4)]
        from_high_s, from_high_t = (2, 3, 3), (2, 3)
        to_low_s, to_low_t = (4, 5), (4, 5, 5)
    for cycle in (high, low):
        core.extend(zip(cycle, cycle[1:]+cycle[:1]))
    src_star = [(v, 0) for v in from_high_s] + [(0, v) for v in to_low_s]
    dst_star = [(v, 1) for v in from_high_t] + [(1, v) for v in to_low_t]
    return high, low, core, src_star, dst_star


def chain(k, simple=True, identify=False):
    high, low, core, src, dst = block(simple)
    width = len(high)+len(low)
    interior = [[width*i+j for j in range(width)] for i in range(k)]
    first = k*width
    n = first + (k+1 if identify else 2)
    q = [0]*n
    pairs, prev = [], []
    for i, vertices in enumerate(interior):
        names = {j+2: v for j, v in enumerate(vertices)}
        s = first+i if identify else first
        t = first+i+1 if identify else first+1
        names.update({0: s, 1: t})
        for h in high:
            q[names[h]] = 4
        for l in low:
            q[names[l]] = 1
        pairs += [(names[a], names[b]) for a, b in core]
        if identify or i == 0:
            pairs.extend((names[a], names[b]) for a, b in src)
            q[s] += 1
        if identify or i == k-1:
            pairs.extend((names[a], names[b]) for a, b in dst)
            q[t] += 4
        if not identify and i:
            # Pair a received stub with a sent stub, preserving the witness orientations.
            curr = [(names[b], True) if a == 0 else (names[a], False) for a, b in src]
            for sense in (False, True):
                p = [v for v, out in prev if out == sense]
                c = [v for v, out in curr if out != sense]
                for u, v in zip(p, c, strict=True):
                    pairs.append((v, u) if sense else (u, v))
        prev = [(names[b], True) if a == 1 else (names[a], False) for a, b in dst]
    initial = [0]*n
    for a, _ in pairs:
        initial[a] += 1
    assert [(i, a-b) for i, (a,b) in enumerate(zip(initial,q)) if a != b] == [(first,1),(n-1,-1)]
    return n, pairs, q, interior


def move(q, recipient, donor):
    q = q.copy()
    q[recipient] += 3
    q[donor] -= 3
    return q


def periodic_repairs(simple):
    """Check the two oriented blocks giving a shortest neutral path at every chain length."""
    high, low, core, src, dst = block(simple)
    p = core+src+dst
    if simple:
        l, h, flip_a, flip_b = 5, 2, [9,13,17,19], [4,5,10,12,15]
    else:
        l, h, flip_a, flip_b = 5, 3, [3,8,13,14], [2,6,7,10]
    patterns = []
    for changed, delta, reversed_edges in [(l,3,flip_a), (h,-3,flip_b)]:
        oriented = [e[::-1] if i in reversed_edges else e for i,e in enumerate(p)]
        tails = [sum(a == v for a,_ in oriented) for v in range(2+len(high)+len(low))]
        expected = [1,1] if delta == 3 else [4,4]
        expected += [4]*len(high)+[1]*len(low)
        expected[changed] += delta
        assert tails == expected
        patterns.append(([int(a == 0) for a,_ in oriented[-10:-5]],
                         [int(a == 1) for a,_ in oriented[-5:]]))
    perm = [3,4,0,1,2]  # slot at t goes to this slot at the next s
    for left,right in [(0,1),(1,0)]:
        assert all(patterns[left][1][i]+patterns[right][0][j] == 1 for i,j in enumerate(perm))
    assert sum(x != int(a == 1) for x,(a,_) in zip(patterns[1][1],dst)) == 1
    return l-2,h-2


def nearest(n, pairs, q):
    """Minimize exchange distance. Check a returned integer orientation independently."""
    m = len(pairs)
    p = np.bincount([a for a, _ in pairs], minlength=n)
    B = np.zeros((n, m), dtype=np.int64)
    for i, (a, b) in enumerate(pairs):
        B[a, i] += 1
        B[b, i] -= 1
    # Reverse a subset of reference edges. Actual tails are p-B*y = q+3*(a-b).
    z = np.column_stack((B, 3*np.eye(n), -3*np.eye(n)))
    rhs = p-np.array(q)
    sol = milp(np.r_[np.zeros(m), np.ones(2*n)], integrality=np.ones(m+2*n),
               bounds=Bounds(np.zeros(m+2*n), np.r_[np.ones(m), np.full(2*n, m)]),
               constraints=LinearConstraint(z, rhs, rhs))
    assert sol.success
    y = np.rint(sol.x[:m]).astype(int)
    assert all(0 <= a <= 1 for a in y)
    actual = p-B@y
    assert all((a-b) % 3 == 0 for a, b in zip(actual, q))
    dist = sum(abs(a-b) for a, b in zip(actual, q))//6
    assert abs(2*dist-sol.fun) < 1e-5
    assert all(x % 3 == 0 for x in divergence(n, pairs, 1-2*y))
    return int(dist), actual.tolist()


def nonincreasing_path(oracle, q, target):
    """Try all orders of exchanges toward one certified closest solution. Return a checked path."""
    failed = set()
    def visit(state):
        if state == target:
            return []
        if tuple(state) in failed:
            return None
        d = oracle.result(state)
        for i in range(len(q)):
            if state[i] >= target[i]:
                continue
            for j in range(len(q)):
                if state[j] > target[j]:
                    nxt = move(state, i, j)
                    if oracle.result(nxt) <= d:
                        tail = visit(nxt)
                        if tail is not None:
                            return [(i, j)] + tail
        failed.add(tuple(state))
        return None
    return visit(q)


def raw_values(n, pairs, q):
    masks = np.arange(1 << n, dtype=np.int32)
    f = np.zeros_like(masks)
    for a, b in pairs:
        f += (masks >> a) & (masks >> b) & 1
    for i, v in enumerate(q):
        f -= v*((masks >> i) & 1)
    return masks, f


def verify_shores(n, pairs, q):
    masks, f = raw_values(n, pairs, q)
    oracle = DeficitOracle(n, pairs)
    d, least, greatest = oracle.result(q, True)
    active = masks[f == f.max()]
    bits = lambda s: sum(1 << i for i in s)
    assert d == f.max() and bits(least) == np.bitwise_and.reduce(active)
    assert bits(greatest) == np.bitwise_or.reduce(active)
    if d == 0:
        return
    assert all(sum(i in e and set(e) <= least for e in pairs) >= q[i]+1 for i in least)
    outside = set(range(n))-greatest
    assert all(q[i] > sum(i in e and (set(e)-{i}) <= greatest for e in pairs) for i in outside)
    for u in range(n):
        for w in range(n):
            if u == w:
                continue
            reverse = (masks & (1 << w) > 0) & (masks & (1 << u) == 0)
            margin = d - int(f[reverse].max())
            dn = d > (f + 3*((masks >> w) & 1) - 3*((masks >> u) & 1)).max()
            assert dn == (u in least and w in outside and margin >= 4)
            # Unrestricted neutral-or-better step cares only about the increasing shores.
            assert (margin >= 3) == (oracle.result(move(q, u, w)) <= d)


def experiments():
    rng = random.Random(35501)
    for simple in (False, True):
        low_index, high_index = periodic_repairs(simple)
        for identify in (False, True):
            for k in (1, 3, 5, 6, 7):
                n, pairs, q, internal = chain(k, simple, identify)
                oracle = DeficitOracle(n, pairs)
                assert mincut(n, pairs) == 5 and oracle.result(q) == 1
                if simple:
                    assert len(set(frozenset(e) for e in pairs)) == len(pairs)
                if not identify:
                    assert all(oracle.deg == 5)
                dist, actual = nearest(n, pairs, q)
                assert dist >= (k+1)//2 and all(any(actual[i] != q[i] for i in p) for p in internal)
                path = nonincreasing_path(oracle, q, actual)
                print("chain", simple, identify, k, n, "nearest", dist, "neutral path",
                      None if path is None else len(path)-1, "exchanges", path, flush=True)
                cur = q.copy()
                for b in range(0, k-1, 2):
                    cur = move(cur, internal[b][low_index], internal[b+1][high_index])
                    assert oracle.result(cur) == int(b+2 < k)
                if k % 2:
                    cur = move(cur, internal[-1][low_index], n-1)
                assert oracle.result(cur) == 0 and dist == (k+1)//2
                if (simple, identify, k) == (True, False, 5):
                    d, least, greatest = oracle.result(q, True)
                    outside = set(range(n))-greatest
                    assert least == {3,4,5,30} and outside == {24,25,26,31}
                    neutral = 0
                    for u in range(n):
                        for w in range(n):
                            # At degree five these are the only moves staying in D <= 1.
                            if q[u] == 1 and q[w] == 4:
                                nxt = move(q,u,w)
                                if oracle.result(nxt) <= d:
                                    nd, p_min, p_max = oracle.result(nxt, True)
                                    assert nd == d and len(p_min) >= len(least) and len(p_max) <= len(greatest)
                                    neutral += 1
                    assert neutral == 34
                    cur = q.copy()
                    for u, w, expected in [(4, 7, 1), (16, 20, 1), (21, 25, 0)]:
                        cur = move(cur, u, w)
                        assert oracle.result(cur) == expected
                if k == 1:
                    for _ in range(3):
                        u, w = rng.sample(range(n), 2)
                        verify_shores(n, pairs, move(q, u, w))


if __name__ == "__main__":
    experiments()
