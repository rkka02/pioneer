"""Exact finite boundary counts, and independently checkable integer witnesses."""
import itertools
import shutil
import subprocess

import networkx as nx
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp


def edges(graph):
    return sorted((min(a, b), max(a, b)) for a, b in graph.edges())


def mincut(n, pairs):
    graph = nx.Graph()
    graph.add_nodes_from(range(n))
    for a, b in pairs:
        if a != b:
            graph.add_edge(a, b, weight=graph.get_edge_data(a, b, {}).get("weight", 0) + 1)
    return nx.stoer_wagner(graph, weight="weight")[0] if nx.is_connected(graph) else 0


def boundary_counts(n, pairs):
    """Tensor index is beta[0:n-1]. Last residue follows from zero sum."""
    assert n >= 1 and len(pairs) < 63
    counts = np.zeros((3,) * (n-1), dtype=np.int64)
    counts.flat[0] = 1
    for a, b in pairs:
        if a == b:
            counts *= 2
            continue
        axes = tuple(v for v in (a, b) if v != n-1)
        signs = tuple(s for v, s in ((a, 1), (b, -1)) if v != n-1)
        counts = np.roll(counts, signs, axes) + np.roll(counts, tuple(-s for s in signs), axes)
    assert int(counts.sum()) == 2**len(pairs)
    return counts


def divergence(n, pairs, values):
    result = [0] * n
    for (a, b), val in zip(pairs, values, strict=True):
        result[a] += val
        result[b] -= val
    return result


def orient(n, pairs, beta, pins=None):
    """Binary y gives signed value 2*y-1. Return a checked witness, or MILP infeasible."""
    assert len(beta) == n and sum(beta) % 3 == 0
    m = len(pairs)
    B = np.zeros((n, m), dtype=int)
    for e, (a, b) in enumerate(pairs):
        B[a, e] += 1
        B[b, e] -= 1
    matrix = np.column_stack((2*B, -3*np.eye(n)))
    rhs = beta + B.sum(axis=1)
    lo, hi = [0]*m + [-m-2]*n, [1]*m + [m+2]*n
    for e, sign in (pins or {}).items():
        lo[e] = hi[e] = (sign+1)//2
    result = milp(np.zeros(m+n), integrality=np.ones(m+n), bounds=Bounds(lo, hi),
                  constraints=LinearConstraint(matrix, rhs, rhs))
    if result.status == 2:
        return None
    assert result.success, result.message
    signs = (2*np.rint(result.x[:m]).astype(int)-1).tolist()
    assert all(abs(s) == 1 for s in signs)
    assert all(s % 3 == b % 3 for s, b in zip(divergence(n, pairs, signs), beta, strict=True))
    assert all(signs[e] == s for e, s in (pins or {}).items())
    return signs


def lift(n, pairs, signs):
    """Integral max-flow rounding by incidence slots, with independent final checks."""
    network = nx.DiGraph()
    weight = [0]*n
    for e, ((a, b), s) in enumerate(zip(pairs, signs, strict=True)):
        residue = s % 3
        weight[a] += residue
        weight[b] += 3-residue
        network.add_edge("s", ("e", e), capacity=1)
        for v in (a, b):
            network.add_edge(("e", e), ("v", v), capacity=1)
    assert all(w % 3 == 0 for w in weight)
    for v, w in enumerate(weight):
        network.add_edge(("v", v), "t", capacity=w//3)
    value, flow = nx.maximum_flow(network, "s", "t")
    assert value == len(pairs)
    f = [s % 3 - 3*flow["e", e]["v", a] for e, ((a, _), s) in enumerate(zip(pairs, signs))]
    assert all(a % 3 == b % 3 and 0 < abs(a) < 3 for a, b in zip(f, signs))
    assert divergence(n, pairs, f) == [0]*n
    return f


def regular_census(n):
    exe = shutil.which("geng") or shutil.which("nauty-geng")
    if exe is None:
        raise RuntimeError("Install nauty geng for the isomorphism census")
    data = subprocess.check_output([exe, "-q", "-c", "-d5", "-D5", str(n)])
    for line in data.splitlines():
        yield edges(nx.from_graph6_bytes(line))


def flower(k):
    """Isaacs J_k. Centers i have three spokes, one outer k-cycle and one twisted 2k-cycle."""
    assert k >= 5 and k % 2 == 1
    pairs = [(i, j*k+i) for i in range(k) for j in (1, 2, 3)]
    for row in (1, 2, 3):
        pairs.extend((row*k+i, row*k+i+1) for i in range(k-1))
        pairs.append((row*k+k-1, {1: 1, 2: 3, 3: 2}[row]*k))
    return pairs


def jlpt():
    return ([(4*i+a, 4*i+b) for i in range(3) for a, b in itertools.combinations(range(4), 2)]
            + [(4*i+2+j, 4*((i+1) % 3)+j) for i in range(3) for j in range(2)])


def splice(n, pairs, root, m, other, tip, permutation):
    """Remove roots and pair their incident half-edges in their input order."""
    def shore(order, es, z, offset):
        index = {v: i+offset for i, v in enumerate(v for v in range(order) if v != z)}
        inside, ports = [], []
        for a, b in es:
            if z in (a, b):
                ports.append(index[b if a == z else a])
            else:
                inside.append((index[a], index[b]))
        return inside, ports
    left, p = shore(n, pairs, root, 0)
    right, q = shore(m, other, tip, n-1)
    assert len(q) == len(p) and sorted(permutation) == list(range(len(q)))
    return left + right + [(v, q[j]) for v, j in zip(p, permutation)]


def fourier(n, pairs):
    """Sum integer characters for beta=0 after fixing the last color."""
    terms = [0]*(len(pairs)+1)
    for prefix in itertools.product(range(3), repeat=n-1):
        color = (*prefix, 0)
        h = sum(color[a] != color[b] for a, b in pairs)
        terms[h] += 1
    numerator = sum(c*(-1)**h * 2**(len(pairs)-h) for h, c in enumerate(terms))
    answer, rem = divmod(numerator, 3**(n-1))
    assert not rem
    return answer, sum(c*2**(len(pairs)-h) for h, c in enumerate(terms) if h)
