"""Modular base rounding, exact distance to graphical outdegrees and exchange stress tests."""
from collections import Counter
from functools import reduce
from itertools import combinations, product
import random

import networkx as nx
import numpy as np
import sympy as sy

from flow_lab import divergence, edges, flower, mincut
from obstructions import seven_cut_graph
from round1_exchange import DeficitOracle, chain, move, nearest, nonincreasing_path, raw_values
from round1_ports import fixtures, LocalOrientations, solve_checked


def rounded_example():
    n,p,_,_ = chain(1,True)
    masks,f = raw_values(n,p,[1]*n)
    A = np.array([[(int(s) >> v) & 1 for v in range(n)] for s in masks])
    b = -np.floor_divide(-f,3)
    cuts = sum(((masks>>u)^(masks>>v))&1 for u,v in p)
    assert np.all(f%3 == cuts%3)
    effective = (cuts-2*((-cuts)%3))//3
    assert np.all(2*(A@np.ones(n,dtype=int))-4*b == 2*effective)
    assert (b[71],b[39],b[71|39],b[71&39]) == (1,1,1,0)
    # Twice the proposed fractional vertex, so integer arithmetic checks every inequality.
    y = np.array([0,0,1,2,2,1,1,1])
    tight = [1,2,39,71,99,135,239,247]
    assert np.all(A@y >= 2*b) and sum(y) == 2*b[-1]
    assert np.all((A@y-2*b)[tight] == 0) and sy.Matrix(A[tight]).det() == -2
    # The exact minimized integer objective additionally witnesses an integrality gap.
    c = A[tight].sum(axis=0)
    assert int(c@y) == 2*sum(b[tight])
    legal = [x for x in product((0,1),repeat=n) if sum(x) == b[-1] and np.all(A@x >= b)]
    integer_optimum = min(int(c@x) for x in legal)
    assert 2*integer_optimum > int(c@y)
    print('fractional vertex, cost vector',c.tolist(),'LP optimum',sum(b[tight]),
          'integer optimum',integer_optimum,flush=True)


def cycle_space_dual(n,p):
    """Return the number of nonzero coefficients in the reduced product on chord signs."""
    components = nx.utils.UnionFind(range(n))
    tree, chords = nx.Graph(),[]
    tree.add_nodes_from(range(n))
    for a,b in p:
        if components[a] == components[b]:
            chords.append((a,b))
        else:
            components.union(a,b)
            tree.add_edge(a,b)
    size = 1 << len(chords)
    masks = np.arange(size)
    polynomial = np.zeros(size,dtype=np.int16)
    polynomial[0] = 1
    evaluations = np.ones(size,dtype=np.int16)
    for a,b in list(tree.edges):
        tree.remove_edge(a,b)
        shore = nx.node_connected_component(tree,a)
        tree.add_edge(a,b)
        form = [(j,int(u in shore)-int(v in shore)) for j,(u,v) in enumerate(chords)
                if (u in shore)!=(v in shore)]
        # Multiplication by a chord variable toggles its bit since its square is one.
        for _ in range(2):
            new = np.zeros_like(polynomial)
            for j,sign in form:
                new += sign*polynomial[masks ^ (1<<j)]
            polynomial = new%3
        values = sum(s*(1-2*((masks>>j)&1)) for j,s in form)
        evaluations *= np.asarray(values)%3 != 0
    # Evaluate every reduced coefficient on the entire sign cube independently.
    transform = polynomial.copy()
    for j in range(len(chords)):
        rows = transform.reshape(-1,2,1<<j)
        a,b = rows[:,0].copy(), rows[:,1].copy()
        rows[:,0],rows[:,1] = (a+b)%3,(a-b)%3
    assert np.array_equal(transform,evaluations)
    return int(np.count_nonzero(polynomial))


def square_expansion(n,p):
    incident = [[] for _ in range(n)]
    for i,(a,b) in enumerate(p):
        incident[a].append(i)
        incident[b].append(i)
    new, ports, order = [],{},0
    for v,star in enumerate(incident):
        d = len(star)
        assert d >= 5
        for j,i in enumerate(star):
            ports[v,i] = order+j
            for offset in (1,2):
                new.append((order+j,order+(j+offset)%d))
        order += d
    external = [(ports[a,i],ports[b,i]) for i,(a,b) in enumerate(p)]
    new += external
    assert len(new) == len(set(frozenset(e) for e in new)) and 2*len(new) == 5*order
    return order,new,len(new)-len(p)


def distance_check(n,p,q):
    """Reverse integral path flows in the reference orientation and recover a closest quota."""
    initial = [0]*n
    network = nx.DiGraph()
    for a,b in p:
        initial[a] += 1
        network.add_edge(a,b,capacity=1+network.get_edge_data(a,b,{}).get('capacity',0))
    for v in range(n):
        network.add_edge(n,v,capacity=max(0,initial[v]-q[v]))
        network.add_edge(v,n+1,capacity=max(0,q[v]-initial[v]))
    value,flow = nx.maximum_flow(network,n,n+1)
    dist = sum(max(0,a-b) for a,b in zip(initial,q))-value
    corrected = initial.copy()
    for a in range(n):
        for b,k in flow[a].items():
            if b < n:
                corrected[a] -= k
                corrected[b] += k
    assert dist == sum(abs(a-b) for a,b in zip(corrected,q))//2
    assert dist == DeficitOracle(n,p).result(q)


def canonical_quota(deg,rng):
    odds = [i for i,d in enumerate(deg) if d%2]
    plus = set(rng.sample(odds,len(odds)//2))
    return [(int(d)+(3 if i in plus else -3) * (d%2))//2 for i,d in enumerate(deg)]


def stress():
    rng = random.Random(3552603)
    aggregate,seen = {},Counter()
    for family,n,p in fixtures():
        seen[family] += 1
        if not 20 <= n <= 40 or seen[family] % 3 == 2 or mincut(n,p) < 5:
            continue
        stats = aggregate.setdefault(family,Counter())
        stats['graphs'] += 1
        oracle = DeficitOracle(n,p)
        for j in range(10):
            q = canonical_quota(oracle.deg,rng)
            if j % 3 == 1:
                for _ in range(1+j//3):
                    q = move(q,*rng.sample(range(n),2))
            d,small,large = oracle.result(q,True)
            if j < 2:
                distance_check(n,p,q)
            if d == 0:
                stats['already feasible'] += 1
                continue
            stats['strict'] += 1
            if any(oracle.result(move(q,u,w)) < d for u in sorted(small) for w in sorted(set(range(n))-large)):
                continue
            stats['strict'] -= 1
            _,target = nearest(n,p,q)
            path = nonincreasing_path(oracle,q,target)
            if path is None:
                stats['undecided'] += 1
            else:
                cur = q
                for step,(u,w) in enumerate(path):
                    cur = move(cur,u,w)
                    if oracle.result(cur) < d:
                        stats['neutral '+str(step)] += 1
                        break
                else:
                    raise AssertionError('path missed its target')
    for family,s in aggregate.items():
        print('stress',family,dict(s),flush=True)


def laminar_check():
    # Exhaust every shore on new chains and one previously documented obstruction, once per graph.
    for n,p,_,_ in [chain(2,True),chain(2,False),chain(2,False,True),
                    (18,seven_cut_graph(),None,None)]:
        deg = np.array([sum(v in e for e in p) for v in range(n)])
        masks = np.arange(1<<n,dtype=np.int32)
        sizes = np.bitwise_count(masks)
        cuts = sum(((masks>>u)^(masks>>v))&1 for u,v in p)
        shores = [int(s) for s in masks[(cuts==5)&((masks&1)==0)]]
        assert all(i&j in (0,i,j) for i,j in combinations(shores,2))
        # Recursive subdivision of the laminar family gives an interval order.
        def order(s, members):
            children = [t for t in members if all(u == t or t & u != t for u in members)]
            rest = s ^ reduce(int.__or__,children,0)
            ans = [i for i in range(n) if rest>>i&1]
            for t in children:
                ans += order(t,[u for u in members if u != t and u&t == u])
            return ans
        odd = [v for v in order((1<<n)-1,shores) if deg[v]%2]
        sign = np.zeros(n,dtype=int)
        sign[odd[::2]],sign[odd[1::2]] = 1,-1
        balances = sum(int(sign[v])*((masks>>v)&1) for v in range(n))
        assert sum(sign)==0 and np.max(np.abs(balances[cuts==5]))==1
        if n == 18:
            prior = np.array([1 if v in set(range(6))|{15,16,17} else -1 for v in range(n)])
            sums = sum(int(prior[v])*((masks>>v)&1) for v in range(n))
            assert np.max(np.abs(sums[cuts==5]))==1 and cuts[511]==7 and sums[511]==3
        print('laminar',n,int(sum(cuts==5))//2,flush=True)


def expansion_check():
    rng = random.Random(3552604)
    panel = [(2,[(0,1)]*7),(4,[(i,i+1) for i in range(3) for _ in range(5)])]
    for simple in (False,True):
        n,p,_,_ = chain(2,simple,True)
        panel.append((n,p))
    n,p,_,_ = chain(1,True)
    panel.append((n,p+[tuple(rng.sample(range(n),2)) for _ in range(9)]))
    for n,p in panel:
        order,new,off = square_expansion(n,p)
        assert mincut(n,p)>=5 and mincut(order,new)==5
        solver = LocalOrientations(order,new)
        witness = solve_checked(solver,[0]*order,{})
        assert witness is not None
        assert all(d%3==0 for d in divergence(n,p,witness[off:]))
        print('expanded',n,order,flush=True)


if __name__=='__main__':
    rounded_example()
    for name,n,p,wanted in [('Petersen',10,edges(nx.petersen_graph()),False),
                            ('flower',20,flower(5),False),
                            ('triangle block',*chain(1,True)[:2],True),
                            ('digon block',*chain(1,False)[:2],True)]:
        nonzero = cycle_space_dual(n,p)
        assert bool(nonzero)==wanted
        print('cycle-space certificate',name,'nonzero reduced coefficients',nonzero,flush=True)
    expansion_check()
    laminar_check()
    stress()
