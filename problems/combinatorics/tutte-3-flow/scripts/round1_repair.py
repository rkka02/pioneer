"""One-edge insertion with a prescribed root. Exact five-cut and reversal certificates."""
from itertools import product
import random

import networkx as nx
import numpy as np
from scipy.sparse import csr_array
from scipy.sparse.csgraph import maximum_flow

from flow_lab import divergence, mincut
from round1_exchange import DeficitOracle, move
from round1_ports import LocalOrientations, fixtures, port_pins, solve_checked


def nontrivial_five_cut(n,p,z=0):
    """For lambda >= 5 find a nontrivial minimum five-shore, or prove that none exists."""
    cap = np.zeros((n+1,n+1),dtype=np.int64)
    for a,b in p:
        cap[a,b] += 1
        cap[b,a] += 1
    for a in np.flatnonzero(cap[z]):
        rooted = cap.copy()
        rooted[n,z] = rooted[n,a] = len(p)+1
        net = csr_array(rooted)
        for sink in range(n):
            if sink in (z,a):
                continue
            flow = maximum_flow(net,n,sink)
            assert flow.flow_value >= 5
            if flow.flow_value == 5:
                res = nx.from_numpy_array((rooted-flow.flow.toarray())>0,create_using=nx.DiGraph)
                shore = set(range(n))-nx.descendants(res,n)
                assert sum((u in shore)!=(v in shore) for u,v in p) == 5
                if len(shore) >= 2:
                    return shore
    return None


# A label (u,v) is a directed edge in the given partial orientation.
CAP_A = [(2,0),(6,0),(7,0),(8,0),(2,1),(3,1),(5,1),(7,1),(2,3),(7,2),
         (3,4),(3,5),(5,4),(6,4),(8,4),(5,8),(7,6),(8,6),(8,7)]
CAP_B = [(2,0),(4,0),(6,0),(8,0),(5,1),(6,1),(7,1),(8,1),(2,3),(2,5),
         (7,2),(5,3),(7,3),(8,3),(4,6),(4,7),(8,4),(5,6),(7,8)]
MIDDLE = [(0,1),(2,0),(6,0),(11,0),(4,1),(1,8),(11,1),(5,2),(6,2),(9,2),
          (5,3),(7,3),(3,9),(10,3),(5,4),(6,4),(7,4),(5,10),(6,8),(7,9),
          (7,10),(8,9),(11,8),(11,10)]
LEFT, RIGHT = [1,0,4,5,2,3],[11,7,10,9,8,6]


def join_lobes(k):
    """k odd middle blocks, alternating between receiving and sending all twelve external edges."""
    assert k > 0 and k%2 == 1
    p, flipped = [],set()
    def add(u,v,reverse):
        if reverse:
            flipped.add(len(p))
        p.append((u,v))
    for off,template,selected in [(0,CAP_A,{1,13}),(9,CAP_B,{2})]:
        for i,(a,b) in enumerate(template):
            add(off+a,off+b,i in selected)
    for j in range(k):
        off = 18+12*j
        for i,(a,b) in enumerate(MIDDLE):
            if j%2:
                a,b = b,a
            add(off+a,off+b,i in (0,1,6))
    for i in range(6):
        add(i,18+LEFT[i],i in (0,4))
        add(9+i,18+12*(k-1)+RIGHT[i],i == 0)
    for j in range(k-1):
        off = 18+12*j
        for i,v in enumerate(LEFT if j%2 else RIGHT):
            a,b = off+v,off+12+v
            if j%2 == 0:
                a,b = b,a
            add(a,b,(i in (0,4)) if j%2 else (i == 0))
    return 18+12*k,p,flipped


def comparability(n,p,signs,x,y,z):
    directed = nx.DiGraph()
    directed.add_nodes_from(range(n))
    directed.add_edges_from((a,b) if k==1 else (b,a) for (a,b),k in zip(p,signs) if z not in (a,b))
    return nx.has_path(directed,x,y) or nx.has_path(directed,y,x)


def small_nontrivial_cut(n,p,z,limit):
    """Two fixed vertices on each side; complete for cuts below ten in a 5-connected graph."""
    cap = np.zeros((n+2,n+2),dtype=np.int64)
    for a,b in p:
        cap[a,b] += 1
        cap[b,a] += 1
    large = len(p)+1
    for u in np.flatnonzero(cap[z]):
        base = cap.copy()
        base[n,z] = base[n,u] = large
        for a,b in p:
            if z in (a,b) or u in (a,b):
                continue
            net = base.copy()
            net[a,n+1] = net[b,n+1] = large
            if maximum_flow(csr_array(net),n,n+1).flow_value <= limit:
                return True
    return False


def partial_obstruction():
    for m,template in [(9,CAP_A),(9,CAP_B),(12,MIDDLE)]:
        bits = np.arange(1 << m)
        cut = sum(((bits>>a)^(bits>>b))&1 for a,b in template)
        sizes = np.bitwise_count(bits)
        assert min(cut[(sizes>0)&(sizes<m)])>=4
        assert min(cut[(sizes>=2)&(sizes<=m-2)])>=6
    for k in (1,3,5,7):
        n,p,flipped = join_lobes(k)
        e,z = (6,15),24
        g = p+[e]
        assert len(set(frozenset(pair) for pair in g)) == len(g)
        assert all(sum(v in pair for pair in g)==5 for v in range(n))
        assert mincut(n,g)==5 and not small_nontrivial_cut(n,g,z,6)
        initial = [1]*len(p)
        assert all(d%3==0 for d in divergence(n,p,initial))
        assert not comparability(n,p,initial,*e,z)
        changes = [int(i in flipped) for i in range(len(p))]
        assert not any(z in p[i] for i in flipped)
        delta = divergence(n,p,changes)
        assert delta[e[0]]==2 and delta[e[1]]==1
        assert all(abs(t) in (0,3) for i,t in enumerate(delta) if i not in e)
        for j in range(k):
            off = 18+12*j
            assert sum(abs(t) for t in delta[off:off+12]) == 3
            shore = set(range(9))|set(range(18,off))
            assert sum((a in shore)!=(b in shore) for a,b in g) == 7
        completed = [1-2*w for w in changes]+[1]
        assert all(t%3==0 for t in divergence(n,g,completed))
        oracle = DeficitOracle(n,g)
        q = [sum(a==v for a,b in g) + int(v==e[0])-int(v==e[1]) for v in range(n)]
        assert set(q)=={1,4} and oracle.result(q)==1
        branch = [next(v for v in range(18+12*j,30+12*j) if abs(delta[v])==3)
                  for j in range(k)]
        for j in range(k-1,0,-2):
            q = move(q,branch[j],branch[j-1])
            assert oracle.result(q)==1
        q = move(q,branch[0],e[0])
        assert oracle.result(q)==0
        assert q == [sum((a if val==1 else b)==v for (a,b),val in zip(g,completed))
                     for v in range(n)]
        print('simple 5-regular, nontrivial min cut 7; order',n,
              'necessary and attained internal branch vertices',k,
              'minimum neutral steps',(k-1)//2,flush=True)


def deletion_tests():
    rng = random.Random(3552605)
    stats = {'atoms':0,'deletions':0,'partial flows':0,'comparable first witness':0,
             'noncomparable first witness':0}
    for group,n,p in fixtures():
        if group not in ('random simple','irregular added edges','flower','Petersen cover'):
            continue
        if mincut(n,p)<5 or nontrivial_five_cut(n,p) is not None:
            continue
        stats['atoms']+=1
        z = next(v for v in range(n) if sum(v in e for e in p)==5)
        for drop in rng.sample([i for i,e in enumerate(p) if z not in e],3):
            residual = p[:drop]+p[drop+1:]
            i = rng.randrange(5)
            pins = port_pins(residual,z,i)
            assert solve_checked(LocalOrientations(n,p),[0]*n,port_pins(p,z,i)) is not None
            signs = solve_checked(LocalOrientations(n,residual),[0]*n,pins)
            stats['deletions']+=1
            if signs is None:
                continue
            stats['partial flows']+=1
            if comparability(n,residual,signs,*p[drop],z):
                stats['comparable first witness']+=1
            else:
                stats['noncomparable first witness']+=1
    print('rooted one-edge checks',stats,flush=True)


def transfer_identity():
    """Count both sides of the Lean criterion, including impossible prescriptions and loops."""
    checks, empty = 0,0
    for n,p in [(2,[(0,1),(1,0)]),(3,[(0,1),(1,2),(2,0),(0,0)])]:
        assert all(t%3==0 for t in divergence(n,p,[1]*len(p)))
        for pinned in product((False,True),repeat=len(p)):
            for x,y in product(range(n),repeat=2):
                direct,transfer = 0,0
                for signs in product((-1,1),repeat=len(p)+1):
                    if all(s==1 or not fixed for s,fixed in zip(signs,pinned)):
                        direct += all(t%3==0 for t in divergence(n,p+[(x,y)],signs))
                for selected in product((0,1),repeat=len(p)):
                    if any(k and fixed for k,fixed in zip(selected,pinned)):
                        continue
                    d = divergence(n,p,selected)
                    for t in (1,2):
                        transfer += all((v+t*(int(i==x)-int(i==y)))%3==0 for i,v in enumerate(d))
                assert direct==transfer
                empty += direct==0
                checks += 1
    assert empty and checks>empty
    print('pinned transfer identity, prescriptions',checks,'infeasible',empty,flush=True)


if __name__ == '__main__':
    transfer_identity()
    partial_obstruction()
    deletion_tests()
