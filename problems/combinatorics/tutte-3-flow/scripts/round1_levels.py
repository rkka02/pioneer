"""Complete level-one exchange components, including signed quotas, on new constructed graphs."""
from collections import Counter
import random

import numpy as np

from flow_lab import mincut
from round1_exchange import DeficitOracle, block, chain


def cycle(k,simple,rng):
    high,low,core,src,dst = block(simple)
    width = len(high)+len(low)
    p = [(width*i+a-2,width*i+b-2) for i in range(k) for a,b in core]
    incoming = [b if a == 0 else a for a,b in src]
    outgoing = [b if a == 1 else a for a,b in dst]
    for i in range(k):
        order = rng.sample(incoming,5)
        p.extend((width*i+a-2,width*((i+1)%k)+b-2) for a,b in zip(outgoing,order))
    return k*width,p


def level_one(n,p,rng):
    deg = [sum(v in e for e in p) for v in range(n)]
    # Every D<=1 quota is in this extended box by the singleton and its complement.
    vals = [np.array([x for x in range(-1,d+2) if (2*x-d)%3==0],dtype=np.int16) for d in deg]
    dims = [len(v) for v in vals]
    size = int(np.prod(dims))
    masks = np.arange(1 << n,dtype=np.int32)
    internal = sum((masks>>a)&(masks>>b)&1 for a,b in p)
    f = internal.astype(np.int16).reshape((2,)*n,order='F')
    for axis,options in enumerate(vals):
        lo,hi = np.take(f,0,axis),np.take(f,1,axis)
        f = np.stack([np.maximum(lo,hi-x) for x in options],axis=axis)
    f = f.ravel(order='F')
    strides = [int(np.prod(dims[:v],dtype=np.int64)) for v in range(n)]
    all_ids = np.arange(size)
    mass = np.zeros(size,dtype=np.int16)
    for st,ds,choices in zip(strides,dims,vals):
        mass += choices[(all_ids//st)%ds]
    feasible = (mass==len(p)) & (f==0)
    deficient = (mass==len(p)) & (f==1)
    oracle = DeficitOracle(n,p)
    for index in rng.sample(np.flatnonzero(feasible|deficient).tolist(),5):
        q = [int(v[(index//s)%len(v)]) for s,v in zip(strides,vals)]
        assert oracle.result(q) == f[index]
    remaining = deficient.copy()
    frontier = np.flatnonzero(feasible)
    counts = [len(frontier)]
    while len(frontier):
        visited = np.zeros(size,dtype=np.bool_)
        digits = [(frontier//s)%d for s,d in zip(strides,dims)]
        for u,upper in enumerate(digits):
            for w,lower in enumerate(digits):
                if u != w:
                    valid = (upper < dims[u]-1) & (lower > 0)
                    visited[frontier[valid]+strides[u]-strides[w]]=True
        frontier = np.flatnonzero(visited & remaining)
        if len(frontier):
            counts.append(len(frontier))
            remaining[frontier]=False
    if remaining.any():
        i = int(np.flatnonzero(remaining)[0])
        print('TRAPPED',n,p,[int(v[(i//s)%len(v)]) for s,v in zip(strides,vals)],flush=True)
    assert not remaining.any(), 'positive-deficit component disjoint from feasible states'
    return counts


def experiments():
    rng = random.Random(3552606)
    panel = []
    for k in (3,4):
        for _ in range(5):
            panel.append(('ring of parallel blocks',*cycle(k,False,rng)))
    for _ in range(3):
        panel.append(('ring of simple blocks',*cycle(3,True,rng)))
    for k,simple,identify in [(3,False,False),(4,False,False),(2,True,False),(3,False,True)]:
        n,p,_,_ = chain(k,simple,identify)
        panel.append(('open chain',n,p))
        for extra in (1,3):
            panel.append(('irregular chain',n,p+[tuple(rng.sample(range(n),2)) for _ in range(extra)]))
    totals = {}
    for group,n,p in panel:
        if mincut(n,p) != 5:
            print('excluded connectivity',group,n,flush=True)
            continue
        tally = totals.setdefault(group,Counter())
        counts = level_one(n,p,rng)
        tally['graphs']+=1
        for dist,count in enumerate(counts):
            tally[dist]+=count
    for group,c in totals.items():
        print('full level-one distances',group,dict(c),flush=True)


if __name__ == '__main__':
    experiments()
