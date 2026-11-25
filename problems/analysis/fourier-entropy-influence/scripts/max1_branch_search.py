"""Search the branching first-moment target, with rational finite upper/lower bounds."""
from fractions import Fraction as Q
from itertools import combinations
import random

import numpy as np

from certificate import enclose_text
from max1_pool import logloss, spine_mean
from walsh import degrees, record_seed, signs, splits, wht


def exact_score(a):
    n=len(a).bit_length()-1
    assert a[0]==0
    den=sum(int(v)**2*int(k) for v,k in zip(a,degrees(n)) if k>=2)
    if not den:
        return Q(0),Q(0)
    ans=[Q(0),Q(0)]
    for s in np.flatnonzero(a).tolist():
        if not s&(s-1):
            continue
        v=int(a[s])**2
        for j in range(n):
            if (s>>j)&1:
                for k,l in enumerate(logloss(Q(int(a[s^(1<<j)])**2,v))):
                    ans[k]+=v*l/den
    return tuple(ans)


def exhaustive():
    n=4
    N=1<<n
    scale=1<<40
    # N^2*n*log2(1+N^2)*scale < 2^63, so integer batch sums are exact.
    weights=np.zeros((2,N+1,N+1),dtype=np.int64)
    for u in range(N+1):
        for v in range(1,N+1):
            lo,hi=logloss(Q(u*u,v*v))
            weights[:,u,v]=[(scale*v*v*lo).__floor__(),(scale*v*v*hi).__ceil__()]
    subsets=list(combinations(range(N),N//2))
    best=[Q(0),Q(0)]
    best_bits=None
    for j in range(0,len(subsets),512):
        batch=np.array(subsets[j:j+512])
        f=np.ones((len(batch),N),dtype=np.int64)
        f[np.arange(len(batch))[:,None],batch]=-1
        a=np.abs(wht(f))
        dd=degrees(n)
        den=np.sum(a*a*np.where(dd>=2,dd,0),axis=1)
        num=np.zeros((2,len(batch)),dtype=np.int64)
        for k in range(n):
            u,v=splits(a,k)
            # Outside empty corresponds to the discarded singleton.
            num+=weights[:,u[:,1:],v[:,1:]].sum(axis=2)
        for t in np.flatnonzero(den):
            for k in (0,1):
                score=Q(int(num[k,t]),scale*int(den[t]))
                if score>best[k]:
                    best[k]=score
                    if not k:
                        best_bits=batch[t].tolist()
    witness=np.ones(N,dtype=np.int64)
    witness[best_bits]=-1
    precise=exact_score(wht(witness))
    assert best[0]<=precise[1] and precise[0]<=best[1]
    print('four-bit balanced maximum',enclose_text((max(best[0],precise[0]),best[1]),12),
          'negative entries',best_bits)


def fast_batch(a,ds):
    den=np.sum(a*a*np.where(ds>=2,ds,0),axis=-1)
    num=np.zeros_like(den,dtype=float)
    for j in range(a.shape[-1].bit_length()-1):
        u,v=splits(a,j)
        u,v=u[...,1:]**2,v[...,1:]**2
        num+=np.sum(v*np.log2(1+u/np.where(v,v,1)),axis=-1)
    return num/np.where(den,den,1)


def hill_climb():
    # Balanced swaps: a' = a - 2 chi(x) + 2 chi(y), with f(x)=1 and f(y)=-1.
    rng=random.Random(411205)
    best=(0,None,None)
    for n in (6,8,10):
        N=1<<n
        ds=degrees(n)
        char=signs(ds[np.arange(N)[:,None]&np.arange(N)]%2)
        for run in range(8):
            f=np.ones(N,dtype=np.int64)
            if run<4:
                f[rng.sample(range(N),N//2)]=-1
            else:
                f=signs(np.arange(N)&1)
                for _ in range(1+(run-4)*2):
                    x=rng.choice(np.flatnonzero(f==1))
                    y=rng.choice(np.flatnonzero(f==-1))
                    f[x],f[y]=-1,1
            a=wht(f)
            score=fast_batch(a,ds)
            for step in range(65):
                x=np.array(rng.choices(np.flatnonzero(f==1),k=32))
                y=np.array(rng.choices(np.flatnonzero(f==-1),k=32))
                trials=a-2*char[x]+2*char[y]
                scores=fast_batch(trials,ds)
                j=np.argmax(scores)
                if scores[j]>score:
                    f[x[j]],f[y[j]]=-1,1
                    a=trials[j]
                    score=scores[j]
            assert np.array_equal(a,wht(f))
            if score>best[0]:
                best=float(score),n,a
    print('balanced-swap search',best[1],'bits, B',enclose_text(exact_score(best[2]),10))


def main():
    exhaustive()
    hill_climb()
    g=record_seed()
    a=wht(g)
    w1=Q(sum(int(a[1<<j])**2 for j in range(18)),len(g)**2)
    I=Q(sum(int(v)**2*int(k) for v,k in zip(a,degrees(18))),len(g)**2)
    for d in (4,20):
        partial,_=spine_mean(g,d)
        assert w1<I
        B=tuple(v/(1-(w1/I)**d) for v in partial)
        print('Numaro tower depth',d,'B',enclose_text(B,15))


if __name__=='__main__':
    main()
