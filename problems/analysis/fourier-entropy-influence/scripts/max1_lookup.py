"""Common-address bent lookup products and self-dual circuits with reused data."""
from collections import Counter
from fractions import Fraction as Q
from math import comb
import random

import numpy as np

from certificate import enclose_text, histogram, summarize
from max1_pool import direct, logloss
from walsh import degrees, entropy, quadratic, signs, splits, wht


def dense_lookup(m,t):
    N=1<<m
    x=np.arange(1<<(m+t+t*N))
    address=x%N
    h=quadratic(m)[address]
    result=np.ones_like(x)
    for j in range(t):
        switch=(x>>(m+j))&1
        label=(x>>(m+t+j*N+address))&1
        result*=np.where(switch,signs(label),h)
    return result


def law(m,t):
    """Exact binomial law of degree and private deletion odds."""
    assert m>0 and m%2==0 and t>=1
    N=1<<m
    q0=Q(1,1<<t)
    rows=Counter()
    for u in range(t+1):
        address_bits=m if u or t%2 else 0
        for a in range(address_bits+1):
            for b in range(t+1):
                prob=Q(comb(t,u)*comb(address_bits,a)*comb(t,b),1<<(2*t+address_bits))
                private_odds=1
                if u==1:
                    private_odds=N if t%2 else N*N if not a else 0
                rows[u,a+b,private_odds]+=prob
    assert sum(rows.values())==1
    influence=sum(p*(u+k) for (u,k,r),p in rows.items())
    assert influence==t+Q(m,2)*(1-(not t%2)*q0)
    h=2*t+2*m*(1-q0)+m*(t%2)*q0
    assert h<=4*influence
    pooled=[Q(0),Q(0)]
    for (u,k,r),p in rows.items():
        if k+u:
            for side,val in enumerate(logloss(Q(r))):
                pooled[side]+=p*(k+u*val)**2/(k+u)
    ratio=tuple(v/influence for v in pooled)
    assert ratio[1]<=17
    return h,influence,ratio


def signed_feedback(n,seed):
    """Reapply a permuted state on affine cosets, with an even phase mask.

    The selectors and phases are unchanged by simultaneous input complement.
    Hence each state remains self-dual and balanced.
    """
    rng=random.Random(seed)
    x=np.arange(1<<n)
    bit=[(x>>j)&1 for j in range(n)]
    f=signs(bit[0])
    for _ in range(12):
        perm=rng.sample(range(n),n)
        addr=sum(bit[j]<<k for k,j in enumerate(perm))
        addr^=rng.randrange(1<<n)
        use=np.ones(len(x),dtype=bool)
        for _ in range(rng.randint(1,4)):
            a,b=rng.sample(range(n),2)
            use&=(bit[a]^bit[b])==rng.randrange(2)
        a,b,c,d=rng.sample(range(n),4)
        phase=(bit[a]^bit[b]) & (bit[c]^bit[d])
        branch=f[addr]*signs(phase)
        f=np.where(use,branch,f)
        assert np.all(f+f[::-1]==0)
        yield f


def main():
    for m in (2,4,16,64):
        for t in (2,3,8,16):
            h,i,rat=law(m,t)
            if m==2 and t in (2,3):
                f=dense_lookup(m,t)
                a=wht(f)
                hh,ii=summarize(histogram(a,degrees(len(f).bit_length()-1)),len(f))
                assert hh[0]<=h<=hh[1] and ii==i
                exact=direct(f)
                assert exact[0]<=rat[1] and rat[0]<=exact[1]
            if m in (2,64):
                print('lookup m,t',m,t,'I',i,'P2/I',enclose_text(rat,6))
    best=[None,None]
    for n in (6,8,10,12,14):
        for repeat in range(12):
            for depth,f in enumerate(signed_feedback(n,412000+repeat),1):
                a=wht(f)
                raw=int(np.sum(a*a*degrees(n)))
                if raw<=len(a)**2:
                    continue
                p=(a/len(a))**2
                h=float(entropy(p))
                i=raw/len(a)**2
                for j,score in enumerate((h/i,h/(i-1))):
                    if best[j] is None or score>best[j][0]:
                        best[j]=score,n,repeat,depth,f
    for j,(_,n,repeat,depth,f) in enumerate(best):
        a=wht(f)
        h,i=summarize(histogram(a,degrees(n)),len(a))
        edge=sum(np.count_nonzero(v!=w) for v,w in (splits(f,k) for k in range(n)))
        assert i==Q(2*edge,len(f))
        print('feedback',('ordinary','amplified')[j],n,repeat,depth,
              enclose_text(tuple(v/(i-j) for v in h),9))
    print('720 deterministic feedback stages, two dense lookup WHTs')


if __name__=='__main__':
    main()
