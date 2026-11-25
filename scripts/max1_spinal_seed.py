"""Rational certificate for the four-copy path substitution in the 9-edge host."""
from collections import Counter
from fractions import Fraction as Q

import numpy as np

from certificate import enclose_text, grid_bounds, histogram, log2_int, summarize
from walsh import PAIRS, degrees, record_seed, seed_parts, splits, wht


def point(x):
    return Q(x),Q(x)


def add(*boxes):
    return grid_bounds(sum(v[0] for v in boxes),sum(v[1] for v in boxes))


def times(a,b):
    products=[x*y for x in a for y in b]
    return grid_bounds(min(products),max(products))


def subtract(a,b):
    return add(a,(-b[1],-b[0]))


def positive_power(a,k):
    assert a[0]>=0
    return grid_bounds(a[0]**k,a[1]**k)


def log_inverse(x):
    """log2(1/x) by the rational atanh series from the previous certificate."""
    assert 0<x<=1
    a,b=log2_int(x.denominator)
    c,d=log2_int(x.numerator)
    return a-d,b-c


def eta_box(p):
    if not p[1]:
        return point(0)
    assert 0<p[0]<=p[1]<=1
    return times(p,(log_inverse(p[1])[0],log_inverse(p[0])[1]))


def core_slices():
    u=seed_parts()
    v=np.zeros_like(u)
    for a,b in PAIRS:
        v[a],v[b]=1,-1
    return wht(u),wht(v)


def core_entropy(types,t):
    terms=[]
    for (a,b),m in types.items():
        coeff=times(point(Q(1,512)),add(point(a),times(point(b),t)))
        square=grid_bounds(0 if coeff[0]<=0<=coeff[1] else min(x*x for x in coeff),
                           max(x*x for x in coeff))
        terms.append(times(point(m),eta_box(square)))
    return add(*terms)


def path_histogram(seed,j,d):
    """Keep every private degree and magnitude in the nonuniform substitution."""
    n=len(seed).bit_length()-1
    a=wht(seed)
    low,high=splits(a,j)
    fixed=histogram(low,degrees(n-1))
    active=histogram(high,degrees(n-1))
    hist=histogram(a,degrees(n))
    den=len(a)
    for _ in range(1,d):
        merged=Counter({(u*den,k):m for (u,k),m in fixed.items()})
        for (u,k),m in active.items():
            for (v,l),s in hist.items():
                merged[(u*v,k+l)]+=m*s
        hist=merged
        den*=len(a)
    return hist,den


def full_first_step(seed,t,core_u,core_v):
    """Exact 621-bit coefficient/degree histogram, independent of H and I transfer."""
    hist,den=path_histogram(seed,0,4)
    tag=(int(t*den),1)
    assert t*den==tag[0] and hist[tag]>0
    hist[tag]-=1
    target=Counter()
    from math import comb
    for (v,k),m in hist.items():
        for l in range(9):
            target[v,k+l]+=9*m*comb(8,l)
    total_den=256*den
    core_nums=[Q(total_den,512)*(int(a)+int(b)*t) for a,b in zip(core_u,core_v)]
    for num,k in zip(core_nums,degrees(9)):
        assert num.denominator==1
        if num:
            target[abs(int(num)),int(k)]+=1
    h,i=summarize(+target,total_den)
    return h,i,len(+target)


def small_dense():
    """One balanced coordinate substitution with actual overlapping input labels."""
    from max1_pool import switch
    f=switch(1)
    g=switch(2)
    j=1
    n=len(f).bit_length()-1
    m=len(g).bit_length()-1
    x=np.arange(1<<(n+m-1))
    inner=(1-g[x&((1<<m)-1)])//2
    other=x>>m
    addr=(other%2**j)+(inner<<j)+((other>>j)<<(j+1))
    a=wht(f)
    b=wht(g)
    assert a[0]==b[0]==0
    lo,hi=splits(a,j)
    fixed=histogram(lo,degrees(n-1))
    active=histogram(hi,degrees(n-1))
    inner_hist=histogram(b,degrees(m))
    model=Counter({(u*len(b),k):v for (u,k),v in fixed.items()})
    for (u,k),v in active.items():
        for (c,d),e in inner_hist.items():
            model[u*c,k+d]+=v*e
    got=histogram(2*wht(f[addr]),degrees(n+m-1))
    assert model==got


def main():
    small_dense()
    seed=record_seed()
    a=wht(seed)
    h,i=summarize(histogram(a,degrees(18)),len(seed))
    q=Q(int(a[1]),len(a))
    assert q==Q(57,256) and i==Q(261,128)
    x=point(q)
    inf=point(i)
    core_u,core_v=core_slices()
    assert core_u[1]==512*q and core_v[1]==2
    types=Counter(zip(map(int,core_u),map(int,core_v)))
    n=18
    for depth in range(1,11):
        t=positive_power(x,4)
        path=add(point(1),x,positive_power(x,2),positive_power(x,3))
        t2=positive_power(t,2)
        private=add(times(path,h),times(point(16),subtract(point(1),t2)))
        h=add(core_entropy(types,t),times(point(Q(9,256)),subtract(private,eta_box(t2))))
        inf=add(point(i),times(point(Q(9,256)),times(path,subtract(inf,point(1)))))
        x=add(point(q),times(point(Q(1,256)),t))
        n=9+36*(n-1)
        score=h[0]/(inf[1]-1),h[1]/(inf[0]-1)
        if depth==1:
            first,actual_i,bins=full_first_step(seed,q**4,core_u,core_v)
            assert first[0]<=h[1] and h[0]<=first[1] and inf[0]<=actual_i<=inf[1]
            print('first full factored WHT',n,'bits',bins,'bins, I =',actual_i,flush=True)
        if depth in (1,2,4,8,10):
            print('depth',depth,'n',n,'amplified',enclose_text(score,20),flush=True)
    ordinary=(score[0]*(1-inf[0]**-80),score[1]*(1-inf[1]**-80))
    assert ordinary[0]>Q('6.5218511673478223969022')
    print('ordinary H/I for depth-80 disjoint amplification',enclose_text(ordinary,22))


if __name__=='__main__':
    main()
