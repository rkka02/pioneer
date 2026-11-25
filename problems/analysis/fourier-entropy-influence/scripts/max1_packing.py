"""Exact spectra for partial/perfect edge packs with an overlapped gate.

Labels are independent private inputs, with a single core bit reused per edge.
Arbitrary signs, orientations and sparse or full matchings are allowed.
"""
from collections import Counter
from fractions import Fraction as Q
from math import comb
import random
import numpy as np

from certificate import enclose_text, histogram, log2_int, summarize
from walsh import degrees, entropy, eta, record_seed, splits, wht


def parallel_matching(n):
    return [(x,x+1) for x in range(0,1<<n,2)]


def scrambled_matching(n,rng):
    mate = {x:x^1 for x in range(1<<n)}
    for _ in range(n*(1<<n)):
        x=rng.randrange(1<<n)
        y=mate[x]
        bit=1<<rng.randrange(n)
        if bit!=x^y and mate[x^bit]==y^bit:
            mate[x],mate[x^bit]=x^bit,x
            mate[y],mate[y^bit]=y^bit,y
    return [(x,y) for x,y in sorted(mate.items()) if x<y]


def oriented_core(n,edges,rng):
    outside=np.ones(1<<n,dtype=np.int64)
    direction=np.zeros_like(outside)
    for x,y in edges:
        diff=x^y
        assert diff and not (diff & (diff-1))
        assert outside[x] and outside[y]
        outside[[x,y]]=0
        sign=rng.choice([-1,1])
        direction[x],direction[y]=sign,-sign
    sites=np.flatnonzero(outside).tolist()
    rng.shuffle(sites)
    outside[sites[:len(sites)//2]]=-1
    assert outside.sum()==0 and direction.sum()==0
    return outside,direction


def gate_data(g,k):
    a=wht(g)
    assert a[0]==0
    t=Q(int(a[1<<k]),len(g))
    hist=histogram(a,degrees(len(g).bit_length()-1))
    h,i=summarize(hist,len(g))
    return a,t,h,i


def exact_pack(outside,orient,edges,g,k):
    a,t,h,inf=gate_data(g,k)
    n=len(outside).bit_length()-1
    fixed=n-1
    w=Q(1,1<<fixed)
    alpha=len(edges)*w
    c=outside*t.denominator+orient*t.numerator
    ca=wht(c)
    cden=len(c)*t.denominator
    assert not ca[0]
    rawden=len(g)*(1<<fixed)
    # Choose a common exact power-of-two denominator for all Walsh slices.
    den=max(cden,rawden)
    total=Counter({(u*(den//cden),d):m for (u,d),m in histogram(ca,degrees(n)).items()})
    private=a.copy()
    private[[0,1<<k]]=0
    for (u,d),m in histogram(private,degrees(len(g).bit_length()-1)).items():
        for j in range(n):
            total[u*(den//rawden),d+j]+=len(edges)*comb(fixed,j)*m
    H,I=summarize(total,den)
    B=outside+orient if t>=0 else outside-orient
    b=wht(B)
    bh,bi=summarize(histogram(b,degrees(n)),len(b))
    energy=Q(sum(int(v)**2*int(d) for v,d in zip(ca,degrees(n))),cden*cden)
    assert I==alpha*inf+energy-alpha*t*t+alpha*fixed*(1-t*t)/2
    assert energy-alpha*t*t >= t*t*(bi-alpha)
    if alpha==1:
        assert I==inf+t*t*(bi-1)+Q(fixed,2)*(1-t*t)
        target=[h[s]+t*t*bh[s]+2*fixed*(1-t*t) for s in (0,1)]
        assert H[0]<=target[1] and target[0]<=H[1]
    if alpha>=Q(255,256):
        # The small slack in R also covers exact equality of entropy intervals.
        R=max([Q(6)]+[bnd[1]/(influ-1) for bnd,influ in [(h,inf),(bh,bi)] if influ>1])
        if I>1:
            assert H[1]<=(R+Q(1,1<<76))*(I-1)
        else:
            assert I==1 and H==(0,0)
        budget=alpha*fixed/2-(1-alpha)
        assert budget>0 and 2*alpha*fixed+2*(1-alpha)+Q(n+4,8)<=6*budget
        if alpha<1:
            upper=alpha*h[1]+t*t*bh[1]+(1-t*t)*(2*alpha*fixed+2*(1-alpha)+Q(n+4,8))
            assert H[1]<=upper
    return total,den,H,I


def dense_pack(outside,orient,edges,g,k):
    n=len(outside).bit_length()-1
    zsize=len(g)//2
    arity=n+len(edges)*(zsize.bit_length()-1)
    assert arity<=21
    x=np.arange(1<<arity)
    core=x%len(outside)
    f=outside[core].copy()
    for j,(u,v) in enumerate(edges):
        sel=(core==u)|(core==v)
        z=(x[sel]>>(n+j*(zsize.bit_length()-1)))%(zsize)
        shared=(orient[core[sel]]<0).astype(np.int64)
        lo=(1<<k)-1
        idx=(z&lo)+((z&~lo)<<1)+(shared<<k)
        f[sel]=g[idx]
    return f


def comparison(n,edges,g,k,rng):
    outside,orient=oriented_core(n,edges,rng)
    hist,den,h,i=exact_pack(outside,orient,edges,g,k)
    f=dense_pack(outside,orient,edges,g,k)
    d=degrees(len(f).bit_length()-1)
    a=wht(f)
    # Compare normalized rational coefficients by magnitude and spectral degree.
    target=Counter({(Q(c,den),s):m for (c,s),m in hist.items() if m})
    got=Counter({(Q(c,len(f)),s):m for (c,s),m in histogram(a,d).items()})
    assert got==target
    edges_i=sum(2*np.count_nonzero(l!=r) for l,r in
                (splits(f,j) for j in range(len(f).bit_length()-1)))
    assert Q(int(edges_i),len(f))==i


def fast_score(outside,orient,edges,t,h,inf):
    n=len(outside).bit_length()-1
    a=len(edges)/(1<<(n-1))
    amps=wht(outside*t.denominator+orient*t.numerator)/(len(outside)*t.denominator)
    p=amps*amps
    x=float(t*t)
    full_h=entropy(p)+a*(h-eta(x)+2*(n-1)*(1-x))
    full_i=np.sum(p*degrees(n))+a*(inf-x+(n-1)*(1-x)/2)
    return full_h/(full_i-1) if full_i>1 else 0.


def partial_entropy(a,den):
    """Entropy of a subprobability, with dyadic coefficient denominator."""
    lo=hi=Q(0)
    for v,m in Counter(abs(int(q)) for q in a if q).items():
        l,h=log2_int(v)
        mass=Q(m*v*v,den*den)
        lo+=2*mass*(den.bit_length()-1-h)
        hi+=2*mass*(den.bit_length()-1-l)
    return lo,hi


def face_check(rng):
    """Glue gates on unequal, nonparallel subcubes, reusing all their free bits."""
    n=5
    faces=[{0:0,1:0},{0:0,1:1,4:0},{0:0,1:1,4:1},{0:1,2:0},{0:1,2:1}]
    private=[1,2,1,2,1]
    arity=n+sum(private)
    x=np.arange(1<<arity)
    f=np.zeros_like(x)
    c=np.zeros(1<<n,dtype=np.int64)
    scale=1<<max(private)
    den=1<<arity
    prediction=Counter()
    copied=Q(0)
    delta_h=[Q(0),Q(0)]
    delta_i=Q(0)
    offset=n
    for face,bits in zip(faces,private):
        fixed=len(face)
        free=[j for j in range(n) if j not in face]
        g=np.array(rng.choices([-1,1],k=1<<(len(free)+bits)),dtype=np.int64)
        a=wht(g)
        addr=sum(((x>>j)&1)<<i for i,j in enumerate(free))
        covered=np.ones(len(x),dtype=bool)
        for j,b in face.items():
            covered &= ((x>>j)&1)==b
        z=(x>>offset)% (1<<bits)
        assert not np.any(f[covered])
        f[covered]=g[(addr+(z<<len(free)))[covered]]
        cells=g.reshape(1<<bits,-1).sum(axis=0)
        mask=covered[:len(c)]
        c[mask]=cells[addr[:len(c)][mask]]*(scale>>bits)
        core_a=a[:len(cells)]
        weight=Q(1,1<<fixed)
        variance=1-Q(sum(int(v)**2 for v in core_a),len(g)**2)
        hg,ig=summarize(histogram(a,degrees(len(free)+bits)),len(g))
        hc=partial_entropy(core_a,len(g))
        for k in (0,1):
            delta_h[k]+=weight*(hg[k]-hc[1-k])
        child_energy=Q(sum(int(v)**2*int(k) for v,k in zip(core_a,degrees(len(free)))),len(g)**2)
        delta_i+=weight*(ig-child_energy)
        copied+=weight*fixed*variance
        a[:len(cells)]=0
        for (v,k),m in histogram(a,degrees(len(free)+bits)).items():
            for l in range(fixed+1):
                prediction[v*(den//(len(g)<<fixed)),k+l]+=m*comb(fixed,l)
        offset+=bits
    assert np.all(f!=0)
    core=wht(c)
    core_den=len(c)*scale
    for (v,k),m in histogram(core,degrees(n)).items():
        prediction[v*(den//core_den),k]+=m
    actual=histogram(wht(f),degrees(arity))
    assert actual==prediction
    full_h,full_i=summarize(actual,den)
    ch=partial_entropy(core,core_den)
    ci=Q(sum(int(v)**2*int(k) for v,k in zip(core,degrees(n))),core_den**2)
    assert full_i==ci+delta_i+copied/2
    lower,upper=[ch[k]+delta_h[k]+2*copied for k in (0,1)]
    assert lower<=full_h[1] and full_h[0]<=upper


def main():
    from max1_pool import switch
    rng=random.Random(41201)
    small=switch(1)
    for n in (2,3,4):
        edges=scrambled_matching(n,rng)
        for m in (1,2,len(edges)):
            comparison(n,edges[:m],small if n%2 else -small,1,rng)
    g=record_seed()
    # Both types of distinguished input, plus a near-dictator.
    gates=[(g,0),(g,9),(switch(6),6)]
    data=[gate_data(f,k) for f,k in gates]
    best={}
    for n in range(3,11):
        for pack in range(8):
            perfect=scrambled_matching(n,rng)
            rng.shuffle(perfect)
            # A coset packing: parallel edges with even parity of the remaining
            # bits form disjoint edges with no adjacency between different edges.
            induced=[(x,y) for x,y in parallel_matching(n) if int(degrees(n)[x])%2==0]
            for edges in [induced,perfect[:len(perfect)//4],perfect[:len(perfect)//2],
                          perfect[:-1],perfect]:
                outside,orient=oriented_core(n,edges,rng)
                for j,(_,t,hh,i) in enumerate(data):
                    score=fast_score(outside,orient,edges,t,float(hh[0]),float(i))
                    if j not in best or best[j][0]<score:
                        best[j]=(float(score),n,edges[:],outside.copy(),orient.copy())
            if pack==0:
                for edges in (perfect[:-1],perfect):
                    outside,orient=oriented_core(n,edges,rng)
                    for f,k in gates:
                        exact_pack(outside,orient,edges,f,k)
    for j,(score,n,edges,outside,orient) in best.items():
        _,_,h,i=exact_pack(outside,orient,edges,*gates[j])
        print("gate",j,"best n,edges,I,score",n,len(edges),i,
              enclose_text(tuple(v/(i-1) for v in h),9))
    print("nine dense WHTs and 960 scored gate/packing instances passed")
    for _ in range(8):
        face_check(rng)
    print("eight mixed-codimension subcube partitions passed")
    n=9
    dense=scrambled_matching(n,rng)
    outside,orient=oriented_core(n,dense[:-1],rng)
    parity=1-2*(degrees(3)%2)
    dictator=np.tile([1,-1],4)
    for f in (parity,dictator,-dictator):
        exact_pack(outside,orient,dense[:-1],f,0)
    print("near-perfect packing at signed singleton values 0, 1, -1 passed")


if __name__=="__main__":
    main()
