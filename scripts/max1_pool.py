"""Certified deterministic transfer of pooled deletion loss in disjoint towers.

The Walsh transform is integer; probability and unary path laws are Fractions.
The last integral is enclosed by midpoint and trapezoid sums of a polynomial
with nonnegative coefficients. All arithmetic in the enclosure is outward.
"""
from collections import Counter, defaultdict
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from functools import lru_cache

import numpy as np

from walsh import degrees, record_seed, signs, wht

BITS = 112
UNIT = 1 << BITS


def grid(q, up):
    n = q.numerator * UNIT
    return -(-n//q.denominator) if up else n//q.denominator


@lru_cache(None)
def ln_integer_bounds(n):
    # Decimal.ln is correctly rounded (ROUND_HALF_EVEN), independently of
    # context rounding. Widen its result by one floating-point neighbor.
    if n == 1:
        return Q(0),Q(0)
    with localcontext() as ctx:
        ctx.prec = 75
        v = Decimal(n).ln()
        return Q(v.next_minus()), Q(v.next_plus())


@lru_cache(None)
def logloss(odds):
    """Rational interval for log2(1+odds), including exact zero."""
    if not odds:
        return Q(0),Q(0)
    x = 1+odds
    nl,nu = ln_integer_bounds(x.numerator)
    dl,du = ln_integer_bounds(x.denominator)
    l2,u2 = ln_integer_bounds(2)
    return Q(grid(max(Q(0),(nl-du)/u2),False),UNIT), Q(grid((nu-dl)/l2,True),UNIT)


def tilted_gate(f, mu):
    """Centered active-block probabilities and output mean at input mean mu."""
    n = len(f).bit_length()-1
    a = wht(f)
    if not mu:
        means = Q(int(a[0]),len(f))
        p = {s:Q(int(a[s])**2,len(f)**2) for s in np.flatnonzero(a).tolist()}
    else:
        # Shift the multilinear polynomial from x to mu+u. The real biased
        # coefficients are these Taylor coefficients times sigma^degree.
        c = [Q(int(x),len(f)) for x in a]
        for i in range(n):
            for s in range(1<<n):
                if not s & (1<<i):
                    c[s] += mu*c[s | (1<<i)]
        means = c[0]
        var = 1-mu*mu
        p = {s:t*t*var**int(degrees(n)[s]) for s,t in enumerate(c) if t}
    assert sum(p.values())==1 and abs(means)<1
    p.pop(0,None)
    active = 1-means*means
    return {s:q/active for s,q in p.items()},means


def unary_extend(previous, singles):
    out = Counter()
    for u, count in previous.items():
        for v, mult in singles.items():
            out[u*v] += count*mult
    return out


def gate_profile(p):
    # Group Boolean masks with identical multisets of nonzero deletion odds.
    degree_mass = defaultdict(Q)
    groups = defaultdict(Q)
    singles = Counter()
    for s,weight in p.items():
        bits = [1<<j for j in range(s.bit_length()) if (s>>j)&1]
        k = len(bits)
        degree_mass[k] += weight
        if k==1:
            singles[weight]+=1
        else:
            odds = tuple(sorted(p[s^b]/weight for b in bits if s^b in p))
            if odds:
                groups[(k,odds)]+=weight
    return degree_mass,groups,singles


def corrections(paths,odds):
    """Unconditional sum on the all-unary event, first and squared log loss."""
    low,high = [Q(0),Q(0)],[Q(0),Q(0)]
    for v,mult in paths.items():
        lo,hi = logloss(odds/v)
        weight = mult*v
        low[0] += weight*lo
        low[1] += weight*lo*lo
        high[0] += weight*hi
        high[1] += weight*hi*hi
    return low,high


def layer(profile,paths):
    weights,groups,_ = profile
    distinct = {r for _,rs in groups for r in rs}
    saved = {r:corrections(paths,r) for r in distinct}
    sides = []
    for up in (False,True):
        sums = defaultdict(lambda:[Q(0),Q(0),Q(0)])
        for (k,rs),prob in groups.items():
            total = Q(0)
            single = Q(0)
            pair = Q(0)
            for r in rs:
                b,v = saved[r][up]
                pair += 2*total*b
                total += b
                single += v
            row = sums[k]
            row[0] += prob*total
            row[1] += prob*single
            row[2] += prob*pair
        sides.append([(k,grid(p,up),*(grid(v,up) for v in sums[k])) for k,p in sorted(weights.items())])
    return sides


def integrand(z,layers,terminal,up,component):
    """Evaluate the pooled, diagonal, or mixed integrand with directed rounding."""
    endpoint = 0 if component=="mixed" else grid(terminal[up][1],up)
    if z==0:
        return endpoint
    pad = UNIT-1 if up else 0
    def mul(a,b):
        return (a*b+pad)>>BITS
    f,b,v = z,0,0
    for stage in layers:
        rows = stage[up]
        powers = [UNIT,f]
        for _ in range(2,rows[-1][0]+1):
            powers.append(mul(powers[-1],f))
        f1=b1=v1=0
        for k,prob,c,s,e in rows:
            f1 += mul(prob,powers[k])
            b1 += mul(powers[k-1],mul(k*prob,b)+mul(z,c))
            child = mul(k*prob,v)
            if component!="mixed":
                child += mul(z,s)
            v1 += mul(powers[k-1],child)
            if k>=2 and component!="diagonal":
                pair = k*(k-1)*mul(prob,mul(b,b))+2*(k-1)*mul(c,mul(b,z))+mul(e,mul(z,z))
                v1 += mul(powers[k-2],pair)
        f,b,v = min(UNIT,f1),b1,v1
    # Terminal root odds only add to paths of total degree one.
    return ((v*UNIT+ (z-1 if up else 0))//z)+endpoint


def integrate(layers,terminal,mean_k,splits,dyads,component):
    """Split [1-2^-j, 1-2^-j-1] into equal intervals, then cover the last gap."""
    assert splits & (splits-1)==0 and (1<<(dyads+1))*splits < UNIT
    mesh = [0]
    for j in range(dyads):
        step = UNIT//((1<<(j+1))*splits)
        start = mesh[-1]
        mesh.extend(start+step*i for i in range(1,splits+1))
    mesh.append(UNIT)
    lower=upper=0
    old = integrand(0,layers,terminal,True,component)
    for left,right in zip(mesh,mesh[1:]):
        new = integrand(right,layers,terminal,True,component)
        lower += (right-left)*integrand((right+left)//2,layers,terminal,False,component)
        upper += (right-left)*(new+old)
        old = new
    return Q(lower,UNIT**2)/mean_k,Q(upper,2*UNIT**2)/mean_k


def tower(gates, observed, splits=8, component="pooled"):
    assert component in ("pooled","mixed","diagonal")
    mu = Q(0)
    unary = Counter({Q(1):1})
    layers=[]
    mean_k=Q(1)
    records={}
    cache={}
    for level,g in enumerate(gates,1):
        key = (id(g),mu)
        if key not in cache:
            p,new_mu = tilted_gate(g,mu)
            cache[key] = gate_profile(p),new_mu
        profile,mu = cache[key]
        layers.append(layer(profile,unary))
        mean_k *= sum(k*v for k,v in profile[0].items())
        unary=unary_extend(unary,profile[2])
        if level in observed:
            terminal = corrections(unary,mu*mu/(1-mu*mu))
            # Pointwise quadrature bounds hold at any mesh resolution.
            dyads = max(10,mean_k.numerator.bit_length()-mean_k.denominator.bit_length()+12)
            bounds=integrate(layers,terminal,mean_k,splits,dyads,component)
            records[level]=bounds
    return records


def direct(f,cross=False):
    """Independent integer WHT and rational log enclosure on an ordinary cube."""
    a = wht(f)
    n = len(f).bit_length()-1
    moment = sum(int(x)**2*int(k) for x,k in zip(a,degrees(n)))
    modes = Counter()
    for s in np.flatnonzero(a).tolist():
        if not s:
            continue
        k = int(degrees(n)[s])
        c = abs(int(a[s]))
        row = tuple(sorted(abs(int(a[s^(1<<j)])) for j in range(n) if (s>>j)&1))
        modes[k,c,row]+=1
    lo=hi=Q(0)
    for (k,c,row),m in modes.items():
        l,h,pair_l,pair_h=Q(0),Q(0),Q(0),Q(0)
        for b in row:
            x,y=logloss(Q(b*b,c*c))
            pair_l += 2*l*x
            pair_h += 2*h*y
            l+=x
            h+=y
        lo += Q(m*c*c,k)*(pair_l if cross else l*l)
        hi += Q(m*c*c,k)*(pair_h if cross else h*h)
    return lo/moment,hi/moment


def switch(w):
    x=np.arange(1<<(w+2))
    private=np.where((x&((1<<w)-1))==0,x>>(w+1),x>>w)
    return signs(private&1)


def print_case(name,results):
    from certificate import enclose_text
    for d,bounds in results.items():
        print(name,d,enclose_text(bounds,6),flush=True)


def spine_bound(g):
    """Upper endpoint of the uniform-in-depth bound from a size-biased leaf."""
    p,mu=tilted_gate(g,Q(0))
    assert not mu
    weights,groups,singles=gate_profile(p)
    branching=sum(k*v for k,v in weights.items() if k>=2)
    if branching==0:
        return Q(0),Q(0)
    m1=m2=branch_loss=Q(0)
    for v,count in singles.items():
        y=logloss(1/v-1)[1]
        m1+=count*v*y
        m2+=count*v*y*y
    for (_,odds),mass in groups.items():
        branch_loss+=mass*sum(logloss(r)[1]**2 for r in odds)
    assert m1<=3*branching and m2<=18*branching
    result=2*(branch_loss+m2)/branching+4*(m1/branching)**2
    return result,branch_loss/branching


def spine_mean(g,cutoff):
    """Enclose the finite-depth leaf mean and its infinite geometric continuation."""
    p,mu=tilted_gate(g,Q(0))
    assert not mu
    weights,groups,singles=gate_profile(p)
    influence=sum(k*v for k,v in weights.items())
    theta=weights.get(1,0)/influence
    if theta==1:
        return (Q(0),Q(0)),(Q(0),Q(0))
    branches=Counter()
    for (_,odds),mass in groups.items():
        for r in odds:
            branches[r]+=mass
    L=max((logloss(r)[1] for r in branches),default=Q(0))
    Y=max((logloss(1/v-1)[1] for v in singles),default=Q(0))
    paths=Counter({Q(1):1})
    partial=[Q(0),Q(0)]
    for a in range(cutoff):
        for r,mass in branches.items():
            ends=corrections(paths,r)
            for side in range(2):
                partial[side]+=mass*ends[side][0]/influence**(a+1)
        paths=unary_extend(paths,singles)
    tail=theta**cutoff*(L+Y*(cutoff+theta/(1-theta)))
    return tuple(partial),(partial[0],partial[1]+tail)


def main():
    from experiments import block_comp,tribes
    # Test both prior-incoming-odds cases on complete ordinary two-level cubes.
    for inner,outer in [(switch(1),switch(1)),(tribes([1,2]),tribes([2,2]))]:
        f=block_comp(outer,inner)
        for cross in (False,True):
            dense=direct(f,cross)
            bounds=tower([inner,outer],{2},splits=16,component="mixed" if cross else "pooled")[2]
            assert bounds[0]<=dense[0]<=dense[1]<=bounds[1]
        dense=direct(f)
        mixed=direct(f,True)
        diag=tower([inner,outer],{2},splits=16,component="diagonal")[2]
        assert diag[0]<=dense[1]-mixed[0] and dense[0]-mixed[1]<=diag[1]
    print("two full-cube comparisons passed",flush=True)
    for w in (2,5,8):
        g=switch(w)
        uniform,m=spine_bound(g)
        assert m<=1+Q((2*w+1)**2,1<<w) and uniform<=88
        result=tower([g]*12,{1,4,12})
        assert all(v[1]<uniform for v in result.values())
        print_case(f"rare switch w={w}",result)
    mixed=[switch(w) for w in (1,4,7,2,8,3)]
    result=tower(mixed,{3,6})
    assert all(v[1]<88 for v in result.values())
    print_case("variable-width switches",result)
    for widths,depth in [([2,2],6),([1,3],6)]:
        g=tribes(widths)
        for w in (1,2,4,8,16,32,64,128):
            rare=Q(1,1<<w)
            mu=(1-2*rare)*(1 if widths==[2,2] else -1)
            p,_=tilted_gate(g,mu)
            assert p[3]>=Q(1,192)
            weights,groups,single=gate_profile(p)
            assert sum(k*v for k,v in weights.items() if k>=2)>=Q(1,96)
            assert sum(m*v*logloss(1/v-1)[1] for v,m in single.items())<=4
            assert sum(m*v*logloss(1/v-1)[1]**2 for v,m in single.items())<=8
            assert sum(m*sum(logloss(r)[1]**2 for r in odds) for (_,odds),m in groups.items())<=12
        result=tower([g]*depth,{1,2,4,5,depth})
        assert all(v[1]<594000 for v in result.values())
        print_case(f"tribes {widths}",result)
    g=record_seed()
    uniform,_=spine_bound(g)
    result=tower([g]*20,{4,12,20},splits=16)
    assert all(v[1]<uniform for v in result.values())
    print_case("Numaro",result)
    print_case("Numaro fine scan",tower([g]*10,range(2,11),splits=32))
    print_case("Numaro all-depth upper",{0:(uniform,uniform)})
    print_case("Numaro cross/I",tower([g]*20,{4,12,20},splits=16,component="mixed"))
    print_case("Numaro diagonal/I",tower([g]*20,{4,12,20},splits=16,component="diagonal"))
    from certificate import enclose_text
    for gate,label in [(g,"Numaro"),(switch(2),"width-2 switch")]:
        _,limit=spine_mean(gate,32)
        p,_=tilted_gate(gate,Q(0))
        weights,groups,singles=gate_profile(p)
        D=sum(k*v for k,v in weights.items() if k>=2)
        first=[sum(m*sum(logloss(r)[s] for r in odds) for (_,odds),m in groups.items())/D
               for s in (0,1)]
        unary=sum(m*v*logloss(1/v-1)[1] for v,m in singles.items())/D
        assert first[1]<=limit[0] and limit[1]<=first[0]+unary
        print(label,"limiting P2/I",enclose_text(tuple(v*v for v in limit),17),flush=True)
        print(label,"conditional branching loss",enclose_text(first,12),flush=True)
    # Independent check of the truncated series on an ordinary two-level cube.
    small=switch(1)
    f=block_comp(small,small)
    a=wht(f)
    raw_i=sum(int(v)**2*int(k) for v,k in zip(a,degrees(9)))
    mean=[Q(0),Q(0)]
    for s in np.flatnonzero(a).tolist():
        for j in range(9):
            if (s>>j)&1:
                val=int(a[s])**2
                for k,cost in enumerate(logloss(Q(int(a[s^(1<<j)])**2,val))):
                    mean[k]+=val*cost/raw_i
    truncated,_=spine_mean(small,2)
    assert mean[0]<=truncated[1] and truncated[0]<=mean[1]


if __name__=="__main__":
    main()
