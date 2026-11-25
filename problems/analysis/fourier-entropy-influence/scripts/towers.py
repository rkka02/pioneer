"""Exact WHT factors for iterated balanced composition; numerical entropy drops."""
from decimal import Decimal as D, localcontext
from functools import lru_cache
import numpy as np

from experiments import block_comp, restrictions
from walsh import checked, degrees, entropy, record_seed, signs, splits


@lru_cache(None)
def e(x):
    return -x*x.ln()/D(2).ln() if x else D(0)


def descent(f, path):
    """path lists the split bit at each gate from bottom to top (monotone seed)."""
    a = checked(f)
    mu,ratio = D(1),D(0)
    types = {}
    for j in set(path):
        u,v = splits(a,j)
        use = v!=0
        pairs,count = np.unique(np.column_stack((np.abs(u[use]),np.abs(v[use]))),
                                axis=0, return_counts=True)
        alpha = D(int(np.sum(v*v)))/D(len(f)**2)
        assert alpha == D(int(a[1<<j]))/D(len(f)) and a[0]==0
        types[j] = (alpha,[(D(int(x))/D(len(f)), D(int(y))/D(len(f)), int(m))
                            for (x,y),m in zip(pairs,count)])
    for j in path:
        alpha,pairs = types[j]
        cost = D(0)
        for u,v,m in pairs:
            w = mu*v
            cost += m*(e(u*u)-(e((u+w)**2)+e((u-w)**2))/2+e(w*w))
        ratio += cost/(alpha*mu)
        mu *= alpha
    return ratio


def certify_all_splits(f):
    from fractions import Fraction as Q
    from itertools import product
    from certificate import log2_int, enclose_text

    @lru_cache(None)
    def term(amplitude):
        if not amplitude:
            return Q(0),Q(0)
        x = abs(amplitude)
        lo,hi = log2_int(x.numerator)
        exponent = x.denominator.bit_length()-1
        assert x.denominator == 1 << exponent
        return 2*x*x*(exponent-hi),2*x*x*(exponent-lo)

    a = checked(f)
    groups = {}
    for j in range(18):
        u,v = splits(a,j)
        ids = v!=0
        pairs,counts = np.unique(np.column_stack((np.abs(u[ids]),np.abs(v[ids]))),
                                 axis=0,return_counts=True)
        alpha = Q(int((v*v).sum()),len(f)**2)
        assert alpha==Q(int(a[1<<j]),len(f))
        data = tuple((Q(int(x),len(f)),Q(int(y),len(f)),int(count))
                     for (x,y),count in zip(pairs,counts))
        if alpha in groups:
            assert groups[alpha]==data
        groups[alpha]=data
    assert len(groups)==2

    @lru_cache(None)
    def step(alpha,mu):
        lo,hi = Q(0),Q(0)
        for u,v,count in groups[alpha]:
            w = mu*v
            a0,a1 = term(u)
            b0,b1 = term(w)
            c0,c1 = term(u+w)
            d0,d1 = term(u-w)
            lo += count*(a0+b0-(c1+d1)/2)
            hi += count*(a1+b1-(c0+d0)/2)
        return lo/(alpha*mu),hi/(alpha*mu)

    for depth,floor in [(4,"7.051852835"),(8,"7.111492048")]:
        answers = []
        for path in product(groups,repeat=depth):
            mu,lo,hi = Q(1),Q(0),Q(0)
            for alpha in path:
                l,h = step(alpha,mu)
                lo,hi,mu = lo+l,hi+h,mu*alpha
            answers.append((lo,hi))
        bounds = min(r[0] for r in answers),min(r[1] for r in answers)
        assert bounds[0]>Q(floor)
        print("depth",depth,"minimum over ALL leaves",enclose_text(bounds,12))


def run():
    with localcontext() as ctx:
        ctx.prec=160  # small weak influences at depth 20 are around 1e-49
        # Balanced monotone 4-bit gate with nonzero adjacent spectral masses.
        x = np.arange(16)
        g = signs((((x&1)!=0) & ((x&14)!=0)) | ((x&14)==14))
        h = block_comp(g,g)
        _,_,r = restrictions(h,checked(h))
        for i in range(4):
            for j in range(4):
                assert abs(float(descent(g,[i,j]))-r[4*j+i,1]/r[4*j+i,0])<1e-10
        seed = record_seed()
        certify_all_splits(seed)
        a = checked(seed)
        p=(a/len(a))**2
        inf = np.sum(p*degrees(18))
        for d in (1,2,8,20):
            ratio = entropy(p)/(inf-1)*(1-inf**(-d))
            print("depth",d,"H/I",ratio,"leaf delta/I (strong, weak, alternating)",
                  [float(descent(seed,([j]*d if j in (0,9) else [0,9]*d)[:d]))
                   for j in (0,9,-1)])


if __name__ == "__main__":
    run()
