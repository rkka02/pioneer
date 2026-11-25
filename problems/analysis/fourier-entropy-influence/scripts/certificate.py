"""Replay the shared-variable lower bound. Decisions use integers and Fractions."""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from math import comb

import numpy as np

from walsh import PAIRS, checked, degrees, record_seed, seed_parts, signs, splits, wht

GRID = 1 << 100


def grid_bounds(lo, hi):
    return Q((lo*GRID).__floor__(), GRID), Q((hi*GRID).__ceil__(), GRID)


@lru_cache(None)
def ln_mantissa(x):
    """Enclose ln(x) on [1,2] by integrating the geometric series."""
    assert 1 <= x <= 2
    z = (x-1)/(x+1)
    z2 = z*z
    power, total = z, Q(0)
    for j in range(40):
        total += 2*power/(2*j+1)
        power *= z2
    return grid_bounds(total, total + 2*power/(81*(1-z2)))


@lru_cache(None)
def log2_int(n):
    e = n.bit_length()-1
    a,b = ln_mantissa(Q(n, 1 << e))
    c,d = ln_mantissa(Q(2))
    return grid_bounds(e+a/d, e+b/c)


def histogram(a, ds):
    """Counter keyed by (absolute numerator, degree); zeros may be omitted."""
    ix = a != 0
    keys, counts = np.unique(np.column_stack((np.abs(a[ix]),ds[ix])),
                             axis=0, return_counts=True)
    return Counter({(int(c),int(d)):int(m) for (c,d),m in zip(keys,counts)})


def summarize(hist, den):
    assert den & (den-1) == 0
    assert sum(m*c*c for (c,d),m in hist.items()) == den**2
    moment = sum(d*m*c*c for (c,d),m in hist.items())
    magnitude = Counter()
    for (c,_),m in hist.items():
        magnitude[c] += m
    lo,hi = Q(0),Q(0)
    for c,m in magnitude.items():
        mass = Q(m*c*c,den**2)
        a,b = log2_int(c)
        lo += 2*mass*(den.bit_length()-1-b)
        hi += 2*mass*(den.bit_length()-1-a)
    return (lo,hi),Q(moment,den**2)


def blocks(gates):
    """Walsh-transform each nonconstant private-frequency slice on the full core.
    Each (g,k) is a gate with one shared core bit and independent private bits.
    """
    degree = degrees(9)
    scale = max(len(g)//2 for g,k in gates)
    average = seed_parts()*scale
    hist = Counter()
    arity = 9
    for (x,y),(g,k) in zip(PAIRS,gates):
        assert x < y and (x^y) & ((x^y)-1) == 0
        left,right = splits(g,k)
        arity += len(left).bit_length()-1
        b0,b1 = wht(left), wht(right)
        b0 *= scale//len(left)
        b1 *= scale//len(left)
        average[x],average[y] = b0[0],b1[0]
        b0[0] = b1[0] = 0
        used = (b0 != 0) | (b1 != 0)
        types,counts = np.unique(np.column_stack((b0[used],b1[used],
                                                 degrees(len(left).bit_length()-1)[used])),
                                 axis=0, return_counts=True)
        for (u,v,d),mult in zip(types,counts):
            cells = np.zeros(512,dtype=np.int64)
            cells[x],cells[y] = u,v
            layer = histogram(wht(cells),degree+d)
            hist.update({key:int(mult)*count for key,count in layer.items()})
    main = wht(average)
    assert main[0] == 0
    hist.update(histogram(main,degree))
    return hist,512*scale,arity


def replicate_histogram(hist, den, m):
    """Independent application of the indicator's product Walsh expansion.
    The distinguished singleton is +1/256 and is the only nonzero input
    coefficient without a private frequency. Degrees retain their multiplicity.
    """
    private = hist.copy()
    assert den%256==0 and private[(den//256,1)]>0
    private[(den//256,1)] -= 1
    gate_terms = Counter({key:m*cnt for key,cnt in private.items() if cnt})
    gate_terms[(den,1)] += 9-m  # untouched private dictators
    total = Counter()
    for (num,d),cnt in gate_terms.items():
        for j in range(9):
            total[(num,d+j)] += comb(8,j)*cnt
    c = 256*seed_parts()
    for u,v in PAIRS[9-m:]:
        c[u],c[v] = 1,-1
    core = histogram(wht(c),degrees(9))
    new_den = den*256
    assert new_den%(256*512)==0
    total.update({(a*(new_den//(256*512)),d):cnt for (a,d),cnt in core.items()})
    return +total,new_den


def enclose_text(interval, digits=18):
    a,b = interval
    scale = 10**digits
    lo,hi = (a*scale).__floor__(),(b*scale).__ceil__()
    def fmt(x):
        return f"{x//scale}.{x%scale:0{digits}d}"
    return f"[{fmt(lo)}, {fmt(hi)}]"


def display(name, h, inf):
    ratio = tuple(v/(inf-1) for v in h)
    print(name, "I", inf, "H", enclose_text(h), "H/(I-1)", enclose_text(ratio))
    return ratio


def check():
    seed = record_seed()
    a = checked(seed)
    assert a[0] == 0 and a[1<<9]*256 == len(a)
    seed_hist = histogram(a,degrees(18))
    h0,i0 = summarize(seed_hist,len(a))
    old = display("published seed",h0,i0)
    assert i0 == Q(261,128)
    null = (signs([0,0,1,1]),0)  # one private dictator
    # Seed replay directly against the full coefficient histogram.
    hist, den, n = blocks([null]*9)
    expected = Counter({(c*(len(a)//den),d):m for (c,d),m in hist.items()})
    assert n == 18 and expected == histogram(a,degrees(18))

    # Direct WHT on a 19-bit realization, with majority of (s,z0,z1) on edge 0.
    majority = signs(degrees(3)>=2)
    hist,den,n = blocks([(majority,0)]+[null]*8)
    idx = np.arange(1<<n)
    core = idx & 511
    table = seed_parts()[core]
    for j,(x,y) in enumerate(PAIRS):
        active = (core==x) | (core==y)
        z = idx[active] >> 9
        if j == 0:
            table[active] = majority[(core[active]==y).astype(int)+2*(z & 3)]
        else:
            table[active] = signs((z >> (j+1)) & 1)
    assert n == 19
    direct = histogram(checked(table),degrees(n))
    assert all(np.all(u>=v) for u,v in (splits(table,i) for i in range(n)))
    assert direct == Counter({(c*(len(table)//den),d):m for (c,d),m in hist.items()})

    # For monotone gates, all singletons are influences. Their sum gives
    # I(seed) + m/256*(I(inner)-1), independently of the degree histogram.
    cases = {}
    for m in (8,9):
        hist,den,n = blocks([null]*(9-m)+[(seed,9)]*m)
        assert (hist,den) == replicate_histogram(seed_hist,len(a),m)
        h,inf = summarize(hist,den)
        assert inf == i0 + Q(m,256)*(i0-1)
        print("expanded nonzero coefficients",sum(hist.values()),"arity",n)
        display(f"{m} edges",h,inf)
        cases[m] = h,inf
    h8,i8 = cases[8]
    h9,i9 = cases[9]
    assert h9[0]/(i9-1) > old[1]

    # Fixed weak singleton provided by the unused first selector of the 8-edge
    # construction. Here B_m of the report is applied to H or I separately.
    # The displayed finite depth and limiting values use positive series weights.
    for depth in (1,None):
        factor = Q(9,256) * (1 if depth == 1 else 1/(1-Q(8,256)))
        h = h9[0]+factor*(h8[0]-h0[1]), h9[1]+factor*(h8[1]-h0[0])
        inf = i9+factor*(i8-i0)
        ratio = display("finite two layers" if depth else "limit",h,inf)
        assert ratio[0] > Q("6.52185022067454")
    assert ratio[0] > Q("6.521850225089574148")
    assert ratio[1] < Q("6.521851")  # negative control against an overstated floor

    # One finite function attaining the stated floor with its ordinary H/I.
    k,depth = 12,72
    weight = Q(9,256)*(1-Q(8,256)**k)/(1-Q(8,256))
    h = h9[0]+weight*(h8[0]-h0[1]), h9[1]+weight*(h8[1]-h0[0])
    inf = i9+weight*(i8-i0)
    ordinary = tuple(v/(inf-1)*(1-inf**(-depth)) for v in h)
    assert ordinary[0] > Q("6.521850225089574148")
    n = 18
    for _ in range(k):
        n = 9+1+8*(n-1)
    n = 9+9*(n-1)
    print("finite ordinary H/I",enclose_text(ordinary,20),"arity",f"{n}^{depth}")
    # Also replay the final finite gate by integer multiplicities at every stage,
    # without using the entropy or influence affine recurrence.
    hist,den = seed_hist,len(a)
    for _ in range(k):
        hist,den = replicate_histogram(hist,den,8)
    hist,den = replicate_histogram(hist,den,9)
    h_check,i_check = summarize(hist,den)
    assert i_check==inf and h_check[0]<=h[1] and h[0]<=h_check[1]
    assert h_check[0]/(inf-1)*(1-inf**(-depth))>Q("6.521850225089574148")
    print("finite gate histogram cross-check passed;",len(hist),"magnitude-degree bins")


if __name__ == "__main__":
    check()
