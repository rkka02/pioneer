"""One outer variable is reused by an inner gate. Group equal Walsh pairs."""
from collections import Counter
from fractions import Fraction

import numpy as np

from walsh import checked, degrees, entropy, record_seed, splits, wht


def group(cols):
    # Includes multiplicity and degree, so influence is recovered independently.
    return np.unique(np.column_stack(cols), axis=0, return_counts=True)


def lift(f, j, i, g, k, orient=1):
    """Distribution as (signed integer numerator, degree, multiplicity) triples.
    Return coefficient denominator and nonzero DC numerator separately.
    i uses the original outer numbering, and j is the replaced variable.
    """
    fa = wht(f)
    ga = wht(g)
    return lift_spectra(fa, j, i, ga, k, orient)


def lift_spectra(fa, j, i, ga, k, orient):
    a, b = splits(fa, j)
    reduced_i = i - (i > j)
    outer_degree = degrees(len(a).bit_length()-1)
    bp = b[np.arange(len(b)) ^ (1 << reduced_i)]
    g0, g1 = splits(ga, k)
    g1 = orient * g1
    private_degree = degrees(len(g0).bit_length()-1)
    den = len(fa)*len(ga)
    core = a*len(ga) + b*g0[0] + bp*g1[0]
    vals, multiplicities = group([core, outer_degree])
    rows = [(int(c), int(d), int(m)) for (c,d), m in zip(vals, multiplicities) if c]
    out = (b != 0) | (bp != 0)
    inn = (g0 != 0) | (g1 != 0)
    inn[0] = False
    outer, oc = group([b[out], bp[out], outer_degree[out]])
    inner, ic = group([g0[inn], g1[inn], private_degree[inn]])
    for (x,y,d),m in zip(outer,oc):
        nums = x*inner[:,0] + y*inner[:,1]
        for c,e,h in zip(nums,inner[:,2],ic):
            if c:
                rows.append((int(c), int(d+e), int(m*h)))
    return den, int(core[0]), rows


def summary(den, rows):
    hist = Counter()
    moment = 0
    for c, d, m in rows:
        hist[abs(c)] += m
        moment += c*c*d*m
    assert sum(c*c*m for c,m in hist.items()) == den**2
    h = sum(m*float(entropy(np.array([(c/den)**2]))) for c,m in hist.items())
    return h, Fraction(moment, den**2), hist


def compose_table(f, j, i, g, k, orient=1):
    """Ordinary full cube for a small independent check of the grouped formula."""
    nf = len(f).bit_length()-1
    x = np.arange(len(f)*len(g)//4)
    outer = x % (len(f)//2)
    z = x >> (nf-1)
    free = ((outer >> (i-(i>j))) & 1) ^ (orient < 0)
    inner = insert_bit(z, k, free)
    return f[insert_bit(outer, j, (1-g[inner])//2)]


def insert_bit(x, j, bit):
    lo = (1 << j)-1
    return (x & lo) + ((x & ~lo) << 1) + (bit << j)


def self_check():
    rng = np.random.default_rng(412)
    for n,m in [(3,4),(6,5),(4,3)]:
        f,g = (rng.choice([-1,1], 1<<d) for d in (n,m))
        for j,i,k in [(0,1,0),(1,0,m-1),(n-1,n-2,1)]:
            for sign in [-1,1]:
                table = compose_table(f,j,i,g,k,sign)
                exact = checked(table)
                den,dc,rows = lift(f,j,i,g,k,sign)
                # Full distribution by signed coefficient AND its degree.
                want = Counter((int(a)*4,int(d)) for a,d in
                               zip(exact,degrees(n+m-2)) if a)
                got = Counter()
                for a,d,count in rows:
                    got[a,d] += count
                assert got == want and dc == 4*exact[0] and den == 4*len(table)


def search():
    self_check()
    f = record_seed()
    fa = checked(f)
    # Cyclic/symmetry assumptions are unnecessary for these tested positions.
    winners = []
    biased = 0
    for j in (0,9):
        for i in range(18):
            if i == j:
                continue
            for k in (0,9):
                for sign in (1,-1):
                    den, dc, rows = lift_spectra(fa,j,i,fa,k,sign)
                    h, influence, _ = summary(den,rows)
                    if dc == 0:
                        winners.append((h/float(influence-1),j,i,k,sign,h,influence))
                    else:
                        biased += 1
    print("one shared bit", len(winners), "balanced;",biased,"biased")
    for result in sorted(winners,reverse=True)[:8]:
        print(result)


if __name__ == "__main__":
    search()
