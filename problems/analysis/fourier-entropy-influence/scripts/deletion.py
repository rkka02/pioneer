"""Spectral deletion loss and the failure of uniform higher-moment estimates."""
from math import comb, log2

import numpy as np

from walsh import checked, degrees, entropy, quadratic, splits


def losses(a):
    """Unnormalised by influence. Accept one Walsh vector or a batch."""
    size = a.shape[-1]
    n = size.bit_length()-1
    p = (a/size)**2
    d = degrees(n)
    total = np.zeros_like(p)
    moment = np.zeros_like(p[...,0])
    log_square = np.zeros_like(moment)
    for i in range(n):
        lo,hi = splits(p,i)
        odds = lo/np.where(hi>0,hi,1)
        loss = np.log2(1+odds)
        shape = (*p.shape[:-1],-1,2,1<<i)
        total.reshape(shape)[...,1,:] += loss.reshape(total.reshape(shape)[...,1,:].shape)
        moment += (hi*(odds**.25)).sum(axis=-1)
        log_square += (hi*loss**2).sum(axis=-1)
    first = (p*total).sum(axis=-1)
    pooled_square = (p*total**2/np.maximum(d,1)).sum(axis=-1)
    # Jensen within each nonempty spectral set.
    assert np.all(pooled_square <= log_square+1e-10)
    return first,moment,log_square,pooled_square


def bent_lookup(m):
    nlabels = 1 << m
    size = 1 << (m+1+nlabels)
    idx = np.arange(size)
    address = idx % nlabels
    data = idx >> (m+1)
    return np.where((idx & nlabels)==0,quadratic(m)[address],
                    1-2*((data>>address)&1))


def lookup_formula(m):
    """Exact grouped coefficients for all even m; test each group on small cubes."""
    from fractions import Fraction as Q
    N = 1<<m
    p0,p1 = Q(1,4*N),Q(1,4*N*N)
    assert 2*N*p0+2*N*N*p1==1
    # Each core deletion has odds 1; a private deletion has odds N.
    pooled = 0.
    for k in range(m+2):
        mass = comb(m+1,k)/2**(m+1)
        pooled += mass*(k+(k+log2(1+N))**2/(k+1))/2
    return 1.5*m+2, m/2+1, (m+1)/2+N**.25/2, pooled


if __name__ == "__main__":
    for m in (2,4,8,16,32,64):
        h,inf,moment,pooled = lookup_formula(m)
        if m<=4:
            f = bent_lookup(m)
            a = checked(f)
            p = (a/len(f))**2
            n = len(f).bit_length()-1
            assert abs(entropy(p)-h)<1e-10 and np.sum(p*degrees(n))==inf
            d,m4,ls,ps = losses(a)
            assert np.isclose(m4,moment) and np.isclose(ps,pooled)
            assert np.isclose(ls,(m+1)/2+np.log2(1+2**m)**2/2)
        print("lookup",m,"H/I, quarter moment/I, pooled square/I",
              h/inf,moment/inf,pooled/inf)
