"""Boolean face identities, degree-sensitive deletion tails and block restriction."""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from math import isqrt

import numpy as np

from certificate import enclose_text
from experiments import block_comp, delta_tribes, tribes
from max1_lookup import dense_lookup, signed_feedback
from max1_pool import direct, ln_integer_bounds, logloss, spine_bound, switch
from walsh import degrees, record_seed, splits, wht


@lru_cache(None)
def upper_root4(v,u,k):
    # Upper dyadic bound on [v^6 (u^2+v^2) / 8^k]^(1/4).
    value=(v**6*(u*u+v*v))<<256
    root=isqrt(isqrt(value>>(3*k)))
    if (root**4)<<(3*k)!=value:
        root+=1
    return root


def boolean_tail(f):
    a=wht(f)
    N=len(a)
    n=N.bit_length()-1
    first=[Q(0),Q(0)]
    diagonal=[Q(0),Q(0)]
    I=Q(0)
    for i in range(n):
        l,r=splits(f,i)
        e=(l+r)//2
        d=(l-r)//2
        assert np.all(e*d==0) and np.all(e*e+d*d==1)
        u,v=splits(a,i)
        assert np.array_equal(u,2*wht(e)) and np.array_equal(v,2*wht(d))
        k=degrees(n-1)
        for w in (lambda j:j,lambda j:(j>=2).astype(np.int64),
                  lambda j:np.maximum(j-2,0),lambda j:j%2):
            parent=int(np.sum(a*a*w(degrees(n))))
            children=int(np.sum(((u+v)**2+(u-v)**2)*w(k)))
            signed=int(np.sum(v*v*(w(k+1)-w(k))))
            assert 2*parent-children==2*signed
            if np.all(w(k+1)>=w(k)):
                assert signed>=0
        for shift in (0,len(u)-1,len(u)//3):
            other=np.arange(len(u))^shift
            assert np.dot(u,v[other])==0
            assert np.dot(u,u[other])+np.dot(v,v[other])==(N*N if shift==0 else 0)
        weight=int(np.sum(v*v))
        alpha=Q(weight,N*N)
        I+=alpha
        bk=degrees(n-1)
        energy=Q(int(np.sum((v*v)*np.left_shift(1,n-1-bk))),N*N*(1<<(n-1)))
        assert energy**3<=alpha**4
        ids=np.flatnonzero(v)
        types=Counter(zip(map(int,np.abs(v[ids])),map(int,np.abs(u[ids])),map(int,bk[ids])))
        upper=sum(m*upper_root4(*tag) for tag,m in types.items())
        assert upper<=weight*(1<<64)
        for (b,c,k),m in types.items():
            p=Q(m*b*b,N*N)
            for j,val in enumerate(logloss(Q(c*c,b*b))):
                first[j]+=p*val
                diagonal[j]+=p*val*val/(k+1)
    assert diagonal[1]<=3*first[0]+50*I
    if I:
        pooled=direct(f)
        mixed=direct(f,True)
        assert pooled[0]*I<=diagonal[1]+mixed[1]*I and diagonal[0]+mixed[0]*I<=pooled[1]*I
        assert first[0]**2<=pooled[1]*I**2
    # All 2D faces: partial Walsh transform has these three cancellations.
    for i,j in combinations(range(n),2):
        left,right=splits(f,j)
        u,v=splits(left,i)
        w,z=splits(right,i)
        a,b,c,d=u+v+w+z,u-v+w-z,u+v-w-z,u-v-w+z
        assert np.all(a*d+b*c==0) and np.all(a*b+c*d==0) and np.all(a*c+b*d==0)
        assert np.all(a*a+b*b+c*c+d*d==16)


def matrix(f,block):
    n=len(f).bit_length()-1
    rest=[i for i in range(n) if i not in block]
    axes=[n-1-i for i in block+rest]
    return f.reshape((2,)*n).transpose(axes).reshape(1<<len(block),-1)


def entropy_box(nums,den):
    """Shannon entropy from an integer mass vector with total den."""
    lo=hi=Q(0)
    mult=Counter(map(int,np.ravel(nums)))
    assert sum(v*m for v,m in mult.items())==den
    mult.pop(0,None)
    for v,m in mult.items():
        l,h=logloss(Q(den-v,v))
        lo+=Q(v*m,den)*l
        hi+=Q(v*m,den)*h
    return lo,hi


def block_data(f,a,B,full_h):
    N=len(f)
    mass=matrix(a*a,B).sum(axis=0)
    h_m=entropy_box(mass,N*N)
    h_cond=(full_h[0]-h_m[1],full_h[1]-h_m[0])
    branches=wht(matrix(f,B))
    # Parseval on the restricted block for every outside frequency.
    assert np.array_equal(mass,(branches*branches).sum(axis=0)*len(branches))
    branch_h=[entropy_box(row*row,len(row)**2) for row in branches]
    ave=[sum(h[j] for h in branch_h)/len(branches) for j in (0,1)]
    j_lower,j_upper=h_m[0]-ave[1],h_m[1]-ave[0]
    alpha=sum(Q(int(np.sum(splits(a,i)[1]**2)),N*N) for i in B)
    assert j_lower<=j_upper and j_upper>=0
    if alpha:
        assert j_upper<=2*alpha/ln_integer_bounds(2)[1]
    else:
        assert j_lower<=0<=j_upper
    if j_lower<0:
        assert np.all(branches*branches==branches[0]*branches[0])
    # An independent conditional-entropy calculation, grouped by marginal mass.
    joint=matrix(a*a,B)
    used=joint!=0
    marg=np.broadcast_to(mass,joint.shape)
    counts=Counter(zip(map(int,joint[used]),map(int,marg[used])))
    cond=[Q(0),Q(0)]
    for (v,m),count in counts.items():
        odds=Q(m-v,v)
        for j,val in enumerate(logloss(odds)):
            cond[j]+=Q(count*v,N*N)*val
    assert cond[0]<=h_cond[1] and h_cond[0]<=cond[1]
    return cond,alpha


def block_checks(f,blocks):
    a=wht(f)
    full_h=entropy_box(a*a,len(f)**2)
    singles={i:block_data(f,a,[i],full_h) for i in sorted(set().union(*blocks))}
    for B in blocks:
        cond,alpha=block_data(f,a,B,full_h)
        assert sum(singles[i][1] for i in B)==alpha
        # H(B|outside) >= sum_i H(i|everything else).
        if cond[0]<sum(singles[i][0][1] for i in B):
            # At equality the conditional distribution on B is a product at
            # every outside frequency. Check it with integer arithmetic.
            joint=matrix(a*a,B)
            for column in joint[:,np.any(joint,axis=0)].T:
                mass=sum(map(int,column))
                marg=[(sum(map(int,splits(column,j)[0])),sum(map(int,splits(column,j)[1])))
                      for j in range(len(B))]
                for s,v in enumerate(column):
                    rhs=1
                    for j,pair in enumerate(marg):
                        rhs*=pair[(s>>j)&1]
                    assert int(v)*mass**(len(B)-1)==rhs


def incompatible_pair(m):
    f=dense_lookup(m,1)
    a=wht(f)
    i=m+1                # private label y_0
    j=0                  # first common address bit
    ids=np.arange(len(a))
    modes=ids[(a!=0)&((ids&(1<<i))!=0)&((ids&(1<<j))!=0)]
    assert modes.size>0
    for s in modes.tolist():
        v=int(a[s])**2
        assert int(a[s^(1<<i)])**2==(1<<m)*v
        assert int(a[s^(1<<j)])**2==v
    return logloss(Q(1<<m))


def first_and_influence(f):
    a=wht(f)
    n=len(a).bit_length()-1
    raw=sum(int(v)**2*int(k) for v,k in zip(a,degrees(n)))
    first=[Q(0),Q(0)]
    for s in np.flatnonzero(a).tolist():
        for i in range(n):
            if (s>>i)&1:
                v=int(a[s])**2
                for j,l in enumerate(logloss(Q(int(a[s^(1<<i)])**2,v))):
                    first[j]+=Q(v,len(a)**2)*l
    return first,Q(raw,len(a)**2)


def balanced_lift():
    f=tribes([1,2])
    h,i=first_and_influence(f)
    for k in (1,2,3):
        prod=np.array([1],dtype=np.int64)
        for _ in range(k):
            prod=np.kron(f,prod)
        g=np.concatenate((prod,-prod))
        assert not np.sum(g)
        hg,ig=first_and_influence(g)
        assert ig==1+k*i and hg[0]<=k*h[1] and k*h[0]<=hg[1]
    f=dense_lookup(2,1)
    lifted=np.concatenate((f,-f))
    # Every private incidence now belongs to a branching set, retaining its loss.
    _,upper=spine_bound(lifted)
    a=wht(lifted)
    ds=degrees(len(lifted).bit_length()-1)
    branching=Q(sum(int(v)**2*int(k) for v,k in zip(a,ds) if k>=2),len(a)**2)
    private=Q(0)
    for s in np.flatnonzero(a).tolist():
        for i in range(3,7):
            if (s>>i)&1:
                assert ds[s]>=2 and int(a[s^(1<<i)])**2==4*int(a[s])**2
                private+=Q(int(a[s])**2,len(a)**2)
    assert private==Q(1,2) and private*logloss(Q(4))[0]**2/branching<=upper


def main():
    balanced_lift()
    lower_ln2=ln_integer_bounds(2)[0]
    upper_prefactor=Q(595,1000)
    assert upper_prefactor**4>Q(1,8)
    assert upper_prefactor*(12/lower_ln2+32/lower_ln2**2)<50
    for code in range(256):
        f=1-2*((code>>np.arange(8))&1)
        boolean_tail(f)
    gates=[record_seed(),block_comp(tribes([2,2]),tribes([1,2])),
           delta_tribes(6,2),dense_lookup(2,3),switch(7)]
    gates.extend(list(signed_feedback(10,412000))[-3:])
    for f in gates:
        boolean_tail(f)
        n=len(f).bit_length()-1
        block_checks(f,[[0,1],[1,n-1],[0,2,n-1],list(range(min(n,5)))])
    for m in (2,4):
        print('private/address pair ratio',m,enclose_text(incompatible_pair(m),8))
    print('256 three-bit functions and 8 structured tables; all face, tail and block checks passed')


if __name__=='__main__':
    main()
