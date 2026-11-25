"""Restriction, noise-flow, certificate, and counterexample-family experiments."""
from fractions import Fraction
import numpy as np

from walsh import checked, degrees, entropy, eta, quadratic, record_seed, signs, splits, wht


def restrictions(f, a, check_children=True):
    """Accept single or batched truth tables. Return H, I, and per-bit Delta,L,J."""
    size = f.shape[-1]
    n = size.bit_length()-1
    p = (a/size)**2
    h = entropy(p)
    influence = (p*degrees(n)).sum(axis=-1)
    result = []
    for i in range(n):
        u,v = splits(a,i)
        left,right = splits(f,i)
        if check_children:
            assert np.array_equal(2*wht(left),u+v) and np.array_equal(2*wht(right),u-v)
        s0,s1 = (u/size)**2,(v/size)**2
        mass = s0+s1
        p0,p1 = ((u+v)/size)**2,((u-v)/size)**2
        prev_h = (entropy(p0)+entropy(p1))/2
        delta = h-prev_h
        local = h-entropy(mass)
        js = entropy(mass)-prev_h
        alpha = s1.sum(axis=-1)
        expected = np.mean(left!=right,axis=-1)
        assert np.array_equal(alpha,expected)
        assert np.max(np.abs(influence-alpha-((p0+p1)*degrees(n-1)).sum(axis=-1)/2)) < 1e-12
        assert np.all(js >= -1e-12) and np.all(js <= 4*alpha+1e-12)
        assert np.all(local <= eta(alpha)+eta(1-alpha)+1e-12)
        result.append((alpha,delta,local,js))
    return h,influence,np.asarray(result)


def exhaustive():
    from deletion import losses
    for n in range(1,5):
        size = 1<<n
        maxima = np.zeros(6)
        for start in range(0,1<<size,512):
            codes = np.arange(start,min(start+512,1<<size))
            f = signs((codes[:,None] >> np.arange(size)) & 1)
            a = wht(f)
            assert np.all((a*a).sum(axis=1)==size**2)
            h,inf,r = restrictions(f,a)
            active = inf>0
            alpha,delta,local,_ = r.transpose(1,0,2)
            ok = alpha[:,active]>0
            # Never count an irrelevant coordinate as a cheap split.
            ratio = delta[:,active]/np.where(ok,alpha[:,active],1)
            vals = [np.max(h[active]/inf[active]),
                    np.max(np.min(np.where(ok,ratio,np.inf),axis=0)),
                    np.max(np.where(ok,ratio,0)),np.max(local[:,active].sum(axis=0)/inf[active])]
            d,m4,_,ps = losses(a)
            assert np.all(local.sum(axis=0) <= d+np.log2(np.e)*inf+1e-12)
            vals.extend((np.max(m4[active]/inf[active]),np.max(ps[active]/inf[active])))
            maxima = np.maximum(maxima,vals)
        print("exhaustive",n,"max H/I,best split,worst split,sum L/I,M1/4/I,pooled square/I",maxima)


def tribes(widths):
    n = sum(widths)
    x = np.arange(1<<n)
    hit = np.zeros(len(x),dtype=bool)
    offset = 0
    for width in widths:
        mask = ((1<<width)-1)<<offset
        hit |= ((x & mask)==mask)
        offset += width
    return signs(hit)


def delta_tribes(k,w):
    f = tribes([w]*k)
    g = f.copy()
    g[(1<<w)-1] = 1  # turn off the minimal true point of the first block
    return np.concatenate((g,f))


def block_comp(outer,inner):
    arity = len(outer).bit_length()-1
    width = len(inner).bit_length()-1
    x = np.arange(1<<(width*arity))
    address = np.zeros_like(x)
    for j in range(arity):
        address |= ((1-inner[(x>>(j*width)) & (len(inner)-1)])//2)<<j
    return outer[address]


def flow(a,t):
    p = (a/len(a))**2
    d = degrees(len(a).bit_length()-1)
    nz = p>0
    d,p = d[nz],p[nz]
    q = p*np.exp(-2*t*(d-d.min()))
    q /= q.sum()
    mean = np.sum(q*d)
    slope = 2*np.sum(q*(d-mean)*np.log2(q))
    variance = np.sum(q*(d-mean)**2)
    return float(entropy(q)),mean,slope,-2*variance


def family_tests():
    from deletion import losses
    cases = {}
    for n in (3,7,11,15,19):
        cases[f"majority {n}"] = signs(degrees(n)>n//2)
    maj3 = cases["majority 3"]
    cases["majority of majorities"] = block_comp(maj3,maj3)
    cases["iterated tribes"] = block_comp(tribes([2,2]),tribes([2,2]))
    for widths in ([1,2,3,4,5],[2]*8,[3]*5,[4]*4):
        cases["tribes "+str(widths)] = tribes(widths)
    for n in (4,8,12,16):
        bent = quadratic(n)
        changed = bent.copy()
        changed[0] *= -1
        cases[f"bent flip selector {n}"] = np.concatenate((bent,changed))
        cases[f"bent sparse mask {n}"] = np.concatenate((bent,np.ones(3*len(bent),dtype=int)))
    # An address selects a data bit. Then reuse data through a parity code.
    for k in (1,2,3):
        m = 1<<k
        idx = np.arange(1<<(k+m))
        s,z = idx & (m-1),idx>>k
        cases[f"address {k}"] = signs((z>>s)&1)
        cases[f"coded address {k}"] = signs(((z>>s)^(z>>((s+1)%m))) & 1)
    # Follow two-bit pointers in a common four-entry table, then read data.
    idx = np.arange(1<<14)
    for hops in (1,2,3,6):
        pos = idx & 3
        for _ in range(hops):
            pos = (idx>>(2+2*pos)) & 3
        cases[f"pointer {hops}"] = signs((idx>>(10+pos)) & 1)
    # Mask a quadratic sign by low-rank parity checks.
    z = np.arange(1<<14)
    for masks in ((7,), (7,28), (7,28,112,448)):
        live = np.ones(len(z),dtype=bool)
        for mask in masks:
            live &= (degrees(14)[z&mask]%2==0)
        cases[f"code mask {len(masks)}"] = np.where(live,quadratic(14),1)
    cases["Numaro"] = record_seed()

    for name,f in cases.items():
        a = checked(f)
        h,inf,r = restrictions(f,a)
        p = (a/len(f))**2
        d = degrees(len(f).bit_length()-1)
        for level in range(len(r)+1):
            assert level*p[d>=level].sum() <= inf
        alpha,delta,local,js = r.T
        split = delta[alpha>0]/alpha[alpha>0]
        dl,m4,ls,ps = losses(a)
        assert sum(local) <= dl+np.log2(np.e)*inf+1e-10
        for t in (0.0,.25,1.0):
            ht,it,slope,di = flow(a,t)
            attenuated = p*np.exp(-2*t*d)
            z = attenuated.sum()
            assert abs(entropy(attenuated)-z*ht-eta(z))<1e-11
            hp,ip,*_ = flow(a,t+1e-5)
            hm,im,*_ = flow(a,t-1e-5)
            assert abs((hp-hm)/2e-5-slope)<1e-6 and abs((ip-im)/2e-5-di)<1e-6
        print(f"{name:29s} H/I {h/inf:.8f}   Delta/I {min(split):.7f}..{max(split):.7f}   sum L/I {sum(local)/inf:.7f}   pooled/I {ps/inf:.7f}")
        if name.startswith("majority "):
            ht,it,*_ = flow(a,5)
            if " of " not in name:
                assert abs(ht/it-np.log2(len(r)))<1e-6
        if name == "Numaro":
            print("seed classes (alpha,Delta,L,JS)",r[[0,9]])
        if name=="majority of majorities":
            assert inf==2.25 and h==5  # direct balanced-composition recurrence
    for w,kmax in ((2,9),(3,6)):
        for k in range(1,kmax+1):
            f = delta_tribes(k,w)
            a = checked(f)
            h,inf,r = restrictions(f,a,False)
            alpha,delta,local,js = r[-1]
            n = w*k
            assert alpha==2.**(-n)
            bound = 2*k*(2.**(-w)-2.**(-n))*np.log2(2**w-1)
            assert local/alpha + 1e-8 >= bound
            print("delta tribes",w,k,"local,delta,proved floor,global",
                  *(round(v,8) for v in (local/alpha,delta/alpha,bound,h/inf)))


def diagnostics():
    # A homogeneous quadratic Boolean sign with four coefficients.
    x = np.arange(16)
    a,b,c,d = (signs((x>>i)&1) for i in range(4))
    f = (a*(b+c)+d*(b-c))//2
    for g in (f,a*b):
        coeff = checked(g)
        assert np.all(degrees(4)[coeff!=0]==2)
        print("homogeneous",flow(coeff,4))
    # Perturb three-bit full parity at one input. Normalized heat can add entropy.
    f = signs(degrees(3)%2)
    f[0] *= -1
    slope = flow(checked(f),0)[2]
    assert abs(slope-(27/32)*np.log2(9))<1e-12
    print("flipped parity normalized H derivative at zero",slope)
    # Bounded low-degree truncation check, and biased orthogonal expansion of a bit.
    m = checked(signs(degrees(3)>=2))
    trunc = wht(np.where(degrees(3)<=1,m,0))
    assert np.max(np.abs(trunc)) == 12  # normalization 8
    bit = checked(np.array([1,-1]))//2
    for k in (4,8,12):
        mu = 1-2.**(-k)
        p = np.array([(bit[0]+bit[1]*mu)**2,bit[1]**2*(1-mu**2)])
        assert p.sum()==1
        print("biased dictator",k,entropy(p)/p[1])
        eps = 2.**(-k)
        mass = (bit[0]+bit[1]*eps)**2
        print("dictator entropy gain/quadratic variation",k,(eta(mass)+eta(1-mass))/eps**2)
    for n in (4,8,16):
        f = tribes([n])
        a = checked(f)
        inf = np.sum(degrees(n)*(a/len(a))**2)
        print("AND certificate cost/I",n,(1+(n-1)/len(f))/inf)
    # Exact WHTs of the factors in Biswas--Sarkar's 30-bit example, (13),(15).
    terms = (7,8,9,10,11,13,14,16,17,19,20,21,22,24,25,26,28)
    x = np.arange(32)
    bits = np.bitwise_xor.reduce([(x&t)==t for t in terms])
    g = signs(bits)
    b = checked(g)
    a = checked(np.concatenate((g,g[::-1])))
    assert b[0]==0
    best = max(Fraction(int(u)**2,64**2)*Fraction(int(np.max(b*b)),32**2)**int(d)
               for u,d in zip(a,degrees(6)))
    inf = Fraction(int(np.sum(b*b*degrees(5))),32**2)*Fraction(int(np.sum(a*a*degrees(6))),64**2)
    assert best == Fraction(1,4096) and Fraction(12)/inf==Fraction(128,45)
    print("30-bit factored maximum mass,I,min-entropy/I",best,inf,Fraction(12)/inf)


if __name__ == "__main__":
    exhaustive()
    family_tests()
    diagnostics()
