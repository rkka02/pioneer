"""Random shared-variable circuits, a single-flip search and deep spectral sampling."""
import numpy as np

from deletion import losses
from walsh import checked, degrees, entropy, record_seed, signs, wht


def scores(f):
    n = len(f).bit_length()-1
    a = wht(f)
    p = (a/len(f))**2
    inf = np.sum(degrees(n)*p)
    if not inf:
        return 0.,0.
    return float(entropy(p)/inf),float(losses(a)[-1]/inf)


def circuits(rng):
    for n in (6,8,10,12):
        x = np.arange(1<<n)
        best = np.zeros(2)
        for _ in range(256):
            pool = [signs((x>>j)&1) for j in range(n)]
            for _ in range(20):
                i,j,k = rng.integers(len(pool),size=3)
                a,b,c = pool[i],pool[j],pool[k]
                op = rng.integers(5)
                if op == 0:
                    out = a*b
                elif op == 1:
                    out = np.minimum(a,b)
                elif op == 2:
                    out = np.maximum(a,b)
                elif op == 3:
                    out = np.where(a<0,b,c)
                else:
                    out = np.sign(a+b+c)
                pool.append(out if rng.integers(2) else -out)
            best = np.maximum(best,scores(pool[-1]))
        print("random circuits",n,"max H/I, pooled/I",best)
    # Optimize each statistic individually. A restart can drop all prior gains.
    for n in (6,8,10):
        for target in (0,1):
            best = 0.
            for _ in range(6):
                f = rng.choice([-1,1],1<<n)
                score = scores(f)[target]
                for _ in range(120):
                    i = rng.integers(len(f))
                    f[i] *= -1
                    trial = scores(f)[target]
                    if trial>=score:
                        score = trial
                    else:
                        f[i] *= -1
                best = max(best,score)
            print("greedy",n,("H/I","pooled/I")[target],best)


def pooled_tower(rng):
    """Sample ordinary Fourier sets exactly, using integer CDFs. Estimate a ratio
    of expectations by aggregate numerator/aggregate degree across samples.
    This last estimate is Monte Carlo; it is not part of the bound certificate.
    """
    a = checked(record_seed())
    support = np.flatnonzero(a)
    cdf = np.cumsum(a[support]**2)
    d = degrees(18)[support]
    logp = np.log2((a[support]/len(a))**2)
    base = np.zeros((18,len(support)))
    for i in range(18):
        b = np.abs(a[support^(1<<i)])
        with np.errstate(divide="ignore"):
            base[i] = 2*np.log2(b/np.abs(a[support]))
    for depth in (2,8,18):
        sums = np.zeros(2)
        for _ in range(16):
            log_odds = np.array([-np.inf])
            for _ in range(depth):
                draws = rng.integers(int(cdf[-1]),size=len(log_odds))
                node = np.searchsorted(cdf,draws,side="right")
                masks = support[node]
                children = []
                for i in range(18):
                    use = (masks & (1<<i))!=0
                    selected = node[use]
                    children.append(np.where(d[selected]==1,log_odds[use]-logp[selected],
                                             base[i,selected]))
                log_odds = np.concatenate(children)
            degree = len(log_odds)
            loss = np.logaddexp2(0,log_odds).sum()
            sums += [loss**2/degree,degree]
        print("Numaro tower depth",depth,"16 sets, total leaves",int(sums[1]),
              "sampled pooled/I",sums[0]/sums[1])


if __name__ == "__main__":
    circuits(np.random.default_rng(412))
    pooled_tower(np.random.default_rng(413))
