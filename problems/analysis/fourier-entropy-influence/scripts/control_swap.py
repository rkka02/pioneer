"""Control an input transposition with a fresh bit; both branches are isomorphic."""
from itertools import combinations
import numpy as np

from walsh import checked, degrees, entropy, record_seed


def search():
    f = record_seed()
    a = checked(f)
    idx = np.arange(len(f))
    influence = np.sum(degrees(18)*(a*a))/len(f)**2
    best = (-1,None)
    for i,j in combinations(range(18),2):
        selected = ((idx >> i) ^ (idx >> j)) & 1
        perm = idx ^ (selected*((1 << i) | (1 << j)))
        # Restriction WHTs differ by the same permutation of character indices.
        b = a[perm]
        c = np.concatenate((a+b, a-b))
        h = entropy((c/(2*len(f)))**2)
        extra = np.mean(f != f[perm])
        assert (c[len(f):]**2).sum() == (2*len(f))**2*extra
        score = h/(influence+extra-1)
        if score > best[0]:
            best = (float(score),(i,j))
    i,j = best[1]
    flip = ((idx >> i) ^ (idx >> j)) & 1
    perm = idx ^ (flip*((1<<i) | (1<<j)))
    c = checked(np.concatenate((f,f[perm])))
    assert np.array_equal(c,np.concatenate((a+a[perm],a-a[perm])))
    print("153 controlled swaps",best)


if __name__ == "__main__":
    search()
