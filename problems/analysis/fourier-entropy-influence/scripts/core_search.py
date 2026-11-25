"""Expose two constant core cells to fresh independent bits; search all 247^2 pairs."""
import numpy as np

from walsh import degrees, entropy, seed_parts, wht


def search():
    c = seed_parts()
    basis = wht(np.eye(512, dtype=np.int64))
    base = wht(c)
    lower, upper = np.where(c == 1)[0], np.where(c == -1)[0]
    best = (-1, None)
    for x in lower:
        p = ((base - basis[x] + basis[upper])/512)**2
        h = entropy(p) + 9*16/256 + 2*18/512
        influence = (p*degrees(9)).sum(axis=1) + 9*5/256 + 2*5.5/512
        scores = h/(influence-1)
        j = int(scores.argmax())
        if scores[j] > best[0]:
            best = (float(scores[j]),(int(x),int(upper[j])))
    print("two independent singleton replacements", len(lower)*len(upper),best)


if __name__ == "__main__":
    search()
