"""All degree histograms reached by deleting a minimum-degree vertex of a target core."""

from collections import Counter
from itertools import combinations_with_replacement
import sys


def shapes(order):
    level = {
        tuple(5 - d for d in deficit)
        for deficit in combinations_with_replacement((2, 1, 0), order)
        if sum(deficit) == 5
    }
    while level:
        for degrees in sorted(level):
            yield len(degrees), tuple(degrees.count(k) for k in range(6))
        if len(next(iter(level))) == 1:
            break
        parents = set()
        for degrees in level:
            remaining = list(degrees)
            degree = remaining.pop(remaining.index(min(remaining)))
            counts = Counter(remaining)
            for neighbours in combinations_with_replacement(sorted(counts), degree):
                used = Counter(neighbours)
                if used[0] or any(used[k] > counts[k] for k in used):
                    continue
                residual = counts - used
                residual.update(k - 1 for k in neighbours)
                parents.add(tuple(sorted(residual.elements())))
        level = parents


if __name__ == "__main__":
    for n, histogram in shapes(int(sys.argv[1])):
        print(n, *histogram)
