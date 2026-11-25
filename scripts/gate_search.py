"""Search over replacements of the nine selector edges, using exact Walsh blocks."""
import numpy as np

from walsh import PAIRS, checked, degrees, entropy, eta, record_seed, seed_parts, signs, splits, wht


def gate(f, free):
    """An edge gate on (s, private bits), with distinguished bit s at index free.
    Return branch means and the contributions with nonempty private frequency.
    Integer dyadic means are represented at scale 2^18, exact for these gates.
    """
    a = wht(f) / len(f)
    mean, t = a[0], a[1 << free]
    a[[0, 1 << free]] = 0
    p = a*a
    return (round((mean+t)*262144), round((mean-t)*262144),
            float((entropy(p) + 16*p.sum()) / 256),
            float(np.sum(p * (4+degrees(len(f).bit_length()-1))) / 256))


def score(choices):
    c = 262144 * seed_parts()
    for (x, y), g in zip(PAIRS, choices):
        c[x], c[y] = g[:2]
    a = wht(c) / (512*262144)
    p = a*a
    h = entropy(p) + sum(g[2] for g in choices)
    influence = np.sum(p*degrees(9)) + sum(g[3] for g in choices)
    return float(h / (influence-1)), h, influence, a[0]


def explore():
    f = record_seed()
    checked(f)
    # The dictator ignores the free coordinate. A sign reversal of the free
    # coordinate is allowed in the signed search, but can lose monotonicity.
    gates = [gate(signs([0, 0, 1, 1]), 0), gate(f, 9), gate(f, 0)]
    print("uniform gates: dictator, weak seed bit, strong seed bit, odd majorities")
    for g in gates + [gate(signs(degrees(n) > n//2), 0) for n in range(3, 16, 2)]:
        print(g[:2], score([g]*9)[:3])
    # Sensitivity of the interference term in (1) relative to zero sharing.
    # This grid varies a rational core model; it does not assert the
    # existence of a gate of equal entropy and influence at each value of t.
    c = seed_parts()
    original_h = entropy((wht(c)/512)**2)
    direction = np.zeros_like(c)
    for x,y in PAIRS:
        direction[x],direction[y] = 1,-1
    gain = []
    for j in range(1,201):
        t = j/2000
        p = (wht(2000*c+j*direction)/(2000*512))**2
        gain.append(entropy(p)-original_h-9/256*(eta(t*t)+16*t*t))
    print("interference grid peak t, gain", (np.argmax(gain)+1)/2000, max(gain))

    # Batch all 3^9 choices (including inverted free direction) for each scale.
    for inner in gates[1:]:
        variants = [gates[0], inner, (inner[1], inner[0], *inner[2:])]
        best = -1
        from itertools import product, islice
        menu = iter(product(range(3), repeat=9))
        while True:
            batch = list(islice(menu, 256))
            if not batch:
                break
            codes = np.array(batch)
            matrix = np.tile(262144*seed_parts(), (len(batch), 1))
            extra_h = np.zeros(len(batch))
            extra_i = np.zeros(len(batch))
            for j, (x,y) in enumerate(PAIRS):
                for k,g in enumerate(variants):
                    sel = codes[:,j] == k
                    matrix[sel, x], matrix[sel, y] = g[:2]
                    extra_h[sel] += g[2]
                    extra_i[sel] += g[3]
            p = (wht(matrix)/(512*262144))**2
            ratios = (entropy(p)+extra_h) / ((p*degrees(9)).sum(axis=1)+extra_i-1)
            k = int(ratios.argmax())
            if ratios[k] > best:
                best, winner = ratios[k], batch[k]
        print("ternary search", inner[:2], best, winner)

    # Another unbalanced substitution: pin the weak or strong seed coordinate
    # at opposite values on two host edges, so the combined table is balanced.
    for i in [9, 0]:
        minus, plus = splits(f, i)
        gs = [gate(np.repeat(h, 2), 0) for h in (minus, plus)]
        scores = []
        for a in range(9):
            for b in range(9):
                if a != b:
                    trial = [gates[0]]*9
                    trial[a], trial[b] = gs
                    scores.append(score(trial)[0])
        print("oppositely biased edge pair", i, min(scores), max(scores))


if __name__ == "__main__":
    explore()
