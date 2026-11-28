"""Exact cross-checks for A181411 and the figure used in the paper."""
from argparse import ArgumentParser
from fractions import Fraction
from math import comb, isqrt, pi


def divisor_sums(limit):
    sums = [0] * (limit + 1)
    for divisor in range(1, limit + 1):
        for multiple in range(divisor, limit + 1, divisor):
            sums[multiple] += divisor
    return sums


def by_pairs(m):
    return sum(d + (m // d if d*d != m else 0)
               for d in range(1, isqrt(m) + 1) if m % d == 0)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--plot', action='store_true')
    args = parser.parse_args()
    last = 256
    sigma = divisor_sums(2 * last)
    assert sigma[1:] == [by_pairs(m) for m in range(1, 2 * last + 1)]
    values = [sum(comb(n, k) * sigma[n+k] for k in range(n+1))
              for n in range(1, last + 1)]
    assert values[:10] == [4, 18, 55, 150, 379, 915, 2146, 4934, 11080, 24833]
    fractions = [Fraction(v, n * 2**n) for n, v in enumerate(values, 1)]
    if args.plot:
        from pathlib import Path
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.pyplot as plt
        fig, ax = plt.subplots(figsize=(6.4, 2.5), constrained_layout=True)
        ax.scatter(range(1, last + 1), list(map(float, fractions)), s=8,
                   color='#126666', linewidth=0)
        ax.axhline(pi*pi/4, color='#ad4026', ls='--', lw=1.2,
                   label=r'$\pi^2/4$')
        ax.set(xlabel='Index $n$', ylabel=r'$A_n/(n2^n)$', xlim=(0, last+3))
        ax.spines[['top', 'right']].set_visible(False)
        ax.legend(frameon=False)
        fig.savefig(Path(__file__).with_name('mean.pdf'),
                    metadata={'CreationDate': None, 'ModDate': None})
    print(f'Verified divisor sums through {2*last} and evaluated {last} exact means.')


if __name__ == '__main__':
    main()
