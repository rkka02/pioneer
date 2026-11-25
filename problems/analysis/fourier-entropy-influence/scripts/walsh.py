"""Integer Walsh transforms in the bit and sign convention of FEI.Challenge."""
from functools import lru_cache
from hashlib import sha256

import numpy as np


def wht(values):
    """Unnormalized, integer butterfly along the last axis (possibly batched)."""
    a = np.array(values, dtype=np.int64, order="C", copy=True)
    size = a.shape[-1]
    if not size or size & (size - 1):
        raise ValueError("last axis must have power-of-two length")
    step = 1
    while step < size:
        b = a.reshape(-1, 2 * step)
        left, right = b[:, :step].copy(), b[:, step:]
        b[:, :step] = left + right
        right[:] = left - right
        step *= 2
    return a


@lru_cache(None)
def degrees(n):
    d = np.zeros(1, dtype=np.int64)
    for _ in range(n):
        d = np.concatenate((d, d + 1))
    return d


def signs(bits):
    return 1 - 2 * np.asarray(bits, dtype=np.int64)


def eta(p):
    p = np.asarray(p, dtype=float)
    return -p * np.log2(np.where(p > 0, p, 1))


def entropy(p):
    return eta(p).sum(axis=-1)


def splits(a, i):
    block = a.reshape(*a.shape[:-1], -1, 2, 1 << i)
    shape = (*a.shape[:-1], a.shape[-1] // 2)
    return block[..., 0, :].reshape(shape), block[..., 1, :].reshape(shape)


def checked(f):
    """Exact Parseval, involution, edge counts and individual influence checks."""
    size = len(f)
    n = size.bit_length() - 1
    assert n <= 24 and np.all(np.abs(f) == 1)  # bounds all int64 sums used here
    a = wht(f)
    assert np.array_equal(wht(a), size * f) and (a*a).sum() == size**2
    for i in range(n):
        x, y = splits(f, i)
        _, b = splits(a, i)
        assert 2 * np.count_nonzero(x != y) * size == (b*b).sum()
    return a


# Numaro's n=18 table in core/selector form. 'base' is the output-bit table
# with all selectors zero. Bit x of base is the value at core input x.
BASE = int("fefefeeefefafc00feaafeaafeaafc00fefeccccfefacc00eeaacc00eeaacc00"
           "fefefeeef0f0f000faaafaaaf000f000fcfcccccf0f000000000000000000000", 16)
PAIRS = [(78, 79), (113, 121), (228, 484), (170, 186), (149, 151),
         (338, 466), (284, 316), (291, 295), (393, 457)]


def seed_parts():
    c = signs([(BASE >> i) & 1 for i in range(512)])
    for pair in PAIRS:
        c[list(pair)] = 0
    return c


def record_seed():
    x = np.arange(1 << 18)
    core = x & 511
    f = seed_parts()[core]
    for j, (u, v) in enumerate(PAIRS):
        active = (core == u) | (core == v)
        f[active] = signs((x[active] >> (9+j)) & 1)
    digest = sha256(",".join(map(str, f.tolist())).encode()).hexdigest()
    assert digest == "f8a7bb2c738d86368305111633376b1a3a83d8ee1f1abcc9a37d841b0f9c7839"
    assert all(np.all(a >= b) for a, b in (splits(f, i) for i in range(18)))
    return f


def quadratic(n):
    x = np.arange(1<<n)
    half = n//2
    return signs(degrees(half)[(x & ((1<<half)-1)) & (x>>half)] % 2)
