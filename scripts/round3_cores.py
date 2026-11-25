"""Exact small-order candidates for a reduced core with a five-spoke completion.

A flag in a labelled lookup table means the indicated induced graph realizes every
boundary. Tables come from integer orientation counts on the graph atlas.
"""

from collections import Counter
from itertools import combinations, permutations
from functools import lru_cache
import shutil
import subprocess

import networkx as nx
import numpy as np
from numba import njit

from flow_lab import boundary_counts, edges


def positions(n):
    return [(i, j) for j in range(n) for i in range(j)]


def strong_table(n):
    pairs = positions(n)
    perm = np.array(list(permutations(range(n))), dtype=np.int32)
    weights = np.zeros((n, n), dtype=np.int32)
    for i, (u, v) in enumerate(pairs):
        weights[u, v] = weights[v, u] = 1 << i
    labels = np.array([weights[perm[:, u], perm[:, v]] for u, v in pairs])
    table = np.zeros(1 << len(pairs), dtype=np.uint8)
    seen = 0
    for g in nx.graph_atlas_g():
        if len(g) != n:
            continue
        p = edges(g)
        transformed = labels[[i for i, e in enumerate(pairs) if g.has_edge(*e)]].sum(axis=0)
        seen += len(np.unique(transformed))
        if p and int(boundary_counts(n, p).min()) > 0:
            table[transformed] = 1
    assert seen == len(table)
    return table


def subset_positions(n, s):
    ix = {e: i for i, e in enumerate(positions(n))}
    return np.array(
        [[ix[(v[a], v[b])] for a, b in positions(s)] for v in combinations(range(n), s)], dtype=np.uint8
    )


@njit
def scan(n, data, ends, tables, subsets):
    flags = np.zeros(len(data), dtype=np.uint8)
    for j, row in enumerate(data):
        degree = np.zeros(n, dtype=np.int32)
        graph = np.zeros(len(ends), dtype=np.uint8)
        for i in range(len(ends)):
            graph[i] = ((int(row[1 + i // 6]) - 63) >> (5 - i % 6)) & 1
            if graph[i]:
                a, b = ends[i]
                degree[a] += 1
                degree[b] += 1
        deficit = 0
        for d in degree:
            deficit += max(5 - d, 0)
        if deficit > 5:
            flags[j] = 1
            continue
        for index in range(3):
            table = tables[index]
            masks = subsets[index]
            for vertex_set in masks:
                label = 0
                for bit, e in enumerate(vertex_set):
                    label |= int(graph[e]) << bit
                if table[label]:
                    flags[j] = 5 + index
                    break
            if flags[j]:
                break
    return flags


@lru_cache(maxsize=20000)
def strong_mask(n, mask):
    pairs = [e for i, e in enumerate(positions(n)) if mask >> i & 1]
    if 2 ** len(pairs) < 3 ** (n - 1):
        return False
    return bool(boundary_counts(n, pairs).min() > 0)


def census(h, m, maximum, tables):
    exe = shutil.which("geng") or shutil.which("nauty-geng")
    raw = subprocess.check_output([exe, "-q", "-c", "-d3", "-D" + str(maximum), str(h), f"{m}:{m}"])
    lines = raw.splitlines()
    width = 1 + (h * (h - 1) // 2 + 5) // 6
    assert all(len(g) == width and g[0] == 63 + h for g in lines)
    sub = tuple(subset_positions(h, n) for n in (5, 6, 7))
    vals = scan(
        h,
        np.frombuffer(b"".join(lines), dtype=np.uint8).reshape((-1, width)),
        np.array(positions(h)),
        tables,
        sub,
    )
    hist = Counter(map(int, vals))
    print(
        "order, size, max degree",
        h,
        m,
        maximum,
        "inputs",
        len(lines),
        "initial histogram",
        dict(hist),
        flush=True,
    )
    for i in np.flatnonzero(vals == 0):
        g = nx.from_graph6_bytes(lines[i])
        assert sum(max(0, 5 - d) for v, d in g.degree()) <= 5
        found = False
        for size in range(8, h + 1):
            ix = positions(size)
            for group in combinations(range(h), size):
                mask = sum(1 << bit for bit, (a, b) in enumerate(ix) if g.has_edge(group[a], group[b]))
                if strong_mask(size, mask):
                    found = True
                    break
            if found:
                hist[size] += 1
                break
        if not found:
            from round3_reduced import test_reduced_core

            print("genuinely reduced", lines[i].decode(), test_reduced_core(h, edges(g)), flush=True)
    print("exact larger induced exclusions", {i: hist[i] for i in range(8, h + 1)}, flush=True)
    survivors = hist[0] - sum(hist[i] for i in range(8, h + 1))
    print("genuinely reduced survivors", survivors)
    expected = {(9, 20): 1151, (9, 21): 12982, (9, 22): 11465, (10, 23): 305148, (11, 25): 289371}
    assert len(lines) == expected[h, m] and survivors == 0


if __name__ == "__main__":
    tables = tuple(strong_table(n) for n in (5, 6, 7))
    for args in ((9, 20, 5), (9, 21, 7), (9, 22, 8), (10, 23, 6), (11, 25, 5)):
        census(*args, tables)
