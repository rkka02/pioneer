"""The order-14 exception to forcing a theta outside a closed prescribed star."""

from collections import Counter, defaultdict
from itertools import permutations, product
import shutil
import subprocess

import networkx as nx
import numpy as np
from flow_lab import edges
from round3_cores import positions, scan, strong_table, subset_positions
from round3_cover import has_strong


def encoded(n, p):
    """Bit chunks for graph6, with one entry per labelled edge."""
    mask = sum(1 << i for i, e in enumerate(positions(n)) if e in p)
    length = n * (n - 1) // 2
    return np.array(
        [sum(((mask >> (i + j)) & 1) << (5 - j) for j in range(6)) for i in range(0, length, 6)],
        dtype=np.uint8,
    )


def shapes():
    geng = shutil.which("geng") or shutil.which("nauty-geng")
    shapes = defaultdict(dict)
    count = 0
    for line in subprocess.check_output([geng, "-cq", "-D5", "8", "10:10"]).splitlines():
        g = nx.from_graph6_bytes(line)
        if any(g.subgraph(s).number_of_edges() > len(s) for s in nx.biconnected_components(g)):
            continue
        count += 1
        sequence = tuple(sorted(d for _, d in g.degree()))
        classes = [
            ([v for v, d in g.degree() if d == k], [i for i, d in enumerate(sequence) if d == k])
            for k in sorted(set(sequence))
        ]
        for parts in product(*(permutations(targets) for vs, targets in classes)):
            label = {a: b for (vs, _), into in zip(classes, parts) for a, b in zip(vs, into)}
            p = frozenset(tuple(sorted((label[a], label[b]))) for a, b in g.edges())
            shapes[sequence].setdefault(p, None)
    assert count == 8
    return {seq: np.stack([encoded(13, p) for p in variants]) for seq, variants in shapes.items()}


def main():
    patterns = shapes()
    genbg = shutil.which("genbg") or shutil.which("nauty-genbg")
    lines = subprocess.check_output([genbg, "-q", "-d0:4", "-D4:4", "8", "5", "20:20"]).splitlines()
    assert len(lines) == 668
    tables = tuple(strong_table(s) for s in (5, 6, 7))
    sub = tuple(subset_positions(13, s) for s in (5, 6, 7))
    chunks = []
    used = 0
    for line in lines:
        g = nx.from_graph6_bytes(line)
        by_deg = sorted(range(8), key=lambda i: 5 - g.degree(i))
        seq = tuple(5 - g.degree(i) for i in by_deg)
        if seq not in patterns:
            continue
        used += 1
        lab = {v: i for i, v in enumerate(by_deg)}
        parts = {(lab[a], b) for a, b in edges(g)}
        blocks = patterns[seq] | encoded(13, parts)
        chunks.append(np.column_stack([np.full(len(blocks), 76, dtype=np.uint8), blocks + 63]))
    data = np.vstack(chunks)
    tally = Counter()
    flags = scan(13, data, np.array(positions(13)), tables, sub)
    tally.update(map(int, flags[flags > 0]))
    assert (used, len(data), tally) == (118, 10875, {5: 855, 6: 2373, 7: 4306})
    print(
        "degree-compatible types",
        used,
        "completions",
        len(data),
        "passing small tables",
        int(sum(flags == 0)),
        flush=True,
    )
    for idx in np.flatnonzero(flags == 0):
        j = nx.from_graph6_bytes(bytes(data[idx]))
        assert j.number_of_edges() == 30
        # All (up to independent side permutations) matchings of degree classes are covered.
        # Check the full core first; fall back to checking induced subgraphs if necessary.
        assert has_strong(j), (nx.to_graph6_bytes(j, header=False), edges(j))
    print(
        "cactus shapes",
        8,
        "bipartite types",
        len(lines),
        "degree-compatible types",
        used,
        "labelled completions tested",
        len(data),
        "small strong witness sizes",
        dict(tally),
        "additional exact tests",
        int(sum(flags == 0)),
        flush=True,
    )


if __name__ == "__main__":
    main()
