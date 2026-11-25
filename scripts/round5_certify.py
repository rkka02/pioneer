"""Rebuild and cross-check the independent isomorphism sieves and the raw Burnside counts."""

import argparse
import csv
import os
import shutil
import subprocess
import tempfile
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from itertools import combinations

import networkx as nx
import numpy as np

from flow_lab import boundary_counts
from round5_burnside import raw_counts
from round5_shapes import shapes

HERE = Path(__file__).resolve().parent
TARGETS = (5, 7, 9, 11, 13, 15)
RAW = {
    5: (1, 0, 0),
    7: (4, 7, 3),
    9: (286, 626, 239),
    11: (83858, 161934, 43580),
    13: (47691730, 75272724, 16278232),
    15: (41181777338, 54440984177, 9955174055),
}


def build(work):
    compiler = os.environ.get("CXX") or shutil.which("clang++") or "c++"
    common = [compiler, "-std=c++17", "-O3", "-march=native"]
    flags = (
        subprocess.run(
            ["pkg-config", "--cflags", "--libs", "nauty"], capture_output=True, text=True
        )
        if shutil.which("pkg-config")
        else None
    )
    nauty = (
        flags.stdout.split()
        if flags and flags.returncode == 0
        else ["-I/opt/homebrew/include", "-L/opt/homebrew/lib", "-lnauty"]
    )
    a, b = work / "census", work / "replay"
    subprocess.run(common + [HERE / "round5_census.cpp", *nauty, "-o", a], check=True)
    subprocess.run(common + [HERE / "round5_replay.cpp", "-o", b], check=True)
    return a, b


def check_negation():
    tested = unique = 0
    for graph in nx.graph_atlas_g():
        n = len(graph)
        if not 1 <= n <= 6:
            continue
        counts = boundary_counts(n, list(graph.edges()))
        opposite = counts
        for axis in range(n - 1):
            opposite = np.take(opposite, [0, 2, 1], axis=axis)
        assert np.array_equal(counts, opposite)
        if np.count_nonzero(counts == 0) == 1:
            assert counts.flat[0] == 0
            unique += 1
        tested += 1
    assert (tested, unique) == (208, 4)
    print("reflected full signatures", tested, "with a unique hole", unique, flush=True)


def probe(binaries):
    # One row for every possible star above each atlas graph through five vertices.
    inputs = []
    expected = []
    for h in nx.graph_atlas_g():
        n = len(h)
        if not 1 <= n <= 5:
            continue
        edges = list(h.edges)
        mask = sum(1 << (v * (v - 1) // 2 + u) for x, y in edges for u, v in [sorted((x, y))])
        holes = int((boundary_counts(n, edges) == 0).sum())
        for ns in range(1 << n):
            joined = edges + [(v, n) for v in range(n) if ns >> v & 1]
            gap = int(boundary_counts(n + 1, joined).min() == 0)
            inputs.append(f"{n} {mask} {ns}")
            expected.append(f"{holes} {gap}")
    for exe in binaries:
        out = subprocess.check_output([exe, "--probe"], input="\n".join(inputs), text=True)
        assert out.splitlines() == expected, exe
    print(
        "both kernels and full orientation tensors agree on",
        len(inputs),
        "atlas extensions",
        flush=True,
    )


def rows(exe, h, primary):
    command = [exe, str(h)]
    schedule = None
    if primary:
        command.append(str(h))
        schedule = "\n".join(" ".join(map(str, (n, *hist))) for n, hist in shapes(h)) + "\n"
    text = subprocess.check_output(command, input=schedule, text=True)
    return [[int(x) for x in line.split()] for line in text.splitlines()]


def raw_control(h):
    # Direct unlabelled geng check. Disconnected graphs are kept.
    executable = shutil.which("geng") or shutil.which("nauty-geng")
    if not executable:
        raise RuntimeError("Install nauty geng for the independent raw census control")
    m = 5 * (h - 1) // 2
    proc = subprocess.Popen(
        [executable, "-q", "-d3", "-D5", str(h), f"{m}:{m}"], stdout=subprocess.PIPE
    )
    counts = Counter()
    for line in proc.stdout:
        # Decode graph6 bits in the standard upper triangular column order.
        digits = [x - 63 for x in line.strip()[1:]]
        degree = [0] * h
        for j in range(1, h):
            for i in range(j):
                bit = j * (j - 1) // 2 + i
                if digits[bit // 6] >> (5 - bit % 6) & 1:
                    degree[i] += 1
                    degree[j] += 1
        counts[degree.count(3)] += 1
    assert proc.wait() == 0 and tuple(counts[i] for i in range(3)) == RAW[h]
    return sum(counts.values())


def explain(graph6):
    """Recover an explicit strong induced witness for any class in the target slices."""
    graph = nx.from_graph6_bytes(graph6.encode())
    n = len(graph)
    deg = dict(graph.degree())
    if (
        n not in TARGETS
        or min(deg.values()) < 3
        or max(deg.values()) > 5
        or sum(5 - d for d in deg.values()) != 5
    ):
        raise ValueError("graph is outside the certified degree slices")
    for k in range(2, n + 1):
        for vertices in combinations(range(n), k):
            induced = graph.subgraph(vertices)
            if min(dict(induced.degree()).values()) < 2 or 2 ** induced.number_of_edges() < 3 ** (
                k - 1
            ):
                continue
            p = [(vertices.index(i), vertices.index(j)) for i, j in induced.edges()]
            least = int(boundary_counts(k, p).min())
            if least:
                print(
                    "strong induced vertices",
                    vertices,
                    "number of balanced boundaries",
                    3 ** (k - 1),
                    "least orientation count",
                    least,
                )
                return
    raise AssertionError("input contradicts census")


def main():
    check_negation()
    with (HERE / "round5_census.tsv").open() as f:
        saved = [list(map(int, line)) for line in list(csv.reader(f, delimiter="\t"))[1:]]
    with tempfile.TemporaryDirectory() as work:
        a, b = build(Path(work))
        probe((a, b))
        for h in TARGETS:
            with ThreadPoolExecutor(2) as pool:
                primary = pool.submit(rows, a, h, True)
                other = pool.submit(rows, b, h, False)
                recorded = []
                for x, y in zip(primary.result(), other.result(), strict=True):
                    assert x[:5] == y[:5] and x[-1] == y[-1]
                    assert x[3] == sum(x[4:]) and y[3] == sum(y[4:])
                    recorded.append(x[:8] + y[5:7] + x[8:])
            assert recorded == [line for line in saved if line[0] == h] and recorded[-1][-1] == 0
            raw = raw_counts(h)
            assert raw == RAW[h]
            if h <= 11:
                assert raw_control(h) == sum(raw)
            print("core order", h, "raw classes", raw, "certified survivors", 0, flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--witness", metavar="GRAPH6", help="explain one raw isomorphism class")
    options = parser.parse_args()
    explain(options.witness) if options.witness else main()
