"""Reproduce a normalized census, validate fourth-coordinate coverage, or summarize logs."""

import argparse
from collections import defaultdict
from hashlib import sha256
from pathlib import Path
import subprocess
from tempfile import NamedTemporaryFile


def primary_mode(n, z):
    if n == 1015 and z >= 13:
        return "sorted"
    if n == 1015 and z >= 9:
        return "cover"
    return "cover-fast"


def run_job(binary, n, z, threads, mode, dest, validate):
    args = [str(binary.resolve()), str(n), str(z), str(z + 1), str(n), str(threads)]
    if mode != "sorted":
        args.append(mode)
    with NamedTemporaryFile(
        "w", dir=dest.parent, prefix=dest.stem + "-", suffix=".partial", delete=False
    ) as output:
        checkpoint = Path(output.name)
        subprocess.run(args, stdout=output, check=True)
    validate(checkpoint, n, z)
    checkpoint.replace(dest)


def read_primary(path, n, z):
    lines = [line.split() for line in path.read_text().splitlines()]
    if any(row[0] == "FOUND" for row in lines):
        raise ValueError(f"positive result in {path}")
    (summary,) = [row for row in lines if row[0] == "complete"]
    assert list(map(int, summary[1:4])) == [n, z, z + 1]
    attrs = dict(zip(summary[5::2], summary[6::2]))
    mode = attrs.get("method", "sorted")
    assert mode == primary_mode(n, z)
    last = n - 7 if mode == "sorted" else n - 3
    assert int(summary[4]) == last
    branches = []
    for row in lines:
        if row[0] == "fourth":
            assert list(map(int, row[1:3])) == [n, z]
            branches.append(tuple(map(int, row[3:])))
    branches.sort()
    assert [row[0] for row in branches] == list(range(z + 1, last + 1))
    assert len(branches) == int(attrs["fourths"])
    six, graphs, valid = map(sum, zip(*(b[1:] for b in branches)))
    assert [six, graphs, valid] == [int(attrs[k]) for k in ("six", "target-graphs", "valid")]
    assert six == sum(int(attrs[k]) for k in ("covered", "sparse", "dense"))
    assert valid == 0
    payload = "".join(" ".join(map(str, b)) + "\n" for b in branches).encode()
    return mode, len(branches), six, graphs, int(attrs["cliques"]), sha256(payload).hexdigest()


def read_independent(path, n, z):
    lines = [line.split() for line in path.read_text().splitlines()]
    assert not any(row[0] == "found" for row in lines)
    (s,) = [row for row in lines if row[0] == "verified"]
    assert list(map(int, s[1:3])) == [n, z]
    a = dict(zip(s[3::2], s[4::2]))
    mode = a.get("method", "sorted")
    assert mode in {"sorted", "cover"}
    assert int(a["fourths"]) == n - (7 if mode == "sorted" else 3) - z and int(a["valid"]) == 0
    return mode, int(a["six"]), int(a["ten"])


def summarize(root, n, lo, hi, with_second):
    totals = defaultdict(int)
    for z in range(lo, hi + 1):
        pm, jobs, six, graphs, cliques, digest = read_primary(root / f"{n}-{z}.log", n, z)
        row = [n, z, pm, jobs, six, graphs, cliques, digest]
        for name, v in [("fourths", jobs), ("six", six), ("graphs", graphs), ("cliques", cliques)]:
            totals[name] += v
        if with_second:
            vm, vs, vt = read_independent(root / f"ind-{n}-{z}.log", n, z)
            row.extend([vm, vs, vt])
            totals["ind-six"] += vs
            totals["ind-ten"] += vt
        print(*row)
    print("total", n, lo, hi, *[f"{k}={v}" for k, v in totals.items()])


def upper(path, n, lo, hi):
    rows = []
    for line in path.read_text().splitlines():
        v = line.split()
        assert v[0] == "upper" and int(v[1]) == n and int(v[-1]) == 0
        rows.append(tuple(map(int, (v[2], v[4], v[6], v[8]))))
    rows.sort()
    assert [r[0] for r in rows] == list(range(lo, hi + 1))
    digest = sha256("".join(" ".join(map(str, r)) + "\n" for r in rows).encode()).hexdigest()
    print(
        "upper",
        n,
        lo,
        hi,
        "shards",
        len(rows),
        "six",
        sum(r[1] for r in rows),
        "ten",
        sum(r[2] for r in rows),
        "valid",
        0,
        "sha256",
        digest,
    )


def profile_counts(path, tag, n):
    (line,) = path.read_text().splitlines()
    fields = line.split()
    assert fields[:2] == [tag, str(n)]
    counts = dict(zip(fields[2::2], map(int, fields[3::2])))
    assert counts["valid"] == 0
    return counts


def report(root):
    print(
        "# Each row gives N, third coordinate, primary traversal, number of fourth jobs, six-point"
    )
    print(
        "# prefixes, target graphs, cliques, SHA-256 of sorted fourth-coordinate records, followed"
    )
    print(
        "# when available by independent traversal, six-point prefixes and complete tuples tested."
    )
    for n, lo, hi, second in [
        (1015, 3, 26, True),
        (1013, 3, 23, True),
        (1014, 3, 44, False),
        (1014, 45, 49, False),
        (1014, 3, 3, True),
        (722, 4, 4, True),
        (723, 4, 4, True),
    ]:
        print()
        summarize(root, n, lo, hi, second)
    print(
        "\n# Independent large-third-coordinate traversals. Sorted records include the third, six, ten, valid."
    )
    for n, lo, hi in [(1015, 27, 1007), (1013, 24, 1005), (1014, 45, 1006)]:
        upper(root / f"upper-{n}.log", n, lo, hi)
    print("\n# Fixed-configuration searches. N, primary six, primary graphs, primary cliques,")
    print("# independent six, independent complete tuples, primary valid, independent valid.")
    for n in range(712, 724):
        p = profile_counts(root / f"profile-{n}.log", "profile", n)
        v = profile_counts(root / f"ind-profile-{n}.log", "profile-verified", n)
        print(
            "floor",
            n,
            p["six"],
            p["graphs"],
            p["cliques"],
            v["six"],
            v["ten"],
            p["valid"],
            v["valid"],
        )
    for file, prefix in [("crt.log", "three axes 1015 "), ("nonunit-1014.log", "nonunit 1014 ")]:
        (row,) = [s for s in (root / file).read_text().splitlines() if s.startswith(prefix)]
        assert row.endswith("valid 0")
        print(row)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    run = sub.add_parser("run")
    run.add_argument("solver", choices=["primary", "independent"])
    run.add_argument("binary", type=Path)
    run.add_argument("threads", type=int)
    audit = sub.add_parser("audit")
    audit.add_argument("--independent", action="store_true")
    upper_cmd = sub.add_parser("upper")
    sub.add_parser("report").add_argument("path", type=Path)
    for p in (run, audit, upper_cmd):
        p.add_argument("path", type=Path)
        p.add_argument("n", type=int)
        p.add_argument("lo", type=int)
        p.add_argument("hi", type=int)
    a = parser.parse_args()
    if a.action == "report":
        report(a.path)
    elif a.action == "upper":
        upper(a.path, a.n, a.lo, a.hi)
    elif a.action == "audit":
        summarize(a.path, a.n, a.lo, a.hi, a.independent)
    else:
        a.path.mkdir(parents=True, exist_ok=True)
        for z in range(a.lo, a.hi + 1):
            primary = a.solver == "primary"
            mode = primary_mode(a.n, z) if primary else "cover"
            dest = a.path / (("" if primary else "ind-") + f"{a.n}-{z}.log")
            validate = read_primary if primary else read_independent
            if dest.exists():
                validate(dest, a.n, z)
            else:
                run_job(a.binary, a.n, z, a.threads, mode, dest, validate)
