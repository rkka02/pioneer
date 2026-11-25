"""Replay the connected degree 3/4/5 census or the all-degree order census."""

import argparse
import re
import subprocess
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor


def check(job):
    group, command, mode = job
    with subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL) as gen:
        checked = subprocess.run([args.checker, *mode], stdin=gen.stdout, capture_output=True, text=True)
        gen.stdout.close()
        checked.check_returncode()
        if gen.wait():
            raise RuntimeError(f"generator failed: {command}")
    if checked.stdout:
        print(checked.stdout, end="", flush=True)
    match = re.fullmatch(r"tested=(\d+) violations=(\d+)\n", checked.stderr)
    if not match:
        raise RuntimeError(checked.stderr)
    return group, int(match[1]), int(match[2])


def jobs(mode):
    if mode == "requested":
        for r, limit in [(3, 20), (4, 16), (5, 14)]:
            for n in range(r + 1, limit + 1):
                if n*r % 2:
                    continue
                command = (["genquarticg", "-c", str(n)] if r == 4 else
                           ["geng", f"-qcd{r}D{r}", str(n)])
                split = 8 if (r, n) in {(3, 20), (5, 14)} else 1
                for j in range(split):
                    yield (r, n), command + ([f"{j}/{split}"] if split > 1 else []), []
    else:
        for n in range(2, 15):
            for r in range((n - 1)//2 + 1):
                if n*r % 2:
                    continue
                # Complementation takes care of positive degrees above (n-1)/2.
                # Include disconnected graphs because their complements can be connected.
                split = 12 if n == 14 and r >= 5 else 1
                for j in range(split):
                    command = ["geng", f"-qd{r}D{r}", str(n)]
                    yield (n,), command + ([f"{j}/{split}"] if split > 1 else []), ["--dual"]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["requested", "small"])
    parser.add_argument("checker", help="path to the compiled check_graphs executable")
    parser.add_argument("--jobs", type=int, default=4, help="number of concurrent nauty pipelines")
    args = parser.parse_args()
    totals = defaultdict(lambda: [0, 0])
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for group, count, violations in pool.map(check, jobs(args.mode)):
            totals[group][0] += count
            totals[group][1] += violations
    for group, result in sorted(totals.items()):
        print(*group, *result)
    print("total", *(sum(x[j] for x in totals.values()) for j in (0, 1)))
