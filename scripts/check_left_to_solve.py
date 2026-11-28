#!/usr/bin/env python3
"""Check one Pioneer submission against its frozen statement using the pinned upstream checker."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
from urllib.request import urlopen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("problem", help="catalogue identifier, e.g. oeis-a250362")
    parser.add_argument("checker", type=Path, help="local open-math-agents checkout")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    catalog = json.loads((root / "catalog.json").read_text())
    paper = next((p for p in catalog["problems"] if p["slug"] == args.problem), None)
    if not paper or "verification" not in paper:
        parser.error("choose a paper with a Left to Solve verification record in catalog.json")
    record = paper["verification"]
    checker = args.checker.resolve()
    fc = Path(os.environ.get("OMA_FC", checker / ".oma" / "formal-conjectures")).resolve()
    proof = (root / paper["path"] / "Solution.lean").read_bytes()
    with urlopen(record["statement_raw_url"], timeout=40) as response:
        statement = response.read()
    if hashlib.sha256(statement).hexdigest() != paper["challenge_sha256"]:
        raise SystemExit("Frozen statement SHA-256 mismatch")
    if hashlib.sha256(proof).hexdigest() != record["proof_sha256"]:
        raise SystemExit("Submitted proof SHA-256 mismatch")
    with TemporaryDirectory(prefix="pioneer-lean-") as scratch:
        workspace = Path(scratch)
        for name in ("statements", "proofs", "tools", "data"):
            (workspace / name).mkdir()
        for name in ("tools/check.sh", "tools/lint.py", "tools/oma_audit.lean",
                     "data/catalog.json", "data/extra.json", "data/extra2.json"):
            data = subprocess.check_output(
                ["git", "-C", str(checker), "show", record["checker_commit"] + ":" + name]
            )
            (workspace / name).write_bytes(data)
        filename = paper["slug"] + ".lean"
        (workspace / "statements" / filename).write_bytes(statement)
        (workspace / "proofs" / filename).write_bytes(proof)
        env = dict(os.environ, OMA_FC=str(fc))
        outcome = subprocess.run(
            ["bash", "tools/check.sh", "proofs/" + filename, str(workspace / "verdict.json")],
            cwd=workspace, env=env, check=False
        )
        verdict = json.loads((workspace / "verdict.json").read_text())
        print(json.dumps(verdict, indent=2, ensure_ascii=False))
        if outcome.returncode or verdict["verdict"] != "accepted":
            raise SystemExit(outcome.returncode or 1)


if __name__ == "__main__":
    main()
