#!/usr/bin/env python3
"""Build the Lean library, verify the frozen hash, and audit each public research declaration."""
import hashlib
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
FROZEN = ROOT / "CatchUpGame" / "Challenge.lean"
EXPECTED = "0c7b6e8f75bde1c74259441029e6abe935610064d7748cd93bb28460ccbb5df3"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def check_hash():
    actual = hashlib.sha256(FROZEN.read_bytes()).hexdigest()
    if actual != EXPECTED:
        raise SystemExit(f"Frozen challenge hash mismatch: {actual}")
    print("Frozen SHA-256", actual, flush=True)


def main():
    check_hash()
    source = (ROOT / "CatchUpGame" / "ResearchLemmas.lean").read_text()
    for path in [ROOT / "CatchUpGame.lean", *FROZEN.parent.glob("*.lean")]:
        if re.search(r"\b(?:sorry|admit|native_decide|axiom)\b", path.read_text()):
            raise SystemExit(f"Unexpected proof placeholder, shortcut or axiom declaration in {path}")
    subprocess.run(["lake", "build"], cwd=ROOT, check=True)
    names = ["CatchUpGame.Research." + name for name in re.findall(
        r"^(?:noncomputable )?(?:theorem|def|inductive) (\w+)", source, re.MULTILINE)]
    if not names:
        raise SystemExit("No public declarations found")
    commands = ["import CatchUpGame",
                *(f"#print axioms {name}" for name in names)]
    result = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=ROOT,
                            input="\n".join(commands) + "\n", text=True,
                            capture_output=True)
    print(result.stdout, end="")
    if result.returncode != 0:
        raise SystemExit(result.stderr or "Lean axiom inspection failed")
    matches = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
                         result.stdout)
    if [name for name, _ in matches] != names:
        raise SystemExit("Incomplete axiom output")
    for name, axioms in matches:
        extra = {a.strip() for a in axioms.split(",") if a.strip()} - ALLOWED
        if extra:
            raise SystemExit(f"{name} uses unexpected axioms {extra}")
    print(f"Audited {len(names)} public declarations.")
    check_hash()


if __name__ == "__main__":
    main()
