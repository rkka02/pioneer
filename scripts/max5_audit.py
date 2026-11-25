"""Print the kernel axioms of every named theorem in FEI, including private ones."""

from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DECL = re.compile(r"^(private )?(?:theorem|lemma)\s+(\w+)", re.M)
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def main():
    files = sorted((ROOT / "FEI").glob("*.lean"))
    imports = ["module"] + ["import all FEI." + file.stem for file in files]
    commands = []
    short_names = set()
    for file in files:
        source = file.read_text()
        assert not re.search(r"\b(?:sorry|admit|axiom)\b", source)
        decls = DECL.findall(source)
        print(
            file.name,
            len(decls),
            "named theorems,",
            sum(bool(v) for v, _ in decls),
            "private",
            flush=True,
        )
        for _, name in decls:
            assert name not in short_names
            short_names.add(name)
            commands.append("#print axioms FEI." + name)
    with tempfile.TemporaryDirectory() as folder:
        check = Path(folder) / "FEICampaignAudit.lean"
        check.write_text("\n".join(imports + commands) + "\n")
        run = subprocess.run(
            ["lake", "env", "lean", str(check)], cwd=ROOT, text=True, capture_output=True
        )
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
    checked = set()
    union = set()
    for block in re.split(r"(?=^')", run.stdout.strip(), flags=re.M):
        if not block:
            continue
        line = " ".join(block.split())
        match = re.fullmatch(
            r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", line
        )
        assert match, line
        name = match[1].split(".")[-1]
        assert name in short_names and name not in checked
        checked.add(name)
        axioms = set(filter(None, (match[2] or "").split(", ")))
        assert axioms <= STANDARD, axioms
        union.update(axioms)
        print(line)
    assert checked == short_names
    print("Verified", len(checked), "named theorems. Union:", ", ".join(sorted(union)))


if __name__ == "__main__":
    main()
