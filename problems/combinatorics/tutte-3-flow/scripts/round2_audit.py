"""Audit all named project theorems, including private helpers in their source context."""

from pathlib import Path
import re
import subprocess
from itertools import combinations

from round1_repair import CAP_A, CAP_B, LEFT, MIDDLE, RIGHT


def check(label, source, count):
    result = subprocess.run(
        ["lake", "env", "lean", "--stdin"], input=source, text=True, capture_output=True, check=True
    )
    output = result.stdout
    lists = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", output)
    independent = output.count("does not depend on any axioms")
    assert len(lists) + independent == count, (label, output)
    used = {axiom.strip() for names in lists for axiom in names.split(",")}
    assert used <= {"propext", "Classical.choice", "Quot.sound"}, (label, used)
    print(label, count, sorted(used), flush=True)


def main():
    public = []
    local = []
    for path in sorted(Path("Tutte3Flow").glob("*.lean")):
        source = path.read_text()
        namespace = re.search(r"^namespace (\S+)", source, re.MULTILINE)
        private = []
        theorems = re.findall(r"^(private |public |)theorem (\w+)", source, re.MULTILINE)
        for visibility, name in theorems:
            command = "#print axioms " + namespace[1] + "." + name
            (private if visibility == "private " else public).append(command)
        if private:
            local.append((path.stem, source + "\n" + "\n".join(private) + "\n", len(private)))
    check("public imports", "import Tutte3Flow\n" + "\n".join(public) + "\n", len(public))
    for label, source, count in local:
        check(label + " private", source, count)
    # Check that the kernel's finite table uses exactly the graph generator's data.
    equalities = ["import Tutte3Flow", "open Tutte3Flow.SevenCut"]
    for name, values in [("middleArcs", MIDDLE), ("leftPorts", LEFT), ("rightPorts", RIGHT)]:
        equalities.append(f"example : {name} = {values} := by decide")
    for name, edges in [("leftDirect", CAP_A), ("rightDirect", CAP_B)]:
        ports = [v for u, v in edges if u == 6 and v < 6]
        masks = sorted(
            sum(1 << v for v in subset) for size in (1, 2) for subset in combinations(ports, size)
        )
        equalities.append(
            f"example : ∀ m : Mask, {name} m = ({masks} : List Nat).contains m.val := by decide"
        )
    subprocess.run(
        ["lake", "env", "lean", "--stdin"], input="\n".join(equalities) + "\n", text=True, check=True
    )
    print("Lean port maps, middle arcs and direct cap states agree with the Python generator")
    print("total", len(public) + sum(count for _, _, count in local))


if __name__ == "__main__":
    main()
