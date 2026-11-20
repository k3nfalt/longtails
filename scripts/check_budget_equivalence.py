"""Check edited public theorem budgets against a Git revision in the current Lean setup.

Run from a built checkout: python3 scripts/check_budget_equivalence.py <base-commit>
New results have no baseline and are audited by the normal Comparator job.
"""

import argparse
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
THEOREMS = ":(glob)LongTails/Theorems/*.lean"


def comparison(source, path):
    namespace = re.search(r"^namespace ([\w.]+)\s*$", source, re.MULTILINE)
    result = re.search(
        r"^theorem result\s*:\s*(.*?)\s*:=\s", source, re.MULTILINE | re.DOTALL
    )
    if not namespace or not result or namespace.end() >= result.start():
        raise ValueError(
            f"{path}: cannot locate the baseline namespace and public claim"
        )
    body = source[namespace.end() : result.start()]
    budgets = re.findall(
        r"^(?:noncomputable )?def (budget|bound)\b", body, re.MULTILINE
    )
    if len(budgets) != 1:
        raise ValueError(f"{path}: expected one public budget or online bound")
    name = namespace[1]
    budget = budgets[0]
    # Keep any scoped options/attributes immediately before the historical result.
    return f"""
{source[: namespace.start()]}
namespace {name}.BudgetBaseline
{body}
example : ({result[1]}) = (type_of% _root_.{name}.result) := rfl
example : {budget} = _root_.{name}.{budget} := rfl
end {name}.BudgetBaseline
"""


def check_baseline_imports(base, paths):
    """Old formulas must not silently resolve helpers to modified implementations."""
    changed = set(
        subprocess.check_output(
            [
                "git",
                "diff",
                "--name-only",
                "--diff-filter=MDT",
                "--no-renames",
                base,
                "HEAD",
                "--",
                "LongTails",
                "lean-toolchain",
                "lake-manifest.json",
                "lakefile.toml",
            ],
            cwd=ROOT,
            text=True,
        ).splitlines()
    )
    if changed & {"lean-toolchain", "lake-manifest.json", "lakefile.toml"}:
        raise ValueError(
            "Cannot replay baseline formulas across a Lean toolchain or dependency configuration change."
        )
    # Read the base revision's project import graph in one Git operation.
    records = subprocess.run(
        [
            "git",
            "grep",
            "-E",
            r"^(public +|private +)?import +",
            base,
            "--",
            "LongTails/*.lean",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    if records.returncode not in (0, 1):
        records.check_returncode()
    imports = {}
    for line in records.stdout.splitlines():
        _, name, statement = line.split(":", 2)
        for module in statement.partition("import ")[2].split("--")[0].split():
            if module.startswith("LongTails."):
                imports.setdefault(name, set()).add(module.replace(".", "/") + ".lean")
    for path in paths:
        pending = list(imports.get(path.as_posix(), ()))
        seen = set()
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            if name in changed:
                raise ValueError(
                    f"{path}: baseline import {name} also changed; equivalence under the old definitions is unverified."
                )
            seen.add(name)
            pending.extend(imports.get(name, ()))


def check(base):
    base = subprocess.check_output(
        ["git", "rev-parse", "--verify", f"{base}^{{commit}}"], cwd=ROOT, text=True
    ).strip()
    diff = (
        subprocess.check_output(
            [
                "git",
                "diff",
                "--name-status",
                "-z",
                "--no-renames",
                base,
                "HEAD",
                "--",
                THEOREMS,
            ],
            cwd=ROOT,
        )
        .decode()
        .split("\0")[:-1]
    )
    paths = []
    for status, name in zip(diff[::2], diff[1::2]):
        if status == "A":
            continue
        if status != "M":
            raise ValueError(
                f"{name}: existing public theorem removed or replaced ({status})"
            )
        paths.append(Path(name))
    if not paths:
        print("No existing public theorem files changed.")
        return
    check_baseline_imports(base, paths)
    modules = [".".join(path.with_suffix("").parts) for path in paths]
    subprocess.run(["lake", "build", *modules], cwd=ROOT, check=True)
    imports = dict.fromkeys(f"import {module}" for module in modules)
    checks = []
    for path in paths:
        original = subprocess.check_output(
            ["git", "show", f"{base}:{path.as_posix()}"], cwd=ROOT, text=True
        )
        print(f"Checking {path.stem}", flush=True)
        lines = []
        for line in comparison(original, path).splitlines():
            if line.startswith("import "):
                imports[line] = None
            else:
                lines.append(line)
        checks.extend(["section", *lines, "end"])
    subprocess.run(
        ["lake", "env", "lean", "-DwarningAsError=true", "--stdin"],
        cwd=ROOT,
        input="\n".join([*imports, *checks]),
        text=True,
        check=True,
    )
    print(f"Lean proved equality for all {len(paths)} edited budgets.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "base", help="Base revision to compare with the checked-out HEAD"
    )
    try:
        check(parser.parse_args().base)
    except (ValueError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Budget equivalence check failed: {error}\n")
