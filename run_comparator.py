"""Generate setup challenges and compare them with the local convergence theorems."""

import argparse
import json
import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parent
WORK = ROOT / ".lake/comparator-check"
COMPARATOR_PACKAGE = ROOT / ".lake/packages/Comparator"


def prepare_tools():
    env = os.environ.copy()
    targets = []
    if "COMPARATOR_BIN" not in env or "COMPARATOR_LANDRUN" not in env:
        targets.append("comparator")
        env.setdefault(
            "COMPARATOR_BIN", str(COMPARATOR_PACKAGE / ".lake/build/bin/comparator")
        )
        env.setdefault(
            "COMPARATOR_LANDRUN", str(COMPARATOR_PACKAGE / "scripts/fake-landrun.sh")
        )
    if "COMPARATOR_LEAN4EXPORT" not in env:
        targets.append("lean4export")
        env["COMPARATOR_LEAN4EXPORT"] = str(
            ROOT / ".lake/packages/lean4export/.lake/build/bin/lean4export"
        )
    if targets:
        subprocess.run(["lake", "build", *targets], cwd=ROOT, check=True)
    return env


def inspect(files, env):
    if not files:
        raise ValueError("No theorem files found")
    modules = [".".join(path.relative_to(ROOT).with_suffix("").parts) for path in files]
    subprocess.run(["lake", "build", *modules], cwd=ROOT, env=env, check=True)
    program = "\n".join(f"import {module}" for module in modules) + "\n"
    program += (ROOT / "tools/ConvergenceMetadata.lean").read_text()
    program += r"""
open Lean Elab Command in
run_cmd do
  let entries ← liftTermElabM ConvergenceMetadata.inspect
  let rows ← entries.mapM fun entry => do
    let info ← Lean.getConstInfo entry.budgetName
    let boundType ← liftTermElabM <| withOptions
      (fun options => options.setBool `pp.fullNames true) (Lean.Meta.ppExpr info.type)
    pure <| Json.mkObj [
      ("module", toJson entry.moduleName.toString),
      ("theorem", toJson entry.theoremName.toString),
      ("setup", toJson entry.setupName.toString),
      ("budget", toJson entry.budgetName.toString),
      ("online", toJson entry.online),
      ("bound_type", toJson boundType.pretty)]
  (← IO.getStdout).putStrLn (Json.arr rows).compress
"""
    result = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=ROOT,
        env=env,
        input=program,
        text=True,
        capture_output=True,
    )
    if result.returncode:
        raise ValueError(f"Theorem inspection failed:\n{result.stdout}{result.stderr}")
    rows = [row for row in json.loads(result.stdout) if row["module"] in modules]
    if sorted(row["module"] for row in rows) != sorted(modules):
        raise ValueError("Expected exactly one convergence theorem per selected module")
    return rows


def generate(rows, work):
    for row in rows:
        name = row["module"].removeprefix("LongTails.Theorems.")
        challenge = f"ComparatorChallenge.{work.name}.{name}"
        source = work / Path(*name.split(".")).with_suffix(".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        setup_module = row["setup"].removesuffix(".spec")
        if row["online"]:
            convergence = "OnlineConvergence"
            bound_type = row["bound_type"]
        else:
            convergence = "Convergence"
            bound_type = f"(let S := {row['setup']}; S.Params → Fin S.numOracles → ℕ)"
        source.write_text(f"""import {setup_module}
noncomputable def {row["budget"]} : {bound_type} := by sorry
theorem {row["theorem"]} : OracleTemplate.{convergence} {row["setup"]} {row["budget"]} := by sorry
""")
        config = source.with_suffix(".json")
        config.write_text(
            json.dumps(
                {
                    "challenge_module": challenge,
                    "solution_module": row["module"],
                    "theorem_names": [row["theorem"]],
                    "definition_names": [row["budget"]],
                    "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
                },
                indent=2,
            )
            + "\n"
        )
        yield config


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "file",
        nargs="?",
        help="Optional file in LongTails/Theorems; otherwise check all",
    )
    parser.add_argument(
        "-j", "--jobs", type=int, default=1, help="Parallel audits (default: 1)"
    )
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    files = sorted((ROOT / "LongTails/Theorems").glob("*.lean"))
    if args.file:
        selected = Path(args.file)
        selected = (
            ROOT / "LongTails/Theorems" / selected
            if selected.parent == Path(".")
            else selected
        ).resolve()
        if selected not in files:
            parser.error("Expected a file in LongTails/Theorems")
        files = [selected]
    env = prepare_tools()
    comparator = env["COMPARATOR_BIN"]
    rows = inspect(files, env)
    work_root = WORK / "ComparatorChallenge"
    work_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="Run", dir=work_root) as directory:
        configs = list(generate(rows, Path(directory)))
        modules = [
            json.loads(config.read_text())["challenge_module"] for config in configs
        ]
        # Build shared dependencies once before concurrent Comparator invocations.
        subprocess.run(["lake", "build", *modules], cwd=ROOT, env=env, check=True)
        failed = []
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            pending = {
                pool.submit(
                    subprocess.run,
                    ["lake", "env", comparator, str(config)],
                    cwd=ROOT,
                    env=env,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True,
                ): config.stem
                for config in configs
            }
            for future in as_completed(pending):
                name = pending[future]
                result = future.result()
                print(f"=== {name} ===", flush=True)
                print(result.stdout, end="", flush=True)
                if result.returncode:
                    failed.append(name)
        if failed:
            raise ValueError("Comparator failed for: " + ", ".join(sorted(failed)))
    summary = (
        f"Checked {len(files)} convergence results and their budgets. "
        "The solutions are okay!"
    )
    print(f"\033[32m{summary}\033[0m" if sys.stdout.isatty() else summary)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
