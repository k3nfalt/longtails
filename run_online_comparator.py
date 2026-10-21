"""Audit online guarantees, their named algorithms, and regret bounds with Comparator."""

import argparse
import json
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

from run_comparator import ROOT, WORK, prepare_tools


def inspect(files, env):
    if not files:
        raise ValueError("No online theorem files found")
    modules = [".".join(path.relative_to(ROOT).with_suffix("").parts) for path in files]
    subprocess.run(["lake", "build", *modules], cwd=ROOT, env=env, check=True)
    program = "\n".join(f"import {module}" for module in modules) + "\n"
    program += (ROOT / "tools/OnlineMetadata.lean").read_text()
    program += r"""
open Lean Elab Command in
run_cmd do
  let entries ← liftTermElabM OnlineMetadata.inspect
  let rows := entries.map fun entry => Json.mkObj [
    ("module", toJson entry.moduleName.toString),
    ("theorem", toJson entry.theoremName.toString),
    ("setup", toJson entry.setupName.toString),
    ("bound", toJson entry.boundName.toString),
    ("method", toJson (entry.methodName.map Name.toString))]
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
        raise ValueError(
            f"Online theorem inspection failed:\n{result.stdout}{result.stderr}"
        )
    rows = [row for row in json.loads(result.stdout) if row["module"] in modules]
    if sorted(row["module"] for row in rows) != sorted(modules):
        raise ValueError("Expected exactly one online theorem per selected module")
    return rows


def generate(rows, work):
    for row in rows:
        name = row["module"].removeprefix("LongTailsOnline.Theorems.")
        challenge = f"ComparatorChallenge.{work.name}.{name}"
        source = work / Path(*name.split(".")).with_suffix(".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        spec = row["setup"]
        program = f"import {spec.removesuffix('.spec')}\n"
        definitions = [row["bound"]]
        if method := row["method"]:
            program += (
                f"noncomputable def {method} : (p : {spec}.Public) → "
                f"OnlineTemplate.Algorithm ({spec}.Observation p) "
                f"({spec}.Action p) ({spec}.Feedback p) := by sorry\n"
            )
            definitions.append(method)
        program += (
            f"noncomputable def {row['bound']} : (p : {spec}.Params) → "
            f"{spec}.Bound p := by sorry\n"
        )
        statement = (
            f"OnlineTemplate.Guarantee {spec} {method} {row['bound']}"
            if method
            else f"OnlineTemplate.Achievable {spec} {row['bound']}"
        )
        program += f"theorem {row['theorem']} : {statement} := by sorry\n"
        source.write_text(program)
        config = source.with_suffix(".json")
        config.write_text(
            json.dumps(
                {
                    "challenge_module": challenge,
                    "solution_module": row["module"],
                    "theorem_names": [row["theorem"]],
                    "definition_names": definitions,
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
        "file", nargs="?", help="File in LongTailsOnline/Theorems; otherwise all"
    )
    parser.add_argument("-j", "--jobs", type=int, default=1, help="Parallel audits")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    directory = ROOT / "LongTailsOnline/Theorems"
    files = sorted(directory.glob("*.lean"))
    if args.file:
        selected = Path(args.file)
        selected = (
            directory / selected if selected.parent == Path(".") else selected
        ).resolve()
        if selected not in files:
            parser.error("Expected a file in LongTailsOnline/Theorems")
        files = [selected]
    env = prepare_tools()
    rows = inspect(files, env)
    work_root = WORK / "ComparatorChallenge"
    work_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="Online", dir=work_root) as directory:
        configs = list(generate(rows, Path(directory)))
        modules = [
            json.loads(config.read_text())["challenge_module"] for config in configs
        ]
        subprocess.run(["lake", "build", *modules], cwd=ROOT, env=env, check=True)
        failed = []
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            pending = {
                pool.submit(
                    subprocess.run,
                    ["lake", "env", env["COMPARATOR_BIN"], str(config)],
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
            raise ValueError(
                "Online Comparator failed for: " + ", ".join(sorted(failed))
            )
    print(
        f"Checked {len(files)} online results, algorithms, and bounds. The solutions are okay!"
    )


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
