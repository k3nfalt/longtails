"""Create missing theorem budget descriptions and save website metadata."""

import argparse
import json
import subprocess
from pathlib import Path

from server.generation_commits import current_commit, verified_output, write_description

ROOT = Path(__file__).resolve().parents[2]

EXTRACTOR = (
    (ROOT / "tools/ConvergenceMetadata.lean").read_text()
    + r"""
set_option format.width 120
open Lean Meta Elab Command

private partial def statementBudgets (type : Expr) : MetaM (Array Json) := do
  match type with
  | .forallE name domain body binderInfo =>
    withLocalDecl name binderInfo domain fun x => statementBudgets (body.instantiate1 x)
  | .letE name type value body _ =>
    let current ← if name == `budget then
      pure #[Json.mkObj [
        ("type", toJson (← ppExpr type).pretty),
        ("value", toJson (← ppExpr value).pretty),
        ("latex", toJson (← TheoremDescriptions.budgetLatex value))]]
      else pure #[]
    withLetDecl name type value fun x => do
      return current ++ (← statementBudgets (body.instantiate1 x))
  | _ =>
    if type.isAppOfArity `OracleTemplate.OnlineConvergence 2 then
      let .const name levels := type.getAppArgs.back!
        | throwError "Expected a bound definition"
      let .defnInfo info ← getConstInfo name | throwError "Expected a bound definition"
      let value := info.value.instantiateLevelParams info.levelParams levels
      return #[Json.mkObj [
        ("type", toJson (← ppExpr (← inferType value)).pretty),
        ("value", toJson (← ppExpr value).pretty),
        ("latex", toJson (← TheoremDescriptions.budgetLatex value))]]
    if type.isAppOfArity ``OracleTemplate.Convergence 2 then
      let budget := type.getAppArgs.back!
      let value ← if let .const name levels := budget then do
        let .defnInfo info ← getConstInfo name | throwError "Expected a budget definition"
        pure (info.value.instantiateLevelParams info.levelParams levels)
        else pure budget
      return ← lambdaBoundedTelescope value 1 fun params body => do
        let .forallE _ domain _ _ ← whnf (← inferType body)
          | throwError "Expected a per-oracle budget"
        let domain ← whnf domain
        unless domain.isAppOfArity ``Fin 1 do
          throwError "Expected a Fin-indexed budget"
        let some count ← getNatValue? (← whnf domain.appArg!)
          | throwError "Expected a concrete oracle count"
        let mut rows := #[]
        for i in [:count] do
          let index := mkApp3 (mkConst ``Fin.mk) (mkNatLit count) (mkNatLit i)
            (← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, mkNatLit count]))
          let (component, _) ← simp (mkApp body index) (← Simp.mkContext {} #[← getSimpTheorems]) #[← Simp.getSimprocs]
          let component ← mkLambdaFVars params component.expr
          rows := rows.push <| Json.mkObj [
            ("oracle", toJson i),
            ("type", toJson (← ppExpr (← inferType component)).pretty),
            ("value", toJson (← ppExpr component).pretty),
            ("latex", toJson (← TheoremDescriptions.budgetLatex component))]
        return rows
    return #[]

run_cmd do
  let rows ← liftTermElabM do
    let entries ← ConvergenceMetadata.inspect
    let mut rows : Array Json := #[]
    for entry in entries do
      let info ← getConstInfo entry.theoremName
      let found ← statementBudgets info.type
      if found.isEmpty then
        throwError "{entry.moduleName}: could not extract the budget"
      rows := rows.push <| Json.mkObj [
        ("setup", toJson entry.setupName.getPrefix.toString),
        ("namespace", toJson entry.setupName.getPrefix.toString),
        ("module", toJson entry.moduleName.toString),
        ("theorem", toJson entry.theoremName.toString),
        ("statement", toJson (← ppExpr info.type).pretty),
        ("budget", if found.size == 1 then found[0]! else Json.null),
        ("budgets", toJson found)]
    return rows
  (← IO.getStdout).putStrLn (Json.arr rows).compress
"""
)


def generate_descriptions(rows, commit, regenerate_all=False):
    results = {}
    for row in rows:
        if row["module"].startswith("LongTails.Theorems.") and row["budgets"]:
            filename = (
                row["module"].removeprefix("LongTails.Theorems.").replace(".", "/")
                + ".tex"
            )
            if regenerate_all or not verified_output(
                ROOT / "server/Theorems/Descriptions" / filename,
            ):
                results.setdefault(filename, []).append(row)
    if not results:
        return
    for name, theorems in sorted(results.items()):
        formulas = []
        for row in theorems:
            for budget in row["budgets"]:
                label = (
                    r"\text{Oracle " + str(budget["oracle"]) + r":}\quad "
                    if len(row["budgets"]) > 1
                    else ""
                )
                formulas.append(r"\[" + label + budget["latex"] + r"\]")
        formula = "\n".join(formulas)
        path = ROOT / "server/Theorems/Descriptions" / name
        write_description(path, formula + "\n", commit, regenerate_all)


def extract_theorems(paths):
    modules = {".".join(path.relative_to(ROOT).with_suffix("").parts) for path in paths}
    program = "\n".join(f"import {module}" for module in sorted(modules))
    program += "\nimport BudgetLatex\n" + EXTRACTOR
    result = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=ROOT,
        input=program,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode:
        raise RuntimeError(f"Budget extraction failed:\n{result.stdout}{result.stderr}")
    return [row for row in json.loads(result.stdout) if row["module"] in modules]


def load_theorems(regenerate_all=False):
    cached = {}
    cache = ROOT / "server/theorems.json"
    if cache.exists():
        for row in json.loads(cache.read_text(encoding="utf-8")):
            cached.setdefault(row["module"], []).append(row)
    rows = []
    pending = []
    for path in sorted((ROOT / "LongTails/Theorems").rglob("*.lean")):
        if "_" in path.stem:
            continue
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        description = (
            ROOT
            / "server/Theorems/Descriptions"
            / path.relative_to(ROOT / "LongTails/Theorems").with_suffix(".tex")
        )
        if not regenerate_all and verified_output(description) and module in cached:
            rows.extend(cached[module])
        else:
            print(f"Queued extraction: {module}", flush=True)
            pending.append(path)
    if pending:
        modules = [
            ".".join(path.relative_to(ROOT).with_suffix("").parts) for path in pending
        ]
        subprocess.run(
            ["lake", "build", *modules, "BudgetLatex"],
            cwd=ROOT,
            capture_output=True,
            check=True,
        )
        print(
            f"Extracting {len(pending)} theorem files in one Lean process", flush=True
        )
        rows.extend(extract_theorems(pending))
        print("Budget extraction complete", flush=True)
    rows = [row for row in rows if row["budgets"]]
    rows.sort(key=lambda row: (row["setup"], row["theorem"]))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--regenerate-all",
        action="store_true",
        help="Regenerate all theorem descriptions and metadata, including existing files.",
    )

    args = parser.parse_args()
    commit = current_commit()
    rows = load_theorems(args.regenerate_all)
    generate_descriptions(rows, commit, args.regenerate_all)
    cache = ROOT / "server/theorems.json"
    cache.parent.mkdir(parents=True, exist_ok=True)
    cache.write_text(
        json.dumps(rows, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
