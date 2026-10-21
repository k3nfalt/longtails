"""Compiler-owned observations and a source-exact proof editing boundary.

This runs trusted Lean/build tools. It is not a sandbox for hostile metaprograms.
"""

import ast
import json
import os
import re
import sys
from pathlib import Path

from .common import checked, command, digest, fields, require, scoped, write_json
from .contracts import lean_name
from .layout import adapt_style_linter, in_category, setup_module
from .project import compact_manifest, initialize_compact, sync_index

FOUNDATIONS = {"propext", "Classical.choice", "Quot.sound"}


def module_name(path):
    return path.removesuffix(".lean").replace("/", ".")


def repository_files(project):
    """Git pins plus every working source; build outputs and our probe are excluded."""
    project = Path(project)
    if compact_manifest(project):
        result = {}
        for path in project.rglob("*"):
            relative = path.relative_to(project)
            if ".lake" in relative.parts or ".git" in relative.parts:
                continue
            require(not path.is_symlink(), "Symlinked project source is not supported")
            if path.is_file():
                result[relative.as_posix()] = digest(path.read_bytes())
        return result
    names = checked(["git", "ls-files", "-z"], project).split("\0")
    result = {}
    for name in names:
        if name:
            path = scoped(project, name)
            require(path.is_file(), "Tracked file disappeared: " + name)
            result[name] = digest(path.read_bytes())
    # New source is as consequential as edited tracked source.
    for path in project.rglob("*.lean"):
        relative = path.relative_to(project)
        if ".lake" not in relative.parts and ".git" not in relative.parts:
            require(not path.is_symlink(), "Symlinked project source is not supported")
            result[relative.as_posix()] = digest(path.read_bytes())
    return result


class Compiler:
    def __init__(self, project, artifacts, lean_bin=None, timeout=1800):
        self.project, self.artifacts = Path(project), Path(artifacts)
        self.artifacts.mkdir(parents=True, exist_ok=True)
        self.env = os.environ.copy()
        if lean_bin:
            self.env["PATH"] = (
                str(Path(lean_bin).resolve()) + os.pathsep + self.env["PATH"]
            )
        self.timeout = timeout

    def run(self, args, *, index_update=False):
        print("autoformalize: " + " ".join(args), file=sys.stderr, flush=True)
        result = command(args, self.project, timeout=self.timeout, env=self.env)
        write_json(self.artifacts / (digest(result) + ".json"), result)
        require(
            result["exit_code"] == 0,
            "Lean/build command failed (full log saved):\n"
            + (result["stdout"] + result["stderr"])[-16000:],
        )
        return result["stdout"]

    def environment(self):
        version = self.run(["lean", "--version"]).strip()
        pin = (self.project / "lean-toolchain").read_text().strip()
        expected = pin.rsplit(":", 1)[-1].removeprefix("v")
        require(
            re.search(
                r"Lean \(version " + re.escape(expected) + r"(?:,|\s|\))", version
            ),
            f"Runtime does not match pinned toolchain {pin}: {version}",
        )
        packages = self.project / ".lake/packages"
        deps = {}
        if packages.exists():
            for package in sorted(packages.iterdir()):
                if package.is_dir():
                    require(
                        (package / ".git").exists(),
                        "Dependency must have verifiable Git provenance: "
                        + package.name,
                    )
                    head = checked(["git", "rev-parse", "HEAD"], package)
                    require(
                        not checked(
                            ["git", "status", "--porcelain", "--untracked-files=no"],
                            package,
                        ),
                        "Dependency has working changes: " + package.name,
                    )
                    # Include untracked sources; don't trust a clean tracked tree alone.
                    extras = checked(
                        ["git", "ls-files", "--others", "--exclude-standard", "-z"],
                        package,
                    )
                    require(
                        not any(
                            p.endswith((".lean", ".toml", ".json"))
                            for p in extras.split("\0")
                            if p
                        ),
                        "Untracked dependency source: " + package.name,
                    )
                    deps[package.name] = head
        manifest = json.loads((self.project / "lake-manifest.json").read_text())
        for package in manifest.get("packages", []):
            if package.get("type") == "git":
                require(
                    deps.get(package["name"]) == package["rev"],
                    "Dependency missing or not at its manifest revision: "
                    + package["name"],
                )
        return {
            "lean": version,
            "toolchain": pin,
            "manifest": digest((self.project / "lake-manifest.json").read_bytes()),
            "packages": deps,
        }

    def sync_index(self):
        sync_index(self.project)

    def build(self, *, final=False, public_paths=None, targets=None):
        self.sync_index()
        selected = sorted(set(targets or ["outputs", "BudgetLatex"]))
        require(
            selected
            and all(
                m in {"outputs", "BudgetLatex"}
                or re.fullmatch(
                    r"(?:outputs|LongTails|Mathlib|Init|Lean|Std)\.[A-Za-z0-9_.]+", m
                )
                for m in selected
            ),
            "Build explicit modules or the outputs aggregate only",
        )
        core = [m for m in selected if m.split(".")[0] in {"Init", "Lean", "Std"}]
        packages = [m for m in selected if m not in core]
        if packages:
            self.run(["lake", "build", *packages])
        if core:
            self.probe(core, "")
        if final:
            sync_index(self.project, check=True)
            self.run(["lake", "--wfail", "build", "outputs", "BudgetLatex"])
            source = adapt_style_linter(
                (
                    self.project / ".lake/packages/mathlib/scripts/lint-style.lean"
                ).read_text(encoding="utf-8")
            )
            native = self.project / ".lake/style-check/RunOutputStyle.lean"
            native.parent.mkdir(parents=True, exist_ok=True)
            native.write_text(source, encoding="utf-8", newline="\n")
            self.run(["lake", "exe", "runOutputStyle"])
            self.run(["lake", "exe", "runLinterNoDocString"])
            if public_paths is None:
                self.run([sys.executable, "run_comparator.py"])
            else:
                for path in sorted(set(public_paths)):
                    self.run([sys.executable, "run_comparator.py", path])

    def probe(self, modules, tail):
        require(
            all(re.fullmatch(r"[A-Za-z0-9_.]+", m) for m in modules),
            "Invalid Lean import",
        )
        helper = Path(__file__).with_name("Inspect.lean").read_text(encoding="utf-8")
        content = "import Lean\n" + "".join(
            "import " + m + "\n" for m in sorted(set(modules))
        )
        content += helper.removeprefix("import Lean\n") + "\n" + tail + "\n"
        path = self.artifacts / (digest(content) + ".lean")
        path.write_text(content, encoding="utf-8", newline="\n")
        return self.run(["lake", "env", "lean", "-j2", str(path.resolve())])

    def inspect(self, units, providers=()):
        names = sorted({n for u in units for n in u["declarations"]} | set(providers))
        for name in names:
            lean_name(name)
        modules = sorted({module_name(u["file"]) for u in units})
        owned = sorted({module_name(u["file"]) for u in units if u["mode"] == "new"})

        def arr(ns):
            return "#[" + ", ".join("`" + n for n in ns) + "]"

        output = self.probe(
            modules, "run_cmd afInspect " + arr(names) + " " + arr(owned)
        )
        records = [
            line.split("AF_INVENTORY ", 1)[1]
            for line in output.splitlines()
            if "AF_INVENTORY " in line
        ]
        require(
            len(records) == 1 and len(records[0]) < 64_000_000,
            "Incomplete or excessive compiler inventory",
        )
        record = json.loads(records[0])
        require(
            set(names) <= {d["name"] for d in record["declarations"]},
            "Compiler omitted named declarations",
        )
        return record

    def parse_proof(self, units, proof):
        # A JSON string is also a Lean string literal for ordinary Unicode text.
        # Escape $ separately: Lean ordinary strings have no interpolation.
        literal = json.dumps(proof, ensure_ascii=False)
        output = self.probe(
            [module_name(u["file"]) for u in units], "run_cmd afParseProof " + literal
        )
        require(
            "AF_PROOF_PARSED" in output,
            "Proof parser did not acknowledge a complete term",
        )

    def catalog(self, units):
        """Run the pinned repository's extractor without writing website metadata."""
        public = [u for u in units if in_category(u["file"], "Theorems")]
        if not public:
            return {"status": "not_applicable", "rows": []}
        relative = "server/Theorems/create_theorem_description.py"
        extractor = self.project / relative
        renderer = self.project / "server/Theorems/BudgetLatex.lean"
        require(
            extractor.is_file() and renderer.is_file(),
            "Repository catalog extractor or BudgetLatex renderer missing",
        )
        # Read the exact static Lean program; do not invoke the publishing entrypoint
        # or maintain a second implementation of the repository's extraction rules.
        tree = ast.parse(extractor.read_text(encoding="utf-8"))
        values = [
            node.value
            for node in tree.body
            if isinstance(node, ast.Assign)
            and any(
                isinstance(t, ast.Name) and t.id == "EXTRACTOR" for t in node.targets
            )
        ]
        metadata = self.project / "tools/ConvergenceMetadata.lean"
        require(
            len(values) == 1
            and isinstance(values[0], ast.BinOp)
            and isinstance(values[0].op, ast.Add),
            "Unsupported repository EXTRACTOR expression",
        )
        expected = ast.parse(
            '(ROOT / "tools/ConvergenceMetadata.lean").read_text()', mode="eval"
        ).body
        require(
            ast.dump(values[0].left) == ast.dump(expected)
            and isinstance(values[0].right, ast.Constant)
            and isinstance(values[0].right.value, str)
            and metadata.is_file(),
            "Repository EXTRACTOR must compose the native metadata helper and static Lean program",
        )
        program = (
            metadata.read_text(encoding="utf-8").removeprefix("import Lean\n")
            + values[0].right.value
        )
        modules = sorted({module_name(u["file"]) for u in public})
        require(
            all(re.fullmatch(r"[A-Za-z0-9_.]+", m) for m in modules),
            "Invalid catalog import",
        )
        self.run(["lake", "build", "BudgetLatex", *modules])
        rows = []
        for unit in public:
            content = (
                "import Lean\nimport "
                + module_name(unit["file"])
                + "\nimport BudgetLatex\nset_option format.width 120\n"
                + program
            )
            path = self.artifacts / (digest(content) + ".lean")
            path.write_text(content, encoding="utf-8", newline="\n")
            output = self.run(["lake", "env", "lean", "-j2", str(path.resolve())])
            records = []
            for line in output.splitlines():
                try:
                    value = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if isinstance(value, list):
                    records.append(value)
            require(
                len(records) == 1,
                "Catalog extractor did not emit exactly one JSON array",
            )
            rows.append(catalog_row(unit, records[0]))
        return {
            "status": "passed",
            "rows": rows,
            "sources": {
                relative: digest(extractor.read_bytes()),
                "server/Theorems/BudgetLatex.lean": digest(renderer.read_bytes()),
                "tools/ConvergenceMetadata.lean": digest(metadata.read_bytes()),
            },
        }

    def topology(self, plan):
        """Use upstream compiler metadata and challenge generation for planned exports."""
        relative = "run_comparator.py"
        script = self.project / relative
        metadata = self.project / "tools/ConvergenceMetadata.lean"
        require(
            script.is_file() and metadata.is_file(),
            "Comparator discovery sources missing",
        )
        units = {u["id"]: u for u in plan["units"]}
        exports = [
            e
            for e in plan["output_contract"]["public_results"]
            if (self.project / units[e["unit"]]["file"]).is_file()
        ]
        setup_units = [
            u
            for u in units.values()
            if in_category(u["file"], "Setups") and (self.project / u["file"]).is_file()
        ]
        if setup_units:
            self.run(
                [
                    "lake",
                    "build",
                    *sorted({module_name(u["file"]) for u in setup_units}),
                ]
            )
            observed = self.inspect(setup_units)
            declarations = {d["name"]: d for d in observed["declarations"]}
            for u in setup_units:
                module = module_name(u["file"])
                spec = declarations.get(module + ".spec")
                require(
                    spec is not None
                    and spec["module"] == module
                    and module + ".spec" in u["declarations"],
                    "Setup must export its module-qualified spec",
                )
        configurations, rows = [], []
        if exports:
            helper = self.artifacts / "comparator-topology.py"
            helper.write_text(
                """import contextlib, json, os, runpy, sys
from pathlib import Path
program = runpy.run_path(sys.argv[1])
work = Path(sys.argv[2])
work.mkdir(parents=True, exist_ok=True)
with contextlib.redirect_stdout(sys.stderr):
    rows = program['inspect']([Path(p) for p in sys.argv[3:]], os.environ.copy())
    configs = [json.loads(p.read_text()) for p in program['generate'](rows, work)]
print('AF_TOPOLOGY ' + json.dumps({'rows': rows, 'configs': configs}))
""",
                encoding="utf-8",
                newline="\n",
            )
            output = self.run(
                [
                    sys.executable,
                    "-X",
                    "utf8",
                    str(helper.resolve()),
                    str(script.resolve()),
                    str((self.artifacts / "Topology").resolve()),
                    *[
                        str((self.project / units[e["unit"]]["file"]).resolve())
                        for e in exports
                    ],
                ]
            )
            records = [
                line.removeprefix("AF_TOPOLOGY ")
                for line in output.splitlines()
                if line.startswith("AF_TOPOLOGY ")
            ]
            require(
                len(records) == 1, "Comparator metadata did not emit exactly one result"
            )
            result = json.loads(records[0])
            configurations, rows = result["configs"], result["rows"]
        actual = {c["solution_module"]: c for c in configurations}
        by_module = {r["module"]: r for r in rows}
        require(
            len(actual) == len(configurations) == len(exports)
            and len(by_module) == len(rows) == len(exports),
            "Comparator output inventory mismatch",
        )
        for e in exports:
            module = module_name(units[e["unit"]]["file"])
            row, config = by_module.get(module), actual.get(module)
            require(
                row is not None
                and row["theorem"] == e["result"]
                and row["setup"] == e["spec"]
                and row["budget"] == e["budget"],
                "Comparator discovers different result/setup/budget identities",
            )
            require(
                config is not None
                and config.get("theorem_names") == [e["result"]]
                and config.get("definition_names") == [e["budget"]],
                "Comparator challenge differs from the planned result/budget",
            )
        return {
            "status": "passed",
            "public_modules": sorted(actual),
            "rows": rows,
            "source": {
                relative: digest(script.read_bytes()),
                "tools/ConvergenceMetadata.lean": digest(metadata.read_bytes()),
            },
        }


def position(code, line, column):
    lines = code.splitlines(keepends=True)
    require(
        type(line) is int
        and type(column) is int
        and 1 <= line <= len(lines)
        and 0 <= column <= len(lines[line - 1]),
        "Lean declaration range is outside source",
    )
    return sum(len(s) for s in lines[: line - 1]) + column


def check_holes(code, holes, declarations, expected_names):
    require(isinstance(holes, list), "Proof holes must be a list")
    by_name = {d["name"]: d for d in declarations}
    require(
        set(expected_names) <= by_name.keys(),
        "New exports must belong to the candidate module",
    )
    seen, intervals = set(), []
    for hole in holes:
        fields(hole, ["declaration", "start", "end"])
        name = hole["declaration"]
        require(
            name in expected_names and name not in seen,
            "Unknown or duplicate proof hole",
        )
        seen.add(name)
        require(
            type(hole["start"]) is int
            and type(hole["end"]) is int
            and 0 <= hole["start"] < hole["end"] <= len(code),
            "Invalid proof offsets",
        )
        require(
            code[hole["start"] : hole["end"]] == "by sorry",
            "Initial proof body must be exactly by sorry",
        )
        decl = by_name[name]
        require(
            decl["kind"] == "theorem" and decl["range"],
            "Hole needs a compiler-located theorem",
        )
        r = decl["range"]
        start, end = (
            position(code, r["start_line"], r["start_column"]),
            position(code, r["end_line"], r["end_column"]),
        )
        require(
            start <= hole["start"] < hole["end"] <= end,
            "Hole lies outside named declaration",
        )
        require(
            not code[hole["end"] : end].strip()
            and code[start : hole["start"]].rstrip().endswith(":="),
            "Hole is not the complete right-hand side of this theorem",
        )
        intervals.append((hole["start"], hole["end"]))
    require(
        all(a[1] <= b[0] for a, b in zip(sorted(intervals), sorted(intervals)[1:])),
        "Overlapping proof holes",
    )
    require(
        {
            d["name"]
            for d in declarations
            if d["name"] in expected_names and d["kind"] == "theorem"
        }
        == seen,
        "Every newly exported theorem starts with a registered sorry body",
    )
    for decl in declarations:
        if decl["kind"] != "theorem" or not decl.get("range"):
            continue
        r = decl["range"]
        # Exclude compiler-generated equation theorems attached to a definition.
        # Only module-owned source ranges are relevant to this candidate text.
        if not 1 <= r["start_line"] <= len(code.splitlines()):
            continue
        start = position(code, r["start_line"], r["start_column"])
        if re.match(r"(?:theorem|lemma)\s", code[start:]):
            require(
                decl["name"] in expected_names,
                "Unplanned top-level theorem: " + decl["name"],
            )


def audit(inventory, holes=(), *, final=False):
    registered = {h["declaration"] for h in holes}
    for d in inventory["declarations"]:
        axioms = set(d["axioms"])
        require(
            d["kind"] != "axiom",
            "New/reused axioms are not mathematical proofs: " + d["name"],
        )
        permitted = FOUNDATIONS | (
            {"sorryAx"} if not final and d["kind"] == "theorem" else set()
        )
        require(
            axioms <= permitted,
            "Forbidden transitive axioms in "
            + d["name"]
            + ": "
            + str(sorted(axioms - permitted)),
        )
        if not final and "sorryAx" in d.get("proof_used", []):
            require(d["name"] in registered, "Unregistered admission: " + d["name"])


def frozen_signature(inventory):
    return {
        d["name"]: {
            key: d[key] for key in ("module", "kind", "type_repr", "value_repr")
        }
        for d in inventory["declarations"]
    }


def check_signature(before, after, *, exact=False):
    require(before.keys() <= after.keys(), "Frozen declaration disappeared")
    if exact:
        require(
            before.keys() == after.keys(),
            "Proof introduced a new module-owned declaration; use a proof without global auxiliaries",
        )
    for name in before:
        require(
            before[name] == after[name], "Frozen type or definition changed: " + name
        )


def check_proof_signature(before, inventory, holes):
    """Preserve the frozen API while admitting Lean's internal proof lemmas.

    Standard simp preprocessing and omega create kernel-checked theorems below
    the enclosing proof's name. They have no source declaration range. Source
    edits remain restricted to the registered bodies, and audit() still checks
    every helper and the transitive axioms of every completed proof.
    """
    after = frozen_signature(inventory)
    check_signature(before, after)
    roots = {h["declaration"] for h in holes}
    records = {d["name"]: d for d in inventory["declarations"]}
    for name in after.keys() - before.keys():
        declaration = records[name]
        owners = [root for root in roots if name.startswith(root + ".")]
        require(len(owners) == 1, "Unplanned proof declaration: " + name)
        owner = owners[0]
        suffix = name[len(owner) + 1 :]
        require(
            re.fullmatch(r"_(?:proof|simp)_\d+(?:_\d+)*", suffix) is not None
            and declaration["kind"] == "theorem"
            and declaration.get("range") is None
            and declaration.get("selection") is None
            and declaration["module"] == before[owner]["module"],
            "New declaration is not an internal proof lemma: " + name,
        )


def render_proofs(original, holes, proofs):
    code = original
    for hole in sorted(holes, key=lambda h: h["start"], reverse=True):
        replacement = proofs.get(hole["declaration"], "by sorry")
        code = code[: hole["start"]] + replacement + code[hole["end"] :]
    return code


def public_layout(unit, code, inventory):
    if not in_category(unit["file"], "Theorems"):
        return
    require(
        len(
            re.findall(
                r"(?m)^(?:noncomputable )?def budget\s*:\s*[^\n]+:=\s*[^\n]+$", code
            )
        )
        == 1,
        "Public convergence module needs exactly one explicit single-line budget definition",
    )
    names = [n for n in unit["declarations"] if n.endswith(".result")]
    require(len(names) == 1, "Public convergence module must export namespace.result")
    name = names[0]
    namespace = name.rsplit(".", 1)[0]
    require(
        re.search(
            r"theorem\s+result\s*:\s*(?:OracleTemplate\.)?Convergence\s+(?:outputs|LongTails)\.Setups\.[A-Za-z0-9_.]+\.spec\s+budget\s*:=",
            code,
        ),
        "Public theorem must explicitly name its setup module spec",
    )
    owned = {
        d["name"] for d in inventory["declarations"] + inventory.get("providers", [])
    }
    require(namespace + ".budget" in owned, "Budget must belong to result's namespace")

    def strip(e):
        while isinstance(e, dict) and e.get("kind") == "metadata":
            e = e["body"]
        return e

    result = next(d for d in inventory["declarations"] if d["name"] == name)
    require(
        result["module"] == module_name(unit["file"]),
        "Public result must belong to its selected module",
    )
    for decl in inventory["declarations"]:
        if (
            decl["module"] != module_name(unit["file"])
            or decl.get("kind") != "theorem"
            or not decl.get("range")
        ):
            continue
        r = decl["range"]
        start = position(code, r["start_line"], r["start_column"])
        if re.match(r"(?:theorem|lemma)\s", code[start:]):
            require(
                decl["name"] == name,
                "Public module must contain only result; put supporting theorems in Proofs",
            )
    declarations = inventory["declarations"] + inventory.get("providers", [])
    expression = strip(result["type_tree"])
    args = []
    while expression.get("kind") == "app":
        args.insert(0, strip(expression["argument"]))
        expression = strip(expression["function"])
    require(
        expression.get("kind") == "const"
        and expression.get("name") == "OracleTemplate.Convergence"
        and len(args) == 2
        and all(a.get("kind") == "const" for a in args),
        "Public result must use the original Convergence without additional binders",
    )
    spec_name, budget_name = [a["name"] for a in args]
    spec = next((d for d in declarations if d["name"] == spec_name), None)
    budget = next((d for d in declarations if d["name"] == budget_name), None)
    require(
        spec is not None
        and setup_module(spec["module"])
        and spec_name == spec["module"] + ".spec",
        "Public spec must be module-qualified",
    )
    require(
        re.search(r"(?m)^import\s+" + re.escape(spec["module"]) + r"\s*$", code),
        "Public theorem must directly import its setup module",
    )
    require(
        budget is not None
        and budget_name == namespace + ".budget"
        and budget["module"] == module_name(unit["file"]),
        "Public budget must be defined in the theorem module namespace",
    )


def catalog_row(unit, rows):
    """Reject undiscovered, ambiguous or unrenderable public theorem exports."""
    require(
        "_" not in Path(unit["file"]).stem,
        "Repository catalog skips public filenames containing underscores",
    )
    require(
        isinstance(rows, list) and all(isinstance(r, dict) for r in rows),
        "Malformed catalog rows",
    )
    names = [n for n in unit["declarations"] if n.endswith(".result")]
    require(len(names) == 1, "Catalog needs exactly one planned public result")
    name = names[0]
    # Match load_theorems' budget-bearing row filter: Lean also generates
    # equation theorems and construction proofs for the budget definition.
    # Retain the expected result even if its budget is missing, so that fails.
    selected = [
        r
        for r in rows
        if r.get("module") == module_name(unit["file"])
        and (r.get("budgets") or r.get("theorem") == name)
    ]
    require(
        len(selected) == 1 and selected[0].get("theorem") == name,
        "Catalog must discover exactly the planned result in each public module; move supporting theorems to Proofs",
    )
    row = selected[0]
    require(
        row.get("namespace") == row.get("setup")
        and isinstance(row.get("setup"), str)
        and setup_module(row["setup"]),
        "Catalog setup/namespace does not match the public result",
    )
    budgets = row.get("budgets")
    require(
        isinstance(budgets, list)
        and budgets
        and all(isinstance(b, dict) for b in budgets),
        "Catalog must extract the per-oracle budget components",
    )
    require(
        [b.get("oracle") for b in budgets] == list(range(len(budgets))),
        "Catalog oracle IDs must be complete, ordered and unique",
    )
    require(
        row.get("budget") == (budgets[0] if len(budgets) == 1 else None),
        "Catalog singular budget disagrees with indexed components",
    )
    for budget in budgets:
        require(
            all(
                isinstance(budget.get(k), str) and budget[k].strip()
                for k in ("type", "value", "latex")
            ),
            "Catalog budget type, value and LaTeX must be nonempty for every oracle",
        )
        require(
            "\\text" not in budget["latex"]
            and "\\operatorname{Lean}" not in budget["latex"],
            "Unsupported budget notation in catalog LaTeX",
        )
    return row


def initialize_project(repository, destination, cache=None):
    repository, destination = Path(repository).resolve(), Path(destination).resolve()
    require(
        repository != destination and not destination.exists(),
        "Run project must be a new isolated checkout",
    )
    require(
        not checked(
            ["git", "status", "--porcelain", "--untracked-files=no"], repository
        ),
        "Start from a checkout without tracked modifications",
    )
    untracked = checked(
        ["git", "ls-files", "--others", "--exclude-standard", "-z"], repository
    ).split("\0")
    for name in filter(None, untracked):
        parts = Path(name).parts
        if (
            parts[0] in {"autoformalization", "autoformalization_evidence"}
            or ".ipynb_checkpoints" in parts
        ):
            continue
        require(
            Path(name).suffix not in {".lean", ".py", ".toml", ".json", ".sh"},
            "Commit or separately preserve untracked project source before initialization: "
            + name,
        )
    for path in (
        "AGENTS.md",
        "LongTails/Template.lean",
        "build.sh",
        "lake-manifest.json",
        "lean-toolchain",
        "lakefile.toml",
        "run_comparator.py",
        "tools/ConvergenceMetadata.lean",
        "server/Theorems/BudgetLatex.lean",
        "server/Theorems/create_theorem_description.py",
    ):
        require(
            (repository / path).is_file(), "Not an auto-math checkout: missing " + path
        )
    for category in ("Algorithms", "Setups", "Proofs", "Theorems"):
        require(
            (repository / "LongTails" / category).is_dir(),
            "Not an auto-math checkout: missing LongTails/" + category,
        )
    return initialize_compact(repository, destination, cache)
