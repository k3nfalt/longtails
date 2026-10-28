"""Narrow, independently reviewed metadata repair in a preserved derivative run."""

import copy
import re
import shutil
from pathlib import Path

from .common import digest, fields, require, scoped
from .layout import in_category
from .lean import audit, check_holes, check_proof_signature, module_name, repository_files
from .output_contract import catalog_contract, declaration_contract, output_checks, review_clauses


def annotated_source(code, declaration, declarations, holes, record):
    """Construct the only permitted delta; never accept arbitrary replacement text."""
    require(not holes, "Metadata repair requires a definition-only unit")
    require(declaration in declarations, "Metadata declaration is not planned")
    short = declaration.rsplit(".", 1)[-1]
    require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", short), "Unsupported declaration name")
    pattern = re.compile(r"(?m)^(?:noncomputable )?def " + re.escape(short) + r"(?=\s|\()")
    matches = list(pattern.finditer(code))
    require(len(matches) == 1, "Expected exactly one planned definition")
    pos = matches[0].start()
    require(record.get('name') == declaration and record.get('kind') == 'definition', "Target is not the recorded definition")
    span, selection = record.get('range'), record.get('selection')
    require(isinstance(span, dict) and isinstance(selection, dict), "Missing compiler declaration ranges")
    lines = code.splitlines(keepends=True)
    line = span['start_line']
    require(isinstance(line, int) and 1 <= line <= len(lines) and span['start_column'] == 0, "Unsupported declaration start")
    require(pos == sum(map(len, lines[:line-1])), "Text match is not the compiler-recorded declaration start")
    column = matches[0].end()-pos-len(short)
    require(selection['start_line'] == line and selection['end_line'] == line
            and selection['start_column'] == column and selection['end_column'] == column+len(short),
            "Definition token differs from compiler-recorded selection")
    previous = code[:pos].rstrip().splitlines()
    require(not previous or not previous[-1].lstrip().startswith("@["), "Existing attribute requires ordinary statement repair")
    require("@[instance_reducible]\n" + code[pos:matches[0].end()] not in code, "Attribute is already present")
    return code[:pos] + "@[instance_reducible]\n" + code[pos:]


def revalidate(run, payload):
    fields(payload, ["unit", "declaration", "authorization"])
    require(isinstance(payload["authorization"], str) and payload["authorization"].strip(), "Explicit user authorization is required")
    parent = run.state.get("metadata_parent")
    require(parent and parent["run"] != str(run.root), "Use a verified derivative; never amend the original run")
    original_root = Path(parent["run"]).resolve()
    derivative_root = run.root.resolve()
    require(not derivative_root.is_relative_to(original_root) and not original_root.is_relative_to(derivative_root), "Derivative and original run paths must be disjoint")
    require(payload["authorization"] == parent["authorization"], "Authorization differs from verified derivative provenance")
    require(run.compiler.project.resolve() == derivative_root/'project', "Compiler project is not bound to derivative root")
    require(not run.compiler.project.resolve().is_relative_to(original_root), "Compiler project overlaps original")
    require(run.state["phase"] == "proofs" and run.state["freeze"] == parent["freeze"], "Expected the preserved original freeze")
    require(not run.state.get("pending"), "Resolve pending review before metadata repair")
    require({h["declaration"] for h in run.all_holes()} == set(run.state["proofs"]), "All original proof slots must already be checked")
    require(digest(run.state["proofs"]) == parent["proofs_digest"], "Original proof bytes changed")
    unit = run.unit(payload["unit"])
    require(unit["mode"] == "new" and not in_category(unit["file"], "Theorems"), "Only a planned definition module can be annotated")
    row = run.state["units"][unit["id"]]
    old = run.get(row["candidate"])
    candidate = copy.deepcopy(old)
    records = [d for d in run.get(row['inventory'])['declarations'] if d['name'] == payload['declaration']]
    require(len(records) == 1, "Missing unique recorded declaration")
    candidate["code"] = annotated_source(old["code"], payload["declaration"], unit["declarations"], old["holes"], records[0])
    path = scoped(run.compiler.project, unit["file"])
    require(path.read_bytes() == old["code"].encode(), "Definition source differs from its accepted candidate")
    original_files = repository_files(run.compiler.project)
    require(digest(original_files) == parent["files_digest"], "Derivative sources differ from verified parent")
    original_proofs = copy.deepcopy(run.state["proofs"])
    for relative in original_files:
        local = scoped(run.compiler.project, relative)
        original = scoped(original_root/'project', relative)
        require(not local.is_symlink() and local.stat().st_nlink == 1, "Derivative source is linked to another file")
        require(not original.exists() or not local.samefile(original), "Derivative source aliases original")
    # Read the original declaration's actual status before changing any source.
    run.compiler.build(targets=[module_name(unit['file'])])
    run.compiler.probe([module_name(unit['file'])],
        'run_cmd do\n  unless (← Lean.getReducibilityStatus `'+payload['declaration']+') == .semireducible do\n    throwError "Original target is not semireducible"')
    path.write_bytes(candidate["code"].encode())
    # Formatting precedes compilation, then complete fresh proof checking precedes review.
    run.compiler.source_style()
    build_root = (run.compiler.project / ".lake/build").resolve()
    require(build_root.is_relative_to(run.compiler.project.resolve()), "Build cache points outside derivative project")
    for relative in ["lib/lean/outputs", "ir/outputs"]:
        cache = (build_root / relative).resolve()
        require(cache.is_relative_to(build_root), "Build-cache path escaped derivative project")
        if cache.exists():
            shutil.rmtree(cache)
    run.compiler.run(["lake", "--wfail", "build", "outputs", "BudgetLatex"])
    run.compiler.declaration_lint()
    inventory = run.inventory()
    check_proof_signature(run.get(parent["freeze"])["signature"], inventory, run.all_holes())
    audit(inventory, final=True)
    current_files = repository_files(run.compiler.project)
    require(current_files.keys() == original_files.keys(), "Metadata repair changed the source file set")
    require({p for p in current_files if current_files[p] != original_files[p]} == {unit["file"]}, "Metadata repair changed other source files")
    require(path.read_bytes() == candidate["code"].encode(), "Annotation source changed during validation")
    require(run.state["proofs"] == original_proofs, "Metadata repair altered proof bodies")
    observed = run.compiler.inspect([unit], candidate["providers"])
    run.compiler.probe([module_name(unit["file"])], """
run_cmd Lean.Elab.Command.liftTermElabM do
  let info ← Lean.getConstInfo `""" + payload["declaration"] + """
  unless (← Lean.getReducibilityStatus `""" + payload["declaration"] + """) == .instanceReducible do
    throwError "Target did not become instance-reducible"
  Lean.Meta.forallTelescopeReducing info.type fun _ type => do
    let type ← Lean.Meta.whnf type
    unless type.getAppFn.isConst && Lean.isClass (← Lean.getEnv) type.getAppFn.constName! do
      throwError "Metadata annotation target is not class-valued"
""")
    owned = [d for d in observed["declarations"] if d["module"] == module_name(unit["file"])]
    check_holes(candidate["code"], [], owned, unit["declarations"])
    declaration_contract([unit], run.get(run.state["graph"]), observed)
    catalog = run.compiler.catalog([unit])
    output = catalog_contract(run.get(run.state["plan"]), catalog, observed, [unit["id"]])
    topology = run.compiler.topology(run.get(run.state["plan"]))
    proof_hashes = {name: digest(body) for name, body in original_proofs.items()}
    evidence = {
        "parent": parent, "authorization": payload["authorization"],
        "unit": unit["id"], "declaration": payload["declaration"],
        "old_candidate": row["candidate"], "old_inventory": row["inventory"],
        "before_source": digest(old["code"]), "after_source": digest(candidate["code"]),
        "only_change": "Insert @[instance_reducible] before the named definition",
        "fresh_warnings_as_errors_build": True, "fresh_signature_and_final_axiom_audit": True,
        "freshly_revalidated_proofs": proof_hashes, "unchanged_other_source_files": True,
        "historical_reviews": "Retained as provenance only; this statement review and new full composition review establish current acceptance.",
    }
    evidence_id = run.put(evidence)
    row.update(candidate=run.put(candidate), inventory=run.put(observed), accepted=False, review=None)
    run.state.update(phase="statements", freeze=None, composition=None, final=None,
                     proof_inventory=run.put(inventory), metadata_revalidation=evidence_id)
    run.state.pop("statement_validation", None)
    context = {
        "unit": unit, "inventory": observed, "catalog": catalog,
        "output_contract_check": output, "comparator_topology": topology,
        "statement_checks": {"source_style": "passed", "declaration_lint": "passed",
                             "catalog_rendering": catalog["status"], "warnings_as_errors": "passed",
                             "order": "format_and_structure_before_semantic_review"},
        "source_code": candidate["code"], "graph": run.get(run.state["graph"]),
        "plan": run.get(run.state["plan"]), "metadata_revalidation": evidence,
        "accepted_prerequisites": {dep: run.get(run.state["units"][dep]["inventory"]) for dep in unit["depends_on"]},
    }
    extra = ["obligation:" + o["id"] for o in context["plan"]["deferred_obligations"] if o["owner"] == unit["id"]]
    extra += ["declaration:" + d["name"] for d in observed["declarations"]]
    extra += ["node:" + n for n in unit["nodes"]]
    extra += output_checks(context["plan"], unit["id"])
    extra += ["metadata:exact_annotation_only", "metadata:all_proofs_freshly_revalidated", "metadata:historical_receipts_not_relabelled"]
    run.queue(run.packet("statement_review", context, review_clauses(unit, context["plan"], context["graph"]), extra_checks=extra), unit["id"])
    run.save("metadata_statement_revalidated", evidence_id)
