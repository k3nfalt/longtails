# Agent protocol, version 2

Every response is one UTF-8 JSON object. Unknown fields, duplicate keys and
nonfinite numbers are rejected. Use LF for Lean source. Run artifacts live outside
the delivered oracle files. Read `next` after each transition; do not infer success
from an adapter exit code or from a Lean build containing sorry warnings.

This version adds exhaustive classification and output inventories. Runs retain
the state-envelope version but are bound to the complete controller/policy hash.
Use the preserved old workflow to load or export an older run; do not migrate
accepted artifacts by adding fields or reuse old approvals for the new schema.

This JSON protocol carries agent responses; delivered Lean files must separately
obey the mandatory output contract in AGENTS.md. Public result candidates retain
the original Setup/Algorithm/Convergence interfaces and must be discoverable by
the repository's catalog extractor with a BudgetLatex-renderable budget.

Every task carries `paths` with absolute workflow, original repository, isolated
project, template, oracle directories, renderer, extractor and toolchain locations.
Repository-relative paths in this protocol resolve under `paths.project`.
`repository_interfaces` supplies the actual template and renderer text from that
checkout. Agent adapters may have a different working directory; use these paths
and submit code through the controller rather than editing repositories directly.

## Graph

```json
{
  "nodes": [{
    "id": "T1", "role": "target",
    "classification": {"kind": "convergence_result", "provenance": "source",
                       "reason": "Standalone source convergence claim", "evidence": ["src_ID_FROM_PACKET"]},
    "statement": "Complete mathematical contract, with inherited setup expanded",
    "objects": [{"id": "K", "type": "natural number", "scope": "outer universal binder",
                 "depends_on": [], "parameter": true, "role": "parameter"}],
    "clauses": [{"id": "rate", "kind": "proposition", "text": "Exact guarantee including constants and cases",
                 "evidence": ["src_ID_FROM_PACKET"], "justification": "Source interpretation or derivation"}],
    "result_context": {"setups": [], "hypotheses": [], "parameters": ["T1/K"]},
    "interpretations": [{"decision": "Definedness decision", "basis": "Source context and deduction",
                         "effect_on_scope": "Why the intended source domain is preserved"}]
  }],
  "edges": [], "targets": ["T1"], "open_issues": [],
  "closure_explanation": "Account for recursively needed statement and proof results, and excluded context citations",
  "inventory": {
    "by_class": {"convergence_result": ["T1"], "supporting_proposition": [], "definition": [],
                 "setup": [], "assumption": [], "parameter": [], "algorithm": []},
    "source_results": ["T1"], "required_closure": ["T1"], "convergence_results": ["T1"],
    "assumptions": [], "parameters": ["T1/K"],
    "counts": {"convergence_result_nodes": 1, "supporting_proposition_nodes": 0, "definition_nodes": 0,
               "setup_nodes": 0, "assumption_nodes": 0, "parameter_nodes": 0, "algorithm_nodes": 0,
               "nodes": 1, "source_results": 1, "required_closure": 1, "public_results": 1,
               "assumptions": 0, "parameters": 1}
  }
}
```

The example shows the schema, not a complete mathematical source. Roles are
`definition`, `setup`, `algorithm`, `assumption`, `parameter`, `lemma`, `theorem`,
`target`. Use no Lean code. Dependency role is separate from classification:
a theorem required only in a proof can still be a standalone convergence result.
Convergence/supporting classifications require a theorem/lemma/target role;
definition/setup/algorithm require their matching role. Assumption may use
assumption/setup/definition; parameter may use parameter/definition.

`classification.kind` is exactly one of the seven keys of `inventory.by_class`.
`provenance` is `source`, `repository` or `derived`; rationale and source evidence
are mandatory. A derived transport lemma is `supporting_proposition`, including
when its conclusion mentions Convergence. Classify source and reused convergence
results by their mathematical role, not their label or file location.

Clause identities are `node/clause`; evidence IDs come from preserved
source line spans, not agent-created quotations. Objects have stable identities;
`depends_on` lists earlier in-scope object identities. Mathematical scope/type
compatibility remains a semantic check. `parameter: false` marks an internal
binder or defined quantity that is not an argument of a dependency application;
the default is true. Object `role` is `parameter`, `bound_variable` or
`defined_quantity`; it must agree with the parameter marker. Clause `kind` is
`proposition`, `definition`, `assumption`, `parameter` or `algorithm`. Every result
node has at least one proposition clause; other classes cannot contain one.
Split substantive claims from definitions instead of hiding them under a
definition label. This does not prohibit Prop-valued definitions of predicates.

Only convergence-result nodes have `result_context`: `setups` names setup nodes,
`hypotheses` lists assumption-kind clause references, and `parameters` lists
parameter object references. All must belong to that result's prerequisite
closure. Record the complete source context, including inherited requirements.
Do not replace assumptions with a theorem's conclusion.

The inventory is mandatory and exact. `by_class` partitions all nodes;
`source_results` lists source-provenance convergence/supporting results;
`required_closure` contains targets and all transitive substantive prerequisites,
excluding source_reference edges; `convergence_results` is the convergence class
within that closure. `assumptions` and `parameters` enumerate all scoped typed
clause/object occurrences. Counts are recomputed, not trusted. Scoped counts do
not deduplicate mathematical concepts; shared identities, domains and argument
substitutions require independent review.

Edges have `provider`, `consumer`, `kind`, `arguments`, `justification`. Kinds are
listed in WORKFLOW.md. Every provider parameter must be bound explicitly, e.g.:

```json
{"provider": "T2", "consumer": "T1", "kind": "uses_result_in_proof",
 "arguments": {"n": {"expression": "K + 1", "uses": ["K"], "justification": "Same natural horizon, shifted index"}},
 "justification": "This result is applied in the source proof"}
```

Internal binders need no cross-node substitution. Context-only edges may use an
empty argument map. Semantic closure cannot be established by graph structure
alone: review the full source. Nonempty open issues prevent acceptance; record
investigation evidence in the run while working toward resolution.

## Global and detailed plan

```json
{
  "units": [{
    "id": "support", "nodes": ["T3", "T4"],
    "file": "outputs/Proofs/Example.lean",
    "declarations": ["OracleTemplate.Example.bound", "OracleTemplate.Example.error"],
    "node_declarations": {"T3": ["OracleTemplate.Example.bound"], "T4": ["OracleTemplate.Example.error"]},
    "clauses": ["T3/bound", "T4/error"], "depends_on": ["setup"], "mode": "new",
    "detail": {"construction": "Ordered declaration interfaces and construction steps",
               "reuse_decisions": ["Explain selected, adapted and rejected matches"],
               "edge_cases": ["Resolve domains and boundaries"],
               "retrieval": ["Record actual queries, tools, returned names and inspected local types"]}
  }],
  "adaptation": {"public_information": "Public versus hidden inputs", "algorithm_identity": "How the source method is pinned",
                 "output": "Output correspondence", "cost": "Iterations versus oracle calls",
                 "probability": "Laws and probability meaning", "source_correspondence": "Contract and necessary transport results"},
  "deferred_obligations": [{"id": "transport", "owner": "support", "requirement": "Exact obligation and how the reviewed statement discharges it"}],
  "output_contract": {
    "public_results": [{
      "node": "T1", "unit": "public", "result": "OracleTemplate.Example.result",
      "setup_unit": "setup", "spec": "outputs.Setups.Example.spec", "budget": "OracleTemplate.Example.budget",
      "cost": {
        "headline": {"expression": "Source headline bound", "unit": "source_cost_unit", "domain": "Source mathematical domain"},
        "execution": {"expression": "Complete indexed template execution bound", "unit": "template_oracle_calls", "domain": "Fin spec.numOracles → Nat"},
        "relationship": {"kind": "conversion", "explanation": "Exact source-to-execution correspondence",
                         "proofs": ["OracleTemplate.Example.costCorrespondence"]}
      }
    }],
    "setups": [{"unit": "setup", "results": ["T1"], "shared_hypotheses": [], "shared_parameters": ["T1/K"],
                "compatibility": [{"result": "T1", "mode": "identical", "justification": "Same complete source context", "proofs": []}]}],
    "counts": {"convergence_results": 1, "public_modules": 1, "setups": 1}
  }
}
```

This plan fragment omits other required units/declarations for readability.
Every node and clause
must have exactly one owner. A unit may group several related nodes into one
cohesive module. Internal declaration order belongs in `detail.construction`.
Cross-unit graph prerequisites must be reflected in `depends_on`. A global plan
is independently reviewed before any statement generation.

`node_declarations` covers exactly the owned node IDs, each mapped to a nonempty
list from the unit's declarations. Actual compiler module ownership is checked.
Result nodes must map to at least one theorem declaration; definition/context
nodes cannot own a theorem. The Reviewer checks the elaborated meaning, including
Prop-valued definitions and all mapped claims, under mandatory `node:<ID>` checks.

`output_contract.public_results` bijects every required convergence-result node
to one unique public unit and module, including reuse. The mapping names the
result, budget, spec and setup unit explicitly. Result and budget are planned
exports of the public unit; spec is a planned export of the setup unit. The
result and budget share a namespace. The spec namespace must equal its setup
module path; it need not equal the result namespace. A raw source
theorem can be owned in Proofs while its public wrapper has `nodes: []`,
`clauses: []`, `node_declarations: {}`. Only mapped public wrappers may do this;
they depend on the raw owner and setup and inherit the source clauses for review.
Alternatively the source node may be owned directly by its public unit. A public
module cannot own unrelated nodes. Supporting/derived results have no extra
public export merely because their Lean statement resembles convergence.

Each `setups` record covers exactly the results using one setup unit. Its
`shared_hypotheses` and `shared_parameters` use source-context IDs. Compatibility
covers every consumer exactly once: `identical` requires equality of the complete
recorded contexts; `equivalent` requires named planned theorem witnesses.
Justification and independent review must establish that no hypotheses, domains
or parameter dependencies are strengthened or dropped. A setup exports
outputs.Setups.<Module>.spec. Compatible public results may share that setup.
Discovery uses the pinned run_comparator.py and tools/ConvergenceMetadata.lean
before statement review and at composition/completion. It checks compiled
result/spec/budget identities and generated challenge configurations for planned
public files. Before those files exist, compiled planned setups are checked for
their module-qualified spec. Counts report actual planned units.

Each source setup listed by `result_context.setups` must be owned by, or be a
dependency of, the chosen concrete setup unit. The Reviewer explicitly reconciles
those node/declaration mappings with the compiled spec body, not only the
hypothesis/parameter arrays.

Headline cost retains its own expression, units and mathematical domain. The
execution quantity is always `template_oracle_calls` in `Fin spec.numOracles → Nat`:
calls to each declared oracle, which may represent batches or events. Its
expression records all components and their oracle meanings. The existing cost
review checks all components, query routing and exhaustion behavior. It does not
automatically count gradient samples or elapsed time. `identity` requires equal
unit/domain records and independent verification of the claimed identity.
`conversion` requires planned correspondence theorem names. Those witnesses
must belong to the public unit's prerequisite closure; composition/final checks
require actual theorem declarations. Preserve the headline claim in the reviewed
success/output/supporting statements as appropriate. A numeric definition alone
does not establish a cost bound on execution. All witness proofs must pass the
ordinary frozen proof and final axiom checks.

The controller verifies the public-result/module/setup counts and the complete
catalog bijection at composition and completion. Per-public-unit checks run
before its statement review. Missing/extra/duplicate results and incorrect setup
associations block progress. Final verification includes both structured
inventories and observed counts; extraction does not publish website metadata.

`new` modules use the four existing oracle categories and UpperCamelCase names.
The controller preserves pre-existing declarations: choose a fresh module or
`reuse`. Reused units name an existing `LongTails/...`, `Mathlib/...`, `Init/...`,
`Lean/...` or `Std/...` module and its actual declarations. Supporting results
belong in Proofs; public convergence results belong in Theorems. Distinct public
cases use distinct modules. Declaration names use explicit qualified ASCII Lean
identifiers (subscript digits are allowed); source mathematical names may be
Unicode. Rename an unsupported exported identifier in a new module if needed.

## Statement candidate

```json
{"unit": "support",
 "code": "import LongTails.Template\nnamespace OracleTemplate.Example\ntheorem bound : True := by sorry\nend OracleTemplate.Example\n",
 "holes": [{"declaration": "OracleTemplate.Example.bound", "start": 80, "end": 88}],
 "providers": []}
```

Offsets above are illustrative: calculate the actual half-open Python Unicode
character interval for `by sorry` in your exact code. The controller verifies it
against Lean's named declaration range and complete right-hand side. Every new
exported theorem has one hole. Use complete definitions and construction proofs.
For `reuse`, send `code: ""`, `holes: []`. `providers` requests additional exact
qualified declarations reachable through the module imports, including deeper
definitions needed for semantic interpretation. Add needed imports before freeze.

Compilation and compiler-owned inventories precede review. The inventory includes
all declarations owned by new modules, full expression structure, raw types and
definition bodies, direct providers, and a list of deeper dependencies not yet
expanded. Theorem proof bodies are excluded from semantic evidence; proof-use and
axiom names are audit metadata. Compiler scaffolding can be justified together in
the written explanation, but required check IDs cannot be omitted.

For public results, `candidate/catalog` contains the actual extractor rows,
rendered budget and extractor/renderer source hashes. Extraction must pass before
the review packet is issued. Inspect the rendered formula's correspondence to the
reviewed budget; renderer success alone says nothing about source faithfulness.
The mandatory `catalog:<unit>` check must pass and cannot be marked not applicable.
Final verification repeats extraction and retains `catalog` in verification.json.

## Bidirectional review

```json
{"basis": "EXACT_PACKET_BASIS", "reviewer": "reviewer",
 "checks": [{"id": "source_to_candidate:T3/bound", "verdict": "match",
             "source": ["src_ID_FROM_PACKET"], "candidate": ["candidate/inventory/declarations/0/type_tree"],
             "comparison": "Specific correspondence of the cited source clause to these elaborated components"}],
 "blockers": [], "notes": []}
```

Return **every** `required_checks` entry exactly once, not only the illustrated
entry. Candidate references are structural pointers supplied in `candidate_ids`;
they must identify the evidence actually discussed. Broad root citations alone
are insufficient reasoning. Source-to-candidate coverage and candidate-to-source
justification each receive a categorical score: `match` passes; `mismatch` or
`unresolved` fails. `not_applicable` requires a reason and is permitted only for
optional topic checks. Clause, declaration, composition, deferred-obligation,
catalog, `inventory:`, `classification:`, `node:`, `output:`, `setup:` and `cost:`
checks cannot be waived. Graph review checks classification and recursive source
completeness; plan review checks the public bijection, setup compatibility and
cost contracts; statement review checks mapped nodes/declarations and relevant
exports; composition repeats the complete inventory/output checks with actual
compiler and catalog evidence. Acceptance is the conjunction of all checks and absence
of blockers; there is no compensating weighted average.

The same format gates graph, global plan, statements, reused results and final
composition. Match the exact basis and registered Reviewer identity. Rejected
records remain immutable; an identical rejected basis cannot be resubmitted.

## Proof and repair

```json
{"declaration": "OracleTemplate.Example.bound", "proof": "by\n  trivial"}
```

After all statements and composition are accepted, `freeze` captures source,
types, definitions, environment and registered proof slots. Each replacement
must parse as one `by` term. Complete prerequisites first. Local `have`/`let`
steps are allowed; new source theorems must return through the graph/statement
gate. Transitive `sorryAx` dependencies cannot pass proof completion.

When `next` requests `repair`, return `{"unit": "support", "reason": "..."}`
to reopen that closure, or `{"reason": "..."}` for a revised graph. The same
operations are available via `reopen`. An interface change in a prerequisite
removes stale descendant modules from the active checkout while retaining their
artifacts for repair. Unrelated accepted work survives.

## PDF acquisition

Pass the original PDF and this external-tool evidence to `init`:

```json
{"original_pdf_sha256": "SHA256_OF_ORIGINAL_BYTES",
 "searches": [{"query": "Paper title author TeX", "timestamp": "ISO-8601 time",
               "tool": "Actual live web-search tool", "results": [{"url": "https://example.org/source", "observation": "What was located and checked"}]}],
 "outcome": "author_tex_found", "version_comparison": "Check authors, version, target statement and notation",
 "user_warning": "", "transcription_pages": []}
```

`outcome` is `author_tex_found` or `transcribed`. The latter requires the actual
warning delivered to the user and nonempty page-level transcription validation
evidence. Search failure is not either outcome. Records must describe real host
tool activity; the controller validates the record's integrity, not the truth of
an agent's asserted web search. No provider-specific search credentials are stored.
