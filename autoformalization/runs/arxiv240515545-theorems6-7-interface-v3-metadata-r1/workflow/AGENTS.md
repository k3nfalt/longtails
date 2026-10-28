# Autoformalization for auto-math

These are the task-specific instructions for formalizing existing mathematics in
auto-math. Apply this file, WORKFLOW.md, PROTOCOL.md, OUTPUT_CONTRACT.md and the
role prompt supplied in each packet. These workflow policies state all output
requirements explicitly; do not infer them from the target repository's AGENTS.md,
README, tutorial or example modules. The user's latest instructions take precedence. This workflow
does not invoke auto-math's novelty-seeking research prompt.

## Repository context

This directory is autoformalization/ within auto-math. The repository root
contains LongTails/, server/, the Lean toolchain and build configuration. The
controller uses this containing repository by default; --repo selects another
checkout. Each run works in a compact project at <run>/project.

In task packets, paths.project identifies that checkout and paths.workflow
identifies these instructions. Generated outputs/, copied LongTails/ dependencies, server/ and build
paths resolve under paths.project. The packet supplies absolute resource paths,
run-local instructions, the complete workflow policy and actual template/renderer
source. Apply these supplied contents before planning. Submit candidates through
the controller. The original repository AGENTS.md hash is provenance, not an
additional source of unstated mathematical or output requirements.

Generated modules use outputs.*; copied dependencies retain LongTails.*.
The controller copies only the selected transitive dependency closure and builds
explicit modules or the outputs aggregate. Retrieve other library files from
paths.repository without copying them into the run. Do not create a library alias.

## Task and roles

Given a TeX package (or PDF) and a target theorem, formalize its recursively required
definitions, assumptions, algorithms and theorem dependencies, then prove the
reviewed statements. Use a Formalizer and an independent Reviewer. Both work toward
the target; independent review never means forced approval. Do not launch another
model service or require notebooks. The workflow does not select a model.

The Formalizer owns source interpretation, graph construction, planning, candidates
and repairs. The Reviewer owns independent semantic verdicts on the exact candidate.
The Formalizer must not write approval on the Reviewer's behalf. Keep separate
contexts and candidate/review artifacts. Read a saved checkpoint after interruption.

## Source and mathematical scope

- Read the whole original TeX package, including local content/macro files, later
  statements, proofs, nested results and appendices. Preserve original text.
- For PDF input, use ONLY live web search to discover the matching author's TeX
  source. Verify paper version and target correspondence. Do not substitute a
  remembered URL or pre-existing local source as the discovery method. Fetching
  a source found by live search is allowed.
- If a documented reasonable search finds no available matching TeX, warn the user
  and convert the PDF to TeX. Validate the transcription against original PDF
  pages. A search outage is an access limitation, not evidence of nonexistence.
- Construct the graph without Lean generation. Record source evidence, mathematical
  contracts, object identity, quantifier scope, dependency arguments and cases.
- Recursively include theorems/lemmas needed in statements AND in proofs. Each
  selected result goes through statement planning, formalization and semantic
  validation before it can be accepted. A library match is not an exemption:
  inspect its actual statement and validate its application against the source.
- Distinguish inheriting another theorem's setup from using its conclusion. Expand
  inherited conditions into an explicit mathematical contract, represented in
  Setups or explicit binders. Never substitute a referenced theorem's conclusion
  for its assumptions. Share a setup only after checking compatible hypotheses,
  parameter domains and dependence; resemblance of algorithms is insufficient.
- Keep statement requirements, proof dependencies and context references separate.
  A citation alone is not proof that a result is needed. Explain exclusions.
- Preserve the author's algorithm, permitted instances, constants, output,
  quantifiers and probability/cost model. Do not invent assumptions to ease proof.

## Resolve mathematical questions autonomously

Investigate source context and proofs, derive consequences, inspect conventional
definitions, and test competing interpretations before escalating a question.
Validation concerns the resulting contract, not private drafting reasoning.

Resolve ordinary implicit conditions from the source's assumptions, definitions
and established mathematical conventions. Record the justification and encode
or derive the condition faithfully. Check all relevant clauses and boundary
cases; reconcile conflicting interpretations before accepting a restriction.
Distinguish necessary interpretation from stronger assumptions introduced for
convenience. Routine deductions require neither redundant source sentences nor
user confirmation. Reopen settled interpretations only when new evidence warrants it.

Leave a substantive issue open only after substantial, documented attempts:
source/scope inspection, relevant proof analysis, deductions, library/literature
lookup where appropriate, and comparison of plausible interpretations. Record
what was tried, what was learned and the exact remaining ambiguity. Continue
independent work. Restricted or completed variants must be accurately labeled;
they do not count as full exact-target completion. A retry count alone neither
justifies giving up nor establishes mathematical ambiguity.

## Exact auto-math output conventions

Before routing files, classify every node by its mathematical role and provenance:
convergence result, supporting proposition, definition, setup, assumption,
parameter or algorithm. Dependency position and source labels do not determine
this classification. A convergence result used only inside another proof remains
a convergence result. A derived transport lemma does not become another source
convergence result merely because its Lean type mentions Convergence.

Maintain the structured graph inventory required by PROTOCOL.md. It partitions
all nodes, computes the recursive required closure, lists every required
convergence result, and counts typed assumption clauses and parameter objects.
These latter counts are scoped occurrences, not claims about the number of
distinct mathematical concepts. Review repeated identities and substitutions.
Keep numerical definitions separate from propositions about their values.
Reusable Prop-valued assumption predicates are permitted. In public successful
fields, write the accuracy inequality inline; do not hide it in a setup-local
success/Guarantee helper. Ordinary mathematical predicates may accompany that
visible criterion. Defining a predicate or bound proves no property or cost relation.

Every convergence result in the required closure needs exactly one public module,
including results used only as dependencies and reused results. The plan records
a bijection from the inventory to public modules, result/spec/budget declarations
and setup contracts. A raw analytic theorem may remain in Proofs while its public
wrapper is a separate unit. Supporting propositions and derived transport lemmas
do not each require public wrappers. Do not infer output counts from the requested
target alone. Review the inventory and actual catalog together.

Use the existing paths and mathematical interfaces:

- outputs/Algorithms/<UpperCamelCase>.lean: algorithms and their outputs.
- outputs/Setups/<UpperCamelCase>.lean: concrete setup and assumptions.
- outputs/Proofs/<UpperCamelCase>.lean: cohesive supporting lemma modules.
- outputs/Theorems/<UpperCamelCase>.lean: public convergence results.

Keep LongTails/Template.lean unchanged. Reuse the pinned lean-toolchain and
lake-manifest.json. Do not copy old compiled artifacts from another Lean version.
Preserve existing repository declarations. No generic Formalized namespace, flat
assumptions.lean/algorithms.lean output, or alternative public theorem API.

Follow the explicit OUTPUT_CONTRACT.md templates: imports, namespace, abbrev spec : Setup, one
explicit single-line public budget definition, and theorem result : Convergence
outputs.Setups.<Module>.spec budget. Put supporting results in Proofs, even if their informal labels say
'theorem'. Group related lemmas; do not create one file per local fact. Distinct
public cases use separate appropriately named modules. Validate namespace/name
compatibility with Comparator and catalog extraction. Each public module has
exactly one main theorem; supporting theorems belong in Proofs.

The template is a mathematical contract, not just a folder convention. Its entire
source and the construction rules are supplied in OUTPUT_CONTRACT.md and
repository_interfaces; no external example is needed to determine requirements:

- Algorithms use OracleTemplate.Algorithm, including the seed/law, state,
  initialization, query, update and output needed by the source method. Queries
  select an oracle ID in Fin numOracles as well as the query value.
- Setups export abbrev spec : Setup under their module namespace,
  outputs.Setups.<Module>. Public results import that module directly and name
  its spec explicitly. Several results may reuse a compatible setup.
  Specify numOracles, Params, Public, Instance, Query, Reply, Output, publicInput,
  valid, admissible, successful and allowedAlgorithm as required by the source.
  Preserve the distinction between public algorithm inputs and hidden instance
  information. Pin the source algorithm family when an unrestricted existential
  algorithm would weaken its claim.
- Theorems define budget : spec.Params → Fin spec.numOracles → Nat in their own
  module and export result : Convergence outputs.Setups.<Module>.spec budget.
  Convergence asserts an allowed algorithm built from Public inputs and successful output for
  every valid parameter and admissible instance/oracle under the template's law.
  Each budget component counts calls to its oracle. execute returns the output
  directly and stops if the next selected oracle's remaining budget is zero.
  Review the complete indexed budget, routing and stopping behavior using the
  existing cost and algorithm correspondence checks.
  Record the source's headline quantity separately, with its own units and domain.
  Iteration counts, batch work, elapsed time and other source quantities are not
  interchangeable with this execution budget. Preserve the headline claim in
  the reviewed setup/success/output or supporting statements as appropriate;
  plan and prove the necessary correspondence. A definition naming a quantity
  is not a proof that actual execution satisfies it.
  Prove the correspondence to the source's iterations, output and probability
  model in Proofs. Never replace these interfaces with look-alike definitions.

Select the namespace, imported proof modules and explicit budget from the reviewed
source contract and explicit workflow templates. Inspect library declarations
only for justified reuse; do not infer syntax/style requirements or import their
mathematical assumptions, algorithm variants or rate formulas as defaults.

The controller checks the resolved Convergence/spec/budget identities and their
module ownership. Before public statement review and at composition,
it runs the pinned repository's theorem extractor and BudgetLatex renderer.
Each public module must yield exactly its planned result, matching setup and
setup namespace, and every oracle budget component with nonempty type, value and
supported LaTeX. The catalog's namespace field is the setup namespace; the result
and budget may use their own namespace.
The complete catalog must also have exactly the public results in the graph/plan
inventory, with the reviewed setup association; no missing, duplicate or extra
module may be hidden by checking modules individually. Composition review
includes the aggregate catalog and explicit output counts before freezing.
The statement review packet includes this catalog evidence; the pre-freeze
validation receipt binds it to reviewed sources. Final verification retains it with the extractor/renderer source hashes. Missing tools, extraction
failures, ambiguous discovery and unsupported notation block acceptance/export.

BudgetLatex is a display renderer, not a proof or semantic validator. Repair an
unsupported formula with a mathematically equivalent supported expression during
statement mode and review it again. Do not round away terms, weaken the source
bound or modify the renderer/template to force acceptance. After freezing, such
repairs require reopening the affected statement closure. Compatibility checking
does not write server/theorems.json or server/Theorems/Descriptions; publishing
those website artifacts is a separate operation.

This workflow explicitly selects the layout and mathematical requirements above
and in OUTPUT_CONTRACT.md. Research defaults in external repository instructions
are not part of this workflow. Preserve the supplied source's method and cases;
do not substitute novelty search or a different algorithm variant.

Do not add explanatory Lean comments/docstrings unless requested. Keep source
correspondence, reviews and unresolved issues in run artifacts outside the Lean
deliverables. No Git commit or push is implied by formalization.

## Statement stage and semantic gate

The statement gate order is mandatory, not a list of optional end-of-run checks:

1. Write the candidate inside the controller transaction and regenerate the
   outputs import index. Run native text/style lint and source budget-syntax lint.
   A formatting failure stops here, before candidate elaboration or semantic review.
2. Materialize pinned dependencies, elaborate the candidate and run the native
   declaration lint (excluding only the repository's docBlame check). Registered
   `by sorry` theorem slots are expected at this stage; they are not proof evidence.
3. Check proof-hole registration, declaration ownership/layout, allowed axioms,
   compiled interfaces and structured parameter/tuning/output designs. For public
   units, run the actual theorem extractor, budget renderer, catalog bijection and
   Comparator discovery/topology checks before issuing a semantic review packet.
4. Obtain independent semantic statement review. A failed earlier mechanical gate
   must never create a pending reviewer packet or an accepted candidate.
5. On the assembled statements, repeat the aggregate checks and record an immutable
   statement-validation receipt with source hashes, environment, graph, plan and
   controller identity. Composition review must cover that exact receipt.
6. Freeze only after the receipt and composition approval match the current sources.
   Then fill registered proof bodies. Check newly inserted proof text/style and
   declaration lint immediately; proof-format repairs stay inside the proof slot.
7. Final verification checks frozen-source preservation, strict compilation, full
   proof Comparator checks and transitive axiom freedom. Native lint repeats only
   as a regression check on proof changes. Catalog, budget-rendering, topology and
   statement-design evidence is carried forward from the verified pre-freeze
   receipt after source and signature preservation checks; it is not first computed
   after proving. No statement-only gate may be deferred to completion.

Text/style lint needs source files; declaration lint and metadata extraction need
elaboration; semantic review needs all of that evidence; proof checks need filled
proofs. Assign every new gate by these dependencies, not by when it was requested.
Graph and plan reviews precede Lean generation and remain separate from semantic
review of the written statements.

Formalize dependencies before consumers. Required theorem/lemma statements start
with registered proof holes ending `:= by sorry`. Concrete definition and algorithm
bodies cannot contain admissions. Supply genuinely checked small construction
proofs where necessary for well-formed definitions; do not assume a missing fact.

Every new/reused/adapted mathematical unit must pass the applicable semantic gate.
Classification, inventory completeness, public-result coverage, definition versus
claim, setup sharing, headline cost units and execution correspondence are
mandatory independent checks. They cannot be marked not applicable. Shared
setups require identical recorded hypotheses/parameters or explicit equivalence
theorems with reviewed mappings; final verification checks those witnesses are
actual proved theorems. Similar names do not establish compatibility.
Review source-to-candidate coverage and candidate-to-source justification against
independently inspected elaborated Lean, including dependencies and argument use.
All required scores/checks must pass; a weighted average cannot offset a mismatch
or unknown. Final composition must discharge all deferred obligations.

Graph acceptance, elaboration and semantic review are distinct. A valid citation
does not establish entailment. Compilation with sorry is not a proof. Never use an
admitted target or dependency as proof evidence for a semantic judgment.

If Convergence packaging differs from the source statement, specify the necessary
execution/output/cost/probability correspondence as supporting obligations inside
the existing structure. Do not create a second public output format or redundant
wrapper. Do not silently change the source guarantee. If the unchanged interface
cannot express the target faithfully, investigate and report that incompatibility.

## Freeze and proof stage

After every statement-format/structure gate and semantic composition review pass,
require the immutable validation receipt for the current exact sources, then freeze the graph revision,
declaration types, concrete definitions, algorithms, setup/success predicates,
budgets, instances, imports and dependency/toolchain versions. Register each
editable proof body by declaration identity and source location.

Prove dependencies before consumers, filling each registered body separately.
Other proof facts are imported from existing accepted sources or introduced as
local have statements; proof-local let definitions are allowed. Named supporting
results discovered in the source are not hidden as unreviewed local facts: their
statements belong in the graph and must pass semantic validation before use.
New purely internal intermediate facts do not require an LLM semantic gate when
they remain inside a frozen proof body and are checked by Lean.

No source-level additions or changes to frozen statements/definitions are permitted
in proof mode. If necessary, return the affected dependency closure to statement
mode, obtain semantic review, and create a new freeze. Do not silently change
imports or assumptions. Keep unaffected accepted work.

Lean may generate internal theorem declarations while elaborating a proof tactic.
These are implementation details of the registered proof body, not new source
statements. The controller permits only its recognized internal proof-lemma
forms under that body's name, with no source declaration range, and audits them
alongside the completed proof. Definitions and other new declarations remain
forbidden after freezing.

No new proof-body semantic gate is needed with an unchanged reviewed contract.
Verify proof-only changes mechanically, compile and audit transitive axioms.
All delivered proofs, including supporting results, must be complete: no sorryAx,
admit or added axioms. The allowed foundational axioms are propext,
Classical.choice and Quot.sound.

Compile the changed output module and its transitive imports after Lean changes.
The controller generates outputs.lean from outputs/ only; final checks build outputs.
Never clone, copy or build the whole LongTails library for a run.
Run native style and declaration lint before statement review and immediately
after proof edits. Use python3 run_comparator.py <theorem-file> for final proved
public results, repeat lint as a proof-change regression, and audit supporting declarations. Do not
claim proof verification from a zero compiler exit code with sorry warnings.

## Progress and honesty

Preserve one canonical candidate, exact review basis, failure evidence and compact
repair history. Repair only the affected content; do not repeat identical failed
requests. Distinguish protocol, citation, semantic, compiler and execution errors.
Informational notes are not blockers. Partial outputs are never approvals.

Record run progress, observed verification, limitations and next actions in the
run artifacts. Clearly distinguish reviewed statements from fully proved results.
Do not fabricate validation records or introduce paper-specific workflow rules.

## Authorized annotation-only derivative revalidation

This version permits one narrow exception to ordinary invalidation: an explicitly
user-authorized derivative run may insert exactly `@[instance_reducible]` before
one planned class-valued definition in a module with no registered proof holes.
The original run, controller, immutable receipts and frozen source are preserved.
This is not an in-place edit or a migration of approval to a new review basis.
No theorem type, definition body, import, budget, instance registration, other
source byte, or checked proof byte may change. The controller constructs the
insertion; it does not accept arbitrary replacement code or warning suppression.

The derivative records the verified parent's state/event/freeze/controller and
proof-byte digest. Old reviews remain explicitly historical provenance. Before
any new review it runs source style, forces fresh compilation of every output
module with warnings as errors, runs declaration lint, compares the complete
original frozen mathematical signature and declaration ownership, and audits all
proofs with final axiom rules. The original proof bodies are retained only when
all these fresh native checks pass. It checks a class-valued target in Lean and
requires every unrelated source byte and every proof byte to remain unchanged.
The transaction restores source and state on compilation, evidence, packet-size,
or state-save failure; unreferenced immutable artifacts convey no acceptance.

The amended unit receives a fresh ordinary statement-review packet, including
the exact metadata delta, historical provenance and fresh proof-validation
receipt. A fresh aggregate composition review covers the entire unchanged
mathematical contract and its metadata amendment; inherited reviews are not
relabeled as current approvals. Only then may the normal controller create a new
freeze and run every normal final gate. The original run remains loadable with
its original controller. Arbitrary attributes, compound edits, incomplete proof
sets, and source/signature changes require the ordinary repair workflow.
