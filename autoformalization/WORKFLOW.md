# End-to-end agent workflow

Read AGENTS.md first. This is the normative execution procedure for a Formalizer
and independent Reviewer working on a supplied source and target. It requires no
notebook or local model server.

## Repository and run context

Give the Formalizer prompts/FORMALIZER.md and the Reviewer prompts/REVIEWER.md,
together with the same source/target request. This component lives under
auto-math/autoformalization; initialization uses the containing repository unless
--repo selects another checkout. The controller creates a compact <run>/project
and supplies its absolute resource paths in each task packet. Repository-relative
Generated outputs/, copied LongTails/ dependencies and server/ paths refer to paths.project. The packet also includes the
actual template and renderer source in repository_interfaces.

Inspect the actual repository revision, worktree state, AGENTS.md, Template.lean,
toolchain, manifest, representative relevant modules and verification scripts.
Do not reset or overwrite other work. Use the compact run project when editing; retrieve library sources read-only from paths.repository.
Record the baseline and run identity. Do not run research_prompt.md.

## 1. Acquire and establish the source

For TeX, preserve the original package and discover local includes/macros. For
PDF, perform live web search for matching author TeX. Record searched sources and
version matching. If unavailable after a reasonable search, warn and transcribe,
retaining PDF page links and transcription validation evidence.

Prefer a unique TeX label. Resolve numbering, paper version and multi-result
statements before proceeding. Source snapshots preserve bytes/file boundaries;
they are not rewritten mathematical summaries.

Artifacts: source manifest, exact source package, target record, search or
transcription evidence when applicable.

## 2. Construct the full dependency graph without Lean

Read the whole paper before choosing local packets. Starting from the target,
recursively discover requirements in BOTH its statement and its proof. Apply the
same process to every required theorem or lemma until the closure is understood.
For external results, locate their exact statements and required assumptions;
do not assume a citation's title determines its content.

Each node records its role, mathematical contract, source evidence, object and
scope identities, parameters, domain/cases, required inputs and their providers.
Each dependency application records argument substitution and permitted scope.

Classify each node independently of its dependency role. Identify source or
repository convergence results, supporting propositions, definitions, setups,
assumptions, parameters and algorithms. Classify every clause and object as well:
assumptions and parameters often occur within a setup rather than as separate
nodes. Split a definition from any substantive claims about its value. Purely
internal algebraic steps may remain planned local proof facts.

Submit the exact classification partition, source-result list, computed required
closure, required convergence-result list and scoped assumption/parameter lists
with their counts. Explain why any result is supporting rather than standalone
convergence. Source-backed convergence results used only in proofs still enter
the public-result inventory; derived correspondence lemmas do not automatically
create extra public results.

Use typed edges:

| Edge | Meaning |
|---|---|
| requires_definition | Needed to express a mathematical object or statement |
| inherits_setup | Brings applicable conditions/definitions into the explicit setup |
| uses_result_in_statement | A substantive logical relation to another result, requiring careful expansion |
| uses_result_in_proof | Used to establish the consumer, not a new consumer premise |
| source_reference | Context/navigation pending interpretation |

Keep setup inheritance separate from theorem truth. Expand references to another
result's setup into its inherited conditions plus the stated modifications.
A shared Setups structure may implement this; each statement must be well-formed
without assuming or invoking the referenced result's proof.

Discover, review and formalize recursively required results before their consumers.
Their order follows dependencies, not theorem numbering. Keep theorem types
separate from proof-use edges, and account explicitly for referenced results
that supply context without adding a mathematical prerequisite.

Compute statement-construction layers and proof order as separate views of the
same graph. Do not turn a context back-reference into a circular proof dependency.
Incrementally construct and checkpoint layers, then review the complete graph.

## 3. Validate the graph and repair

Mechanical checks: unique identities, valid source spans, complete bindings,
dependency argument mappings, typed references, scope consistency and valid
construction order. These checks cannot establish semantic completeness.
The controller checks inventory partitions and counts against node, clause and
object records, and closure against all substantive dependency edges. Independent
review must detect missing source results and incorrect classifications; a
mechanically self-consistent incomplete graph is still unacceptable.

The Reviewer independently checks both directions against the whole source:
missing obligations, unjustified additions, inheritance, theorem/proof scope,
constants, algorithms, randomness, definedness, cases and cross-node consistency.
Review the exact graph that will be handed to planning.

On failure, save observations, hypothesized cause, proposed repair and regression
checks. Patch the canonical graph, validate the patch and reassess its affected
closure. Do not weaken a gate or repeatedly regenerate unchanged content. Resolve
routine deductions without asking the user. Escalate a genuine unresolved issue
only with the investigation record required by AGENTS.md.

Exit: GRAPH_ACCEPTED. This is reviewed working-contract acceptance, not a proof
of equivalence to natural language. Later discoveries can reopen it explicitly.

## 4. Construct and review the global plan

For every required node, assign declaration(s), module, dependency order, reuse
strategy and obligation owner. Plan all supporting result statements as well as
the target. Keep related lemmas together in Proofs modules.

Map each owned node to explicit exported declarations. Separately map every
required convergence result to one public unit with its exact result, spec,
budget and setup unit. Raw analytic proof ownership can stay in Proofs; its
mapped public wrapper owns no duplicate graph node or clause. Every public unit
must occur in this mapping. Verify the result/module/setup counts before review.

Record complete source hypotheses and parameter identities for each result.
For each shared setup, give identical contexts or explicit equivalence witnesses
for every consumer. Different hypotheses cannot be silently merged into a
stronger shared setup. Correspondence witnesses belong to the public result's
dependency closure and receive ordinary theorem review/proof verification.

Use auto-math's exact existing interfaces and routing. Specify Public versus
Params information; valid/admissible/successful/allowedAlgorithm; query/reply/output;
state, initialization, update and output; explicit public budget and result.

Check that the source method is actually pinned, rather than approving any
existential algorithm. Record the correspondence between source iterations and
primitive queries, batching, selected/averaged/last output, probability laws,
epsilon conventions and horizon quantifiers. A source result or transport lemma
needed to prove the final Convergence export belongs in Proofs with a reviewed
statement. No parallel public API or mandatory duplicate theorem wrappers.
Record the headline quantity's expression, units and mathematical domain
separately from the template's Fin spec.numOracles → Nat call budget. Record every
oracle's component, routing and budget-exhaustion behavior. If quantities differ, plan
an explicit correspondence theorem; preserve the source's primary guarantee in
the setup/success/output or supporting theorem as appropriate. Check the
actual claimed execution relation, not merely a definition of a bound.

Record all deferred obligations and where the final composition will enforce
them. The plan cannot silently alter the graph: revise and re-review the graph
first if its mathematical contract changes.

Exit: PLAN_ACCEPTED with complete ownership and no unresolved semantic blocker.

## 5. Plan each layer and retrieve usable Lean declarations

For each unit, inspect accepted local oracle declarations and pinned Mathlib.
Use LeanSearch for discovery and local Lean/source inspection for actual types,
definitions, instances and hypotheses. Check argument use at the intended site.
Inspect near matches and refine searches before choosing reuse, adaptation or new
construction. A miss or service failure is not proof that a declaration is absent.

The detailed plan includes exact declaration interfaces, domain/edge decisions,
imports, selected providers, construction steps and semantic review obligations.
Reusing a theorem avoids reproving it when valid, but does not skip the source
correspondence gate for the use being formalized.

## 6. Generate and validate statements

Formalize dependencies before consumers. Implement complete definitions and
algorithms; write each required theorem/lemma statement with a registered
`:= by sorry` body. Do not use placeholders in computational definitions.

Compile under auto-math's pinned environment and inspect the elaborated
declarations independently of the Formalizer's proposed mappings. Inventory
types/binders/instances, assumptions, conclusions, operation applications,
definition bodies and relevant provider meanings. Do not use unfinished proof
bodies as semantic evidence.

Use the bidirectional gate for every mathematical unit, including all source
theorem dependencies and any new adapter lemmas. Review reused declarations in
their actual applications. The gate requires:

1. All source obligations covered by the intended formal components.
2. All substantive formal components justified by source/derived interpretation.
3. Correct objects, domains, quantifiers, constants, operations and argument scope.
4. Exact algorithm behavior, permitted information, randomness, output and costs.
5. Definedness and boundary behavior consistent with the accepted contract.
6. Accepted dependencies, current compiler/provider evidence and valid citations.
7. No substantive mismatch or unresolved uncertainty.

Every applicable score/check must pass. A numerical average cannot compensate
for failure. Informational observations are separate from blockers. Source
evidence, compiler evidence and structural plan evidence have distinct roles.

Reuse focused packets for local checks; allow explicit expansion to broader
source/provider context. Deduplicate provider definitions while retaining each
meaningful application and its arguments. No exhaustive model call per compiler
plumbing constant.

## 7. Review composition and freeze

Rebuild the assembled modules. Inspect actual final types and dependencies.
Discharge every deferred obligation; reconcile source cases and theorem-group
relationships. All supporting statements and the main result must be accepted.
Recompute the complete catalog and match it bijectively to the reviewed public
result inventory, including setup associations. Inspect every node/declaration
mapping, shared-setup compatibility and cost correspondence witness against the
actual elaborated inventory. These checks are mandatory before freezing.

Freeze the exact source/graph/plan revisions, repository/toolchain/dependency
basis, theorem and lemma types, setup fields, definitions, algorithm behavior,
budget, imports and instances. Record each declaration's editable proof-body
span and the Reviewer acceptance for this exact candidate.

Exit: STATEMENTS_ACCEPTED. Expected registered sorry holes remain; no claim of
proof completion or suitability for the proved-result catalog is made.

## 8. Plan and fill proofs separately

Follow the proof dependency order. Read the source proof and inspect available
proved local/library lemmas. Plan applications and intermediate steps, then
replace the current registered proof body. Compile incrementally.

Source theorems discovered during proof work must first pass the same graph,
statement and semantic process. Do not hide an unreviewed source theorem as a
local have merely to avoid review. New purely internal proof facts may be local
have statements, proved in Lean, without a semantic LLM gate.

Maintain unit statuses separately. A consumer can compile against a frozen sorry
dependency during work, but it is not PROVED until its transitive dependencies
are free of admissions. Prefer completing dependencies before the consumer.

If a new top-level helper, import or changed statement is essential, record the
reason and reopen only the affected statement closure. Renew its semantic review
and freeze. Preserve unaffected work. No silent changes outside proof spans.

## 9. Verify completed output

Check frozen source regions and elaborated interfaces/providers for changes.
Run the required repository build and explicit Comparator mode for public results.
Audit all delivered declarations, including auxiliary results, for transitive
axioms. Only propext, Classical.choice and Quot.sound are permitted. Verify no
unfinished bodies or custom axioms remain.

Enforce the exact output contract in AGENTS.md: UpperCamelCase paths, the
original template interfaces and namespace/spec/budget/result conventions.
Run the pinned repository's actual theorem extractor and BudgetLatex renderer
for every public module, including reused public results. Require exactly the
planned result, matching setup/namespace and one successfully rendered budget.
This check also runs before public statement review, so unsupported notation is
repaired before freeze. A failed final check prevents completion and export.
Save catalog rows and extractor/renderer hashes in final verification; do not
omit the source inventory, public-result mapping and validated counts from the
completion artifact. Final checks repeat the aggregate bijection and confirm
that all cost/setup correspondence witnesses are actual theorem declarations.
Do not
generate or publish website metadata as part of compatibility checking.
Keep existing core files unchanged. Report
exact files, source coverage, verification results and any remaining source
interpretation limits. Do not commit, push or publish a website without authority.

Exit: PROVED only when the entire required result closure passes. A supported
restricted variant has a separate status and cannot close the original target.

## Checkpoints and repairs

Save a checkpoint after every accepted unit, review, repair and proof completion:
current source/target identity, candidate revision, graph, plans, declaration
inventory, reviews, compiler observations, frozen regions, open findings, recent
repair causes and next concrete action. Exclude private reasoning transcripts
from review packets. Never accept truncated or interrupted model output.

Bind caches to actual source/target, dependency, candidate, policy and environment
identities. Resume the failed stage of a valid checkpoint; do not replay known
failed drafts or rerun unrelated accepted units. A changed node invalidates its
affected descendants, not the entire unrelated project.

Runs are bound to the exact controller and policy hashes. Preserve the complete
old workflow directory before upgrading contracts if old runs must remain
loadable. Resume or export those runs with their preserved controller; do not
rewrite completed artifacts or reinterpret an old accepted graph as satisfying
a newer inventory schema.
