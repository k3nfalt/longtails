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
actual template and renderer source in repository_interfaces and the complete
OUTPUT_CONTRACT.md in policy. The contract includes the exact imported Lean API,
construction templates and all output requirements; no external examples or
repository-root instructions are required to determine them.

Inspect the actual repository revision, worktree state, supplied workflow policy
and interface source, toolchain, manifest and verification scripts. Consult
library modules for reuse only, not for unstated output/style requirements.
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

Use the Lean templates and field rules in the supplied OUTPUT_CONTRACT.md. Record
each parameter's mathematical role and public/hidden status, explicit tuning
dependencies, the visible accuracy criterion, actual output selection, inline
budget components and the derivation from the source rate. Put these designs in
the existing unit detail/adaptation/deferred-obligation fields. A free sufficient
horizon is not an explicit complexity formula; an unmet tuning/work implication
is not a substitute for output accuracy. Keep the exact source statement in
reviewed supporting lemmas and prove the adaptation. Resolve genuine source/API
incompatibilities before plan acceptance without silently changing the source.
The four output:parameter_roles, output:accuracy_contract, output:explicit_budget
and output:source_adaptation checks are mandatory for every public node at plan,
public statement and composition review.

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

Run aggregate style, elaboration, declaration lint, catalog/rendering, interface
and topology checks before composition review. Bind the results in the immutable
statement-validation receipt. Inspect actual final types and dependencies.
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

Require the exact statement-validation receipt accepted at composition and
bound into the freeze. Verify source preservation outside registered proof slots
and frozen declaration signatures before carrying its catalog rows, renderer hashes,
interface/topology evidence and validated counts into final verification. The
statement-only checks already passed in steps 6 and 7. Full proof Comparator,
strict warning-free build and transitive axiom audit run here because they require
completed proofs. Native lint is a proof-change regression, not a first statement
format check. A failed final check prevents completion and export.
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

Develop controller changes in one isolated candidate from an exact live baseline.
Use one writer per file; coordinate ownership before any delegated edits. Test the
earliest failure boundary of every gate and the order of downstream actions.
Before deployment, hold the workflow upgrade lock and existing run locks, compare
all live workflow hashes against the baseline, and abort on concurrent edits.
Preserve the old controller, accepted run/state/source artifacts and exports; apply
only reviewed changed files atomically with rollback on validation failure. Never
reset unrelated work or migrate accepted runs by editing their state hashes.

Runs are bound to the exact controller and policy hashes. Preserve the complete
old workflow directory before upgrading contracts if old runs must remain
loadable. Resume or export those runs with their preserved controller; do not
rewrite completed artifacts or reinterpret an old accepted graph as satisfying
a newer inventory schema.

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
