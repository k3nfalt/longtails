# Explicit LongTails output contract for autoformalization

This is normative workflow policy, supplied in full to both agents in every task
packet. Together with the other supplied workflow policies, it states the output
requirements completely. Do not infer requirements from repository-root
AGENTS.md, the research prompt, a README, the tutorial, or existing results.
Library retrieval is for exact declarations and reusable mathematics, not for
discovering unstated conventions. The user selects a source theorem; this
workflow formalizes it and proves its adaptation to this public interface. It
does not search for a different algorithm or an improved research result.

## 1. Exact imported interface

The following is the complete interface currently used by the workflow. It is
reference code: import `LongTails.Template` in delivered modules; do not redeclare
these structures. The controller checks this block against the actual pinned
`repository_interfaces["LongTails/Template.lean"]` before issuing task packets.
A mismatch is an interface-version error requiring a workflow contract update,
not permission to edit the project's template or ignore the mismatch.

<!-- BEGIN PINNED TEMPLATE -->
```lean
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

namespace OracleTemplate

universe uP uD uI uQ uR uO

structure Algorithm (Query : Type uQ) (Reply : Type uR) (Output : Type uO) (numOracles : ℕ := 1) where
  Seed : Type := Unit
  [seedSpace : MeasurableSpace Seed]
  law : ProbabilityMeasure Seed := by exact ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
  State : Type (max uQ uR uO)
  initial : Seed → State
  query : State → Fin numOracles × Query
  update : State → Reply → State
  output : State → Output

attribute [instance] Algorithm.seedSpace

structure Oracle (Query : Type uQ) (Reply : Type uR) (numOracles : ℕ := 1) where
  Seed : ℕ → Type := fun _ => Unit
  [seedSpace : ∀ k, MeasurableSpace (Seed k)]
  law : ProbabilityMeasure ((k : ℕ) → Seed k) := by
    exact ⟨MeasureTheory.Measure.dirac (fun _ => ()), inferInstance⟩
  answer : (k : ℕ) → (Fin numOracles × Query) → Seed k → Reply

attribute [instance] Oracle.seedSpace

private def _run
    {Query : Type uQ} {Reply : Type uR} {Output : Type uO}
    {numOracles : ℕ}
    (oracle : ℕ → (Fin numOracles × Query) → Reply)
    (A : Algorithm Query Reply Output numOracles) :
    Nat → Nat → (Fin numOracles → ℕ) → A.State → Output
  | 0, _, _, state => A.output state
  | k + 1, call, remaining, state =>
      let query := A.query state
      if remaining query.1 = 0 then A.output state
      else
        let reply := oracle call query
        let remaining := Function.update remaining query.1 (remaining query.1 - 1)
        _run oracle A k (call + 1) remaining (A.update state reply)

def execute
    {Query : Type uQ} {Reply : Type uR} {Output : Type uO}
    {numOracles : ℕ}
    (oracle : Oracle Query Reply numOracles) (A : Algorithm Query Reply Output numOracles)
    (budget : Fin numOracles → ℕ) (seed : A.Seed := by exact ())
    (oracleSeed : (k : ℕ) → oracle.Seed k := by exact fun _ => ()) : Output :=
  _run (fun k query => oracle.answer k query (oracleSeed k))
    A (∑ i, budget i) 0 budget (A.initial seed)

structure Setup where
  numOracles : ℕ := 1
  Params : Type uP
  Public : Type uD
  Instance : Public → Type uI
  Query : Public → Type uQ
  Reply : Public → Type uR
  Output : Public → Type uO
  publicInput : Params → Public
  valid : Params → Prop
  admissible : (p : Params) → Instance (publicInput p) →
    Oracle (Query (publicInput p)) (Reply (publicInput p)) numOracles → Prop
  successful : {Ω : Type} → [MeasurableSpace Ω] →
    (p : Params) → Instance (publicInput p) →
    (Ω → Output (publicInput p)) → ProbabilityMeasure Ω → Prop
  allowedAlgorithm : (p : Public) → Algorithm (Query p) (Reply p) (Output p) numOracles → Prop :=
    fun _ _ => True

def Convergence (S : Setup)
    (budget : S.Params → Fin S.numOracles → ℕ) : Prop :=
  ∃ makeAlgorithm : (p : S.Public) → Algorithm (S.Query p) (S.Reply p) (S.Output p) S.numOracles,
    (∀ p, S.valid p →
      ∀ (I : S.Instance (S.publicInput p))
        (oracle : Oracle (S.Query (S.publicInput p)) (S.Reply (S.publicInput p)) S.numOracles),
        S.admissible p I oracle →
          let A := makeAlgorithm (S.publicInput p)
          let result := fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
            execute oracle A (budget p) seed.1 seed.2
          S.successful p I result
            ⟨(A.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩) ∧
    ∀ p, S.valid p → S.allowedAlgorithm (S.publicInput p) (makeAlgorithm (S.publicInput p))

end OracleTemplate
```
<!-- END PINNED TEMPLATE -->

## 2. File and declaration templates

Generate only `outputs/{Algorithms,Setups,Proofs,Theorems}/Name.lean` modules.
Use UpperCamelCase module filenames and new directory names. Copied library
dependencies retain their original namespaces and are read-only. Do not create
an alias library, a `Formalized` namespace, or a parallel public theorem API.
Group related supporting lemmas into cohesive modules. Do not add explanatory
Lean comments/docstrings unless the user requests them; keep source evidence,
design decisions and reviews in run artifacts. Do not publish, commit or push.

The angle-bracket tokens below are explicitly schematic substitution positions,
not Lean syntax to submit. Replace every token with reviewed, concrete Lean.
Do not substitute an opaque helper for an expression required to be inline.

```lean
-- outputs/Setups/<Name>.lean
import LongTails.Template
import outputs.Algorithms.<Method>

namespace outputs.Setups.<Name>
open OracleTemplate MeasureTheory

structure Params where
  <problem class constants, accuracy, initial data and type instances>

structure Public where
  <exactly the inputs legitimately available to the algorithm>

def publicInput (p : Params) : Public := <explicit projection or derived inputs>

noncomputable abbrev spec : Setup where
  numOracles := <number of separately counted oracle IDs>
  Params := Params
  Public := Public
  Instance p := <hidden instance type>
  Query p := <query type>
  Reply p := <reply type>
  Output p := <returned object type>
  publicInput := publicInput
  valid p := <parameter domain>
  admissible p I O := <instance and oracle assumptions>
  successful p I output P := <explicit output criterion and needed regularity>
  allowedAlgorithm p A := <source algorithm family restriction>

end outputs.Setups.<Name>
```

```lean
-- outputs/Algorithms/<Method>.lean
import LongTails.Template

namespace outputs.Algorithms.<Method>
open OracleTemplate MeasureTheory

noncomputable def algorithm (p : <public input type>) :
    Algorithm (<Query p>) (<Reply p>) (<Output p>) <numOracles> where
  Seed := <private randomness type; Unit for a deterministic method>
  seedSpace := <measurable space instance>
  law := <probability law of private randomness>
  State := <state including all output-selection memory>
  initial seed := <initial state>
  query state := (<oracle ID>, <query computed from state>)
  update state reply := <actual source update and memory update>
  output state := <named returned object extracted from state>

end outputs.Algorithms.<Method>
```

Place shared public input types in the algorithm module or a shared definition
module when necessary to avoid an import cycle; the setup can refer to that
type. Every component must use the same reviewed parameter mapping. The agent
must supply actual definitions, not the schematic tokens above.

```lean
-- outputs/Theorems/<Name>.lean
import outputs.Setups.<Name>
import outputs.Proofs.<Name>Convergence

namespace outputs.Theorems.<Name>
open OracleTemplate

noncomputable def budget : (let S := outputs.Setups.<Name>.spec; S.Params → Fin S.numOracles → ℕ) := fun p i => <one explicit formula in the setup parameters for oracle i>

theorem result : Convergence outputs.Setups.<Name>.spec budget := by
  refine ⟨<algorithm factory on Public>, ?_, ?_⟩
  · intro p hp I O hadm
    <prove successful for the actual execute output and its product law>
  · intro p hp
    <prove allowedAlgorithm for the same algorithm factory>

end outputs.Theorems.<Name>
```

The setup namespace must equal its module path. Public result and budget share
their module namespace. Import the setup directly and name its fully qualified
`spec` in `result`. Each Theorems module has exactly one main `result`; supporting
rate inequalities and algebraic lemmas belong in Proofs. Preserve the public
inventory bijection: do not silently discard a required source convergence case.
Registered proposition bodies may be `by sorry` only during statement mode;
concrete definitions and algorithms must be complete even then. Completion
requires every proof, including all support, to be free of admissions.

## 3. Meaning of every field

- `Params`: problem-class constants, requested accuracy and initial data, plus
  explicitly justified method-family settings. Classify every field as problem
  data, accuracy, known input, analysis-only bound, or fixed family setting.
  Derived tuning and derived execution counts must never be Params fields:
  compute them in publicInput or the algorithm using named definitions in Algorithms.
  Do not put an arbitrary sufficient call count in Params to
  avoid deriving complexity. No field may encode the conclusion as an assumption.
- `Public` and `publicInput`: the algorithm receives only these inputs, not I or
  O. Record how every tuning expression depends on allowed known information.
  A computed tuning in publicInput is permitted; a hidden exact objective gap,
  unknown minimizer, future trajectory statistic or unknown oracle law is not
  automatically available. Analysis parameters may remain outside Public.
- `Instance`: the hidden function, component functions, operator, constraints,
  or other source object. Do not leak it into Public merely to simplify proofs.
- `Query` / `Reply`: give the exact information in one call. Distinguish a single
  gradient sample, a mini-batch, all-worker replies, values, Hessians, projections
  and event queries. Declare the unit rather than calling all of them gradients.
- `Output`: return the object promised by the accuracy criterion: a point, a
  feasible pair or a justified certificate. Internal trajectories belong in the
  algorithm/proof layer. An existence claim for a good iterate is not an output
  selector; prove the implemented selector uses only available replies.
- `valid`: positivity, dimensions, probability ranges and parameter-domain
  restrictions justified by the source. Do not hide `requiredWork ≤ p.K` here
  instead of substituting a derived horizon into the algorithm and budget.
- `admissible`: the source assumptions on I and O, including the oracle's
  mathematical relationship to I. Use inequalities for supplied upper bounds;
  justify exact equalities or show the required equivalence. Do not assume a
  convergence conclusion, execution correspondence or cost bound to prove it.
- `successful`: the explicit output accuracy and any necessary feasibility,
  measurability and integrability. It must not require the reader to unpack a
  setup-local `Guarantee` bundling descent estimates and conditional tuning
  corollaries. Numerical definitions and ordinary reusable mathematical
  predicates may be named, but keep the accuracy inequality visible inline.
  Put intermediate estimates in Proofs. If a source headline also promises time
  or communication, state that additional criterion explicitly and separately;
  a genuinely needed point-and-cost output is allowed.
- `allowedAlgorithm`: pin the source method using equality to the concrete tuned
  algorithm, or a precise family predicate with justified existential settings.
  A fixed user-requested method-family setting is allowed; do not leave derived
  tuning unspecified. Default True is allowed only if the requested source claim
  is genuinely existence of an unrestricted algorithm, with that choice reviewed.
- `budget`: a vector of natural-number call limits, one per declared oracle ID.
  Supply an explicit, human-readable formula derived from the source bound.
- `Convergence`: one factory from Public must work for every valid p and every
  admissible I/O. Prove success for its actual execution AND membership of that
  same factory in the allowed family. Do not replace this type with a look-alike.

## 4. Success templates in Lean

Choose the source's actual accuracy and probability mode. These are schematic
clauses to instantiate, not assumptions authorizing a different norm or metric:

```lean
-- Expected squared-gradient accuracy (epsilon is the gradient-scale target).
successful p f output P :=
  Measurable output ∧
  Integrable (fun ω => ‖gradient f (output ω)‖ ^ 2) (P : Measure _) ∧
  (∫ ω, ‖gradient f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε ^ 2

-- Expected function gap: p.xstar is an analysis-only reference point.
-- admissible must include IsMinOn f Set.univ p.xstar and the source gap bound.
successful p f output P :=
  Measurable output ∧
  Integrable (fun ω => f (output ω) - f p.xstar) (P : Measure _) ∧
  (∫ ω, f (output ω) - f p.xstar ∂(P : Measure _)) ≤ p.ε

-- Deterministic guarantee for every seed; use the source's chosen norm.
successful p f output _ := ∀ ω, ‖gradient f (output ω)‖ ≤ p.ε

-- Almost-sure guarantee, distinct from a pointwise guarantee.
successful p f output P :=
  ∀ᵐ ω ∂(P : Measure _), ‖gradient f (output ω)‖ ≤ p.ε

-- High-probability guarantee; prove the event's required measurability.
successful p f output P :=
  Measurable output ∧
  (P : Measure _) {ω | p.ε < ‖gradient f (output ω)‖} ≤ ENNReal.ofReal p.δ
```

For the last template valid must include `0 < p.δ ∧ p.δ < 1`, and admissible or
proved regularity must establish measurability of the event. For any integral,
prove the necessary integrability; a totalized integral must not produce a
vacuous accuracy claim. Gradient/fderiv/infimum notation requires its intended
differentiability/boundedness/nonemptiness hypotheses or corresponding proofs.
Keep `≤ p.ε` instead of `≤ p.ε ^ 2` when the source defines ε as the
squared-gradient tolerance; record the convention, do not silently change it.

For minimizer-based accuracy, put the reference `xstar` in analysis-only Params
and `IsMinOn f Set.univ p.xstar` in admissible. Exclude it from Public unless the
source explicitly supplies it to the method. Do not introduce minimizer existence
inside successful. If the source only assumes a lower bound/infimum, retain that
criterion with its boundedness conditions; do not add attainment as an assumption.

Do not write `successful := enoughCalls → accuracy` or
`successful := tuningEquality → accuracy` to bypass tuning or budget obligations.
Do not erase a conditional source hypothesis either. Derive its discharge in the
advertised domain or record the specific interface incompatibility at plan time.
Ordinary implications defining mathematical objects, such as proximal maps, are
permitted with the necessary existence facts; syntax alone is not a defect.

## 5. Budget and tuning templates in Lean

The exact budget type is:

```lean
(let S := outputs.Setups.<Name>.spec; S.Params → Fin S.numOracles → ℕ)
```

For one oracle, ignore its unique ID and expand the proved sufficient count:

```lean
noncomputable def budget : (let S := outputs.Setups.<Name>.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => <explicit sufficient natural-number expression>
```

For multiple oracles, give every component explicitly. For example, a two-oracle
budget may have the following shape when the source analysis proves these costs:

```lean
noncomputable def budget : (let S := outputs.Setups.<Name>.spec; S.Params → Fin S.numOracles → ℕ) := fun p i => if i.val = 0 then <explicit oracle-zero count> else <explicit oracle-one count>
```

The following numerical example illustrates explicit tuning and counting for a
specific stochastic squared-gradient analysis. It is NOT a universal rate or
permission to import its assumptions into a different source theorem:

```lean
structure ExampleParams where
  L : ℝ
  Δ : ℝ
  σ : ℝ
  ε : ℝ

noncomputable def exampleStep (p : ExampleParams) : ℝ :=
  1 / (p.L + 2 * p.L * p.σ ^ 2 / p.ε ^ 2)

noncomputable def exampleHorizon (p : ExampleParams) : ℕ :=
  ⌈4 * p.L * p.Δ / p.ε ^ 2 + 8 * p.L * p.Δ * p.σ ^ 2 / p.ε ^ 4⌉₊ + 1

noncomputable def exampleBudget : ExampleParams → Fin 1 → ℕ := fun p _ => ⌈4 * p.L * p.Δ / p.ε ^ 2 + 8 * p.L * p.Δ * p.σ ^ 2 / p.ε ^ 4⌉₊ + 1
```

The algorithm may reuse named tuning definitions; the public budget must expand
its formula rather than return `horizon p`. In the example the required domains
are L>0, Δ≥0, σ≥0, ε>0 and the criterion is expected squared gradient ≤ε².
For an actual public export use the spec-based type above, not ExampleParams.

Unacceptable ways to evade the explicit complexity requirement include:

```lean
fun p _ => p.K
fun p _ => p.T * p.B
fun p _ => p.calls
```

These are mathematically functions of parameters, but when those fields are free
execution counts they state no derived accuracy complexity. Renaming a free
count, hiding it in a helper, or adding an unused epsilon term does not repair it.
First derive tuning/horizon/batch size as functions of the reviewed inputs, then
expand the actual count. An unnecessary free `extra` count belongs in a general
supporting lemma; specialize it in the public complexity result. A legitimate
source-prescribed family setting must be explicitly justified in the plan and
its remaining effect on the budget explained.

For an imported source inequality `error(K) ≤ bound(p,K)`:

1. Preserve the source inequality as a reviewed supporting lemma.
2. Solve for a concrete K, step size and batch size in the admitted domain.
3. Prove tuning legality and `bound(p,K) ≤ target(p)` including rounding/zero cases.
4. Implement the output selection and prove its accuracy with the source law.
5. Relate K to actual per-oracle execution counts, including initialization,
   batching, rejected queries, validation, and all other charged calls.
6. Write those counts inline in the public budget and prove the Convergence wrapper.

Count in the declared unit. If one answer contains S primitive samples, prove
the conversion before advertising a sample bound; arbitrary batches without an
upper size bound do not give a primitive-cost bound. Keep time, communication
and expectation bounds separate from the hard Nat execution budget.
For indexed budgets prove routing and stopping correspondence: execute stops
when the next selected component is empty, even if others are nonempty.
Increasing a budget requires proof at that budget or output stability; success
is not generally monotone in the number of updates.

Simplify the final expression while preserving every required term and the source
claim. A supported constant-factor larger execution budget is allowed only with
a proof that it suffices and does not change a source constant that must remain
exact. Render every component with the pinned BudgetLatex; readability is a
separate semantic review, not a consequence of fitting on one line.

## 6. Probability and information requirements

For stochastic-gradient access state joint measurability of `Function.uncurry g`,
pointwise integrability, vector unbiasedness `∫ ξ, g x ξ ∂μ = gradient f x`, and
integrable variance with `∫ ξ, ‖g x ξ - gradient f x‖ ^ 2 ∂μ ≤ σ ^ 2` when these
are the source assumptions. Use a ProbabilityMeasure or IsProbabilityMeasure.
For IID source samples require measurable sample maps, `iIndepFun`, and the
correct marginal pushforwards under an abstract ambient law. Derive finite-prefix
product laws internally; do not restrict the source to a finite sample space or
prescribe a product ambient law merely to ease proof. For other noise models,
encode the actual source dependence instead of imposing IID.

Use explicit measure arguments `∂P` in every public expectation. Do not use
`letI : MeasureSpace ...` to choose a hidden distribution, and do not introduce
custom expectation/averaging wrappers such as `expected` or `sampleMean` to hide
the public accuracy expression. Name local step size, initial gap and iteration
count `η`, `Δ`, and `K` respectively, where those quantities occur. Reuse their
definitions in the algorithm and proof; keep the public budget formula expanded.

For IID samples reuse this exact existing declaration, importing
`LongTails.Setups.StochasticGeneralizedSmoothAndConvex`; do not redeclare IID:

```lean
-- Existing API, shown completely as reference, not code to redeclare.
structure IID {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (ξ : ℕ → Ξ → Ω) (p : Measure Ω) (P : Measure Ξ) : Prop where
  measurable : ∀ k, Measurable (ξ k)
  independent : ProbabilityTheory.iIndepFun ξ P
  marginal : ∀ k, P.map (ξ k) = p
```

Use the fully qualified type in assumptions:

```lean
(h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
```

Here Ω is the single-sample space, Ξ the ambient space, ξ the sample maps,
p their common marginal measure, and P the ambient measure. Supply the source's
probability-measure instances explicitly. The fields are accessed as
`h_samples.measurable`, `h_samples.independent`, and `h_samples.marginal`.
This requirement does not impose IID on a source with dependent noise.

Convergence uses the product of the algorithm's seed law and the oracle tape law;
check that this independence matches the source. An average expected rate can be
converted using an independent uniform output index with a proved law. A best
iterate selector must use accessible replies; stochastic gradients are not exact
gradient norms. Distinguish pre-update, post-update, last and average iterates,
and count any extra evaluation needed to select or certify the output.

## 7. Source preservation and interface incompatibility

Source fidelity and this public structure are separate mandatory obligations.
Moving a raw analytic statement into Proofs does not authorize dropping it from
the reviewed dependency graph. Record each public wrapper's derivation from its
source owner, and preserve all required cases and the public inventory mapping.
Routine justified algebra, rounding and output transport require no redundant
user confirmation. Never silently strengthen assumptions, change the method, or
assume a trajectory-dependent statistic is a known tuning input.

If a required source result cannot yield this public interface, identify the
exact obstacle before accepting the plan. For example, tuning from an unknown
run-dependent Hessian statistic is not a supplied algorithm. Investigate whether
the source proves an a-priori substitute. If not, report the concrete conflict and
the smallest justified options to the user. Do not disguise an analytic rate as
an accuracy result, invent a global bound, or waive a mandatory public result.
User-approved departures must be recorded in the source contract, plan and review.

## 8. Required plan and review evidence

Use protocol version 3, including `output_contract.schema_version: 3` and the
mandatory `design` record on every public result. PROTOCOL.md supplies every
field and a full JSON shape. Parameter roles, tuning dependencies, selector,
criterion, budget components, boundary proofs and adaptation must be structured
there; free-text construction/adaptation fields supplement rather than replace
these records. Keep cost units and actual correspondence theorem references in
`output_contract.public_results[].cost`. Do not add other unrecognized keys.
These must be concrete designs, not “follow the tutorial” or pointers to examples.

At plan, public statement and composition review, report these additional checks
per public source node. They cannot be marked not_applicable:

- `output:parameter_roles:<node>`: all parameter roles and public/hidden inputs
  are justified; tuning and execution counts are actually derived or the precise
  source-prescribed family settings are justified.
- `output:accuracy_contract:<node>`: the public criterion is visible, describes
  the actual implemented output, retains regularity/feasibility, and has no
  undischarged tuning/work premise masquerading as success.
- `output:explicit_budget:<node>`: the displayed formula derives sufficient
  counts in the declared units; every oracle component, rounding and boundary
  case is covered. Bare counts/helpers or unused accuracy symbols are not evidence.
- `output:source_adaptation:<node>`: identify raw source statements, actual
  adapter declarations and the reason the public contract follows without
  unapproved changes. Preserve source cases and method identity.

At plan time cite source and the concrete design/proof obligations, not imagined
compiler results. At statement/composition time inspect the actual elaborated
definitions, their transitive meanings and displayed catalog; do not use sorry
proofs as evidence. Require match on every mandatory check before freezing.
Unresolved or mismatching cases block acceptance; final proof completion also
requires strict compilation, lint, Comparator and supporting-declaration axiom
audits with only propext, Classical.choice and Quot.sound. Rendering, structural
validation and independent semantic review are distinct; do not claim that the
controller automatically proves human readability or natural-language equivalence.

The controller does not blacklist parameter names: K can be a kurtosis constant,
and T can be a legitimate problem constant. It rejects single-field count-only
arithmetic (including offsets, scaling and natural ceilings), opaque `helper p`
budgets and bare projections/products. Changing K to k or N does not repair
`p.k + 1`, `2 * p.N`, or `⌈p.N⌉₊`. For structured designs, nonconstant components
must depend on an accuracy field unless an exact problem-size cost is explicitly
justified. Every field labeled accuracy must also appear in the declared success
criterion. Simple zero-multiplication decorations are ignored. An exact
accuracy-independent cost such as `p.n * p.m` is allowed only when every referenced
field is classified as problem_data and its component has an explicit
accuracy_independent_reason and named proof obligations. Constant initialization
components similarly need an accuracy-independent justification and proofs.
These are narrow mechanical checks, not a complete semantic decision procedure.
Parameter roles and accuracy_independent_reason are claims from the Formalizer,
not trusted facts. The reviewer must establish them from the source assumptions,
actual valid/admissible predicates, algorithm control flow and cost correspondence.
A field used only as a free horizon cannot be justified by calling it problem_data
or family_setting. Likewise, an accuracy-independent reason plus a theorem name
does not prove that a field measures an external problem size. Require the actual
source relationship and the theorem's relevant statement; report unresolved if
it cannot be established. These semantic facts cannot be decided from a formula
or identifier spelling alone. All rules about hidden counts and decorative
accuracy continue to apply, including disguises outside the lint's narrow scope.

Write the complete budget lambda using binder `p` for Params in the design and
in Lean. Their expressions must agree modulo whitespace/comments. Components
list every oracle in order; `uses` lists exactly the `p.field` dependencies of
each expression. The algorithm's derived tuning can use only parameters marked
public. At public statement/composition review the actual Params structure fields,
definition identities and theorem witness kinds are checked against the design.
These statement checks run before semantic statement review and again at
composition, before freezing. Native text/style lint runs before elaboration; native
declaration lint runs immediately after elaboration. A source-bound validation
receipt is mandatory for freeze. Final verification checks proof-only source and
signature preservation before carrying the receipt's results forward; it does not
defer statement defects to the completed-proof stage.

Review packets supply source snapshots for the complete unit prerequisite closure,
including indirect Algorithms modules. Compiler inventories are deduplicated:
names resolve through declaration_evidence to immutable JSON records in objects/.
Each reference includes its absolute path and content hash. Read the full referenced
record whenever its inline preview is insufficient; verify its SHA-256 against
the canonical JSON content (sorted keys, compact separators, UTF-8, no final LF).
Source snapshots also include the original file-byte SHA-256. Do not substitute
a different live file for reviewed evidence. Unexpanded library dependencies must
be inspected when relevant; report unresolved if sufficient evidence is unavailable.
Match verdicts on the four output checks must cite the corresponding
candidate/interface_evidence/results/<node> pointer (or a descendant), and explain
the relevant source and declaration evidence. Missing evidence is not a match.
Packets are checked in their UTF-8 pretty-printed form, including the full task
envelope and policy, and must be strictly below 64,000,000 bytes. Oversize packets
fail closed; evidence is never silently truncated to satisfy the size limit.
