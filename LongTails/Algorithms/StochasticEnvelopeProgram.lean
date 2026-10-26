import LongTails.Algorithms.StochasticEnvelopeLocalization
import LongTails.Algorithms.QueryPlan
import Mathlib.Probability.Distributions.Geometric

namespace LongTails.Algorithms.StochasticEnvelopeProgram

open OracleTemplate

noncomputable def levelProbability (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) : unitInterval :=
  ⟨1 / 2 + t / 16, by constructor <;> linarith⟩

noncomputable def levelLaw (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    MeasureTheory.ProbabilityMeasure ℕ :=
  ⟨ProbabilityTheory.geometricMeasure (levelProbability t ht ht1), inferInstance⟩

variable {Q R U : Type*}

def slotCalls (cost : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, slot => slotCalls cost n (slot + 1) + cost slot

def slotPlan (cost : ℕ → ℕ) (step : (i : ℕ) → U → QueryPlan Q R U (cost i)) :
    (n slot : ℕ) → U → QueryPlan Q R U (slotCalls cost n slot)
  | 0, _, state => .done state
  | n + 1, slot, state => (step slot state).bind (slotPlan cost step n (slot + 1))

noncomputable def algorithm {S : Type} [MeasurableSpace S]
    (law : MeasureTheory.ProbabilityMeasure S) (q0 : Q) (u0 : U)
    (program : S → Σ k, QueryPlan Q R U k) : Algorithm Q R U where
  Seed := S
  law := law
  State := Σ k, QueryPlan Q R U k
  initial := program
  query state := (0, QueryPlan.query q0 state)
  update := QueryPlan.update
  output := QueryPlan.output u0

section LocalizationPlans
open OracleTemplate
variable {Q R U : Type*}

def castPlan {k m : ℕ} (h : k = m) (plan : QueryPlan Q R U k) : QueryPlan Q R U m :=
  h ▸ plan

def collectPlans {k : ℕ} : (n : ℕ) → (Fin n → QueryPlan Q R U k) →
    QueryPlan Q R (Fin n → U) (k * n)
  | 0, _ => .done Fin.elim0
  | n + 1, plans => (plans 0).bind fun value =>
      (collectPlans n (fun i => plans i.succ)).map (fun values i => Fin.cases value values i)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def clippedPlan (Λ D C μ : ℝ) (center anchor : E) :
    (K : ℕ) → QueryPlan E E (ℕ × E × E) K
  | 0 => .done (0, anchor, anchor)
  | K + 1 => castPlan (Nat.add_comm 1 K) ((clippedPlan Λ D C μ center anchor K).bind
      fun state => .ask (Gradient.acceleratedQuery state) fun reply =>
        .done (HeavyTailedMarkovGradient.projectedClippedUpdate Λ D C anchor state
          (reply + μ • (Gradient.acceleratedQuery state - center))))

noncomputable def stagePlan (L μ p s a U D : ℝ) (center anchor : E)
    (K replicas : ℕ) : QueryPlan E E E (K * (replicas + 1)) :=
  let σ := s + a * μ * U + 2 * a * L * D
  let e := μ * D ^ 2 / 131072
  let Λ := 2 * (L + μ) + e * (K : ℝ) ^ 2 / (16 * D ^ 2)
  let C := 4 * (L + μ) * D + e / D * (256 * σ * D / e) ^ (p / (p - 1))
  (collectPlans (replicas + 1) (fun _ =>
    (clippedPlan Λ D C μ center anchor K).map (fun state => state.2.1))).map
      MultiplicativeRobustEstimator.medoid

noncomputable def refinePlan (L μ p s a U n : ℝ) (center start : E)
    (K replicas : ℕ) : (J : ℕ) → QueryPlan E E E (K * (replicas + 1) * J)
  | 0 => .done start
  | J + 1 => castPlan (by ring : K * (replicas + 1) + K * (replicas + 1) * J =
      K * (replicas + 1) * (J + 1))
      ((refinePlan L μ p s a U n center start K replicas J).bind fun anchor =>
        let D := U / (2 : ℝ) ^ J
        (stagePlan L μ p s a U D center anchor K replicas).map fun point =>
          if D ≤ (s / μ + a * U) * n ^ (-(p - 1) / p) then anchor else point)


end LocalizationPlans

section Substitution
open OracleTemplate
variable {Q R U A B : Type*}

def substitutePlan (cost : ℕ → ℕ) (child : (i : ℕ) → Q → QueryPlan A B R (cost i)) :
    {k : ℕ} → QueryPlan Q R U k → (slot : ℕ) → QueryPlan A B U (slotCalls cost k slot)
  | _, .done value, _ => .done value
  | _, .ask query next, slot => (child slot query).bind fun reply =>
      substitutePlan cost child (next reply) (slot + 1)


end Substitution

section PilotPlans
open OracleTemplate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def robustPlan (point : E) (b replicas : ℕ) :
    QueryPlan E E E ((b + 1) * 8 * (replicas + 1)) :=
  (collectPlans (replicas + 1) (fun _ =>
    collectPlans 8 (fun _ =>
      castPlan (Nat.one_mul (b + 1))
        (collectPlans (b + 1) (fun _ => (.ask point fun reply => .done reply)))))).map
      StochasticEnvelopePilot.robustMean

noncomputable def pilotPlan (L μ β radius : ℝ) (center : E) (b replicas : ℕ) :
    (N : ℕ) → QueryPlan E E (E × E) ((b + 1) * 8 * (replicas + 1) * N)
  | 0 => .done (center, center)
  | N + 1 => castPlan (by ring : (b + 1) * 8 * (replicas + 1) +
        (b + 1) * 8 * (replicas + 1) * N = (b + 1) * 8 * (replicas + 1) * (N + 1))
      ((pilotPlan L μ β radius center b replicas N).bind fun state =>
        (robustPlan (InexactGradient.query (InexactGradient.momentum (L + μ) μ (2 * β)) state)
          b replicas).map fun reply =>
            let next := StochasticEnvelopePilot.update L μ β center state reply
            (center + clip radius (next.1 - center), center + clip radius (next.2 - center)))

noncomputable def radiusPlan (L μ s β : ℝ) (center : E) (b replicas N : ℕ) :
    QueryPlan E E ℝ ((b + 1) * 8 * (replicas + 1) * (N + 1)) :=
  castPlan (by ring : (b + 1) * 8 * (replicas + 1) * N + (b + 1) * 8 * (replicas + 1) =
      (b + 1) * 8 * (replicas + 1) * (N + 1))
    ((robustPlan center b replicas).bind fun estimate =>
      let S := 4 * (‖estimate‖ + s) / μ
      let radius := 72 * Real.sqrt ((L + μ) / μ) * S
      (pilotPlan L μ β radius center b replicas N).map fun state =>
        2 * ‖center - state.1‖ + 128 * s / μ)

noncomputable def approximatePlan (L μ p s a n β : ℝ) (center : E)
    (b pilotReplicas innerReplicas N K J : ℕ) :
    QueryPlan E E E ((b + 1) * 8 * (pilotReplicas + 1) * (N + 1) + K * (innerReplicas + 1) * J) :=
  castPlan (Nat.add_comm _ _) ((radiusPlan L μ s β center b pilotReplicas N).bind fun U =>
    refinePlan L μ p s a U n center center K innerReplicas J)


end PilotPlans

section DebiasedPlan
open OracleTemplate
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def debiasedValue (v : ℝ) (n : ℕ) (base upper lower : E) : E :=
  base + ((1 - v) ^ n * v)⁻¹ • (upper - lower)

noncomputable def debiasedPlan (v : ℝ) (cost : ℕ → ℕ)
    (plans : (ell : ℕ) → QueryPlan E E E (cost ell)) (n : ℕ) :
    QueryPlan E E E (cost 0 + cost (n + 1) + cost n) :=
  castPlan (by omega : cost n + cost (n + 1) + cost 0 = cost 0 + cost (n + 1) + cost n)
    ((plans 0).bind fun base => (plans (n + 1)).bind fun upper =>
      (plans n).map fun lower => debiasedValue v n base upper lower)


end DebiasedPlan

structure ApproximationTuning where
  beta : ℝ
  block : ℕ
  pilotReplicas : ℕ
  innerReplicas : ℕ
  pilotSteps : ℕ
  innerSteps : ℕ
  stages : ℕ

noncomputable def approximationTuning (κ p a n : ℝ) : ApproximationTuning :=
  let η₀ := (2 : ℝ) ^ (-128 : ℝ) * κ ^ (-12 : ℝ) * a ^ (2 * p) * n ^ (-2 * (p - 1))
  let η₁ := (2 : ℝ) ^ (-32 : ℝ) * a ^ p * n ^ (-(p - 1))
  let N := ⌈17 * Real.sqrt κ * Real.log (1 + 1024 * κ)⌉₊
  let J := ⌈2 * Real.log (1 + n / a)⌉₊
  { beta := 1 / (1024 * κ)
    block := ⌈(1073741824 : ℝ) ^ (p / (p - 1))⌉₊
    pilotReplicas := 7 + ⌈2 * Real.log (1 + (N + 1 : ℝ) / η₀)⌉₊
    innerReplicas := 7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η₁)⌉₊
    pilotSteps := N
    innerSteps := ⌈(268435456 : ℝ) ^ (p / (p - 1)) * (Real.sqrt κ + n + 1)⌉₊
    stages := J }

def ApproximationTuning.calls (c : ApproximationTuning) : ℕ :=
  (c.block + 1) * 8 * (c.pilotReplicas + 1) * (c.pilotSteps + 1) +
    c.innerSteps * (c.innerReplicas + 1) * c.stages

noncomputable def tunedApproximationPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L μ p s a n : ℝ) (center : E) :
    QueryPlan E E E (approximationTuning ((L + μ) / μ) p a n).calls :=
  let c := approximationTuning ((L + μ) / μ) p a n
  approximatePlan L μ p s a n c.beta center c.block c.pilotReplicas c.innerReplicas
    c.pilotSteps c.innerSteps c.stages

noncomputable def tunedEnvelopePlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L μ p s a m v : ℝ) (center : E) (n : ℕ) :
    QueryPlan E E E ((approximationTuning ((L + μ) / μ) p a (m * (2 : ℝ) ^ 0)).calls +
      (approximationTuning ((L + μ) / μ) p a (m * (2 : ℝ) ^ (n + 1))).calls +
      (approximationTuning ((L + μ) / μ) p a (m * (2 : ℝ) ^ n)).calls) :=
  (debiasedPlan v (fun ell => (approximationTuning ((L + μ) / μ) p a (m * (2 : ℝ) ^ ell)).calls)
    (fun ell => tunedApproximationPlan L μ p s a (m * (2 : ℝ) ^ ell) center) n).map
      (fun z => μ • (center - z))

section CursorMachine
variable {Q R U S Ω : Type*}

def statePlan (query : ℕ → U → Q) (update : ℕ → U → R → U) :
    (N call : ℕ) → U → QueryPlan Q R U N
  | 0, _, state => .done state
  | N + 1, call, state => .ask (query call state) fun reply =>
      statePlan query update N (call + 1) (update call state reply)

def cursorCalls (cost : ℕ → S → ℕ) (seeds : ℕ → S) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | N + 1, call, slot => cost call (seeds slot) + cursorCalls cost seeds N (call + 1) (slot + 1)

def cursorRun (cost : ℕ → S → ℕ) (response : ℕ → S → Q → (ℕ → Ω) → R)
    (query : ℕ → U → Q) (update : ℕ → U → R → U) (seeds : ℕ → S) (ξ : ℕ → Ω) :
    ℕ → ℕ → ℕ → ℕ → U → U × ℕ
  | 0, _, _, raw, state => (state, raw)
  | N + 1, call, slot, raw, state =>
      cursorRun cost response query update seeds ξ N (call + 1) (slot + 1)
        (raw + cost call (seeds slot))
        (update call state (response call (seeds slot) (query call state) (fun j => ξ (raw + j))))

end CursorMachine

structure RecoveryTuning where
  accuracyScale : ℝ
  innerSteps : ℕ
  replicas : ℕ
  stages : ℕ

noncomputable def recoveryTuning (L μ p s a U D η : ℝ) : RecoveryTuning :=
  let n := 1 + ((s / μ + a * U) / D) ^ (p / (p - 1))
  let J := ⌈2 * Real.log (1 + n / a)⌉₊
  { accuracyScale := n
    innerSteps := ⌈(268435456 : ℝ) ^ (p / (p - 1)) * (Real.sqrt ((L + μ) / μ) + n + 1)⌉₊
    replicas := 7 + ⌈2 * Real.log (1 + (J + 1 : ℝ) / η)⌉₊
    stages := J }

def RecoveryTuning.calls (c : RecoveryTuning) : ℕ := c.innerSteps * (c.replicas + 1) * c.stages

noncomputable def recoveryPlan {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L μ p s a U D η : ℝ) (center : E) : QueryPlan E E E (recoveryTuning L μ p s a U D η).calls :=
  let c := recoveryTuning L μ p s a U D η
  refinePlan L μ p s a U c.accuracyScale center center c.innerSteps c.replicas c.stages

end LongTails.Algorithms.StochasticEnvelopeProgram
