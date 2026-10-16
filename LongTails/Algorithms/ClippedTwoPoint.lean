import LongTails.Algorithms.Clipping
import LongTails.Algorithms.QueryPlan
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace LongTails.Algorithms.ClippedTwoPoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def directionEstimate (d : ℕ) (τ : ℝ) (u : E) (a : ℝ) : E :=
  ((d : ℝ) * OracleTemplate.clip τ a) • u

noncomputable def estimate (d : ℕ) (τ γ : ℝ) (u : E) (plus minus : ℝ) : E :=
  directionEstimate d τ u ((plus - minus) / (2 * γ))

noncomputable def batchSize (T A α : ℝ) : ℕ := Nat.ceil (T * α / A)

noncomputable def batchWeight (T A α : ℝ) : ℝ := α / (batchSize T A α : ℝ)

noncomputable def batchRecord {N : ℕ} (B : Fin N → ℕ) (j : Fin (∑ i, B i)) : (i : Fin N) × Fin (B i) :=
  finSigmaFinEquiv.symm j


noncomputable def pairPlan (d : ℕ) (τ γ : ℝ) (x u : E) :
    OracleTemplate.QueryPlan E ℝ E 2 :=
  .ask (x + γ • u) (fun plus =>
    .ask (x - γ • u) (fun minus => .done (estimate d τ γ u plus minus)))

noncomputable def batchPlan (d : ℕ) (τ γ : ℝ) (x : E) {B : ℕ} (u : Fin B → E) :
    OracleTemplate.QueryPlan E ℝ E (2 * B) :=
  OracleTemplate.QueryPlan.map (fun values => (B : ℝ)⁻¹ • values.sum)
    (OracleTemplate.QueryPlan.traverse B (fun i => pairPlan d τ γ x (u i)))


noncomputable def acceleratedMix (t : ℕ) (x z : E) : E :=
  ((t : ℝ) / (t + 2)) • x + (2 / (t + 2 : ℝ)) • z

noncomputable def acceleratedUpdate (project : E → E) (h : ℝ) (t : ℕ)
    (state : E × E) (g : E) : E × E :=
  let next := project (state.2 - ((t + 1 : ℝ) / h) • g)
  (acceleratedMix t state.1 next, next)

noncomputable def roundPlan (d : ℕ) (τ γ h : ℝ) (project : E → E)
    (t : ℕ) (state : E × E) {B : ℕ} (u : Fin B → E) :
    OracleTemplate.QueryPlan E ℝ (E × E) (2 * B) :=
  OracleTemplate.QueryPlan.map (acceleratedUpdate project h t state)
    (batchPlan d τ γ (acceleratedMix t state.1 state.2) u)

def solverCalls (B : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * B n + solverCalls B n

noncomputable def solverPlan (d : ℕ) (τ γ h : ℝ) (project : E → E)
    (initial : E × E) (B : ℕ → ℕ) (u : (t : ℕ) → Fin (B t) → E) :
    (n : ℕ) → OracleTemplate.QueryPlan E ℝ (E × E) (solverCalls B n)
  | 0 => .done initial
  | n + 1 => OracleTemplate.QueryPlan.bind (solverPlan d τ γ h project initial B u n)
      (fun state => roundPlan d τ γ h project n state (u n))

noncomputable def solverState {Ω : Type*} (d : ℕ) (τ γ h : ℝ) (project : E → E)
    (initial : E × E) (B : ℕ → ℕ) (u : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m : ℕ) : ℕ → E × E
  | 0 => initial
  | n + 1 =>
      let state := solverState d τ γ h project initial B u g ξ m n
      let center := acceleratedMix n state.1 state.2
      acceleratedUpdate project h n state ((B n : ℝ)⁻¹ • ∑ i : Fin (B n),
        estimate d τ γ (u n i)
          (g (center + γ • u n i) (ξ (m + (∑ j ∈ Finset.range n, B j) + i)))
          (g (center - γ • u n i) (ξ (m + (∑ j ∈ Finset.range n, B j) + i))))

noncomputable def solverOutput {Ω : Type*} (d : ℕ) (τ γ h : ℝ) (project : E → E)
    (initial : E × E) (B : ℕ → ℕ) (u : (t : ℕ) → Fin (B t) → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m n : ℕ) : E :=
  (solverState d τ γ h project initial B u g ξ m n).1

noncomputable def selectByDifference (a b : E) (difference : ℝ) : E :=
  if difference ≤ 0 then a else b

noncomputable def comparisonPairPlan (s : ℝ) (a b : E) :
    OracleTemplate.QueryPlan E ℝ ℝ 2 :=
  .ask a (fun plus => .ask b (fun minus => .done (OracleTemplate.clip s (plus - minus))))

noncomputable def selectionPlan (s : ℝ) (a b : E) (T : ℕ) :
    OracleTemplate.QueryPlan E ℝ E (2 * T) :=
  OracleTemplate.QueryPlan.map (fun values => selectByDifference a b ((T : ℝ)⁻¹ * values.sum))
    (OracleTemplate.QueryPlan.traverse T (fun _ => comparisonPairPlan s a b))

def dualSolverCalls (B : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => (2 * B n + 2 * B n) + dualSolverCalls B n

noncomputable def dualSolverPlan (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (project : E → E)
    (initial : E × E) (B : ℕ → ℕ)
    (u v : (t : ℕ) → Fin (B t) → E) :
    (n : ℕ) → OracleTemplate.QueryPlan E ℝ ((E × E) × (E × E)) (dualSolverCalls B n)
  | 0 => .done (initial, initial)
  | n + 1 => OracleTemplate.QueryPlan.bind
      (dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B u v n)
      (fun states => OracleTemplate.QueryPlan.bind
        (roundPlan d τ₁ γ₁ h project n states.1 (u n))
        (fun first => OracleTemplate.QueryPlan.map (fun second => (first, second))
          (roundPlan d τ₂ γ₂ h project n states.2 (v n))))

noncomputable def adaptiveSelectionPlan (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h s : ℝ)
    (project : E → E) (initial : E × E) (B : ℕ → ℕ)
    (u v : (t : ℕ) → Fin (B t) → E) (N T : ℕ) :
    OracleTemplate.QueryPlan E ℝ E (2 * T + dualSolverCalls B N) :=
  OracleTemplate.QueryPlan.bind (dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B u v N)
    (fun states => selectionPlan s states.1.1 states.2.1 T)

noncomputable def roundState {Ω : Type*} (d : ℕ) (τ γ h : ℝ) (project : E → E)
    (t : ℕ) (state : E × E) {B : ℕ} (u : Fin B → E)
    (g : E → Ω → ℝ) (ξ : ℕ → Ω) (m : ℕ) : E × E :=
  acceleratedUpdate project h t state ((B : ℝ)⁻¹ • ∑ i : Fin B,
    estimate d τ γ (u i)
      (g (acceleratedMix t state.1 state.2 + γ • u i) (ξ (m + i)))
      (g (acceleratedMix t state.1 state.2 - γ • u i) (ξ (m + i))))

noncomputable def dualSolverState {Ω : Type*} (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ)
    (project : E → E) (initial : E × E) (B : ℕ → ℕ)
    (u v : (t : ℕ) → Fin (B t) → E) (g : E → Ω → ℝ) (ξ : ℕ → Ω)
    (m : ℕ) : ℕ → (E × E) × (E × E)
  | 0 => (initial, initial)
  | n + 1 =>
      let states := dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B u v g ξ m n
      let start := m + 2 * ∑ j ∈ Finset.range n, B j
      (roundState d τ₁ γ₁ h project n states.1 (u n) g ξ start,
        roundState d τ₂ γ₂ h project n states.2 (v n) g ξ (start + B n))

noncomputable def adaptiveOutput {Ω : Type*} (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h s : ℝ)
    (project : E → E) (initial : E × E) (B : ℕ → ℕ)
    (u v : (t : ℕ) → Fin (B t) → E) (g : E → Ω → ℝ) (ξ : ℕ → Ω)
    (m N T : ℕ) : E :=
  let states := dualSolverState d τ₁ τ₂ γ₁ γ₂ h project initial B u v g ξ m N
  selectByDifference states.1.1 states.2.1 ((T : ℝ)⁻¹ * ∑ i : Fin T,
    OracleTemplate.clip s
      (g states.1.1 (ξ (m + 2 * (∑ j ∈ Finset.range N, B j) + i)) -
        g states.2.1 (ξ (m + 2 * (∑ j ∈ Finset.range N, B j) + i))))

noncomputable def adaptiveAlgorithm {S : Type} [MeasurableSpace S]
    (law : MeasureTheory.ProbabilityMeasure S) (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h s : ℝ)
    (project : E → E) (initial : E × E) (B : ℕ → ℕ)
    (u v : S → (t : ℕ) → Fin (B t) → E) (N T : ℕ) : OracleTemplate.Algorithm E ℝ E :=
  OracleTemplate.QueryPlan.algorithm law initial.1 initial.1 (2 * T + dualSolverCalls B N)
    (fun seed => adaptiveSelectionPlan d τ₁ τ₂ γ₁ γ₂ h s project initial B (u seed) (v seed) N T)

end LongTails.Algorithms.ClippedTwoPoint
