import LongTails.Setups.StochasticLocalHessianConvex
import LongTails.Algorithms.DampedGeneralizedAccelerated
import LongTails.Algorithms.RobustGeneralizedAccelerated
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

namespace LongTails.Algorithms.NoisyDampedNewton

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def shifted (H : E →L[ℝ] E) (τ : ℝ) : E →L[ℝ] E :=
  H + τ • ContinuousLinearMap.id ℝ E

noncomputable def response (H : E →L[ℝ] E) (τ : ℝ) (g : E) : E :=
  (shifted H τ).inverse (-g)

def Certified (M₀ M₁ ρ δ α τ : ℝ) (s : E) : Prop :=
  ‖s‖ ≤ ρ ∧ M₁ * ‖s‖ ^ 2 ≤ α / 4 ∧ 4 * (δ + M₀ * ‖s‖) ≤ α * τ

noncomputable def backtrackIndex (M₀ M₁ ρ δ α η : ℝ) (H : E →L[ℝ] E) (g : E) : ℕ := by
  classical
  exact if h : ∃ j : ℕ, Certified M₀ M₁ ρ δ α (η * 2 ^ j) (response H (η * 2 ^ j) g)
    then Nat.find h else 0

noncomputable def backtrackCurvature (M₀ M₁ ρ δ α η : ℝ) (H : E →L[ℝ] E) (g : E) : ℝ :=
  η * 2 ^ backtrackIndex M₀ M₁ ρ δ α η H g

open OracleTemplate.GeneralizedAccelerated (Iterate tentativeWeight coupling)

structure Trial (E : Type*) where
  previous : Iterate E
  curvature : ℝ
  displacement : E

noncomputable def prepare (M₀ M₁ ρ δ α : ℝ) (s : Iterate E) (H : E →L[ℝ] E) (g : E) : Trial E :=
  let B := shifted H δ
  let τ := backtrackCurvature M₀ M₁ ρ (2 * δ) α s.guess B g
  ⟨s, τ, response B τ g⟩

noncomputable def trialPoint (t : Trial E) : E :=
  coupling t.previous + t.displacement

noncomputable def actualWeight (t : Trial E) : ℝ :=
  t.previous.guess / t.curvature * tentativeWeight t.previous

noncomputable def finish (floor : ℝ) (t : Trial E) (u : E) : Iterate E := by
  classical
  let γ := t.previous.guess / t.curvature
  let a := actualWeight t
  let B := t.previous.A + a
  exact ⟨B, ((1 - γ) * t.previous.A / B) • t.previous.x +
    (γ * (t.previous.A + tentativeWeight t.previous) / B) • trialPoint t,
    t.previous.z - a • u,
    if t.curvature = t.previous.guess then max floor (t.previous.guess / 2)
    else 2 * t.previous.guess⟩

open LongTails.Setups.StochasticLocalHessianConvex (Params Point)
open OracleTemplate.RobustGradient (pilotCenter centeredClip)
open OracleTemplate.RobustGeneralized (meanBlock)

noncomputable def scaleBase (p : Params) : ℝ :=
  2 + p.Δ / p.ε + p.δ * p.R ^ 2 / p.ε + p.M₀ * p.R ^ 3 / p.ε +
    p.M₁ * p.R ^ 2 + (p.R / p.ρ) ^ 2 + 1 / p.β + p.σ ^ 2 * p.R ^ 2 / p.ε ^ 2

noncomputable def confidence (p : Params) : ℝ := 100 * Real.log (scaleBase p)

noncomputable def target (p : Params) : ℝ := 32 * p.R ^ 2 / p.ε

noncomputable def curvatureFloor (p : Params) : ℝ := 2 / target p

noncomputable def tolerance (p : Params) : ℝ := 1 / (262144 * confidence p)

noncomputable def initialIterate (p : Params) : Iterate (Point p.d) :=
  ⟨min (target p / 4) (p.R ^ 2 / (2 * p.Δ)), p.x0, p.x0, curvatureFloor p⟩

noncomputable def modelRadius (p : Params) (a : ℝ) : ℝ :=
  2 * Real.sqrt (p.ε / (1073741824 * confidence p ^ 2 * a))

noncomputable def modelGroups (p : Params) : ℕ := max 1 ⌈16 * confidence p⌉₊

noncomputable def modelSize (p : Params) (a : ℝ) : ℕ :=
  max 1 ⌈576 * p.σ ^ 2 / modelRadius p a ^ 2⌉₊

noncomputable def modelCost (p : Params) (a : ℝ) : ℕ := modelGroups p * modelSize p a

noncomputable def modelEstimate (p : Params) (a : ℝ) (v : ℕ → Point p.d) : Point p.d :=
  pilotCenter (modelRadius p a)
    (fun i : Fin (modelGroups p) => meanBlock (i * modelSize p a) (modelSize p a) v)

noncomputable def updateSize (p : Params) (a : ℝ) : ℕ :=
  max 1 ⌈16777216 * p.σ ^ 2 * a * confidence p ^ 2 / p.ε⌉₊

noncomputable def updateRadius (p : Params) (a : ℝ) : ℝ := p.R / (256 * a * confidence p)

noncomputable def updateEstimate (p : Params) (t : Trial (Point p.d)) (v : ℕ → Point p.d) : Point p.d :=
  centeredClip (updateRadius p (actualWeight t)) (-(t.curvature • t.displacement))
    (meanBlock 0 (updateSize p (actualWeight t)) v)

inductive State (E : Type*) where
  | model (s : Iterate E) (received : ℕ) (replies : ℕ → E)
  | hessian (s : Iterate E) (estimate : E)
  | correction (t : Trial E) (received : ℕ) (replies : ℕ → E)
  | done (s : Iterate E)

noncomputable def resume (p : Params) (s : Iterate (Point p.d)) : State (Point p.d) := by
  classical
  exact if target p / 2 ≤ s.A then .done s else .model s 0 (fun _ => 0)

noncomputable def algorithm (p : Params) :
    OracleTemplate.Algorithm (Point p.d) (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)) (Point p.d) 2 where
  State := State (Point p.d)
  initial _ := by
    classical
    exact if p.Δ ≤ p.ε then .done (initialIterate p) else resume p (initialIterate p)
  query state := match state with
    | .model s _ _ => (0, coupling s)
    | .hessian s _ => (1, coupling s)
    | .correction t _ _ => (0, trialPoint t)
    | .done s => (0, s.x)
  update := by
    classical
    exact fun state reply => match state with
      | .model s n v =>
        let w := Function.update v n (match reply with | .inl g => g | .inr _ => 0)
        if n + 1 < modelCost p (tentativeWeight s) then .model s (n + 1) w
        else .hessian s (modelEstimate p (tentativeWeight s) w)
      | .hessian s g =>
        let H := match reply with | .inl _ => 0 | .inr H => H
        .correction (prepare p.M₀ p.M₁ p.ρ p.δ (tolerance p) s H g) 0 (fun _ => 0)
      | .correction t n v =>
        let w := Function.update v n (match reply with | .inl g => g | .inr _ => 0)
        if n + 1 < updateSize p (actualWeight t) then .correction t (n + 1) w
        else resume p (finish (curvatureFloor p) t (updateEstimate p t w))
      | .done s => .done s
  output state := match state with
    | .model s _ _ => s.x
    | .hessian s _ => s.x
    | .correction t _ _ => t.previous.x
    | .done s => s.x

noncomputable def output (p : Params) (budget : Fin 2 → ℕ)
    (O : OracleTemplate.Oracle (Point p.d) (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)) 2)
    (ξ : (k : ℕ) → O.Seed k) : Point p.d :=
  OracleTemplate.execute O (algorithm p) budget () ξ

end LongTails.Algorithms.NoisyDampedNewton
