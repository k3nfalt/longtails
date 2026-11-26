import LongTails.Proofs.HessianModelFlowDescent
import LongTails.Proofs.Execution

namespace LongTails.Proofs.HessianModelFlowExecution

open LongTails.Setups.PointwiseHessianStationarity
open LongTails.Algorithms.PointwiseHessianModelFlow OracleTemplate MeasureTheory

variable {p : Params}

private noncomputable def reply (f : Point p → ℝ) (x : Point p) : Reply p :=
  (f x, gradient f x, fderiv ℝ (gradient f) x)

private noncomputable def next (f : Point p → ℝ) (s : State p) : State p :=
  update p s (reply f (queryPoint s))

private def invariant (f : Point p → ℝ) (k : ℕ) : State p → Prop
  | .active x => k * (3 / 4 * energyCap p) ≤ f 0 - f x
  | .done x => ‖gradient f x‖ ≤ p.ε

private lemma iterate_invariant (hp : broadSpec.valid p) (f : Point p → ℝ)
    (O : Oracle (Point p) (Reply p)) (hf : broadSpec.admissible p f O) (k : ℕ) :
    invariant f k ((next f)^[k] (.active 0)) := by
  induction k with
  | zero => simp [invariant]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    cases h : (next f)^[k] (.active 0) with
    | done x =>
      rw [h] at ih
      exact ih
    | active x =>
      rw [h] at ih
      change (k : ℝ) * (3 / 4 * energyCap p) ≤ f 0 - f x at ih
      change invariant f _ (step p x (gradient f x) (fderiv ℝ (gradient f) x))
      have hs := HessianModelFlowDescent.step_spec hp hf.1 hf.2.1 x
      cases hz : step p x (gradient f x) (fderiv ℝ (gradient f) x) with
      | done y => rw [hz] at hs; exact hs
      | active y =>
        rw [hz] at hs
        change f y + 3 / 4 * energyCap p ≤ f x at hs
        change ((k + 1 : ℕ) : ℝ) * (3 / 4 * energyCap p) ≤ f 0 - f y
        push_cast
        linarith

lemma budget_large (hp : broadSpec.valid p) :
    let S := p.Δ * Real.sqrt (p.L₀ + p.L₁ * p.ε) / (p.ε * Real.sqrt p.ε)
    p.Δ < ((⌊32 * S / 3⌋₊ + 1 : ℕ) : ℝ) * (3 / 4 * energyCap p) := by
  dsimp only
  have hpos := HessianModelFlowPath.cap_pos hp
  let S := p.Δ * Real.sqrt (p.L₀ + p.L₁ * p.ε) / (p.ε * Real.sqrt p.ε)
  have heq : 32 * S / 3 * (3 / 4 * energyCap p) = p.Δ := by
    have hA := Real.sqrt_pos.2 (RelativeHessianTuning.curvature_pos hp)
    have hε := hp.2.2.2.2.2
    have hs := Real.sqrt_pos.2 hε
    dsimp only [S, energyCap, radius]
    field_simp
    ring
  calc
    _ = 32 * S / 3 * (3 / 4 * energyCap p) := heq.symm
    _ < _ := by
      push_cast
      exact mul_lt_mul_of_pos_right (Nat.lt_floor_add_one _) (by positivity)

lemma success (hp : broadSpec.valid p) (f : Point p → ℝ) (O : Oracle (Point p) (Reply p))
    (hf : broadSpec.admissible p f O) (k : ℕ) (hk : p.Δ < k * (3 / 4 * energyCap p)) :
    broadSpec.successful p f (fun ω : (algorithm p).Seed × ((i : ℕ) → O.Seed i) =>
      execute O (algorithm p) (fun _ => k) ω.1 ω.2)
      ⟨((algorithm p).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let s := (next f)^[k] (.active 0)
  have hex (seed : (algorithm p).Seed) (ξ : (i : ℕ) → O.Seed i) :
      execute O (algorithm p) (fun _ => k) seed ξ = output s := by
    rw [execute_eq_of_answer_eq O (reply f) (fun hist q u => hf.2.2.2.2 hist u q), execute_iterate]
    rfl
  have hs := iterate_invariant hp f O hf k
  change invariant f k s at hs
  have hacc : ‖gradient f (output s)‖ ≤ p.ε := by
    cases h : s with
    | done x => rw [h] at hs; exact hs
    | active x =>
      rw [h] at hs
      have hgap := hf.2.2.1 x
      change (k : ℝ) * (3 / 4 * energyCap p) ≤ f 0 - f x at hs
      linarith
  let P : ProbabilityMeasure ((algorithm p).Seed × ((i : ℕ) → O.Seed i)) :=
    ⟨((algorithm p).law : Measure _).prod (O.law : Measure _), inferInstance⟩
  change broadSpec.successful p f _ P
  let : IsProbabilityMeasure (P : Measure ((algorithm p).Seed × ((i : ℕ) → O.Seed i))) := P.prop
  simp only [hex]
  exact ⟨measurable_const, integrable_const _, by simpa using hacc⟩

end LongTails.Proofs.HessianModelFlowExecution
