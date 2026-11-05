import LongTails.Algorithms.TaylorCorrectedNewton
import LongTails.Proofs.PowerMirrorGeometry
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

namespace LongTails.Proofs.TaylorCorrectedStep

open scoped RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open LongTails.Algorithms.TaylorCorrectedNewton

lemma model_continuous (η : ℝ) (z w g : E) (H : E →L[ℝ] E) :
    Continuous (model η z w g H) := by
  unfold model
  fun_prop

lemma modelPoint_optimal [FiniteDimensional ℝ E] {ρ : ℝ} (hρ : 0 ≤ ρ)
    (η : ℝ) (c z w g : E) (H : E →L[ℝ] E) :
    modelPoint η ρ c z w g H ∈ Metric.closedBall c ρ ∧
      IsMinOn (model η z w g H) (Metric.closedBall c ρ) (modelPoint η ρ c z w g H) := by
  have he := (isCompact_closedBall c ρ).exists_isMinOn
    (show (Metric.closedBall c ρ).Nonempty from ⟨c, by simpa using hρ⟩)
    (model_continuous η z w g H).continuousOn
  simpa only [modelPoint, dite_eq_left he] using Classical.choose_spec he

lemma model_hasGradientAt [CompleteSpace E] (η : ℝ) (z w g v : E) (H : E →L[ℝ] E)
    (hH : ∀ a b, ⟪a, H b⟫ = ⟪H a, b⟫) :
    HasGradientAt (model η z w g H) (η • (g + 2 • H (v - w)) + (v - z)) v := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hs := (hasFDerivAt_id (𝕜 := ℝ) v).sub_const w
  have hl := (hasFDerivAt_const g v).inner ℝ hs
  have hq := hs.inner ℝ (H.hasFDerivAt.comp v hs)
  have hn := (((hasFDerivAt_id (𝕜 := ℝ) v).sub_const z).norm_sq).mul_const (1 / 2 : ℝ)
  convert ((hl.add hq).const_mul η).add hn using 1
  · funext y
    simp [model, div_eq_mul_inv]
  · ext u
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply,
      inner_sub_right, hH, real_inner_comm u]
    ring_nf
    simp

lemma modelPoint_variational [FiniteDimensional ℝ E] {ρ : ℝ} (hρ : 0 ≤ ρ)
    (η : ℝ) (c z w g : E) (H : E →L[ℝ] E)
    (hH : ∀ a b, ⟪a, H b⟫ = ⟪H a, b⟫) (u : E) (hu : u ∈ Metric.closedBall c ρ) :
    η * ⟪g + 2 • H (modelPoint η ρ c z w g H - w), modelPoint η ρ c z w g H - u⟫ ≤
      ⟪z - modelPoint η ρ c z w g H, modelPoint η ρ c z w g H - u⟫ := by
  have hm := modelPoint_optimal hρ η c z w g H
  have hd := model_hasGradientAt η z w g (modelPoint η ρ c z w g H) H hH
  have hh := PowerMirrorGeometry.minimizer_derivative_nonneg (convex_closedBall c ρ)
    hm.1 hu hm.2 hd.hasFDerivAt
  simp only [InnerProductSpace.toDual_apply_apply, inner_add_left, inner_sub_left,
    inner_sub_right, real_inner_smul_left] at hh ⊢
  linarith

lemma eval_collect {n : ℕ} (oracle : Fin n × E → Reply E) (w : E) (k : ℕ)
    (indices : Fin k → Fin n) :
    OracleTemplate.QueryPlan.eval oracle (collect w k indices) = fun i => oracle (indices i, w) := by
  induction k with
  | zero => funext i; exact Fin.elim0 i
  | succ k ih =>
    simp only [collect, OracleTemplate.QueryPlan.eval, OracleTemplate.QueryPlan.eval_map, ih]
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma eval_augmentPlan {n : ℕ} {U : Type*} (oracle : Fin n × E → Reply E)
    (augment : E → Reply E → Reply E) {k : ℕ}
    (plan : OracleTemplate.QueryPlan (Fin n × E) (Reply E) U k) :
    OracleTemplate.QueryPlan.eval oracle (augmentPlan augment plan) =
      OracleTemplate.QueryPlan.eval (fun q => augment q.2 (oracle q)) plan := by
  induction plan with
  | done value => rfl
  | ask q next ih => exact ih (augment q.2 (oracle q))

lemma inner_points_mem [FiniteDimensional ℝ E] {n : ℕ}
    (oracle : Fin n × E → Reply E) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (η : ℝ) (c w : E) (cache : Fin n → Reply E) (k : ℕ) (z : E)
    (indices : Fin k → Fin n) (j : Fin k) :
    (OracleTemplate.QueryPlan.eval oracle (inner η ρ c w cache k z indices)).2 j ∈
      Metric.closedBall c ρ := by
  induction k generalizing z with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    rw [LongTails.Algorithms.TaylorCorrectedNewton.inner, OracleTemplate.QueryPlan.eval_bind, OracleTemplate.QueryPlan.eval_map]
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [Fin.cons_zero, step, OracleTemplate.QueryPlan.eval] using
        (modelPoint_optimal hρ η c z w (meanGradient cache) (meanHessian cache)).1
    · simpa only [Fin.cons_succ] using ih _ (fun i => indices i.succ) j

lemma corrected_distance (z v u e : E) (η : ℝ) :
    ‖z - u‖ ^ 2 / 2 - ‖v - (2 * η) • e - u‖ ^ 2 / 2 =
      ⟪z - v, v - u⟫ + ‖z - v‖ ^ 2 / 2 +
        2 * η * ⟪e, v - u⟫ - 2 * η ^ 2 * ‖e‖ ^ 2 := by
  have h₁ : z - u = (z - v) + (v - u) := by abel
  have h₂ : v - (2 * η) • e - u = (v - u) - (2 * η) • e := by module
  rw [h₁, h₂, norm_add_sq_real, norm_sub_sq_real (v - u) ((2 * η) • e), norm_smul,
    Real.norm_eq_abs, inner_smul_right, real_inner_comm (v - u) e]
  nlinarith [sq_abs (2 * η)]

lemma model_correction (z v u e gv gw hs : E) {η : ℝ}
    (hmodel : η * ⟪gw + (2 : ℝ) • hs, v - u⟫ ≤ ⟪z - v, v - u⟫) :
    η * ⟪(2 : ℝ) • gv - gw, v - u⟫ + ‖z - v‖ ^ 2 / 2 +
      2 * η * ⟪e - (gv - gw - hs), v - u⟫ - 2 * η ^ 2 * ‖e‖ ^ 2 ≤
        ‖z - u‖ ^ 2 / 2 - ‖v - (2 * η) • e - u‖ ^ 2 / 2 := by
  rw [corrected_distance]
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left] at hmodel ⊢
  linarith

lemma averaged_model_correction {n : ℕ} [NeZero n]
    (z v u gv gw hs : E) (e : Fin n → E) {η : ℝ}
    (hmodel : η * ⟪gw + (2 : ℝ) • hs, v - u⟫ ≤ ⟪z - v, v - u⟫)
    (hmean : ∑ i, e i = (n : ℝ) • (gv - gw - hs)) :
    η * ⟪(2 : ℝ) • gv - gw, v - u⟫ + ‖z - v‖ ^ 2 / 2 -
        2 * η ^ 2 * ((n : ℝ)⁻¹ * ∑ i, ‖e i‖ ^ 2) ≤
      ‖z - u‖ ^ 2 / 2 - (n : ℝ)⁻¹ * (∑ i, ‖v - (2 * η) • e i - u‖ ^ 2) / 2 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have he : ∑ i, ⟪e i - (gv - gw - hs), v - u⟫ = 0 := by
    rw [← sum_inner, Finset.sum_sub_distrib, hmean]
    simp [Nat.cast_smul_eq_nsmul, smul_sub]
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => model_correction z v u (e i) gv gw hs hmodel)
  have hscaled := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (n : ℝ)⁻¹)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, he, mul_zero,
    add_zero, ← Finset.sum_div] at hscaled
  field_simp at hscaled ⊢
  nlinarith only [hscaled]

lemma bregman_balance (f : E → ℝ) (g : E → E) (u v w : E) :
    ⟪(2 : ℝ) • g v - g w, v - u⟫ =
      f v - f u + 2 * (f u - f v - ⟪g v, u - v⟫) -
        (f u - f w - ⟪g w, u - w⟫) + (f v - f w - ⟪g w, v - w⟫) := by
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left]
  ring

lemma averaged_descent {n : ℕ} [NeZero n] (f : E → ℝ) (g : E → E)
    (z v u w hs : E) (e : Fin n → E) {η C : ℝ} (hη : 0 ≤ η)
    (hmodel : η * ⟪g w + (2 : ℝ) • hs, v - u⟫ ≤ ⟪z - v, v - u⟫)
    (hmean : ∑ i, e i = (n : ℝ) • (g v - g w - hs))
    (hD : 0 ≤ f v - f w - ⟪g w, v - w⟫)
    (hvariance : (n : ℝ)⁻¹ * ∑ i, ‖e i‖ ^ 2 ≤ C * (f v - f w - ⟪g w, v - w⟫))
    (hstep : 4 * η * C ≤ 1) :
    η * (f v - f u + 2 * (f u - f v - ⟪g v, u - v⟫) -
      (f u - f w - ⟪g w, u - w⟫)) + ‖z - v‖ ^ 2 / 2 +
      η / 2 * (f v - f w - ⟪g w, v - w⟫) ≤
        ‖z - u‖ ^ 2 / 2 - (n : ℝ)⁻¹ * (∑ i, ‖v - (2 * η) • e i - u‖ ^ 2) / 2 := by
  have hh := averaged_model_correction z v u (g v) (g w) hs e hmodel hmean
  rw [bregman_balance f g u v w] at hh
  have hv := mul_le_mul_of_nonneg_left hvariance (show 0 ≤ 2 * η ^ 2 by positivity)
  have ht := mul_le_mul_of_nonneg_right hstep (mul_nonneg hη hD)
  nlinarith only [hh, hv, ht]

end LongTails.Proofs.TaylorCorrectedStep
