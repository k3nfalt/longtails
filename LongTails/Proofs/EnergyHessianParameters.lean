import LongTails.Algorithms.EnergyHessianReuse
import LongTails.Proofs.CappedCubicModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace LongTails.Proofs.EnergyHessianParameters

open LongTails.Setups.GradientDependentHessian LongTails.Algorithms.EnergyHessianReuse
open scoped RealInnerProductSpace

lemma radius_pos (p : Params) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (hL : 0 ≤ p.L₁) :
    0 < radius p := by
  unfold radius
  split_ifs with h
  · positivity
  · have hp : 0 < p.L₁ := lt_of_le_of_ne hL (Ne.symm h)
    positivity

lemma radius_cap (p : Params) (hL : 0 ≤ p.L₁) :
    p.L₁ * radius p ^ 2 ≤ 1 / 10000 := by
  unfold radius
  split_ifs with h
  · simp [h]
  · have hp : 0 < Real.sqrt p.L₁ := Real.sqrt_pos.mpr (lt_of_le_of_ne hL (Ne.symm h))
    have hs := Real.sq_sqrt hL
    field_simp
    nlinarith

lemma step_certificate (p : Params) (g : p.E) (B : p.E →L[ℝ] p.E) (δ σ : ℝ)
    (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (hL : 0 ≤ p.L₁) (hg : g ≠ 0)
    (hB : ∀ x y : p.E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    certificate p g B δ σ (selectedStep p g B δ σ).1 (selectedStep p g B δ σ).2 := by
  classical
  obtain ⟨s, μ, hs⟩ := CappedCubicModel.model_certificate B g δ σ
    (radius_pos p hΔ hε hL) hg hB
  have he : ∃ z : p.E × ℝ, certificate p g B δ σ z.1 z.2 := ⟨(s, μ), hs⟩
  simpa only [selectedStep, dite_eq_left he] using Classical.choose_spec he

lemma coefficient_lower (p : Params) (a : Point p) :
    100 * (p.m * p.L₀ + p.L₁ * ‖a.g‖) ≤ coefficient p a := le_max_right _ _

lemma coefficient_previous (p : Params) (a : Point p) : a.σ ≤ 2 * coefficient p a := by
  have h : a.σ / 2 ≤ coefficient p a := le_max_left _ _
  linarith

lemma move_best (p : Params) (a : Point p) (s g : p.E) :
    (move p a s g).bestNorm ≤ a.bestNorm ∧ (move p a s g).bestNorm ≤ ‖g‖ :=
  ⟨min_le_right _ _, min_le_left _ _⟩

lemma move_best_gradient (p : Params) (G : p.E → p.E) (a : Point p) (s : p.E)
    (hbest : ‖G a.best‖ = a.bestNorm) :
    ‖G (move p a s (G (a.x + s))).best‖ = (move p a s (G (a.x + s))).bestNorm := by
  dsimp [move]
  split_ifs with h
  · exact (min_eq_left h.le).symm
  · rw [min_eq_right (le_of_not_gt h)]
    exact hbest

lemma logarithmic_decay {x : ℝ} (hx : 0 ≤ x) :
    (3 / 4 : ℝ) ^ ⌈Real.log (1 + x) / Real.log (4 / 3)⌉₊ * (1 + x) ≤ 1 := by
  let k := ⌈Real.log (1 + x) / Real.log (4 / 3)⌉₊
  have hlog : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hk : Real.log (1 + x) ≤ (k : ℝ) * Real.log (4 / 3) :=
    (div_le_iff₀ hlog).mp (Nat.le_ceil _)
  have hloginv : Real.log (3 / 4 : ℝ) = -Real.log (4 / 3 : ℝ) := by
    convert Real.log_inv (4 / 3 : ℝ) using 1; norm_num
  have hh : Real.exp (Real.log (3 / 4 : ℝ) * (k : ℝ) + Real.log (1 + x)) ≤ 1 := by
    calc
      _ ≤ Real.exp 0 := by
        apply Real.exp_le_exp.mpr
        rw [hloginv]
        nlinarith
      _ = 1 := Real.exp_zero
  rw [Real.exp_add, Real.exp_log (show 0 < 1 + x by positivity),
    ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 4), Real.rpow_natCast] at hh
  exact hh

lemma burn_initial_bound (p : Params) (hL₀ : 0 < p.L₀) (hL₁ : 0 ≤ p.L₁)
    (hG : 0 ≤ p.G₀) (hm : 1 ≤ p.m) :
    (3 / 4 : ℝ) ^ burnCount p * (100 * (p.m * p.L₀ + p.L₁ * p.G₀)) ≤
      100 * p.m * p.L₀ := by
  have hm' : (0 : ℝ) < p.m := by exact_mod_cast (show 0 < p.m by omega)
  have hb : 0 < (p.m : ℝ) * p.L₀ := mul_pos hm' hL₀
  have hx : 0 ≤ p.L₁ * p.G₀ / (p.m * p.L₀) := by positivity
  have hh := mul_le_mul_of_nonneg_right (logarithmic_decay hx) (show 0 ≤ 100 * p.m * p.L₀ by positivity)
  have heq : (1 + p.L₁ * p.G₀ / (p.m * p.L₀)) * (100 * p.m * p.L₀) =
      100 * (p.m * p.L₀ + p.L₁ * p.G₀) := by field_simp
  rw [mul_assoc, heq] at hh
  simpa only [one_mul, burnCount] using hh

lemma cap_multiplier_charge (p : Params) {μ r : ℝ} (hL : 0 ≤ p.L₁)
    (hcap : μ * (r - radius p) = 0) :
    p.L₁ * μ * r = 100 * p.L₁ * Real.sqrt p.L₁ * μ * r ^ 2 := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hr : r = radius p := sub_eq_zero.mp ((mul_eq_zero.mp hcap).resolve_left hμ)
  rw [hr]
  unfold radius
  split_ifs with hLzero
  · simp [hLzero]
  · have hs : Real.sqrt p.L₁ ≠ 0 := ne_of_gt
      (Real.sqrt_pos.mpr (lt_of_le_of_ne hL (Ne.symm hLzero)))
    field_simp

lemma radius_inverse_bound (p : Params) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (hL : 0 ≤ p.L₁) :
    1 / radius p ≤ 100 * Real.sqrt p.L₁ + p.ε / p.Δ := by
  unfold radius
  split_ifs with h
  · simp [h]
  · have hs : 0 < Real.sqrt p.L₁ := Real.sqrt_pos.mpr (lt_of_le_of_ne hL (Ne.symm h))
    simp only [one_div_div, div_one]
    have he : 0 ≤ p.ε / p.Δ := by positivity
    linarith

lemma coefficient_initial (p : Params) (g : p.E) (hL₀ : 0 ≤ p.L₀) (hL₁ : 0 ≤ p.L₁) :
    coefficient p (initial p g) = 100 * (p.m * p.L₀ + p.L₁ * ‖g‖) := by
  have hb : 0 ≤ 100 * (p.m * p.L₀ + p.L₁ * ‖g‖) := by positivity
  dsimp [coefficient, initial]
  rw [max_eq_right (by linarith)]

lemma coefficient_nonneg (p : Params) (a : Point p) (hL₀ : 0 ≤ p.L₀) (hL₁ : 0 ≤ p.L₁) :
    0 ≤ coefficient p a :=
  (show 0 ≤ 100 * (p.m * p.L₀ + p.L₁ * ‖a.g‖) by positivity).trans (coefficient_lower p a)

lemma coefficient_transition (p : Params) (a : Point p) (s g : p.E)
    (hL₀ : 0 ≤ p.L₀) (hL₁ : 0 ≤ p.L₁) :
    coefficient p (move p a s g) ≤ coefficient p a / 2 + 100 * p.m * p.L₀ + 100 * p.L₁ * ‖g‖ := by
  have hσ := coefficient_nonneg p a hL₀ hL₁
  have hbase : 0 ≤ 100 * p.m * p.L₀ + 100 * p.L₁ * ‖g‖ := by positivity
  change max (coefficient p a / 2) (100 * (p.m * p.L₀ + p.L₁ * ‖g‖)) ≤ _
  apply max_le <;> nlinarith

lemma interpolation_scale {q v A ε : ℝ} (hq : 0 < q) (hv : 0 ≤ v) (hε : 0 < ε)
    (hq2 : q ^ 2 * ε = A) :
    let b := 1 / (100 * (q + v))
    0 < b ∧ b ^ 2 * A ≤ ε / 10000 ∧ b ^ 2 * v ^ 2 ≤ 1 / 10000 ∧
      1 / b = 100 * (q + v) := by
  have hden : 0 < 100 * (q + v) := by positivity
  have hden2 : 0 < (100 * (q + v)) ^ 2 := sq_pos_of_pos hden
  dsimp only
  refine ⟨by positivity, ?_, ?_, by simp⟩
  · have heq : (1 / (100 * (q + v))) ^ 2 * A = A / (100 * (q + v)) ^ 2 := by rw [div_pow, one_pow]; ring
    rw [heq]
    apply (div_le_iff₀ hden2).mpr
    have hh : q ^ 2 ≤ (q + v) ^ 2 := by nlinarith
    have hh' := mul_le_mul_of_nonneg_right hh hε.le
    nlinarith
  · have heq : (1 / (100 * (q + v))) ^ 2 * v ^ 2 = v ^ 2 / (100 * (q + v)) ^ 2 := by rw [div_pow, one_pow]; ring
    rw [heq]
    apply (div_le_iff₀ hden2).mpr
    nlinarith

lemma block_horizon (p : Params) :
    27000 * p.Δ * Real.sqrt (p.m * p.L₀) / (p.ε * Real.sqrt p.ε) +
      15000 * p.Δ * Real.sqrt (p.m * p.L₁) / p.ε + 72 ≤
      (blockCount p : ℝ) * (p.m + 1) := by
  have hm : (0 : ℝ) < p.m + 1 := by positivity
  exact (div_le_iff₀ hm).mp (Nat.le_ceil _)

lemma rounded_block_costs {R : ℝ} (hR : 0 ≤ R) {m : ℕ} (hm : 1 ≤ m) :
    let B := ⌈(R + 72) / (m + 1)⌉₊
    B * (m + 1) ≤ ⌈R⌉₊ + m + 73 ∧ 2 * B ≤ ⌈2 * R / m⌉₊ + 146 := by
  let B := ⌈(R + 72) / (m + 1)⌉₊
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmp : (0 : ℝ) < m + 1 := by positivity
  have hmp0 : (0 : ℝ) < m := by linarith
  have hceil : (B : ℝ) < (R + 72) / (m + 1) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hB : (B : ℝ) * (m + 1) < R + 72 + ((m : ℝ) + 1) := by
    have hh := (mul_lt_mul_iff_left₀ hmp).mpr hceil
    have heq : ((R + 72) / ((m : ℝ) + 1)) * (m + 1) = R + 72 :=
      div_mul_cancel₀ _ (ne_of_gt hmp)
    nlinarith
  have hRceil := Nat.le_ceil R
  dsimp only
  change B * (m + 1) ≤ ⌈R⌉₊ + m + 73 ∧ 2 * B ≤ ⌈2 * R / (m : ℝ)⌉₊ + 146
  constructor
  · exact_mod_cast (show (B : ℝ) * ((m : ℝ) + 1) ≤ (⌈R⌉₊ : ℝ) + m + 73 by linarith)
  · have hfrac : (R + 72) / ((m : ℝ) + 1) ≤ R / m + 72 := by
      apply (div_le_iff₀ hmp).mpr
      have hdiv : R / m * m = R := div_mul_cancel₀ _ (ne_of_gt hmp0)
      have hpos : 0 ≤ R / m := by positivity
      nlinarith
    have hceil2 := Nat.le_ceil (2 * R / (m : ℝ))
    have htwo : 2 * R / (m : ℝ) = 2 * (R / m) := by ring
    have hceil2' : 2 * (R / (m : ℝ)) ≤ (⌈2 * R / (m : ℝ)⌉₊ : ℝ) := by
      calc
        _ = 2 * R / (m : ℝ) := htwo.symm
        _ ≤ _ := hceil2
    exact_mod_cast (show (2 : ℝ) * B ≤ (⌈2 * R / (m : ℝ)⌉₊ : ℝ) + 146 by linarith)

end LongTails.Proofs.EnergyHessianParameters
