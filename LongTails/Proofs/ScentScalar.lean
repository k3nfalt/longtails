import LongTails.Algorithms.Scent
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue

namespace OracleTemplate.Scent

open Real

noncomputable def psi (x : ℝ) : ℝ := exp x - 1 - x

noncomputable def breg (a b : ℝ) : ℝ := exp (-a) - exp (-b) + exp (-b) * (a - b)

lemma psi_nonneg (x : ℝ) : 0 ≤ psi x := by
  unfold psi; have := add_one_le_exp x; linarith

lemma breg_eq (a b : ℝ) : breg a b = exp (-b) * psi (b - a) := by
  unfold breg psi
  have : exp (-a) = exp (-b) * exp (b - a) := by rw [← exp_add]; ring_nf
  rw [this]; ring

lemma breg_nonneg (a b : ℝ) : 0 ≤ breg a b := by
  rw [breg_eq]; exact mul_nonneg (exp_pos _).le (psi_nonneg _)

lemma exp_le_two_mul_one_add_psi (u : ℝ) : exp u ≤ 2 * (1 + psi u) := by
  unfold psi
  rcases le_or_gt u 0 with hu | hu
  · have := exp_pos u; nlinarith
  · have := quadratic_le_exp_of_nonneg hu.le; nlinarith [sq_nonneg (u - 1)]

lemma psi_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : psi x ≤ exp x := by
  unfold psi; linarith

lemma psi_neg_le_half_sq {x : ℝ} (hx : 0 ≤ x) : psi (-x) ≤ x ^ 2 / 2 := by
  unfold psi
  have h : exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
    have h1 : 1 + x + x ^ 2 / 2 ≤ exp x := quadratic_le_exp_of_nonneg hx
    have h2 : exp (-x) = (exp x)⁻¹ := exp_neg x
    rw [h2]
    have hpos : 0 < 1 + x + x ^ 2 / 2 := by positivity
    calc (exp x)⁻¹ ≤ (1 + x + x ^ 2 / 2)⁻¹ := by
          exact inv_anti₀ hpos h1
      _ ≤ 1 - x + x ^ 2 / 2 := by
          rw [inv_le_iff_one_le_mul₀ hpos]
          nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), mul_nonneg hx (sq_nonneg x)]
  linarith

lemma sq_exp_sub_one_le_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    (exp u - 1) ^ 2 ≤ 2 * exp u * psi u := by
  unfold psi
  have hs : u ≤ sinh u := self_le_sinh_iff.mpr hu
  rw [sinh_eq] at hs
  have hprod : exp u * exp (-u) = 1 := by rw [← exp_add]; simp
  nlinarith [exp_pos u]

lemma sq_exp_sub_one_le_of_nonpos {u : ℝ} (hu : u ≤ 0) :
    (exp u - 1) ^ 2 ≤ 2 * psi u := by
  unfold psi
  let f : ℝ → ℝ := fun v => -(exp (2 * v)) + 4 * exp v - 3 - 2 * v
  have hderiv : ∀ v, HasDerivAt f (-(exp (2 * v) * 2) + 4 * exp v - 0 - 2) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => exp (2 * v)) (exp (2 * v) * 2) v := by
      have : HasDerivAt (fun v : ℝ => 2 * v) 2 v := by
        simpa using (hasDerivAt_id v).const_mul (2 : ℝ)
      exact this.exp
    have h2 : HasDerivAt (fun v : ℝ => 4 * exp v) (4 * exp v) v := (hasDerivAt_exp v).const_mul 4
    have h3 : HasDerivAt (fun v : ℝ => 2 * v) 2 v := by
      simpa using (hasDerivAt_id v).const_mul (2 : ℝ)
    exact ((h1.neg.add h2).sub (hasDerivAt_const v (3 : ℝ))).sub h3
  have hanti : AntitoneOn f (Set.Iic 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
    · exact fun v _ => (hderiv v).continuousAt.continuousWithinAt
    · exact fun v _ => (hderiv v).differentiableAt.differentiableWithinAt
    · intro v _
      rw [(hderiv v).deriv]
      have hexp2 : exp (2 * v) = exp v * exp v := by rw [← exp_add]; ring_nf
      nlinarith [sq_nonneg (exp v - 1)]
  have h0 : f 0 = 0 := by simp [f]; norm_num
  have hfu : f 0 ≤ f u := hanti (by simp [Set.mem_Iic, hu]) (by simp) hu
  have hexp2 : exp (2 * u) = exp u * exp u := by rw [← exp_add]; ring_nf
  rw [h0] at hfu
  simp only [f] at hfu
  nlinarith [hfu, hexp2]

lemma sq_exp_sub_one_le (u : ℝ) : (exp u - 1) ^ 2 ≤ 2 * exp (max u 0) * psi u := by
  rcases le_or_gt 0 u with hu | hu
  · rw [max_eq_left hu]; exact sq_exp_sub_one_le_of_nonneg hu
  · rw [max_eq_right hu.le, exp_zero, mul_one]; exact sq_exp_sub_one_le_of_nonpos hu.le

lemma sq_exp_sub_one_le_of_le {u Δ : ℝ} (hu : u ≤ Δ) (hΔ : 0 ≤ Δ) :
    (exp u - 1) ^ 2 ≤ 2 * exp Δ * psi u := by
  refine le_trans (sq_exp_sub_one_le u) ?_
  have : exp (max u 0) ≤ exp Δ := exp_le_exp.mpr (max_le hu hΔ)
  have := psi_nonneg u
  nlinarith

section Spmd

variable {α ν s : ℝ}

lemma exp_spmd (hα : 0 ≤ α) :
    exp (spmd α ν s) = exp ν * (1 + α * exp s) / (1 + α * exp ν) := by
  unfold spmd
  have h1 : 0 < 1 + α * exp s := by positivity
  have h2 : 0 < 1 + α * exp ν := by positivity
  rw [exp_sub, exp_add, exp_log h1, exp_log h2]

lemma exp_neg_spmd (hα : 0 ≤ α) :
    exp (-(spmd α ν s)) = (exp (-ν) + α) / (1 + α * exp s) := by
  rw [exp_neg, exp_spmd hα]
  have h1 : 0 < 1 + α * exp s := by positivity
  have h2 : 0 < 1 + α * exp ν := by positivity
  have h3 : 0 < exp ν := exp_pos ν
  rw [exp_neg]
  field_simp

lemma spmd_mem_Icc (hα : 0 ≤ α) {c0 c1 : ℝ} (hν : ν ∈ Set.Icc c0 c1) (hs : s ∈ Set.Icc c0 c1) :
    spmd α ν s ∈ Set.Icc c0 c1 := by
  have hexp : exp (spmd α ν s) = exp ν * (1 + α * exp s) / (1 + α * exp ν) := exp_spmd hα
  have h2 : 0 < 1 + α * exp ν := by positivity
  have hlo : exp c0 ≤ exp (spmd α ν s) := by
    rw [hexp, le_div_iff₀ h2]
    have ha := exp_le_exp.mpr hν.1
    have hb := exp_le_exp.mpr hs.1
    nlinarith [mul_nonneg hα (exp_pos ν).le, mul_nonneg hα (exp_pos s).le,
      mul_nonneg hα (sub_nonneg.mpr ha), mul_nonneg hα (sub_nonneg.mpr hb),
      mul_nonneg (mul_nonneg hα (exp_pos ν).le) (sub_nonneg.mpr hb),
      mul_nonneg (mul_nonneg hα (exp_pos s).le) (sub_nonneg.mpr ha)]
  have hhi : exp (spmd α ν s) ≤ exp c1 := by
    rw [hexp, div_le_iff₀ h2]
    have ha := exp_le_exp.mpr hν.2
    have hb := exp_le_exp.mpr hs.2
    nlinarith [mul_nonneg hα (exp_pos ν).le, mul_nonneg hα (exp_pos s).le,
      mul_nonneg (mul_nonneg hα (exp_pos ν).le) (sub_nonneg.mpr hb),
      mul_nonneg (mul_nonneg hα (exp_pos c1).le) (sub_nonneg.mpr ha)]
  exact ⟨exp_le_exp.mp hlo, exp_le_exp.mp hhi⟩

lemma spmd_foc (hα : 0 ≤ α) :
    α * (1 - exp s * exp (-(spmd α ν s))) = exp (-(spmd α ν s)) - exp (-ν) := by
  rw [exp_neg_spmd hα]
  have h1 : 0 < 1 + α * exp s := by positivity
  field_simp
  ring

lemma three_point (a b u : ℝ) :
    (exp (-a) - exp (-b)) * (a - u) = breg u b - breg u a - breg a b := by
  unfold breg; ring

lemma spmd_regret (hα : 0 ≤ α) (u : ℝ) :
    α * (1 - exp s * exp (-(spmd α ν s))) * (spmd α ν s - u) ≤
      breg u ν - breg u (spmd α ν s) := by
  rw [spmd_foc hα, three_point]
  linarith [breg_nonneg (spmd α ν s) ν]

lemma exp_neg_le_of_spmd (hα : 0 ≤ α) {ρ : ℝ} (hρ : α * exp s ≤ ρ) :
    exp (-ν) ≤ (1 + ρ) * exp (-(spmd α ν s)) := by
  rw [exp_neg_spmd hα]
  have h1 : 0 < 1 + α * exp s := by positivity
  rw [mul_div_assoc', le_div_iff₀ h1]
  nlinarith [exp_pos (-ν)]

end Spmd

section Lipschitz

lemma mul_log_lipschitz {C lo hi : ℝ} (hlo : 0 < lo) (u : ℝ)
    (hC : ∀ r ∈ Set.Icc lo hi, |-(log r + 1) - u| ≤ C) {p q : ℝ}
    (hp : p ∈ Set.Icc lo hi) (hq : q ∈ Set.Icc lo hi) :
    |(-(p * log p) - u * p) - (-(q * log q) - u * q)| ≤ C * |p - q| := by
  have hdiff : ∀ r ∈ Set.Icc lo hi, DifferentiableAt ℝ (fun r : ℝ => -(r * log r) - u * r) r := by
    intro r hr
    have hr0 : r ≠ 0 := (lt_of_lt_of_le hlo hr.1).ne'
    exact ((hasDerivAt_mul_log hr0).neg.sub ((hasDerivAt_id r).const_mul u)).differentiableAt
  have hbound : ∀ r ∈ Set.Icc lo hi, ‖deriv (fun r : ℝ => -(r * log r) - u * r) r‖ ≤ C := by
    intro r hr
    have hr0 : r ≠ 0 := (lt_of_lt_of_le hlo hr.1).ne'
    have hd : HasDerivAt (fun r : ℝ => -(r * log r) - u * r) (-(log r + 1) - u * 1) r :=
      (hasDerivAt_mul_log hr0).neg.sub ((hasDerivAt_id r).const_mul u)
    rw [hd.deriv, Real.norm_eq_abs, mul_one]
    exact hC r hr
  have := (convex_Icc lo hi).norm_image_sub_le_of_norm_deriv_le hdiff hbound hq hp
  simpa [Real.norm_eq_abs] using this

end Lipschitz

end OracleTemplate.Scent
