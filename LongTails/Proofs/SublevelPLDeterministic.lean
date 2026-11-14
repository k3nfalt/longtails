import LongTails.Proofs.GdConvex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped RealInnerProductSpace

namespace OracleTemplate.SublevelRobustGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma pathwise_descent {f : E → ℝ} {L : ℝ} (hL : 0 < L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x v : E) :
    f (x - (1 / L) • v) ≤ f x - (‖gradient f x‖ ^ 2 - ‖v - gradient f x‖ ^ 2) / (2 * L) := by
  have hu := Gradient.smooth_upper_bound hg hlip x (x - (1 / L) • v)
  have he : x - (1 / L) • v - x = -((1 / L) • v) := by abel
  rw [he, inner_neg_right, norm_neg, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)] at hu
  set u := gradient f x
  set e := v - u
  have hv : v = u + e := by simp [e]
  have hin : ⟪u, v⟫ = ‖u‖ ^ 2 + ⟪u, e⟫ := by
    rw [hv, inner_add_right, real_inner_self_eq_norm_sq]
  have hsq : ‖v‖ ^ 2 = ‖u‖ ^ 2 + 2 * ⟪u, e⟫ + ‖e‖ ^ 2 := by
    rw [hv, norm_add_sq_real]
  have hkey : f x + -(1 / L * ⟪u, v⟫) + L / 2 * (1 / L * ‖v‖) ^ 2 =
      f x - (‖u‖ ^ 2 - ‖e‖ ^ 2) / (2 * L) := by
    have h2 : (1 / L * ‖v‖) ^ 2 = ‖v‖ ^ 2 / L ^ 2 := by
      field_simp
    rw [hin, h2, hsq]
    field_simp
    ring
  linarith

lemma concave_tangent {a b q : ℝ} (ha : 0 < a) (hb : 0 < b) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    b ^ q ≤ a ^ q + q * a ^ (q - 1) * (b - a) := by
  have hs : -1 ≤ b / a - 1 := by
    have : 0 ≤ b / a := by positivity
    linarith
  have h := rpow_one_add_le_one_add_mul_self hs hq0 hq1
  have hba : (1 + (b / a - 1)) = b / a := by ring
  rw [hba, Real.div_rpow hb.le ha.le] at h
  have haq : 0 < a ^ q := Real.rpow_pos_of_pos ha q
  have h2 : b ^ q ≤ a ^ q * (1 + q * (b / a - 1)) := by
    rw [div_le_iff₀ haq] at h
    linarith
  have h3 : a ^ q * (1 + q * (b / a - 1)) = a ^ q + q * a ^ (q - 1) * (b - a) := by
    have hqm : a ^ (q - 1) = a ^ q / a := by
      rw [Real.rpow_sub ha, Real.rpow_one]
    rw [hqm]
    field_simp
  linarith [h2, h3]

lemma recursion_step {a b c p : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hp1 : 1 < p) (hp2 : p ≤ 2) (hrec : b ≤ a - c * a ^ p) :
    a ^ (-(p - 1)) + (p - 1) * c ≤ b ^ (-(p - 1)) := by
  set q := p - 1 with hq
  have hq0 : 0 < q := by linarith
  have hq1 : q ≤ 1 := by linarith
  have hap : a ^ p = a ^ q * a := by
    rw [hq, Real.rpow_sub ha, Real.rpow_one]
    field_simp
  have htan := concave_tangent ha hb hq0.le hq1
  have haq : 0 < a ^ q := Real.rpow_pos_of_pos ha q
  have hbq : 0 < b ^ q := Real.rpow_pos_of_pos hb q
  have haq1 : a ^ (q - 1) = a ^ q / a := by rw [Real.rpow_sub ha, Real.rpow_one]
  have hdiff : b ^ q ≤ a ^ q - q * c * (a ^ q) ^ 2 := by
    rw [haq1] at htan
    have h1 : a ^ q / a * (b - a) ≤ a ^ q / a * (-(c * a ^ p)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    have h2 : a ^ q / a * (-(c * a ^ p)) = -(c * (a ^ q) ^ 2) := by
      rw [hap]
      field_simp
    have h3 : q * (a ^ q / a) * (b - a) ≤ q * (-(c * (a ^ q) ^ 2)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (h1.trans (le_of_eq h2)) hq0.le
    linarith
  rw [Real.rpow_neg ha.le, Real.rpow_neg hb.le]
  rw [inv_eq_one_div, inv_eq_one_div, div_add' _ _ _ haq.ne', div_le_div_iff₀ haq hbq]
  have hX : 0 ≤ 1 + q * c * a ^ q := by positivity
  have h4 : (1 + q * c * a ^ q) * b ^ q ≤ (1 + q * c * a ^ q) * (a ^ q - q * c * (a ^ q) ^ 2) :=
    mul_le_mul_of_nonneg_left hdiff hX
  have h5 : (1 + q * c * a ^ q) * (a ^ q - q * c * (a ^ q) ^ 2) ≤ 1 * a ^ q := by
    have : (1 + q * c * a ^ q) * (a ^ q - q * c * (a ^ q) ^ 2) =
        a ^ q - (q * c) ^ 2 * (a ^ q) ^ 3 := by ring
    rw [this]
    nlinarith [sq_nonneg (q * c), pow_nonneg haq.le 3]
  linarith

lemma recursion_sum {c p : ℝ} (hc : 0 < c) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (u : ℕ → ℝ) (K : ℕ) (hpos : ∀ j, j ≤ K → 0 < u j)
    (hrec : ∀ j, j < K → u (j + 1) ≤ u j - c * u j ^ p) :
    (p - 1) * c * K ≤ u K ^ (-(p - 1)) := by
  induction K with
  | zero =>
    simp only [Nat.cast_zero, mul_zero]
    exact (Real.rpow_pos_of_pos (hpos 0 le_rfl) _).le
  | succ K ih =>
    have h1 := ih (fun j hj => hpos j (by omega)) (fun j hj => hrec j (by omega))
    have h2 := recursion_step (hpos K (by omega)) (hpos (K + 1) le_rfl) hc hp1 hp2
      (hrec K (by omega))
    push_cast
    linarith

lemma contradiction_of_large_K {L τ α ε K : ℝ} (hL : 0 < L) (hτ : 0 < τ)
    (hα1 : 1 ≤ α) (hα2 : α < 2) (hε : 0 < ε)
    (hK : 32 * α / (7 * (2 - α)) * L * τ ^ (2 / α) * ε ^ (-(2 - α) / α) ≤ K)
    (hpot : (2 / α - 1) * (7 / (16 * L) * τ ^ (-(2 / α))) * K ≤ (2 * ε) ^ (-(2 / α - 1))) :
    False := by
  have hα0 : 0 < α := by linarith
  have h2α : 0 < 2 - α := by linarith
  have hq : 2 / α - 1 = (2 - α) / α := by field_simp
  have hτp : 0 < τ ^ (2 / α) := Real.rpow_pos_of_pos hτ _
  have hτn : τ ^ (-(2 / α)) = (τ ^ (2 / α))⁻¹ := Real.rpow_neg hτ.le _
  have hεp : 0 < ε ^ (-(2 - α) / α) := Real.rpow_pos_of_pos hε _
  have hlhs : (2 / α - 1) * (7 / (16 * L) * τ ^ (-(2 / α))) * K ≥
      (2 / α - 1) * (7 / (16 * L) * τ ^ (-(2 / α))) *
        (32 * α / (7 * (2 - α)) * L * τ ^ (2 / α) * ε ^ (-(2 - α) / α)) := by
    apply mul_le_mul_of_nonneg_left hK
    rw [hq, hτn]
    positivity
  have hval : (2 / α - 1) * (7 / (16 * L) * τ ^ (-(2 / α))) *
      (32 * α / (7 * (2 - α)) * L * τ ^ (2 / α) * ε ^ (-(2 - α) / α)) =
      2 * ε ^ (-(2 - α) / α) := by
    rw [hq, hτn]
    field_simp
    ring
  have hrhs : (2 * ε) ^ (-(2 / α - 1)) ≤ ε ^ (-(2 - α) / α) := by
    rw [hq, Real.mul_rpow (by norm_num) hε.le]
    have h2 : (2 : ℝ) ^ (-((2 - α) / α)) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      have : 0 ≤ (2 - α) / α := by positivity
      linarith
    have hε' : 0 < ε ^ (-((2 - α) / α)) := Real.rpow_pos_of_pos hε _
    have heq : ε ^ (-(2 - α) / α) = ε ^ (-((2 - α) / α)) := by ring_nf
    rw [heq]
    nlinarith
  nlinarith

end OracleTemplate.SublevelRobustGradient
