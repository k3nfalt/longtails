import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SoftQuadraticDynamics

noncomputable def weight (z : ℝ) : ℝ := 1 / (1 + Real.exp z)

lemma weight_pos (z : ℝ) : 0 < weight z := by
  unfold weight
  positivity

lemma weight_le_one (z : ℝ) : weight z ≤ 1 := by
  unfold weight
  apply (div_le_iff₀ (by positivity : 0 < 1 + Real.exp z)).2
  linarith [Real.exp_pos z]

lemma weight_ge_half {z : ℝ} (hz : z ≤ 0) : 1 / 2 ≤ weight z := by
  unfold weight
  apply (le_div_iff₀ (by positivity : 0 < 1 + Real.exp z)).2
  have he : Real.exp z ≤ 1 := by simpa using Real.exp_le_exp.mpr hz
  linarith

lemma weighted_score_le_one (z : ℝ) : weight z * z ≤ 1 := by
  unfold weight
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : 0 < 1 + Real.exp z)).2
  linarith [Real.add_one_le_exp z]

lemma scaled_weighted_score_le (K z : ℝ) (hK : 0 < K) :
    weight (K * z) * z ≤ 1 / K := by
  apply (le_div_iff₀ hK).2
  nlinarith [weighted_score_le_one (K * z)]

lemma mean_energy_identity (a q b f : ℝ) :
    (a + b * q + f) ^ 2 + (q + b * a) ^ 2 =
      (1 + b ^ 2) * (a ^ 2 + q ^ 2) + 4 * b * a * q +
        2 * f * (a + b * q) + f ^ 2 := by
  ring

lemma mean_imbalance_identity (a q b f : ℝ) :
    (a + b * q + f) ^ 2 - (q + b * a) ^ 2 =
      (1 - b ^ 2) * (a ^ 2 - q ^ 2) + 2 * f * (a + b * q) + f ^ 2 := by
  ring

lemma mean_energy_bound (a q : ℝ) :
    a ^ 2 + q ^ 2 ≤ 2 * |a * q| + |a ^ 2 - q ^ 2| := by
  by_cases h : q ^ 2 ≤ a ^ 2
  · rw [abs_of_nonneg (sub_nonneg.mpr h), abs_mul]
    have hqa : |q| ≤ |a| := by
      rw [← sq_le_sq]
      simpa using h
    nlinarith [sq_abs a, sq_abs q, abs_nonneg a, abs_nonneg q]
  · rw [abs_of_nonpos (by linarith : a ^ 2 - q ^ 2 ≤ 0), abs_mul]
    have haq : |a| ≤ |q| := by
      rw [← sq_le_sq]
      simpa using (le_of_lt (lt_of_not_ge h))
    nlinarith [sq_abs a, sq_abs q, abs_nonneg a, abs_nonneg q]

lemma pre_hitting_weight_comparison {ι : Type*} [Fintype ι] (z : ι → ℝ)
    (i : ι) (hi : z i ≤ 0) :
    ∑ j, weight (z j) ≤
      2 * Real.sqrt (Fintype.card ι) * ∑ j, weight (z j) ^ 2 := by
  let B : ℝ := ∑ j, weight (z j) ^ 2
  have hB : 1 / 4 ≤ B := by
    have hs : weight (z i) ^ 2 ≤ B := Finset.single_le_sum
      (fun j _ => sq_nonneg (weight (z j))) (Finset.mem_univ i)
    have hw := weight_ge_half hi
    nlinarith
  have hc : (∑ j, weight (z j)) ^ 2 ≤ (Fintype.card ι : ℝ) * B := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : ι => (1 : ℝ)) (fun j => weight (z j))
    simpa [B] using h
  have hn : (0 : ℝ) ≤ Fintype.card ι := by positivity
  have hr := Real.sq_sqrt hn
  have hprod := mul_nonneg hn (show 0 ≤ 4 * B ^ 2 - B by nlinarith)
  have hbound : (∑ j, weight (z j)) ^ 2 ≤
      (2 * Real.sqrt (Fintype.card ι) * B) ^ 2 := by
    nlinarith
  have hnonneg : 0 ≤ 2 * Real.sqrt (Fintype.card ι) * B := by positivity
  exact (sq_le_sq₀ (Finset.sum_nonneg (fun j _ => (weight_pos (z j)).le)) hnonneg).mp hbound

lemma cumulative_mean_discretization_bound (b Q Xp Xm U E D : ℝ)
    (hb : 0 ≤ b) (hb₁ : b ≤ 1) (hQ : 0 ≤ Q) (hU : 0 ≤ U)
    (henergy : 4 * Xm ≤ 4 * Xp + Q + U + E)
    (hwork : Q ≤ 2 * b * (Xp + Xm) + D + U) :
    Q ≤ 8 * b * Xp + 3 * U + b * E + 2 * D := by
  have hm := mul_le_mul_of_nonneg_left henergy hb
  have hq := mul_nonneg (sub_nonneg.mpr hb₁) hQ
  have hu := mul_nonneg (sub_nonneg.mpr hb₁) hU
  nlinarith

end LongTails.Proofs.SoftQuadraticDynamics
