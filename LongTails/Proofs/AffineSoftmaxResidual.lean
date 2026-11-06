import Mathlib.Analysis.Normed.Module.Convex
import LongTails.Proofs.SimplexEntropy
import LongTails.Algorithms.AffineSoftmaxEstimator
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace LongTails.Proofs.AffineSoftmaxResidual

open LongTails.Algorithms.AffineSoftmaxEstimator

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma reciprocal_bounds (weights : List ℝ)
    (hw : ∀ w ∈ weights, 1 ≤ w ∧ w ≤ 2) :
    0 ≤ reciprocal weights ∧ reciprocal weights ≤ 1 := by
  induction weights with
  | nil => simp [reciprocal]
  | cons w ws ih =>
    have hh := hw w (by simp)
    have ht := ih (fun v hv => hw v (by simp [hv]))
    change 0 ≤ (2 - w) * reciprocal ws ∧ (2 - w) * reciprocal ws ≤ 1
    constructor
    · exact mul_nonneg (by linarith) ht.1
    · nlinarith [mul_nonneg (show 0 ≤ 2 - w by linarith)
        (show 0 ≤ 1 - reciprocal ws by linarith)]

lemma gibbsWeight_pos [Nonempty ι] (τ : ℝ) (v : ι → ℝ) (i : ι) :
    0 < gibbsWeight τ v i := by
  unfold gibbsWeight
  exact div_pos (Real.exp_pos _) (Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty)

lemma gibbsWeight_sum [Nonempty ι] (τ : ℝ) (v : ι → ℝ) :
    ∑ i, gibbsWeight τ v i = 1 := by
  have hp : 0 < ∑ i, Real.exp (v i / τ) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  simp only [gibbsWeight, ← Finset.sum_div]
  exact div_self hp.ne'

lemma gibbsWeight_log [Nonempty ι] (τ : ℝ) (v : ι → ℝ) (i : ι) :
    Real.log (gibbsWeight τ v i) = v i / τ - Real.log (∑ j, Real.exp (v j / τ)) := by
  have hp : 0 < ∑ j, Real.exp (v j / τ) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  rw [gibbsWeight, Real.log_div (Real.exp_pos _).ne' hp.ne', Real.log_exp]

lemma weight_nonneg (s : Snapshot ι E) (τ : ℝ) (x : E) (i : ι) :
    0 ≤ weight s τ x i := by
  unfold weight gibbsWeight
  positivity

lemma weight_sum [Nonempty ι] (s : Snapshot ι E) (τ : ℝ) (x : E) :
    ∑ i, weight s τ x i = 1 := by
  exact gibbsWeight_sum τ (fun i => affine s i x)

lemma base_norm_le [Nonempty ι] (s : Snapshot ι E) (τ : ℝ) (x : E)
    {G : ℝ} (hG : ∀ i, ‖s.field i‖ ≤ G) : ‖base s τ x‖ ≤ G := by
  unfold base
  calc
    ‖∑ i, weight s τ x i • s.field i‖ ≤
        ∑ i, ‖weight s τ x i • s.field i‖ := norm_sum_le _ _
    _ = ∑ i, weight s τ x i * ‖s.field i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg s τ x i)]
    _ ≤ ∑ i, weight s τ x i * G :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hG i)
        (weight_nonneg s τ x i))
    _ = G := by rw [← Finset.sum_mul, weight_sum, one_mul]

lemma correction_eq (w : ℝ) (g a b : E) :
    correction w g a b = w • g - a - (w - 1) • b := by
  unfold correction
  module

lemma weighted_correction (q w : ι → ℝ) (g a : ι → E)
    (hq : ∑ i, q i = 1) :
    let b := ∑ i, q i • a i
    ∑ i, q i • correction (w i) (g i) (a i) b =
      (∑ i, (q i * w i) • g i) - (∑ i, q i * w i) • b := by
  dsimp only
  simp_rw [correction_eq, smul_sub, smul_smul]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_smul]
  have hw : ∑ i, q i * (w i - 1) = (∑ i, q i * w i) - 1 := by
    simp_rw [mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, hq]
  rw [hw]
  module

lemma correction_norm_le {w D G : ℝ} {g a b : E}
    (hw : 1 ≤ w) (hga : ‖g - a‖ ≤ D) (hab : ‖a - b‖ ≤ 2 * G) :
    ‖correction w g a b‖ ≤ w * D + (w - 1) * (2 * G) := by
  have hw0 : 0 ≤ w := by linarith
  have hw1 : 0 ≤ w - 1 := by linarith
  unfold correction
  calc
    ‖w • (g - a) + (w - 1) • (a - b)‖ ≤
        ‖w • (g - a)‖ + ‖(w - 1) • (a - b)‖ := norm_add_le _ _
    _ = w * ‖g - a‖ + (w - 1) * ‖a - b‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hw0, abs_of_nonneg hw1]
    _ ≤ w * D + (w - 1) * (2 * G) :=
      add_le_add (mul_le_mul_of_nonneg_left hga hw0)
        (mul_le_mul_of_nonneg_left hab hw1)

lemma correction_sq_le {w D G c : ℝ} {g a b : E}
    (hw : 1 ≤ w) (hw2 : w ≤ 2) (hc : w - 1 ≤ 2 * c)
    (hD : 0 ≤ D) (hG : 0 ≤ G)
    (hga : ‖g - a‖ ≤ D) (hab : ‖a - b‖ ≤ 2 * G) :
    ‖correction w g a b‖ ^ 2 ≤ 8 * D ^ 2 + 32 * (G * c) ^ 2 := by
  have hn := correction_norm_le hw hga hab
  have h1 := mul_le_mul_of_nonneg_right hw2 hD
  have h2 := mul_le_mul_of_nonneg_right hc (show 0 ≤ 2 * G by positivity)
  have hbound : ‖correction w g a b‖ ≤ 2 * D + 4 * (G * c) := by
    nlinarith
  have hn0 := norm_nonneg (correction w g a b)
  nlinarith [sq_nonneg (2 * D - 4 * (G * c))]

lemma exp_small_residual {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    1 ≤ Real.exp c ∧ Real.exp c ≤ 2 ∧ Real.exp c - 1 ≤ 2 * c := by
  have he := Real.exp_bound_div_one_sub_of_interval hc (by linarith : c < 1)
  have hden : 0 < 1 - c := by linarith
  have hlin : Real.exp c ≤ 1 + 2 * c := by
    apply he.trans
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hc (show 0 ≤ 1 - 2 * c by linarith)]
  exact ⟨Real.one_le_exp_iff.mpr hc, by linarith, by linarith⟩


lemma probability_log_sensitivity (p q v w : ι → ℝ) {τ B c : ℝ}
    (hτ : 0 < τ) (hB : 0 ≤ B) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1)
    (hlog : ∀ i, τ * (Real.log (p i) - Real.log (q i)) = v i - w i - c)
    (hvw : ∀ i, |v i - w i| ≤ B) :
    ∑ i, |p i - q i| ≤ 2 * B / τ := by
  have h1 := OracleTemplate.SimplexEntropy.relative_entropy_lower
    (fun i => (hp i).le) hq hpsum hqsum
  have h2 := OracleTemplate.SimplexEntropy.relative_entropy_lower
    (fun i => (hq i).le) hp hqsum hpsum
  simp only [abs_sub_comm (q _) (p _)] at h2
  have he : (∑ i, (p i * Real.log (p i) - p i * Real.log (q i))) +
      (∑ i, (q i * Real.log (q i) - q i * Real.log (p i))) =
      ∑ i, (p i - q i) * (Real.log (p i) - Real.log (q i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hs : τ / 2 * (∑ i, |p i - q i|) ^ 2 ≤
      τ * ∑ i, (p i - q i) * (Real.log (p i) - Real.log (q i)) := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hτ.le
    rw [he] at hh
    nlinarith only [hh]
  have hsum : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hpsum, hqsum, sub_self]
  have hi (i : ι) : τ * ((p i - q i) * (Real.log (p i) - Real.log (q i))) =
      (p i - q i) * (v i - w i) - c * (p i - q i) := by
    calc
      _ = (p i - q i) * (τ * (Real.log (p i) - Real.log (q i))) := by ring
      _ = _ := by rw [hlog]; ring
  rw [Finset.mul_sum] at hs
  simp_rw [hi] at hs
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero] at hs
  have hb : (∑ i, (p i - q i) * (v i - w i)) ≤ B * ∑ i, |p i - q i| := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |(p i - q i) * (v i - w i)| := le_abs_self _
      _ = |p i - q i| * |v i - w i| := abs_mul _ _
      _ ≤ |p i - q i| * B := mul_le_mul_of_nonneg_left (hvw i) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hn : 0 ≤ ∑ i, |p i - q i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  apply (le_div_iff₀ hτ).2
  by_contra hh
  have hpos : 0 < ∑ i, |p i - q i| := by
    by_contra hn'
    have hz : (∑ i, |p i - q i|) = 0 := le_antisymm (le_of_not_gt hn') hn
    rw [hz, zero_mul] at hh
    exact hh (by positivity)
  nlinarith only [hs, hb, hpos, lt_of_not_ge hh]



lemma gibbsWeight_difference [Nonempty ι] (v w : ι → ℝ) {τ B : ℝ}
    (hτ : 0 < τ) (hB : 0 ≤ B) (hvw : ∀ i, |v i - w i| ≤ B) :
    ∑ i, |gibbsWeight τ v i - gibbsWeight τ w i| ≤ 2 * B / τ := by
  have hv : 0 < ∑ i, Real.exp (v i / τ) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hw : 0 < ∑ i, Real.exp (w i / τ) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  apply probability_log_sensitivity (gibbsWeight τ v) (gibbsWeight τ w) v w hτ hB
    (gibbsWeight_pos τ v) (gibbsWeight_pos τ w)
    (gibbsWeight_sum τ v) (gibbsWeight_sum τ w) (c :=
      τ * (Real.log (∑ i, Real.exp (v i / τ)) - Real.log (∑ i, Real.exp (w i / τ))))
    _ hvw
  intro i
  unfold gibbsWeight
  rw [Real.log_div (Real.exp_pos _).ne' hv.ne', Real.log_div (Real.exp_pos _).ne' hw.ne',
    Real.log_exp, Real.log_exp]
  field_simp
  ring


lemma probability_mixture_difference (p q : ι → ℝ) (g h : ι → E) {D G B : ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) (hG : 0 ≤ G)
    (hgh : ∀ i, ‖g i - h i‖ ≤ D) (hh : ∀ i, ‖h i‖ ≤ G)
    (hpq : ∑ i, |p i - q i| ≤ B) :
    ‖(∑ i, p i • g i) - ∑ i, q i • h i‖ ≤ D + G * B := by
  have he : (∑ i, p i • g i) - ∑ i, q i • h i =
      (∑ i, p i • (g i - h i)) + ∑ i, (p i - q i) • h i := by
    simp_rw [smul_sub, sub_smul, Finset.sum_sub_distrib]
    module
  have hfirst : ‖∑ i, p i • (g i - h i)‖ ≤ D :=
    norm_sum_smul_le (fun i _ => hp i) hpsum (fun i _ => hgh i)
  have hsecond : ‖∑ i, (p i - q i) • h i‖ ≤ G * B := by
    calc
      _ ≤ ∑ i, ‖(p i - q i) • h i‖ := norm_sum_le _ _
      _ = ∑ i, |p i - q i| * ‖h i‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ i, |p i - q i| * G := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hh i) (abs_nonneg _))
      _ = G * ∑ i, |p i - q i| := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ G * B := mul_le_mul_of_nonneg_left hpq hG
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)


lemma gibbs_reweight [Nonempty ι] (τ : ℝ) (v w : ι → ℝ) (i : ι) :
    gibbsWeight τ v i * Real.exp ((w i - v i) / τ) /
      (∑ j, gibbsWeight τ v j * Real.exp ((w j - v j) / τ)) = gibbsWeight τ w i := by
  have hv : 0 < ∑ j, Real.exp (v j / τ) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hw : 0 < ∑ j, Real.exp (w j / τ) :=
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have he (j : ι) : Real.exp (v j / τ) * Real.exp ((w j - v j) / τ) = Real.exp (w j / τ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hp (j : ι) : gibbsWeight τ v j * Real.exp ((w j - v j) / τ) =
      Real.exp (w j / τ) / ∑ k, Real.exp (v k / τ) := by
    unfold gibbsWeight
    calc
      _ = (Real.exp (v j / τ) * Real.exp ((w j - v j) / τ)) /
          (∑ k, Real.exp (v k / τ)) := by ring
      _ = _ := by rw [he]
  simp_rw [hp]
  rw [← Finset.sum_div]
  unfold gibbsWeight
  field_simp

end LongTails.Proofs.AffineSoftmaxResidual
