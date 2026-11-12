import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import LongTails.Proofs.SimplexEntropy
import LongTails.Proofs.AffineSoftmaxResidual

namespace LongTails.Proofs.AffineResidualEntropy

noncomputable def divergence {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, (p i * Real.log (p i) - p i * Real.log (q i))

lemma divergence_nonneg {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) : 0 ≤ divergence p q := by
  have h := OracleTemplate.SimplexEntropy.relative_entropy_lower hp hq hpsum hqsum
  exact le_trans (by positivity) h

lemma divergence_three_point {ι : Type*} [Fintype ι] (u p q : ι → ℝ) :
    divergence u p - divergence u q - divergence q p =
      ∑ i, (u i - q i) * (Real.log (q i) - Real.log (p i)) := by
  unfold divergence
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma entropy_model_bound {ι : Type*} [Fintype ι] {p q u s : ι → ℝ} {c : ℝ}
    (hu : ∀ i, 0 ≤ u i) (hq : ∀ i, 0 < q i)
    (husum : ∑ i, u i = 1) (hqsum : ∑ i, q i = 1)
    (hlog : ∀ i, Real.log (q i) = Real.log (p i) - s i - c) :
    (∑ i, (p i - u i) * s i) - divergence u p ≤ c + ∑ i, p i * s i := by
  have hn := divergence_nonneg hu hq husum hqsum
  have he : divergence u q = divergence u p + (∑ i, u i * s i) + c := by
    unfold divergence
    simp_rw [hlog]
    have hi i : u i * Real.log (u i) - u i * (Real.log (p i) - s i - c) =
        (u i * Real.log (u i) - u i * Real.log (p i)) + u i * s i + u i * c := by ring
    simp_rw [hi]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, husum, one_mul]
  rw [he] at hn
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  linarith

lemma exp_quadratic_of_abs_le_one {s : ℝ} (hs : |s| ≤ 1) :
    Real.exp s ≤ 1 + s + s ^ 2 := by
  have h := Real.exp_bound hs (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, sq_abs] at h
  have hh := (abs_le.mp h).2
  nlinarith [sq_nonneg s]

lemma exp_neg_quadratic {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-s) ≤ 1 - s + s ^ 2 := by
  have hp : 0 < 1 + s := by linarith
  have he : 1 + s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
  calc
    Real.exp (-s) = 1 / Real.exp s := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (1 + s) := one_div_le_one_div_of_le hp he
    _ ≤ 1 - s + s ^ 2 := by
      apply (div_le_iff₀ hp).mpr
      nlinarith [mul_nonneg hs (sq_nonneg s)]

lemma log_mixture_bound {ι : Type*} [Fintype ι] (p s : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hs : ∀ i, 0 ≤ s i) :
    Real.log (∑ i, p i * Real.exp (-s i)) ≤
      -(∑ i, p i * s i) + ∑ i, p i * (s i) ^ 2 := by
  have hpos : 0 < ∑ i, p i * Real.exp (-s i) := by
    have hex : ∃ i, 0 < p i := by
      by_contra hn
      push Not at hn
      have hz : ∑ i, p i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (hn i) (hp i)
      linarith
    obtain ⟨i, hi⟩ := hex
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hp j) (Real.exp_pos _).le)
      ⟨i, Finset.mem_univ i, mul_pos hi (Real.exp_pos _)⟩
  have hb : (∑ i, p i * Real.exp (-s i)) ≤
      1 - (∑ i, p i * s i) + ∑ i, p i * (s i) ^ 2 := by
    calc
      _ ≤ ∑ i, p i * (1 - s i + (s i) ^ 2) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (exp_neg_quadratic (hs i)) (hp i)
      _ = _ := by simp only [mul_add, mul_sub, mul_one, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, hpsum]
  have hl := Real.log_le_sub_one_of_pos hpos
  linarith

lemma log_mixture_signed_bound {ι : Type*} [Fintype ι] (p s : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hs : ∀ i, |s i| ≤ 1) :
    Real.log (∑ i, p i * Real.exp (s i)) ≤
      (∑ i, p i * s i) + ∑ i, p i * (s i) ^ 2 := by
  have hpos : 0 < ∑ i, p i * Real.exp (s i) := by
    have hex : ∃ i, 0 < p i := by
      by_contra hn
      push Not at hn
      have hz : ∑ i, p i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (hn i) (hp i)
      linarith
    obtain ⟨i, hi⟩ := hex
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hp j) (Real.exp_pos _).le)
      ⟨i, Finset.mem_univ i, mul_pos hi (Real.exp_pos _)⟩
  have hb : (∑ i, p i * Real.exp (s i)) ≤
      1 + (∑ i, p i * s i) + ∑ i, p i * (s i) ^ 2 := by
    calc
      _ ≤ ∑ i, p i * (1 + s i + (s i) ^ 2) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (exp_quadratic_of_abs_le_one (hs i)) (hp i)
      _ = _ := by simp only [mul_add, mul_one, Finset.sum_add_distrib, hpsum]
  have hl := Real.log_le_sub_one_of_pos hpos
  linarith

lemma entropy_log_model_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    {p u : ι → ℝ} (s : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hu : ∀ i, 0 ≤ u i) (husum : ∑ i, u i = 1) :
    (∑ i, (p i - u i) * s i) - divergence u p ≤
      Real.log (∑ i, p i * Real.exp (-s i)) + ∑ i, p i * s i := by
  let q := LongTails.Algorithms.AffineSoftmaxEstimator.gibbsWeight 1
    (fun i => Real.log (p i) - s i)
  have he i : Real.exp (Real.log (p i) - s i) = p i * Real.exp (-s i) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (hp i)]
  apply entropy_model_bound (q := q) hu
    (LongTails.Proofs.AffineSoftmaxResidual.gibbsWeight_pos _ _)
    husum (LongTails.Proofs.AffineSoftmaxResidual.gibbsWeight_sum _ _)
  intro i
  dsimp only [q]
  rw [LongTails.Proofs.AffineSoftmaxResidual.gibbsWeight_log]
  simp only [div_one, he]

lemma entropy_nonnegative_step {ι : Type*} [Fintype ι] [Nonempty ι]
    {p u : ι → ℝ} (s : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hpsum : ∑ i, p i = 1) (hu : ∀ i, 0 ≤ u i) (husum : ∑ i, u i = 1)
    (hs : ∀ i, 0 ≤ s i) :
    (∑ i, (p i - u i) * s i) - divergence u p ≤ ∑ i, p i * (s i) ^ 2 := by
  have h := entropy_log_model_bound s hp hu husum
  have hl := log_mixture_bound p s (fun i => (hp i).le) hpsum hs
  linarith

lemma entropy_signed_step {ι : Type*} [Fintype ι] [Nonempty ι]
    {p u : ι → ℝ} (s : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hpsum : ∑ i, p i = 1) (hu : ∀ i, 0 ≤ u i) (husum : ∑ i, u i = 1)
    (hs : ∀ i, |s i| ≤ 1) :
    (∑ i, (p i - u i) * s i) - divergence u p ≤ ∑ i, p i * (s i) ^ 2 := by
  have h := entropy_log_model_bound s hp hu husum
  have hl := log_mixture_signed_bound p (fun i => -s i) (fun i => (hp i).le) hpsum
    (fun i => by simpa only [abs_neg] using hs i)
  simp only [mul_neg, Finset.sum_neg_distrib, neg_sq] at hl
  linarith

lemma scaled_step {ι : Type*} [Fintype ι] {p u b : ι → ℝ} {a η : ℝ}
    (ha : 0 < a)
    (hstep : (∑ i, (p i - u i) * (η * b i / a)) - divergence u p ≤
      ∑ i, p i * (η * b i / a) ^ 2) :
    η * (∑ i, (p i - u i) * b i) - a * divergence u p ≤
      η ^ 2 / a * ∑ i, p i * (b i) ^ 2 := by
  have hlin : (∑ i, (p i - u i) * (η * b i / a)) =
      η / a * ∑ i, (p i - u i) * b i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsq : (∑ i, p i * (η * b i / a) ^ 2) =
      η ^ 2 / a ^ 2 * ∑ i, p i * (b i) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hlin, hsq] at hstep
  have h := mul_le_mul_of_nonneg_left hstep ha.le
  convert h using 1 <;> field_simp

lemma simplex_entropy_nonpos {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    (∑ i, p i * Real.log (p i)) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i _
  have hi : p i ≤ 1 := by
    rw [← hpsum]
    exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  by_cases hz : p i = 0
  · simp [hz]
  · exact mul_nonpos_of_nonneg_of_nonpos (hp i)
      (Real.log_nonpos (lt_of_le_of_ne (hp i) (Ne.symm hz)).le hi)

lemma uniform_divergence_bound {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    divergence p (fun _ => (Fintype.card ι : ℝ)⁻¹) ≤ Real.log (Fintype.card ι) := by
  have he := simplex_entropy_nonpos hp hpsum
  simp only [divergence, Real.log_inv, mul_neg, sub_neg_eq_add,
    Finset.sum_add_distrib, ← Finset.sum_mul, hpsum, one_mul]
  linarith

open LongTails.Algorithms.AffineSoftmaxEstimator in
lemma gibbs_divergence_identity {ι : Type*} [Fintype ι] [Nonempty ι]
    {τ : ℝ} (hτ : τ ≠ 0) (values p : ι → ℝ) (hpsum : ∑ i, p i = 1) :
    τ * divergence p (gibbsWeight τ values) =
      smoothValue τ values - (∑ i, p i * values i) + τ * ∑ i, p i * Real.log (p i) := by
  have he (i : ι) : τ * (p i * Real.log (p i) - p i * Real.log (gibbsWeight τ values i)) =
      τ * (p i * Real.log (p i)) - p i * values i + p i * smoothValue τ values := by
    rw [AffineSoftmaxResidual.gibbsWeight_log]
    unfold smoothValue
    field_simp
    ring
  unfold divergence
  rw [Finset.mul_sum]
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, hpsum]
  ring

open LongTails.Algorithms.AffineSoftmaxEstimator in
lemma gibbs_variational_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    {τ : ℝ} (hτ : 0 < τ) (values p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1) :
    (∑ i, p i * values i) - τ * ∑ i, p i * Real.log (p i) ≤ smoothValue τ values := by
  have hn := divergence_nonneg hp (AffineSoftmaxResidual.gibbsWeight_pos τ values)
    hpsum (AffineSoftmaxResidual.gibbsWeight_sum τ values)
  have he := gibbs_divergence_identity hτ.ne' values p hpsum
  nlinarith

open LongTails.Algorithms.AffineSoftmaxEstimator in
lemma gibbs_variational_eq {ι : Type*} [Fintype ι] [Nonempty ι]
    {τ : ℝ} (hτ : τ ≠ 0) (values : ι → ℝ) :
    (∑ i, gibbsWeight τ values i * values i) -
      τ * ∑ i, gibbsWeight τ values i * Real.log (gibbsWeight τ values i) = smoothValue τ values := by
  have he := gibbs_divergence_identity hτ values (gibbsWeight τ values)
    (AffineSoftmaxResidual.gibbsWeight_sum τ values)
  simp only [divergence, sub_self, Finset.sum_const_zero, mul_zero] at he
  linarith

end LongTails.Proofs.AffineResidualEntropy
