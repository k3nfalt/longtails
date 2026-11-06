import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

open scoped BigOperators NNReal

namespace LongTails.Proofs.StratifiedSubGaussianSampling

lemma ceiling_cost {T : ℕ} (N : ℕ) (w : Fin T → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1) :
    ∑ i, ⌈(N : ℝ)*w i⌉₊ ≤ N+T := by
  have h (i : Fin T) : (⌈(N : ℝ)*w i⌉₊ : ℝ) ≤ (N : ℝ)*w i+1 :=
    (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg N) (hw i))).le
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin T))) => h i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hwsum] at hh
  simpa only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, ← Nat.cast_sum, ← Nat.cast_add, Nat.cast_le] using hh

lemma ceiling_positive (N : ℕ) (hN : 0 < N) (w : ℝ) (hw : 0 < w) :
    0 < ⌈(N : ℝ)*w⌉₊ := by
  have hn : 0 < (N : ℝ)*w := mul_pos (by exact_mod_cast hN) hw
  exact Nat.ceil_pos.mpr hn

lemma scalar_coefficient_square (N : ℕ) (hN : 0 < N) (w : ℝ) (hw : 0 ≤ w) :
    w ^ 2 / (⌈(N : ℝ)*w⌉₊ : ℝ) ≤ w/N := by
  by_cases hw0 : w = 0
  · subst w; simp
  have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hc : 0 < (⌈(N : ℝ)*w⌉₊ : ℝ) := by exact_mod_cast ceiling_positive N hN w hwpos
  apply (div_le_div_iff₀ hc hn).mpr
  have hceil := Nat.le_ceil ((N : ℝ)*w)
  have hh := mul_le_mul_of_nonneg_left hceil hw
  nlinarith

lemma sum_scalar_coefficient_square {T : ℕ} (N : ℕ) (hN : 0 < N) (w : Fin T → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1) :
    ∑ i, w i ^ 2 / (⌈(N : ℝ)*w i⌉₊ : ℝ) ≤ 1/(N : ℝ) := by
  calc
    ∑ i, w i ^ 2 / (⌈(N : ℝ)*w i⌉₊ : ℝ) ≤ ∑ i, w i/N :=
      Finset.sum_le_sum fun i _ => scalar_coefficient_square N hN (w i) (hw i)
    _ = _ := by rw [← Finset.sum_div, hwsum]

lemma weaken_proxy {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {X : Ω → ℝ} {c d : ℝ≥0} (h : ProbabilityTheory.HasSubgaussianMGF X c P)
    (hcd : c ≤ d) : ProbabilityTheory.HasSubgaussianMGF X d P := by
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans (Real.exp_le_exp.mpr ?_)⟩
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (show (c : ℝ) ≤ d from hcd) (sq_nonneg t)) (by norm_num)

lemma expanded_coefficient_square_sum {T : ℕ} (N : ℕ) (hN : 0 < N) (w : Fin T → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1) :
    (∑ j : (i : Fin T) × Fin ⌈(N : ℝ)*w i⌉₊,
      (w j.1 / (⌈(N : ℝ)*w j.1⌉₊ : ℝ)) ^ 2) ≤ 1/(N : ℝ) := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have he (i : Fin T) : (⌈(N : ℝ)*w i⌉₊ : ℝ) * (w i/(⌈(N : ℝ)*w i⌉₊ : ℝ))^2 =
      w i^2/(⌈(N : ℝ)*w i⌉₊ : ℝ) := by
    by_cases hc : (⌈(N : ℝ)*w i⌉₊ : ℝ) = 0
    · simp [hc]
    · field_simp
  simp_rw [he]
  exact sum_scalar_coefficient_square N hN w hw hwsum

lemma stratified_sum_mgf {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {T : ℕ} (N : ℕ) (hN : 0 < N) (w : Fin T → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (X : ((i : Fin T) × Fin ⌈(N : ℝ)*w i⌉₊) → Ω → ℝ)
    (hind : ProbabilityTheory.iIndepFun X P) (variance : ℝ≥0)
    (hmgf : ∀ j, ProbabilityTheory.HasSubgaussianMGF (X j) variance P) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun ω => ∑ j : (i : Fin T) × Fin ⌈(N : ℝ)*w i⌉₊,
        (w j.1/(⌈(N : ℝ)*w j.1⌉₊ : ℝ)) * X j ω)
      ⟨(variance : ℝ)/N, by positivity⟩ P := by
  let a := fun j : (i : Fin T) × Fin ⌈(N : ℝ)*w i⌉₊ =>
    w j.1/(⌈(N : ℝ)*w j.1⌉₊ : ℝ)
  have hi := hind.comp (fun j x => a j*x) (fun _ => measurable_const.mul measurable_id)
  have hh := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun hi
    (s := Finset.univ) (fun j _ => (hmgf j).const_mul (a j))
  apply weaken_proxy hh
  apply NNReal.coe_le_coe.mp
  push_cast
  change (∑ j : (i : Fin T) × Fin ⌈(N : ℝ)*w i⌉₊, a j^2 * (variance : ℝ)) ≤ (variance : ℝ)/N
  rw [← Finset.sum_mul]
  have hc := expanded_coefficient_square_sum N hN w hw hwsum
  exact (mul_le_mul_of_nonneg_right hc variance.coe_nonneg).trans_eq (by ring)

lemma ceiling_weight_normalization (N : ℕ) (hN : 0 < N) (w : ℝ) (hw : 0 ≤ w) :
    (⌈(N : ℝ)*w⌉₊ : ℝ)*(w/(⌈(N : ℝ)*w⌉₊ : ℝ)) = w := by
  by_cases hw0 : w = 0
  · simp [hw0]
  have hc : (⌈(N : ℝ)*w⌉₊ : ℝ) ≠ 0 := by
    exact_mod_cast (ceiling_positive N hN w (lt_of_le_of_ne hw (Ne.symm hw0))).ne'
  field_simp

lemma stratified_centered_identity {T : ℕ} (N : ℕ) (hN : 0 < N) (w : Fin T → ℝ)
    (hw : ∀ i, 0 ≤ w i) (μ : Fin T → ℝ)
    (Y : ((i : Fin T) × Fin ⌈(N : ℝ)*w i⌉₊) → ℝ) :
    (∑ i, w i/(⌈(N : ℝ)*w i⌉₊ : ℝ) * ∑ j, Y ⟨i,j⟩) - ∑ i, w i*μ i =
      ∑ j : (i : Fin T) × Fin ⌈(N : ℝ)*w i⌉₊,
        (w j.1/(⌈(N : ℝ)*w j.1⌉₊ : ℝ))*(Y j-μ j.1) := by
  rw [← Finset.sum_sub_distrib, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, ceiling_weight_normalization N hN (w i) (hw i)]

end LongTails.Proofs.StratifiedSubGaussianSampling
