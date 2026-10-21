import LongTails.Proofs.GeneralCovarianceReverseFisherDensity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.HasLaw

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralCovarianceReverseFisherTail

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma weighted_variance {k : ℕ} (ρ : Fin k → ℝ) (hρ : ∑ j, ρ j = 1) (w : Fin k → V) :
    ∑ j, ρ j * ‖w j‖ ^ 2 =
      ‖∑ j, ρ j • w j‖ ^ 2 + ∑ j, ρ j * ‖w j - ∑ l, ρ l • w l‖ ^ 2 := by
  set m := ∑ l, ρ l • w l with hm
  have h1 : ∑ j, ρ j * ‖w j - m‖ ^ 2 =
      ∑ j, ρ j * ‖w j‖ ^ 2 - 2 * ⟪m, m⟫ + ‖m‖ ^ 2 := by
    simp_rw [norm_sub_sq_real, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul _ _ (‖m‖ ^ 2), hρ, one_mul]
    congr 2
    rw [hm, sum_inner]
    simp_rw [inner_smul_left, conj_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [h1, real_inner_self_eq_norm_sq]
  ring

lemma norm_sum_sq_le {k : ℕ} (ρ : Fin k → ℝ) (hρ0 : ∀ j, 0 ≤ ρ j) (hρ : ∑ j, ρ j = 1)
    (w : Fin k → V) :
    ‖∑ j, ρ j • w j‖ ^ 2 ≤ ∑ j, ρ j * ‖w j‖ ^ 2 := by
  rw [weighted_variance ρ hρ w]
  have : 0 ≤ ∑ j, ρ j * ‖w j - ∑ l, ρ l • w l‖ ^ 2 :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hρ0 j) (sq_nonneg _))
  linarith

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma integral_exp_inner (w : V) (c : ℝ) :
    ∫ z, Real.exp (c * ⟪w, z⟫) ∂stdGaussian V = Real.exp (‖w‖ ^ 2 * c ^ 2 / 2) := by
  have hX : HasLaw (fun z : V => ⟪w, z⟫) (gaussianReal 0 (‖w‖ ^ 2).toNNReal) (stdGaussian V) :=
    ⟨by fun_prop, by
      change (stdGaussian V).map (innerSL ℝ w) = _
      rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
        variance_dual_stdGaussian, innerSL_apply_norm]⟩
  have h := mgf_gaussianReal hX c
  rw [mgf] at h
  rw [h]
  congr 1
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  ring

lemma integrable_exp_inner (w : V) (c : ℝ) :
    Integrable (fun z => Real.exp (c * ⟪w, z⟫)) (stdGaussian V) := by
  have hX : (stdGaussian V).map (fun z : V => ⟪w, z⟫) = gaussianReal 0 (‖w‖ ^ 2).toNNReal := by
    change (stdGaussian V).map (innerSL ℝ w) = _
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, innerSL_apply_norm]
  have hi := integrable_exp_mul_gaussianReal (μ := 0) (v := (‖w‖ ^ 2).toNNReal) c
  rw [← hX] at hi
  exact (integrable_map_measure (f := fun z : V => ⟪w, z⟫) (g := fun x => Real.exp (c * x))
    (by fun_prop) (by fun_prop)).mp hi

noncomputable def softWeight {k : ℕ} (c : Fin k → V) (z : V) (j : Fin k) : ℝ :=
  Real.exp (-‖z - c j‖ ^ 2 / 2)

noncomputable def softResp {k : ℕ} (c : Fin k → V) (z : V) (j : Fin k) : ℝ :=
  softWeight c z j / ∑ l, softWeight c z l

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma softTotal_pos {k : ℕ} [NeZero k] (c : Fin k → V) (z : V) :
    0 < ∑ l, softWeight c z l :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma softResp_nonneg {k : ℕ} [NeZero k] (c : Fin k → V) (z : V) (j : Fin k) :
    0 ≤ softResp c z j :=
  div_nonneg (Real.exp_pos _).le (softTotal_pos c z).le

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma sum_softResp {k : ℕ} [NeZero k] (c : Fin k → V) (z : V) : ∑ j, softResp c z j = 1 := by
  unfold softResp
  rw [← Finset.sum_div]
  exact div_self (softTotal_pos c z).ne'

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma softResp_le_one {k : ℕ} [NeZero k] (c : Fin k → V) (z : V) (j : Fin k) :
    softResp c z j ≤ 1 := by
  rw [← sum_softResp c z]
  exact Finset.single_le_sum (fun l _ => softResp_nonneg c z l) (Finset.mem_univ j)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma continuous_softResp {k : ℕ} [NeZero k] (c : Fin k → V) (j : Fin k) :
    Continuous (fun z => softResp c z j) := by
  unfold softResp softWeight
  exact (by fun_prop : Continuous fun z : V => Real.exp (-‖z - c j‖ ^ 2 / 2)).div
    (continuous_finsetSum _ (fun l _ => by fun_prop)) (fun z => (softTotal_pos c z).ne')

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma softResp_le_exp {k : ℕ} [NeZero k] (c : Fin k → V) (i : Fin k) (hc : c i = 0) (z : V)
    (j : Fin k) :
    softResp c z j ≤ Real.exp ((⟪c j, z⟫ - ‖c j‖ ^ 2 / 2) / 2) := by
  have h0 := softResp_nonneg c z j
  have h1 := softResp_le_one c z j
  have h2 : softResp c z j ≤ Real.exp (⟪c j, z⟫ - ‖c j‖ ^ 2 / 2) := by
    unfold softResp
    rw [div_le_iff₀ (softTotal_pos c z)]
    have hi : softWeight c z i ≤ ∑ l, softWeight c z l :=
      Finset.single_le_sum (f := fun l => softWeight c z l) (fun l _ => (Real.exp_pos _).le)
        (Finset.mem_univ i)
    have hexp : softWeight c z j = Real.exp (⟪c j, z⟫ - ‖c j‖ ^ 2 / 2) * softWeight c z i := by
      unfold softWeight
      rw [hc, sub_zero, ← Real.exp_add]
      congr 1
      rw [norm_sub_sq_real, real_inner_comm]
      ring
    rw [hexp]
    exact mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le
  have h3 : softResp c z j ^ 2 ≤ Real.exp ((⟪c j, z⟫ - ‖c j‖ ^ 2 / 2) / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]
    push_cast
    calc softResp c z j ^ 2 = softResp c z j * softResp c z j := sq _
      _ ≤ 1 * Real.exp (⟪c j, z⟫ - ‖c j‖ ^ 2 / 2) := mul_le_mul h1 h2 h0 zero_le_one
      _ = _ := by rw [one_mul]; congr 1; ring
  exact (pow_le_pow_iff_left₀ h0 (Real.exp_pos _).le two_ne_zero).mp h3

lemma integral_softResp_le {k : ℕ} [NeZero k] (c : Fin k → V) (i : Fin k) (hc : c i = 0)
    (j : Fin k) :
    ∫ z, softResp c z j ∂stdGaussian V ≤ Real.exp (-‖c j‖ ^ 2 / 8) := by
  have hb : Integrable (fun z => Real.exp ((⟪c j, z⟫ - ‖c j‖ ^ 2 / 2) / 2)) (stdGaussian V) := by
    have := (integrable_exp_inner (c j) (1 / 2)).const_mul (Real.exp (-‖c j‖ ^ 2 / 4))
    refine this.congr (ae_of_all _ (fun z => ?_))
    simp only
    rw [← Real.exp_add]
    congr 1
    ring
  calc ∫ z, softResp c z j ∂stdGaussian V
      ≤ ∫ z, Real.exp ((⟪c j, z⟫ - ‖c j‖ ^ 2 / 2) / 2) ∂stdGaussian V :=
        integral_mono_of_nonneg (ae_of_all _ (fun z => softResp_nonneg c z j)) hb
          (ae_of_all _ (fun z => softResp_le_exp c i hc z j))
    _ = Real.exp (-‖c j‖ ^ 2 / 4) * ∫ z, Real.exp (1 / 2 * ⟪c j, z⟫) ∂stdGaussian V := by
        rw [← integral_const_mul]
        congr 1
        ext z
        rw [← Real.exp_add]
        congr 1
        ring
    _ = Real.exp (-‖c j‖ ^ 2 / 8) := by
        rw [integral_exp_inner, ← Real.exp_add]
        congr 1
        ring

lemma entropy_le {k : ℕ} (p : Fin k → ℝ) (hp0 : ∀ j, 0 ≤ p j) (hp : ∑ j, p j = 1) :
    ∑ j, -(p j * Real.log (p j)) ≤ Real.log k := by
  have hk : (0 : ℝ) < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      simp at hp
    · exact_mod_cast h
  have hj : ∀ j, -(p j * Real.log (p j)) ≤ p j * Real.log k + (1 / k - p j) := by
    intro j
    rcases (hp0 j).lt_or_eq with h | h
    · have hl := Real.log_le_sub_one_of_pos (show 0 < 1 / (k * p j) by positivity)
      rw [Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub,
        Real.log_mul hk.ne' h.ne'] at hl
      have : p j * (1 / (k * p j)) = 1 / k := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hl (hp0 j)]
    · rw [← h]
      simp only [zero_mul, neg_zero, zero_add, sub_zero]
      positivity
  calc ∑ j, -(p j * Real.log (p j)) ≤ ∑ j, (p j * Real.log k + (1 / k - p j)) :=
        Finset.sum_le_sum (fun j _ => hj j)
    _ = Real.log k := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp, Finset.sum_sub_distrib, hp]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have : (k : ℝ) * (1 / k) = 1 := by field_simp
        linarith

lemma tail_bound {k : ℕ} [NeZero k] (c : Fin k → V) (i : Fin k) (hc : c i = 0) :
    ∫ z, ‖∑ j, softResp c z j • c j‖ ^ 2 ∂stdGaussian V ≤ 8 * Real.log k := by
  set p : Fin k → ℝ := fun j => ∫ z, softResp c z j ∂stdGaussian V with hpdef
  have hint : ∀ j, Integrable (fun z => softResp c z j) (stdGaussian V) := fun j =>
    (integrable_const (1 : ℝ)).mono' (continuous_softResp c j).aestronglyMeasurable
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (softResp_nonneg c z j)]
        exact softResp_le_one c z j))
  have hp0 : ∀ j, 0 ≤ p j := fun j => integral_nonneg (fun z => softResp_nonneg c z j)
  have hp1 : ∑ j, p j = 1 := by
    simp only [hpdef]
    rw [← integral_finsetSum _ (fun j _ => hint j)]
    simp [sum_softResp]
  have hbd : ∀ j, p j * ‖c j‖ ^ 2 ≤ 8 * -(p j * Real.log (p j)) := by
    intro j
    rcases (hp0 j).lt_or_eq with h | h
    · have hle := integral_softResp_le c i hc j
      have hlog : Real.log (p j) ≤ -‖c j‖ ^ 2 / 8 := by
        rw [Real.log_le_iff_le_exp h]; exact hle
      nlinarith
    · rw [← h]; simp
  have hcont : Continuous (fun z => ‖∑ j, softResp c z j • c j‖ ^ 2) :=
    (continuous_finsetSum _ (fun j _ => (continuous_softResp c j).smul continuous_const)).norm.pow 2
  calc ∫ z, ‖∑ j, softResp c z j • c j‖ ^ 2 ∂stdGaussian V
      ≤ ∫ z, ∑ j, softResp c z j * ‖c j‖ ^ 2 ∂stdGaussian V := by
        refine integral_mono_of_nonneg (ae_of_all _ (fun z => sq_nonneg _))
          (integrable_finsetSum _ (fun j _ => (hint j).mul_const _))
          (ae_of_all _ (fun z => norm_sum_sq_le _ (softResp_nonneg c z) (sum_softResp c z) _))
    _ = ∑ j, p j * ‖c j‖ ^ 2 := by
        rw [integral_finsetSum _ (fun j _ => (hint j).mul_const _)]
        simp_rw [integral_mul_const]
        rfl
    _ ≤ ∑ j, 8 * -(p j * Real.log (p j)) := Finset.sum_le_sum (fun j _ => hbd j)
    _ ≤ 8 * Real.log k := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (entropy_le p hp0 hp1) (by norm_num)

end LongTails.Proofs.GeneralCovarianceReverseFisherTail
