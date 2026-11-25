import LongTails.Proofs.CyclicLogisticInradius
import LongTails.Proofs.CyclicLogisticWaves
import LongTails.Proofs.FiniteLogisticHardFamily

open scoped RealInnerProductSpace
open LongTails.Setups.CyclicLogisticFeatureLearning
open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)
open LongTails.Proofs.CyclicLogisticWaves
open LongTails.Proofs.CyclicLogisticInradius

namespace LongTails.Proofs.CyclicLogisticComparison

@[reducible] noncomputable def params (m : ℕ) : Params :=
  ⟨dim m, 6, 2 * amplitude m, 1 / 4, 1 / 512⟩

noncomputable def examples (m : ℕ) : Data (params m) :=
  fun i => (1 / 2 : ℝ) • FiniteLogisticHardFamily.data (dc m) (square m) (nyquist m) (amplitude m) i

private noncomputable def coeff : Fin 6 → ℝ := ![0,0,0,1/256,1/256,-1/256]

private lemma coeff_bound (i : Fin 6) : |coeff i| ≤ 1 / 256 := by fin_cases i <;> norm_num [coeff]

private noncomputable def e (m : ℕ) := (Real.sqrt 2 / 2) • dc m
private noncomputable def f (m : ℕ) := (1 / 256 : ℝ) • sumFeature (square m)

set_option maxHeartbeats 1500000 in
private lemma features (m : ℕ) (i : Fin 6) :
    sumFeature (examples m i) = axes (e m) (f m) i ∧
    diffFeature (examples m i) = (amplitude m * Real.sqrt 2 / 2) • nyquist m +
      coeff i • diffFeature (square m) := by
  obtain ⟨hz,hz',hv,hv'⟩ := feature_eigen m
  have hneg {d : ℕ} (a : Features d) : sumFeature (-a) = -sumFeature a ∧ diffFeature (-a) = -diffFeature a := by
    simpa using feature_smul (-1 : ℝ) a
  fin_cases i <;>
    simp [examples, FiniteLogisticHardFamily.data, axes, e, f, coeff,
      (feature_smul ..).1, (feature_smul ..).2, (feature_add ..).1, (feature_add ..).2,
      (hneg ..).1, (hneg ..).2, hz,hz',hv,hv', smul_smul] <;> constructor <;> module

lemma valid (m : ℕ) : spec.valid (params m) := by
  have h := amplitude_pos m
  have h' := amplitude_le m
  change 0 < 2 * _ ∧ 2 * _ ≤ 1 ∧ (0:ℝ) < 1/4 ∧ (1:ℝ)/4 ≤ 1 ∧
    (0:ℝ) < 1/512 ∧ (1:ℝ)/512 ≤ 1 ∧ 0 < dim m ∧ Even (dim m)
  refine ⟨by linarith, by linarith, by norm_num, by norm_num, by norm_num, by norm_num,
    by unfold dim half; omega, ⟨half m, rfl⟩⟩

lemma geometry (m : ℕ) : Geometry (params m) (examples m) := by
  obtain ⟨hz, _, hv, _, hzv, _⟩ := modes m
  rw [real_inner_self_eq_norm_sq] at hz hv
  have hnz : ‖dc m‖ = 1 := by nlinarith [norm_nonneg (dc m)]
  have hnv : ‖nyquist m‖ = 1 := by nlinarith [norm_nonneg (nyquist m)]
  obtain ⟨heq,hed,hfv,hdv,hfd⟩ := orthogonal_modes m
  obtain ⟨hl,hu⟩ := norm_square_sum m
  have h₂ := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hp := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)
  have hl₂ : 1 ≤ Real.sqrt 2 := by nlinarith
  have hu₂ : Real.sqrt 2 ≤ 2 := by nlinarith
  have ha := amplitude_pos m
  have hne : ‖e m‖ = Real.sqrt 2 / 2 := by simp [e,norm_smul,Real.norm_eq_abs,abs_of_pos, hp,hnz]
  have hnf : ‖f m‖ = 1/256 * ‖sumFeature (square m)‖ := by norm_num [f,norm_smul,Real.norm_eq_abs]
  have hf (i : Fin 6) := features m i
  constructor
  · intro i
    rw [(hf i).1]
    fin_cases i <;> simp [axes, hne, hnf] <;> linarith
  · intro i
    rw [(hf i).2]
    change _ ≤ 2 * amplitude m
    have h := norm_add_le ((amplitude m * Real.sqrt 2 / 2) • nyquist m)
      (coeff i • diffFeature (square m))
    simp only [norm_smul, Real.norm_eq_abs, hnv, mul_one, square_diff,
      abs_of_pos (by positivity : 0 < amplitude m * Real.sqrt 2 / 2)] at h
    nlinarith [mul_le_mul_of_nonneg_right (coeff_bound i) ha.le, mul_le_mul_of_nonneg_left hu₂ ha.le]
  · intro i j
    rw [(hf i).1,(hf j).2]
    fin_cases i <;> simp [axes, e, f, inner_add_right, inner_neg_left, real_inner_smul_left,
      real_inner_smul_right, hzv,hed,hfv,hfd]
  · have heq' : sumFeature ∘ examples m = axes (e m) (f m) := funext fun i => (hf i).1
    rw [heq']
    intro v hv'
    have h := inradius (e m) (f m) (r := 1/256) (by norm_num)
      (by rw [hne]; linarith) (by rw [hnf]; linarith)
      (by simp [e,f,real_inner_smul_left,real_inner_smul_right,heq]) v hv'
    obtain ⟨i,hi⟩ := h
    exact ⟨i, by rw [(hf i).1]; change _ ≤ -(1/512:ℝ)*_; norm_num at hi ⊢; exact hi⟩
  · refine ⟨nyquist m, hnv, fun i => ?_⟩
    rw [(hf i).2, inner_add_left, real_inner_smul_left, real_inner_smul_left, hdv,
      real_inner_self_eq_norm_sq, hnv]
    change 2 * amplitude m * (1/4) ≤ _
    nlinarith [mul_le_mul_of_nonneg_right hl₂ ha.le]

lemma linear_delay (m : ℕ) (η : ℝ) (hη : 0 < η) (k : ℕ) (hk : 1048576 * k ≤ dim m) :
    ¬ ∀ i, 0 < ⟪examples m i, FiniteLogisticHardFamily.linearPath (examples m) η k⟫ := by
  let D := FiniteLogisticHardFamily.data (dc m) (square m) (nyquist m) (amplitude m)
  obtain ⟨hz,hc,hv,hzc,hzv,hcv⟩ := modes m
  have h : 1048576 * (k : ℝ) * amplitude m ^ 2 ≤ 1 := by
    have hk' : 1048576 * (k : ℝ) ≤ dim m := by exact_mod_cast hk
    nlinarith [mul_le_mul_of_nonneg_right hk' (sq_nonneg (amplitude m)), amplitude_sq m]
  apply mt _ (FiniteLogisticHardFamily.fails_to_separate (dc m) (square m) (nyquist m)
    (η := η * (1/2) ^ 2) (by positivity) hz hc hv hzc hzv hcv k h)
  intro hs i
  have hi := hs i
  change 0 < ⟪(1/2 : ℝ) • D i, FiniteLogisticHardFamily.linearPath (fun j => (1/2 : ℝ) • D j) η k⟫ at hi
  rw [real_inner_smul_left, ← real_inner_smul_right, FiniteLogisticHardFamily.scaled_path] at hi
  exact hi

end LongTails.Proofs.CyclicLogisticComparison
