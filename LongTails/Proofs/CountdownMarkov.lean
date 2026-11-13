import LongTails.Proofs.FiniteMarkovLaw
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic

namespace OracleTemplate.CountdownMarkov

def step (H : ℕ) (jump : Bool) (x : ℕ) : ℕ :=
  if x = 0 then if jump then H else 0 else x - 1

def run (H : ℕ) (jumps : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, x => x
  | n + 1, x => step H (jumps n) (run H jumps n x)

lemma step_false (H x : ℕ) : step H false x = x - 1 := by
  simp only [step, Bool.false_eq_true, ↓reduceIte]
  split_ifs <;> omega

lemma step_le {H x : ℕ} (hx : x ≤ H) (jump : Bool) : step H jump x ≤ H := by
  unfold step
  split_ifs <;> omega

lemma run_le {H x : ℕ} (hx : x ≤ H) (jumps : ℕ → Bool) (n : ℕ) :
    run H jumps n x ≤ H := by
  induction n with
  | zero => exact hx
  | succ n ih => exact step_le ih _

lemma run_no_jump (H x n : ℕ) (jumps : ℕ → Bool)
    (h : ∀ k < n, jumps k = false) : run H jumps n x = x - n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, h n (by omega), step_false, ih (fun k hk => h k (by omega))]
    omega

lemma coalesce_no_jump {H x y : ℕ} (hx : x ≤ H) (hy : y ≤ H)
    (jumps : ℕ → Bool) (h : ∀ k < H, jumps k = false) :
    run H jumps H x = run H jumps H y := by
  rw [run_no_jump H x H jumps h, run_no_jump H y H jumps h]
  omega

open MeasureTheory ProbabilityTheory

noncomputable def kernel (H : ℕ) (p : unitInterval) : Kernel ℝ ℝ := by
  classical
  exact Kernel.piecewise (measurableSet_singleton (0 : ℝ))
    (Kernel.const ℝ (bernoulliMeasure (H : ℝ) 0 p))
    (Kernel.deterministic (fun x : ℝ => max 0 (x - 1)) (by fun_prop))

instance kernel_markov (H : ℕ) (p : unitInterval) : IsMarkovKernel (kernel H p) := by
  unfold kernel
  infer_instance

lemma kernel_zero (H : ℕ) (p : unitInterval) :
    kernel H p 0 = bernoulliMeasure (H : ℝ) 0 p := by
  simp [kernel, Kernel.piecewise_apply]

lemma kernel_nonzero (H : ℕ) (p : unitInterval) {x : ℝ} (hx : x ≠ 0) :
    kernel H p x = Measure.dirac (max 0 (x - 1)) := by
  simp [kernel, Kernel.piecewise_apply, hx, Kernel.deterministic_apply]

lemma kernel_succ (H n : ℕ) (p : unitInterval) :
    kernel H p (n + 1 : ℕ) = Measure.dirac (n : ℝ) := by
  rw [kernel_nonzero H p (by positivity)]
  congr 1
  push_cast
  simp

noncomputable def weight (H : ℕ) (p : unitInterval) (i : Fin (H + 1)) : ℝ :=
  if i = 0 then 1 / (1 + H * (p : ℝ)) else (p : ℝ) / (1 + H * (p : ℝ))

lemma weight_nonneg (H : ℕ) (p : unitInterval) (i : Fin (H + 1)) :
    0 ≤ weight H p i := by
  have hp : 0 ≤ (p : ℝ) := p.property.1
  unfold weight
  split_ifs <;> positivity

lemma weight_sum (H : ℕ) (p : unitInterval) :
    ∑ i : Fin (H + 1), weight H p i = 1 := by
  have hp : 0 ≤ (p : ℝ) := p.property.1
  have hd : 0 < 1 + H * (p : ℝ) := by positivity
  rw [Fin.sum_univ_succ]
  simp [weight, Fin.succ_ne_zero]
  field_simp

noncomputable def stationaryMeasure (H : ℕ) (p : unitInterval) : Measure ℝ :=
  Measure.sum (fun i : Fin (H + 1) =>
    ENNReal.ofReal (weight H p i) • Measure.dirac (i.val : ℝ))

instance stationaryMeasure_probability (H : ℕ) (p : unitInterval) :
    IsProbabilityMeasure (stationaryMeasure H p) := by
  apply HasSum.isProbabilityMeasure_sum_dirac (weight_nonneg H p)
  simpa only [weight_sum H p] using hasSum_fintype (weight H p)

noncomputable def stationaryLaw (H : ℕ) (p : unitInterval) : ProbabilityMeasure ℝ :=
  ⟨stationaryMeasure H p, inferInstance⟩

lemma stationary_weight_identity {K : Type*} [CommSemiring K]
    (H : ℕ) (a b p r : K) (hab : a * p = b) (har : a * r + b = a)
    (f : ℕ → K) :
    a * (p * f H + r * f 0) + b * ∑ i ∈ Finset.range H, f i =
      a * f 0 + b * ∑ i ∈ Finset.range H, f (i + 1) := by
  have hs : f H + ∑ i ∈ Finset.range H, f i =
      f 0 + ∑ i ∈ Finset.range H, f (i + 1) := by
    have h := Finset.sum_range_succ' f H
    rw [Finset.sum_range_succ] at h
    simpa only [add_comm] using h
  calc
    _ = a * r * f 0 + b * (f H + ∑ i ∈ Finset.range H, f i) := by
      rw [mul_add, ← mul_assoc, hab]
      ring
    _ = a * r * f 0 + b * (f 0 + ∑ i ∈ Finset.range H, f (i + 1)) := by rw [hs]
    _ = (a * r + b) * f 0 + b * ∑ i ∈ Finset.range H, f (i + 1) := by ring
    _ = _ := by rw [har]

lemma stationaryMeasure_apply (H : ℕ) (p : unitInterval) {s : Set ℝ}
    (hs : MeasurableSet s) :
    stationaryMeasure H p s =
      ENNReal.ofReal (1 / (1 + H * (p : ℝ))) * Measure.dirac (0 : ℝ) s +
      ENNReal.ofReal ((p : ℝ) / (1 + H * (p : ℝ))) *
        ∑ i : Fin H, Measure.dirac ((i.val : ℝ) + 1) s := by
  rw [stationaryMeasure, Measure.sum_apply _ hs, tsum_fintype, Fin.sum_univ_succ]
  simp only [weight, ↓reduceIte, Fin.succ_ne_zero, Fin.val_zero, Nat.cast_zero,
    Measure.smul_apply, smul_eq_mul, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  rw [Finset.mul_sum]

lemma stationaryMeasure_comp_apply (H : ℕ) (p : unitInterval) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (kernel H p ∘ₘ stationaryMeasure H p) s =
      ENNReal.ofReal (1 / (1 + H * (p : ℝ))) * bernoulliMeasure (H : ℝ) 0 p s +
      ENNReal.ofReal ((p : ℝ) / (1 + H * (p : ℝ))) *
        ∑ i : Fin H, Measure.dirac (i.val : ℝ) s := by
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [stationaryMeasure, lintegral_sum_measure, lintegral_smul_measure,
    lintegral_dirac' _ (Kernel.measurable_coe _ hs), tsum_fintype]
  rw [Fin.sum_univ_succ]
  simp only [weight, ↓reduceIte, Fin.succ_ne_zero, Fin.val_zero, Nat.cast_zero,
    kernel_zero, Fin.val_succ, kernel_succ, smul_eq_mul]
  rw [Finset.mul_sum]

lemma stationary (H : ℕ) (p : unitInterval) :
    kernel H p ∘ₘ stationaryMeasure H p = stationaryMeasure H p := by
  have hp : 0 ≤ (p : ℝ) := p.property.1
  have hp1 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.property.2
  have hd : 0 < 1 + H * (p : ℝ) := by positivity
  have hab : ENNReal.ofReal (1 / (1 + H * (p : ℝ))) * ENNReal.ofReal (p : ℝ) =
      ENNReal.ofReal ((p : ℝ) / (1 + H * (p : ℝ))) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have har : ENNReal.ofReal (1 / (1 + H * (p : ℝ))) * ENNReal.ofReal (1 - (p : ℝ)) +
      ENNReal.ofReal ((p : ℝ) / (1 + H * (p : ℝ))) =
      ENNReal.ofReal (1 / (1 + H * (p : ℝ))) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  ext s hs
  rw [stationaryMeasure_comp_apply H p hs, stationaryMeasure_apply H p hs]
  have hb : bernoulliMeasure (H : ℝ) 0 p s =
      ENNReal.ofReal (p : ℝ) * Measure.dirac (H : ℝ) s +
      ENNReal.ofReal (1 - (p : ℝ)) * Measure.dirac (0 : ℝ) s := by
    simp only [bernoulliMeasure_def, Measure.add_apply, Measure.smul_apply]
    change (unitInterval.toNNReal p : ENNReal) * Measure.dirac (H : ℝ) s +
      (unitInterval.toNNReal (unitInterval.symm p) : ENNReal) * Measure.dirac (0 : ℝ) s = _
    simp only [← ENNReal.ofReal_coe_nnreal]
    rfl
  rw [hb]
  have hh := stationary_weight_identity H _ _ _ _ hab har
    (fun i => Measure.dirac (i : ℝ) s)
  simpa only [← Fin.sum_univ_eq_sum_range, Nat.cast_zero, Nat.cast_add, Nat.cast_one] using hh

lemma integrable_stationary {E : Type*} [NormedAddCommGroup E]
    (H : ℕ) (p : unitInterval) (f : ℝ → E) :
    Integrable f (stationaryMeasure H p) := by
  apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
  exact (hasSum_fintype _).summable

lemma integral_stationary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (H : ℕ) (p : unitInterval) (f : ℝ → E) :
    (∫ x, f x ∂stationaryMeasure H p) =
      ∑ i : Fin (H + 1), weight H p i • f (i.val : ℝ) := by
  rw [stationaryMeasure, integral_sum_dirac_eq_tsum (fun _ => ENNReal.ofReal_ne_top)
    ((hasSum_fintype _).summable), tsum_fintype]
  simp only [ENNReal.toReal_ofReal (weight_nonneg H p _)]

lemma integral_stationary_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (H : ℕ) (p : unitInterval) (f : ℝ → E) :
    (∫ x, f x ∂stationaryMeasure H p) =
      (1 / (1 + H * (p : ℝ))) • f 0 +
        ((p : ℝ) / (1 + H * (p : ℝ))) • ∑ i : Fin H, f ((i.val : ℝ) + 1) := by
  rw [integral_stationary, Fin.sum_univ_succ]
  simp only [weight, ↓reduceIte, Fin.succ_ne_zero, Fin.val_zero, Nat.cast_zero,
    Fin.val_succ, Nat.cast_add, Nat.cast_one, Finset.smul_sum]

lemma stationaryMeasure_zero (H : ℕ) (p : unitInterval) :
    stationaryMeasure H p {0} = ENNReal.ofReal (1 / (1 + H * (p : ℝ))) := by
  rw [stationaryMeasure_apply H p (measurableSet_singleton 0)]
  have hz (i : Fin H) : (i.val : ℝ) + 1 ≠ 0 := by positivity
  simp [hz]

lemma stationaryMeasure_nonzero (H : ℕ) (p : unitInterval) :
    stationaryMeasure H p {x | x ≠ 0} =
      ENNReal.ofReal (H * (p : ℝ) / (1 + H * (p : ℝ))) := by
  have hp : 0 ≤ (p : ℝ) := p.property.1
  rw [stationaryMeasure_apply H p (by measurability)]
  have hz (i : Fin H) : (i.val : ℝ) + 1 ≠ 0 := by positivity
  have hs : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton 0).compl
  simp only [Measure.dirac_apply' _ hs]
  simp [hz]
  rw [← ENNReal.ofReal_natCast H, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end OracleTemplate.CountdownMarkov
