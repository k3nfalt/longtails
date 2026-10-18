import LongTails.Proofs.CharacteristicLogMoments
import LongTails.Proofs.ZerothOrderSmoothing
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.CharacteristicGradientBounds

open LongTails.Setups.QuantileSymmetricRemainderConvex
open LongTails.Algorithms.CharacteristicGradient
open CharacteristicLogMoments

lemma integrable_euclidean_of_coordinates {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → Space d} (hi : ∀ i, Integrable (fun ω => X ω i) P) :
    Integrable X P := by
  have hp : Integrable (fun ω i => X ω i) P := integrable_pi_iff.mpr hi
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.toContinuousLinearMap.integrable_comp hp

lemma vector_bias_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → Space d} {g : Space d} {b : ℝ} (hb : 0 ≤ b)
    (hi : Integrable X P) (hcoord : ∀ i, |(∫ ω, X ω i ∂P) - g i| ≤ b) :
    ‖(∫ ω, X ω ∂P) - g‖ ≤ Real.sqrt d * b := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hb)).mp
  calc
    _ = ∑ i, ((∫ ω, X ω i ∂P) - g i) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs,
        OracleTemplate.ZerothOrder.integral_euclidean_apply hi]
    _ ≤ ∑ _i : Fin d, b ^ 2 := Finset.sum_le_sum fun i _ => by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2
    _ = (Real.sqrt d * b) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]

lemma vector_error_second_bound {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → Space d} {g : Space d} {v : ℝ}
    (hi : ∀ i, Integrable (fun ω => (X ω i - g i) ^ 2) P)
    (hv : ∀ i, (∫ ω, (X ω i - g i) ^ 2 ∂P) ≤ v) :
    Integrable (fun ω => ‖X ω - g‖ ^ 2) P ∧
    (∫ ω, ‖X ω - g‖ ^ 2 ∂P) ≤ d * v := by
  have he (ω : Ω) : ‖X ω - g‖ ^ 2 = ∑ i, (X ω i - g i) ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  simp_rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  calc
    _ ≤ ∑ _i : Fin d, v := Finset.sum_le_sum fun i _ => hv i
    _ = _ := by simp

lemma batch_bounds {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {g : Ω → Space d} {v : Space d}
    (hg : Measurable g) {t G r M : ℝ} (ht : 0 < t) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hG : ∀ i, |v i| ≤ G) (htr : t * (G + r) ≤ 1 / 4)
    (hnoise : ∀ i, NoiseCondition (p.map (fun ω => (g ω - v) i)) r M) :
    let P := Measure.pi (fun _ : Fin K => p)
    let X := fun ξ : Fin K → Ω => batchEstimate t (fun j => g (ξ j))
    Integrable X P ∧
    ‖(∫ ξ, X ξ ∂P) - v‖ ≤ Real.sqrt d * (M * t + (1 / 2 : ℝ) ^ K / t) ∧
    Integrable (fun ξ => ‖X ξ - v‖ ^ 2) P ∧
    (∫ ξ, ‖X ξ - v‖ ^ 2 ∂P) ≤ 4 * d / t ^ 2 := by
  intro P X
  have hcoord (i : Fin d) :
      Integrable (fun ξ => X ξ i) P ∧
      |(∫ ξ, X ξ i ∂P) - v i| ≤ M * t + (1 / 2 : ℝ) ^ K / t ∧
      Integrable (fun ξ => (X ξ i) ^ 2) P ∧
      (∫ ξ, (X ξ i) ^ 2 ∂P) ≤ 1 / t ^ 2 := by
    let z := fun ω => (g ω - v) i
    have hz : Measurable z := by
      exact ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin d → ℝ))).comp (hg.sub_const v)
    let μ := p.map z
    let : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hz.aemeasurable).mpr inferInstance
    have hm (j : Fin K) : P.map (fun ξ => z (ξ j)) = μ := by
      rw [show (fun ξ : Fin K → Ω => z (ξ j)) = z ∘ (fun ξ => ξ j) from rfl,
        ← Measure.map_map hz (measurable_pi_apply j), (measurePreserving_eval (fun _ : Fin K => p) j).map_eq]
    have hs := coordinate_estimator_bounds (iIndepFun_pi (fun _ : Fin K => hz.aemeasurable))
      (fun j => hz.comp (measurable_pi_apply j)) hm (hnoise i) ht hr
      (show t * (|v i| + r) ≤ 1 / 4 by nlinarith [mul_le_mul_of_nonneg_left (hG i) ht.le])
    have he (ξ : Fin K → Ω) : (fun j => v i + z (ξ j)) = (fun j => g (ξ j) i) := by
      funext j
      dsimp [z]
      ring
    simp_rw [he] at hs
    exact hs
  have hi : Integrable X P := integrable_euclidean_of_coordinates fun i => (hcoord i).1
  have herr (i : Fin d) := scalar_error_second_bound (hcoord i).1 (hcoord i).2.2.1
    (hcoord i).2.2.2 ht (show |t * v i| ≤ 1 by
      rw [abs_mul, abs_of_pos ht]
      nlinarith [mul_le_mul_of_nonneg_left (hG i) ht.le, mul_nonneg ht.le hr])
  have hv := vector_error_second_bound (fun i => (herr i).1) (fun i => (herr i).2)
  refine ⟨hi, vector_bias_bound (by positivity) hi (fun i => (hcoord i).2.1), hv.1, ?_⟩
  convert hv.2 using 1
  ring

lemma measurable_batchEstimate {d K : ℕ} (t : ℝ) :
    Measurable (batchEstimate (d := d) (K := K) t) := by
  unfold batchEstimate
  apply (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hU (j : Fin K) : Measurable (fun replies : Fin K → Space d => phaseIncrement t (replies j i)) := by
    have hy : Measurable (fun replies : Fin K → Space d => replies j i) :=
      ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin d → ℝ))).comp (measurable_pi_apply j)
    unfold phaseIncrement
    fun_prop
  exact ((Complex.measurable_im.comp (measurable_logPolynomial hU)).neg).div_const t

lemma measurable_batch_oracle {d K : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {g : Space d → Ω → Space d} (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    Measurable (fun z : Space d × (Fin K → Ω) => batchEstimate t (fun j => g z.1 (z.2 j))) := by
  apply (measurable_batchEstimate t).comp
  apply Measurable.of_eval
  intro j
  exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

end LongTails.Proofs.CharacteristicGradientBounds
