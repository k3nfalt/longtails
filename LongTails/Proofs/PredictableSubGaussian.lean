import LongTails.Proofs.AdaptiveOracleConcentration
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.PredictableSubGaussian

lemma predictable_direction_mgf {Ω Z E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : Measure Ω} [IsProbabilityMeasure P] {p : Measure Z} [IsProbabilityMeasure p]
    {ξ : ℕ → Ω → Z} (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = p)
    (X : (n : ℕ) → (Fin n → Z) × Z → E) (hX : ∀ n, Measurable (X n))
    (direction : (n : ℕ) → (Fin n → Z) → E) (hdir : ∀ n, Measurable (direction n))
    (a : ℕ → ℝ) (variance R A : ℝ) (hv : 0 ≤ variance) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hdirnorm : ∀ n h, ‖direction n h‖ ≤ R)
    (hmgf : ∀ n h u t, Integrable (fun z => Real.exp (t * ⟪X n (h, z), u⟫)) p ∧
      (∫ z, Real.exp (t * ⟪X n (h, z), u⟫) ∂p) ≤
        Real.exp (variance * ‖u‖ ^ 2 * t ^ 2 / 2))
    (N : ℕ) (hcoeff : ∑ i ∈ Finset.range N, a i ^ 2 ≤ A) :
    HasSubgaussianMGF (fun ω => ∑ i ∈ Finset.range N,
      a i * ⟪X i ((fun j => ξ j ω), ξ i ω), direction i (fun j => ξ j ω)⟫)
      ⟨variance * R ^ 2 * A, by positivity⟩ P := by
  let increment := fun (n : ℕ) (hz : (Fin n → Z) × Z) =>
    a n * ⟪X n hz, direction n hz.1⟫
  have hinc (n : ℕ) : Measurable (increment n) :=
    ((hX n).inner ((hdir n).comp measurable_fst)).const_mul _
  have hcombined (t : ℝ) :
      Integrable (fun ω => Real.exp (t * ∑ i ∈ Finset.range N,
        increment i ((fun j => ξ j ω), ξ i ω))) P ∧
      (∫ ω, Real.exp (t * ∑ i ∈ Finset.range N,
        increment i ((fun j => ξ j ω), ξ i ω)) ∂P) ≤
        Real.exp (variance * R ^ 2 * A * t ^ 2 / 2) := by
    let cost := fun n => variance * R ^ 2 * (t * a n) ^ 2 / 2
    have hpoint (n : ℕ) (h : Fin n → Z) :
        Integrable (fun z => Real.exp (t * increment n (h, z))) p ∧
        (∫ z, Real.exp (t * increment n (h, z)) ∂p) ≤ Real.exp (cost n) := by
      have hh := hmgf n h (direction n h) (t * a n)
      have heq (z : Z) : t * increment n (h, z) =
          (t * a n) * ⟪X n (h, z), direction n h⟫ := by dsimp [increment]; ring
      simp_rw [heq]
      refine ⟨hh.1, hh.2.trans (Real.exp_le_exp.mpr ?_)⟩
      have hnorm : ‖direction n h‖ ^ 2 ≤ R ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hR).2 (hdirnorm n h)
      have hm := mul_le_mul_of_nonneg_left hnorm
        (show 0 ≤ variance * (t * a n) ^ 2 / 2 by positivity)
      dsimp [cost]
      nlinarith
    have hh := AdaptiveOracleConcentration.iid_predictable_sum_exponential_bound hξ hind hlaw
      cost t hinc (fun n h => (hpoint n h).1) (fun n h => (hpoint n h).2) N
    refine ⟨hh.1, hh.2.trans (Real.exp_le_exp.mpr ?_)⟩
    calc
      ∑ i ∈ Finset.range N, cost i =
          (variance * R ^ 2 * t ^ 2 / 2) * ∑ i ∈ Finset.range N, a i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [cost]
        ring
      _ ≤ (variance * R ^ 2 * t ^ 2 / 2) * A :=
        mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = variance * R ^ 2 * A * t ^ 2 / 2 := by ring
  refine ⟨fun t => (hcombined t).1, ?_⟩
  intro t
  exact (hcombined t).2

end LongTails.Proofs.PredictableSubGaussian
