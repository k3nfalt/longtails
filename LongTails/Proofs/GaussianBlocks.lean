import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.MuonProcess
import Mathlib.Probability.Distributions.Gaussian.Real

namespace LongTails.Proofs.GaussianBlocks

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable abbrev stdStream : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

noncomputable def blockMean (B t : ℕ) (ξ : ℕ → ℝ) : ℝ :=
  (1 / (B : ℝ)) * ∑ j ∈ Finset.range B, ξ (B * t + j)

lemma measurable_blockMean (B t : ℕ) : Measurable (blockMean B t) := by
  unfold blockMean
  fun_prop

lemma sum_law (k : ℕ) :
    stdStream.map (fun τ : ℕ → ℝ => ∑ j ∈ Finset.range k, τ j) = gaussianReal 0 (k : ℝ≥0) := by
  induction k with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, gaussianReal_zero_var]
      rw [Measure.map_const]
      simp
  | succ k ih =>
      have hind : IndepFun (∑ j ∈ Finset.range k, fun τ : ℕ → ℝ => τ j) (fun τ => τ k) stdStream :=
        (iIndepFun_infinitePi (X := fun _ (ω : ℝ) => ω) (fun _ => measurable_id)).indepFun_finsetSum_of_notMem
          (fun i => measurable_pi_apply i) (by simp)
      have hX : HasLaw (∑ j ∈ Finset.range k, fun τ : ℕ → ℝ => τ j) (gaussianReal 0 (k : ℝ≥0))
          stdStream := by
        refine ⟨by fun_prop, ?_⟩
        rw [← ih]
        congr 1
        funext τ
        simp
      have hY : HasLaw (fun τ : ℕ → ℝ => τ k) (gaussianReal 0 1) stdStream :=
        ⟨(measurable_pi_apply k).aemeasurable, Measure.infinitePi_map_eval _ _⟩
      have hsum := gaussianReal_add_gaussianReal_of_indepFun hind hX hY
      have he : (∑ j ∈ Finset.range k, fun τ : ℕ → ℝ => τ j) + (fun τ => τ k) =
          fun τ : ℕ → ℝ => ∑ j ∈ Finset.range (k + 1), τ j := by
        funext τ
        simp [Finset.sum_range_succ]
      rw [he] at hsum
      rw [hsum]
      congr 1
      · simp
      · push_cast
        rfl

lemma mean_law {B : ℕ} (hB : 0 < B) :
    stdStream.map (fun τ : ℕ → ℝ => (1 / (B : ℝ)) * ∑ j ∈ Finset.range B, τ j) =
      gaussianReal 0 (1 / (B : ℝ≥0)) := by
  have hcomp : (fun τ : ℕ → ℝ => (1 / (B : ℝ)) * ∑ j ∈ Finset.range B, τ j) =
      (fun x => (1 / (B : ℝ)) * x) ∘ (fun τ : ℕ → ℝ => ∑ j ∈ Finset.range B, τ j) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), sum_law, gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_natCast, one_div, NNReal.coe_inv]
    field_simp

lemma block_law {B : ℕ} (hB : 0 < B) (t : ℕ) :
    MeasurePreserving (fun ξ : ℕ → ℝ => ((fun i : Fin (B * t) => ξ i), blockMean B t ξ)) stdStream
      ((Measure.pi fun _ : Fin (B * t) => gaussianReal 0 1).prod
        (gaussianReal 0 (1 / (B : ℝ≥0)))) := by
  have hsplit := OracleTemplate.StochasticGeneralized.splitStream_preserving
    (gaussianReal 0 1) (B * t)
  have hmean : MeasurePreserving (fun τ : ℕ → ℝ => (1 / (B : ℝ)) * ∑ j ∈ Finset.range B, τ j)
      stdStream (gaussianReal 0 (1 / (B : ℝ≥0))) :=
    ⟨by fun_prop, mean_law hB⟩
  have hp := ((MeasurePreserving.id (Measure.pi fun _ : Fin (B * t) => gaussianReal 0 1)).prod
    hmean).comp hsplit
  convert hp using 1
  funext ξ
  rfl

lemma freeze {B : ℕ} (hB : 0 < B) (t : ℕ) {F : (Fin (B * t) → ℝ) × ℝ → ℝ}
    (hF : Integrable F ((Measure.pi fun _ : Fin (B * t) => gaussianReal 0 1).prod
      (gaussianReal 0 (1 / (B : ℝ≥0))))) :
    (∫ ξ, F ((fun i : Fin (B * t) => ξ i), blockMean B t ξ) ∂stdStream) =
      ∫ p, ∫ z, F (p, z) ∂gaussianReal 0 (1 / (B : ℝ≥0))
        ∂(Measure.pi fun _ : Fin (B * t) => gaussianReal 0 1) := by
  have h := MuonProcess.pair_local_integral (block_law hB t) hF MeasurableSet.univ
  simpa using h

end LongTails.Proofs.GaussianBlocks
