import LongTails.Proofs.RelativeCurvatureInitialization
import LongTails.Proofs.RelativeCurvatureExecution

namespace LongTails.Proofs.RelativeCurvatureDetection

open MeasureTheory OracleTemplate LongTails.Algorithms.QuarticMetricStage
open LongTails.Algorithms.RelativeCurvatureSearch
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma detection_probability {ι : Type*} [Fintype ι]
    (D C : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (eig : ι → ℝ)
    (hc : ∀ i v, ⟪b i, C v⟫ = eig i * ⟪b i, v⟫)
    (he : ∀ i, eig i ≤ 1) (hC : ‖C‖ ≤ 2)
    (hd : 0 < Module.finrank ℝ E) (x : Point E) (H : ℝ) {a : ℝ}
    (ha : 0 < a) (ha₁ : a ≤ 1) (O : Fin 2 × E → Reply E) (n : ℕ)
    (hn : 2 * Real.log (16 * (Module.finrank ℝ E : ℝ) / a) / Real.sqrt a ≤ n)
    (hp : ∀ v, ‖(product D x H (a / (128 * (12 : ℝ) ^ n)) v).eval O - C v‖ ≤
      (a / (128 * (12 : ℝ) ^ n)) / 4)
    (hv : ∀ v, ‖(product D x H (a / 4) v).eval O - C v‖ ≤ a / 16)
    (i : ι) (hi : eig i ≤ -2 * a) :
    ((PMF.uniformOfFintype (Fin (Module.finrank ℝ E) → Bool)).toMeasure).real
      {s | ∃ out, (search D x H a (seed s) n).eval O = some out} ≥ 1 / 16 := by
  have hb := RelativeCurvatureInitialization.seed_overlap hd (b i) (b.norm_eq_one i)
  apply hb.trans (measureReal_mono ?_)
  intro s hs
  have hunit := RelativeCurvatureInitialization.seed_norm hd s
  have hnorm : ‖seed s‖⁻¹ • (seed s : E) = seed s := by rw [hunit, inv_one, one_smul]
  apply RelativeCurvatureExecution.search_complete D C x H ha ha₁ hC (seed s) O n
    (RelativeCurvatureSpectrum.transformed_norm C ha.le ha₁ hC) hp hv
  · rw [hnorm]
    exact RelativeCurvatureSpectrum.amplified_filter C b eig hc ha ha₁
      (by exact_mod_cast hd) (seed s) n i hi hs hn
  · dsimp only
    rw [hnorm]
    exact RelativeCurvatureSpectrum.filter_shifted_quadratic C b eig hc ha.le ha₁ he
      (seed s) hunit.le n

end LongTails.Proofs.RelativeCurvatureDetection
