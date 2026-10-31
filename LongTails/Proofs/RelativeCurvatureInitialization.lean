import LongTails.Algorithms.RelativeCurvatureSearch
import LongTails.Proofs.HeavyTailedRademacherInitialization
import LongTails.Proofs.HeavyTailedSospDetection

namespace LongTails.Proofs.RelativeCurvatureInitialization

open MeasureTheory OracleTemplate.MatrixGeneralizedZO
open LongTails.Algorithms.RelativeCurvatureSearch
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma seed_norm (hd : 0 < Module.finrank ℝ E) (s : Fin (Module.finrank ℝ E) → Bool) :
    ‖(seed s : E)‖ = 1 := by
  simpa only [seed, LinearIsometryEquiv.norm_map] using HeavyTailedProbeGeometry.initialVector_norm hd s

lemma seed_overlap (hd : 0 < Module.finrank ℝ E) (e : E) (he : ‖e‖ = 1) :
    ((PMF.uniformOfFintype (Fin (Module.finrank ℝ E) → Bool)).toMeasure).real
      {s | 1 / (2 * (Module.finrank ℝ E : ℝ)) ≤ ⟪e, seed s⟫ ^ 2} ≥ 1 / 16 := by
  let d := Module.finrank ℝ E
  let b := stdOrthonormalBasis ℝ E
  have hg : b.repr e ≠ 0 := by
    intro h
    have hh := congrArg norm h
    simp [he] at hh
  have hb := HeavyTailedRademacherInitialization.scalar_sign_amplification (b.repr e) hg
  apply hb.trans (measureReal_mono ?_)
  intro s hs
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hi : ⟪e, seed s⟫ = (Real.sqrt (d : ℝ))⁻¹ * ⟪b.repr e, signVec s⟫ := by
    rw [← b.repr.inner_map_map]
    simp [seed, b, LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector, d, inner_smul_right]
  have hh : (1 : ℝ) / 2 ≤ ⟪b.repr e, signVec s⟫ ^ 2 := by simpa [he] using hs
  change 1 / (2 * (d : ℝ)) ≤ ⟪e, seed s⟫ ^ 2
  rw [hi, mul_pow, inv_pow, Real.sq_sqrt hd0.le]
  change 1 / (2 * (d : ℝ)) ≤ (d : ℝ)⁻¹ * ⟪b.repr e, signVec s⟫ ^ 2
  have hm := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hd0.le)
  convert hm using 1
  ring

lemma repeated_seed_failure (hd : 0 < Module.finrank ℝ E) (e : E) (he : ‖e‖ = 1) (R : ℕ) :
    (Measure.pi fun _ : Fin R =>
      (PMF.uniformOfFintype (Fin (Module.finrank ℝ E) → Bool)).toMeasure).real
      {s | ∀ j, ⟪e, seed (s j)⟫ ^ 2 < 1 / (2 * (Module.finrank ℝ E : ℝ))} ≤
        Real.exp (-(R : ℝ) / 16) := by
  let Q := (PMF.uniformOfFintype (Fin (Module.finrank ℝ E) → Bool)).toMeasure
  let S := {s : Fin (Module.finrank ℝ E) → Bool |
    1 / (2 * (Module.finrank ℝ E : ℝ)) ≤ ⟪e, seed s⟫ ^ 2}
  have hb := HeavyTailedSospDetection.independent_block_failure Q S
    (Set.toFinite S).measurableSet R (1 / 16) (seed_overlap hd e he)
  have he : -(1 / 16 : ℝ) * R = -(R : ℝ) / 16 := by ring
  rw [he] at hb
  simpa only [S, Set.mem_ofPred_eq, not_le] using hb

lemma repeated_failure_tuning {ρ K : ℝ} (hρ : 0 < ρ) (hK : 0 < K) (R : ℕ)
    (hR : 16 * Real.log (K / ρ) ≤ R) : Real.exp (-(R : ℝ) / 16) ≤ ρ / K := by
  have he := Real.exp_le_exp.mpr (show -(R : ℝ) / 16 ≤ -Real.log (K / ρ) by linarith)
  rw [Real.exp_neg, Real.exp_log (div_pos hK hρ), inv_div] at he
  exact he

end LongTails.Proofs.RelativeCurvatureInitialization
