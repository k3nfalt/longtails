import LongTails.Proofs.MintyCutMoments
import LongTails.Algorithms.DimensionAdaptiveMinty

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.MintyCutPotential

open LongTails.Setups.FiniteDimensionalWeakMinty LongTails.Algorithms.DimensionAdaptiveMinty
open LongTails.Algorithms.CovarianceSoftCut CovarianceSoftCutLocalization CovarianceSoftCutDensity

def potential (p : Params) (z : E p) (cuts : List (E p × E p)) : ℝ :=
  let q := geometry p
  let α := margin p
  Real.log (mass q α (2/α) cuts) + (2/α) * ∫ y, lossSum q α cuts y ∂targetMeasure q α z

lemma geometry_pos (p : Params) (hd : 0 < p.d) : 0 < (geometry p).L := by
  change 0 < 4 / Real.sqrt (p.d : ℝ)
  positivity

lemma potential_empty (p : Params) (z : E p) : potential p z [] =
    Real.log (mass (geometry p) (margin p) (2/margin p) []) := by
  simp [potential, lossSum, List.length_nil]

lemma decrease (p : Params) (hd : 0 < p.d) (hR : 0 < p.R) (hα : 0 < margin p)
    (z u : E p) (hu : ‖u‖ = 1) (cuts : List (E p × E p))
    (hcut : margin p ≤ ⟪u,center p cuts-z⟫) :
    potential p z (cuts ++ [(u,center p cuts)]) + 1/8 ≤ potential p z cuts := by
  let q := geometry p
  let α := margin p
  let x := center p cuts
  let μ := targetMeasure q α z
  have hL := geometry_pos p hd
  have hs := MintyCutMoments.directional_square q hL hα z u hu
  have he : (α / (4*q.L))^2 = α^2 * p.d / 256 := by
    change (α / (4*(4/Real.sqrt p.d)))^2 = _
    have hsqrt : 0 < Real.sqrt (p.d : ℝ) := by positivity
    field_simp [hsqrt.ne']
    nlinarith [Real.sq_sqrt (show 0 ≤ (p.d : ℝ) by positivity)]
  have hd' : (0:ℝ) < p.d := by exact_mod_cast hd
  have hv : (∫ y, ⟪u,y-z⟫^2 ∂μ) ≤ α^2/256 := by
    rw [he] at hs
    change (p.d : ℝ) * _ ≤ _ at hs
    exact (le_of_mul_le_mul_left (by linarith only [hs] :
      (p.d:ℝ) * (∫ y, ⟪u,y-z⟫^2 ∂μ) ≤ p.d * (α^2/256)) hd')
  have hint := integrable_targetMeasure_of_continuous q hL α hα z
    (fun y => ⟪u,y-z⟫^2) (by fun_prop)
  have hh : (∫ y, hinge q α (u,x) y ∂μ) ≤ α / 256 := by
    calc
      _ ≤ ∫ y, ⟪u,y-z⟫^2 / α ∂μ := by
        apply integral_mono (integrable_targetMeasure_of_continuous q hL α hα z _
          (continuous_hinge q α _)) (hint.div_const α)
        intro y
        change max 0 (⟪u,y-x⟫ + α/2) ≤ _
        rw [show y-x = (y-z) - (x-z) by abel, inner_sub_right]
        calc
          _ ≤ max 0 (-⟪u,x-z⟫ + ⟪u,y-z⟫ + α/2) := by apply max_le_max_left; linarith
          _ ≤ _ := CovarianceSoftCutPotential.shiftedHinge_le_noise_square _ _ α hα (by
            change α ≤ ⟪u,x-z⟫ at hcut
            linarith)
      _ = (∫ y, ⟪u,y-z⟫^2 ∂μ) / α := integral_div α _
      _ ≤ α / 256 := (div_le_iff₀ hα).mpr (by linarith)
  have hm := mass_append_centroid_contracts q hd hR α hα cuts u
  have hpos := mass_pos q hR α (2/α) (cuts ++ [(u,x)])
  have hpos' := mass_pos q hR α (2/α) cuts
  have hl := Real.log_le_log hpos hm
  rw [Real.log_mul (by norm_num) hpos'.ne'] at hl
  have h56 := Real.log_le_sub_one_of_pos (by norm_num : 0 < (5/6:ℝ))
  change Real.log (mass q α (2/α) (cuts ++ [(u,x)])) + _ + 1/8 ≤ _
  unfold potential
  change _ + 2/α * (∫ y, lossSum q α (cuts ++ [(u,x)]) y ∂μ) + 1/8 ≤
    _ + 2/α * (∫ y, lossSum q α cuts y ∂μ)
  rw [targetMeasure_lossSum_append q hL α hα z cuts (u,x), mul_add]
  have hpen := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2/α)
  have heq : (2/α)*(α/256) = 1/128 := by field_simp [show α ≠ 0 from hα.ne']; ring
  rw [heq] at hpen
  linarith only [hl, h56, hpen]

lemma cumulative_bound (p : Params) (hd : 0 < p.d) (hR : 0 < p.R) (hα : 0 < margin p)
    (hsmall : margin p ≤ (geometry p).L * p.R) (z : E p) (hz : ‖z‖ ≤ p.R)
    (cuts : List (E p × E p)) :
    potential p z [] - potential p z cuts ≤
      p.d * Real.log (8 * (geometry p).L * p.R / margin p) := by
  let q := geometry p
  let α := margin p
  let A := Metric.closedBall z (α / (4*q.L))
  have hL := geometry_pos p hd
  have hr : 0 < α / (4*q.L) := by positivity
  have hpos : 0 < volume A := (Metric.measure_ball_pos volume z hr).trans_le
    (measure_mono Metric.ball_subset_closedBall)
  have hfin : volume A ≠ ⊤ := (isCompact_closedBall z (α/(4*q.L))).measure_lt_top.ne
  have ha := mass_lower_target q α (2/α) cuts A Metric.isClosed_closedBall.measurableSet
    (target_ball_subset q hL hR α hsmall z hz) hpos.ne' hfin
  have hreal := ENNReal.toReal_pos hpos.ne' hfin
  have hl := Real.log_le_log (mul_pos hreal (Real.exp_pos _)) ha
  rw [Real.log_mul hreal.ne' (Real.exp_ne_zero _), Real.log_exp] at hl
  rw [potential_empty, mass_empty, potential]
  change Real.log (volume.real (Metric.closedBall (0 : E p) (2*p.R))) -
    (Real.log (mass q α (2/α) cuts) + (2/α) * ∫ y, lossSum q α cuts y ∂targetMeasure q α z) ≤ _
  rw [integral_targetMeasure]
  have hvol := target_log_volume_ratio q hL hR α hα z
  change Real.log _ - Real.log (volume A).toReal = (p.d:ℝ) * _ at hvol
  change Real.log (volume A).toReal + _ ≤ _ at hl
  change _ - (_ + (2/α) * ((volume A).toReal⁻¹ * ∫ y in A, lossSum q α cuts y)) ≤ _
  linarith only [hl, hvol]

end LongTails.Proofs.MintyCutPotential
