import LongTails.Proofs.CohypoRegularizedOperator
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.FullRangeResolvent

open OracleTemplate.StochasticCohypomonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {F : E → E} {G : E → Set E} {J : ℝ → E → E} {L ρ η : ℝ}

noncomputable def fixedMap (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) (a : ℝ)
    (x : E) : E :=
  (1 - a) • x + a • resH H hη hηL x

lemma fixedMap_nonexpansive (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1)
    {a : ℝ} (ha : 0 ≤ a) (haη : a * η ≤ 2 * (η - ρ)) (x y : E) :
    ‖fixedMap H hη hηL a x - fixedMap H hη hηL a y‖ ≤ ‖x - y‖ := by
  set z := resH H hη hηL x
  set w := resH H hη hηL y
  have hz := H.resH_mem hη hηL x
  have hw := H.resH_mem hη hηL y
  set dx := x - y
  set dz := z - w
  set du := η⁻¹ • (dx - dz)
  have hsum : (F z + (η⁻¹ • (x - z) - F z)) - (F w + (η⁻¹ • (y - w) - F w)) = du := by
    simp only [du, dx, dz, smul_sub]
    abel
  have hc := H.cohypo z w _ hz _ hw
  rw [hsum] at hc
  have hdz : dz = dx - η • du := by
    simp only [du, smul_smul, mul_inv_cancel₀ hη.ne', one_smul]
    abel
  have hc2 : (η - ρ) * ‖du‖ ^ 2 ≤ ⟪du, dx⟫ := by
    have e : ⟪du, dz⟫ = ⟪du, dx⟫ - η * ‖du‖ ^ 2 := by
      rw [hdz, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
    rw [show ⟪du, z - w⟫ = ⟪du, dz⟫ from rfl, e] at hc
    nlinarith
  have hd : fixedMap H hη hηL a x - fixedMap H hη hηL a y = dx - (a * η) • du := by
    simp only [fixedMap]
    have : (1 - a) • x + a • z - ((1 - a) • y + a • w) = dx - a • (dx - dz) := by
      simp only [dx, dz, smul_sub, sub_smul, one_smul]
      abel
    rw [show resH H hη hηL x = z from rfl, show resH H hη hηL y = w from rfl, this, hdz]
    simp only [mul_smul]
    congr 1
    congr 1
    abel
  have hsq : ‖dx - (a * η) • du‖ ^ 2 ≤ ‖dx‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_comm]
    have hn := sq_nonneg ‖du‖
    have h1 : 0 ≤ a * η := by positivity
    nlinarith [mul_nonneg h1 hn, mul_le_mul_of_nonneg_left hc2 h1,
      mul_le_mul_of_nonneg_right haη (mul_nonneg h1 hn)]
  rw [hd]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

lemma resH_of_zero (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) {u : E}
    (hu : -F u ∈ G u) : resH H hη hηL u = u := by
  have hfix : Function.IsFixedPt (fun y => J η (u - η • F y)) u := by
    refine H.res_unique hη ?_
    have : η⁻¹ • (u - η • F u - u) = -F u := by
      rw [show u - η • F u - u = -(η • F u) by abel, smul_neg, smul_smul,
        inv_mul_cancel₀ hη.ne', one_smul]
    rwa [this]
  exact ((H.inner_lip hη hηL u).fixedPoint_unique hfix).symm

lemma fixedMap_of_zero (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) (a : ℝ) {u : E}
    (hu : -F u ∈ G u) : fixedMap H hη hηL a u = u := by
  simp only [fixedMap, resH_of_zero H hη hηL hu, sub_smul, one_smul]
  abel

lemma sub_fixedMap (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) (a : ℝ) (x : E) :
    x - fixedMap H hη hηL a x = a • (x - resH H hη hηL x) := by
  simp only [fixedMap, smul_sub, sub_smul, one_smul]
  abel

end LongTails.Proofs.FullRangeResolvent
