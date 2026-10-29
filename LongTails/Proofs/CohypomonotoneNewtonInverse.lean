import LongTails.Algorithms.CohypomonotoneNewton
import LongTails.Proofs.CohypomonotoneNewtonGeometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CohypomonotoneNewtonInverse

open LongTails.Algorithms.CohypomonotoneNewton
open LongTails.Proofs.CohypomonotoneNewtonGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma linear_bijective (D : E →L[ℝ] E) (hlow : ∀ v, ‖v‖ ≤ ‖D v‖) :
    Function.Bijective D := by
  have hinj : Function.Injective D.toLinearMap := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hh := hlow v
    rw [show D v = 0 from hv, norm_zero] at hh
    exact norm_le_zero_iff.mp hh
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

lemma linearSolve_eq (D : E →L[ℝ] E) (b : E) (hlow : ∀ v, ‖v‖ ≤ ‖D v‖) :
    D (linearSolve D b) = b := by
  have hex : ∃ v, D v = b := (linear_bijective D hlow).2 b
  simpa only [linearSolve, dite_eq_left hex] using hex.choose_spec

lemma linearInverse_right (D : E →L[ℝ] E) (hlow : ∀ v, ‖v‖ ≤ ‖D v‖) (v : E) :
    D (linearInverse D v) = v := by
  have hbi := linear_bijective D hlow
  simp only [linearInverse, dite_eq_left hbi]
  exact (LinearEquiv.ofBijective D.toLinearMap hbi).toContinuousLinearEquiv.apply_symm_apply v

lemma linearInverse_left (D : E →L[ℝ] E) (hlow : ∀ v, ‖v‖ ≤ ‖D v‖) (v : E) :
    linearInverse D (D v) = v := by
  have hbi := linear_bijective D hlow
  simp only [linearInverse, dite_eq_left hbi]
  exact (LinearEquiv.ofBijective D.toLinearMap hbi).toContinuousLinearEquiv.symm_apply_apply v

lemma linearInverse_norm (D : E →L[ℝ] E) (hlow : ∀ v, ‖v‖ ≤ ‖D v‖) :
    ‖linearInverse D‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  have hh := hlow (linearInverse D v)
  simpa only [linearInverse_right D hlow, one_mul] using hh

lemma expansive_surjective {T : E → E} {D : E → E →L[ℝ] E}
    (hT : ∀ x, HasFDerivAt T (D x) x)
    (hexp : ∀ x y, ‖x - y‖ ≤ ‖T x - T y‖) : Function.Surjective T := by
  intro w
  let r := ‖T 0 - w‖
  have hr : 0 ≤ r := norm_nonneg _
  have hc : Continuous (fun x => ‖T x - w‖) :=
    ((continuous_iff_continuousAt.mpr fun x => (hT x).continuousAt).sub continuous_const).norm
  have h0 : (0 : E) ∈ Metric.closedBall 0 (2 * r + 1) :=
    Metric.mem_closedBall_self (by positivity)
  obtain ⟨x, _, hmin⟩ := (isCompact_closedBall (0 : E) (2 * r + 1)).exists_isMinOn
    ⟨0, h0⟩ hc.continuousOn
  have hall : ∀ y, ‖T x - w‖ ≤ ‖T y - w‖ := by
    intro y
    by_cases hy : y ∈ Metric.closedBall 0 (2 * r + 1)
    · exact hmin hy
    · have hy' : 2 * r + 1 < ‖y‖ := by simpa using hy
      have he := hexp y 0
      rw [sub_zero] at he
      have ht : ‖T y - T 0‖ ≤ ‖T y - w‖ + r := by
        simpa [r, norm_sub_rev w (T 0)] using norm_sub_le (T y - w) (T 0 - w)
      have hx := hmin h0
      change ‖T x - w‖ ≤ r at hx
      linarith
  have hlocal : IsLocalMin (fun y => ‖T y - w‖ ^ 2) x :=
    Filter.Eventually.of_forall fun y => pow_le_pow_left₀ (norm_nonneg _) (hall y) 2
  have hd := ((hT x).sub_const w).norm_sq
  have hzero := hlocal.hasFDerivAt_eq_zero hd
  have hl : ∀ v, ‖v‖ ≤ ‖D x v‖ := expansive_derivative (hT x) (fun y => hexp y x)
  have hv := linearSolve_eq (D x) (T x - w) hl
  have hz := DFunLike.congr_fun hzero (linearSolve (D x) (T x - w))
  simp only [two_smul, add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    innerSL_apply_apply, hv, real_inner_self_eq_norm_sq] at hz
  refine ⟨x, sub_eq_zero.mp (norm_eq_zero.mp ?_)⟩
  nlinarith [sq_nonneg ‖T x - w‖]

lemma trustRegion_spec (D : E →L[ℝ] E) (r : E) {R : ℝ} (hR : 0 ≤ R) :
    ‖trustRegion D r R‖ ≤ R ∧
      ∀ d, ‖d‖ ≤ R → ‖r + D (trustRegion D r R)‖ ≤ ‖r + D d‖ := by
  have hc : Continuous (fun d => ‖r + D d‖) := (continuous_const.add D.continuous).norm
  obtain ⟨v, hv, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hR⟩ hc.continuousOn
  have hex : ∃ v, ‖v‖ ≤ R ∧ ∀ d, ‖d‖ ≤ R → ‖r + D v‖ ≤ ‖r + D d‖ := by
    refine ⟨v, ?_, ?_⟩
    · simpa using hv
    · intro d hd
      exact hmin (by simpa using hd)
  simpa only [trustRegion, dite_eq_left hex] using hex.choose_spec

lemma damping_bounds {M r : ℝ} :
    0 ≤ 1 / max 1 (2 * M * r) ∧ 1 / max 1 (2 * M * r) ≤ 1 ∧
      M * (1 / max 1 (2 * M * r)) * r ≤ 1 / 2 := by
  have hp : 0 < max 1 (2 * M * r) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨le_of_lt (one_div_pos.mpr hp), (div_le_one hp).mpr (le_max_left _ _), ?_⟩
  have hh := (div_le_one hp).mpr (le_max_right 1 (2 * M * r))
  have he : 2 * (M * (1 / max 1 (2 * M * r)) * r) =
      (2 * M * r) / max 1 (2 * M * r) := by ring
  linarith

lemma inverseUpdate_residual {F : E → E} {J : E → E →L[ℝ] E} {M γ B : ℝ}
    (hM : 0 ≤ M)
    (hT : ∀ x, HasFDerivAt (fun x => x + γ • F x)
      (ContinuousLinearMap.id ℝ E + γ • J x) x)
    (hD : ∀ x y, ‖(ContinuousLinearMap.id ℝ E + γ • J x) -
      (ContinuousLinearMap.id ℝ E + γ • J y)‖ ≤ M * ‖x - y‖)
    (hexp : ∀ x y, ‖x - y‖ ≤ ‖(x + γ • F x) - (y + γ • F y)‖)
    (x target : E) (hB : ‖x + γ • F x - target‖ ≤ B) :
    ‖inverseUpdate M γ target x (F x, J x) +
        γ • F (inverseUpdate M γ target x (F x, J x)) - target‖ ≤
      (1 - 1 / (2 * max 1 (2 * M * B))) * ‖x + γ • F x - target‖ := by
  let r := x + γ • F x - target
  let D := ContinuousLinearMap.id ℝ E + γ • J x
  let v := linearSolve D (-r)
  let t := 1 / max 1 (2 * M * ‖r‖)
  have hl : ∀ u, ‖u‖ ≤ ‖D u‖ := expansive_derivative (hT x) (fun y => hexp y x)
  have hv : D v = -r := linearSolve_eq D (-r) hl
  have hvn : ‖v‖ ≤ ‖r‖ := by simpa [hv] using hl v
  obtain ⟨ht, ht1, hsmall⟩ := damping_bounds (M := M) (r := ‖r‖)
  have hh := damped_newton_residual hT hM hD x target v hv hvn ht ht1 hsmall
  have hp : 0 < max 1 (2 * M * ‖r‖) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hm : max 1 (2 * M * ‖r‖) ≤ max 1 (2 * M * B) :=
    max_le_max_left 1 (mul_le_mul_of_nonneg_left hB (by positivity))
  have hinv := one_div_le_one_div_of_le hp hm
  have hcomp : 1 / (2 * max 1 (2 * M * B)) ≤ t / 2 := by
    dsimp [t]
    have he : 1 / (2 * max 1 (2 * M * B)) = (1 / max 1 (2 * M * B)) / 2 := by ring
    rw [he]
    linarith
  change ‖(x + t • v) + γ • F (x + t • v) - target‖ ≤ _
  have hb := mul_le_mul_of_nonneg_right hcomp (norm_nonneg r)
  change ‖(x + t • v) + γ • F (x + t • v) - target‖ ≤ (1 - t / 2) * ‖r‖ at hh
  nlinarith only [hh, hb]

lemma inverseLength_accuracy {M B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    (1 - 1 / (2 * max 1 (2 * M * B))) ^ inverseLength M B ε * B ≤ ε := by
  let C := 2 * max 1 (2 * M * B)
  have hC : 2 ≤ C := by dsimp [C]; linarith [le_max_left 1 (2 * M * B)]
  have hC0 : 0 < C := by linarith
  have hc : 0 < 1 / C := one_div_pos.mpr hC0
  have hc1 : 1 / C ≤ 1 := (div_le_one hC0).mpr (by linarith)
  have hpos : 0 < 1 + B / ε := by positivity
  have hN : Real.log (1 + B / ε) ≤ (1 / C) * inverseLength M B ε := by
    have hn := Nat.le_ceil (C * Real.log (1 + B / ε))
    have he : (1 / C) * (C * Real.log (1 + B / ε)) = Real.log (1 + B / ε) := by
      field_simp
    have hp := mul_le_mul_of_nonneg_left hn hc.le
    rw [he] at hp
    simpa only [inverseLength, C, Nat.cast_add, Nat.cast_one, mul_add, mul_one] using
      hp.trans (le_add_of_nonneg_right hc.le)
  have hpow : (1 - 1 / C) ^ inverseLength M B ε ≤ 1 / (1 + B / ε) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - 1 / C)
      (by linarith [Real.add_one_le_exp (-(1 / C))] : 1 - 1 / C ≤ Real.exp (-(1 / C)))
      (inverseLength M B ε)
    rw [← Real.exp_nat_mul] at h
    refine h.trans ?_
    have he : 1 / (1 + B / ε) = Real.exp (-Real.log (1 + B / ε)) := by
      rw [Real.exp_neg, Real.exp_log hpos, one_div]
    rw [he]
    apply Real.exp_le_exp.mpr
    nlinarith only [hN]
  have he : ε * (1 + B / ε) = ε + B := by field_simp
  calc
    (1 - 1 / C) ^ inverseLength M B ε * B ≤ 1 / (1 + B / ε) * B :=
      mul_le_mul_of_nonneg_right hpow hB
    _ = B / (1 + B / ε) := by ring
    _ ≤ ε := (div_le_iff₀ hpos).mpr (by rw [he]; linarith)

end LongTails.Proofs.CohypomonotoneNewtonInverse
