import LongTails.Proofs.ThirdOrderMaskedExecution
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.ThirdOrderMaskedScaling

attribute [-instance] LongTails.Setups.FiniteSumNondualSmoothConvex.pointMeasurableSpace
  LongTails.Setups.FiniteSumNondualSmoothConvex.pointBorelSpace

open LongTails.Proofs.ThirdOrderMaskedOracle
open LongTails.Proofs.RelativeHessianSimulation (axes axes_orthonormal)
open LongTails.Proofs.AbcHardOracle (coin Scale toUnit coin_measurable toUnit_norm_sub)

section Shift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma shift_gradient (h : E → ℝ) (c x : E) :
    gradient (fun y => h (y - c)) x = gradient h (x - c) := by
  simp only [gradient, fderiv_comp_sub]

lemma shift_hessian (h : E → ℝ) (c x : E) :
    fderiv ℝ (gradient (fun y => h (y - c))) x = fderiv ℝ (gradient h) (x - c) := by
  have e : gradient (fun y => h (y - c)) = fun y => gradient h (y - c) :=
    funext (shift_gradient h c)
  rw [e, fderiv_comp_sub]

lemma shift_third (h : E → ℝ) (c x : E) :
    fderiv ℝ (fderiv ℝ (gradient (fun y => h (y - c)))) x =
      fderiv ℝ (fderiv ℝ (gradient h)) (x - c) := by
  have e : fderiv ℝ (gradient (fun y => h (y - c))) = fun y => fderiv ℝ (gradient h) (y - c) :=
    funext (shift_hessian h c)
  rw [e, fderiv_comp_sub]

end Shift

variable {d n : ℕ}

noncomputable def unitScaled (S : Scale) (π : Fin (n + 1) ↪ Fin d) (z : Space d) : ℝ :=
  S.a * hardValue π ((1 / S.lam) • z)

lemma unitScaled_eq (S : Scale) (π : Fin (n + 1) ↪ Fin d) :
    unitScaled S π = fun z => S.a * hardValue π ((1 / S.lam) • z) := rfl

lemma objective_eq (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d) :
    objective S π x0 = fun y => unitScaled S π (y - x0) := rfl

lemma hardValue_smooth (π : Fin (n + 1) ↪ Fin d) : ContDiff ℝ 3 (hardValue π) :=
  RelativeHessianLocalized.smooth (axes π)

lemma unitScaled_smooth (S : Scale) (π : Fin (n + 1) ↪ Fin d) : ContDiff ℝ 3 (unitScaled S π) := by
  rw [unitScaled_eq]
  exact contDiff_const.mul ((hardValue_smooth π).comp (by fun_prop))

lemma objective_smooth (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d) :
    ContDiff ℝ 3 (objective S π x0) := by
  rw [objective_eq]
  exact (unitScaled_smooth S π).comp (by fun_prop)

lemma objective_gradient (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    gradient (objective S π x0) x = objGrad S π x0 x := by
  rw [objective_eq, shift_gradient]
  rw [unitScaled_eq, ThirdOrderAffineCalculus.scale_gradient (hardValue_smooth π)]
  simp only [objGrad, hardGrad, toUnit, mul_one_div]

lemma objective_hessian (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    fderiv ℝ (gradient (objective S π x0)) x =
      (S.a * (1 / S.lam) ^ 2) • fderiv ℝ (gradient (hardValue π)) (toUnit S x0 x) := by
  rw [objective_eq, shift_hessian]
  rw [unitScaled_eq, ThirdOrderAffineCalculus.scale_hessian (hardValue_smooth π)]
  rfl

lemma objective_third (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    fderiv ℝ (fderiv ℝ (gradient (objective S π x0))) x =
      (S.a * (1 / S.lam) ^ 3) • fderiv ℝ (fderiv ℝ (gradient (hardValue π))) (toUnit S x0 x) := by
  rw [objective_eq, shift_third]
  rw [unitScaled_eq, ThirdOrderAffineCalculus.scale_third (hardValue_smooth π)]
  rfl

lemma objective_gradient_lipschitz (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x y : Space d) :
    ‖gradient (objective S π x0) x - gradient (objective S π x0) y‖ ≤
      2 ^ 55 * S.a / S.lam ^ 2 * ‖x - y‖ := by
  have ha := S.ha
  have hl := S.hlam
  rw [objective_gradient, objective_gradient, objGrad, objGrad, ← smul_sub, norm_smul,
    Real.norm_of_nonneg (by positivity)]
  have h := ThirdOrderChainLipschitz.value_gradient_lipschitz (axes_orthonormal π)
    (toUnit S x0 x) (toUnit S x0 y)
  rw [toUnit_norm_sub] at h
  calc _ ≤ S.a / S.lam * (2 ^ 55 * (‖x - y‖ / S.lam)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

lemma objective_hessian_lipschitz (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x y : Space d) :
    ‖fderiv ℝ (gradient (objective S π x0)) x - fderiv ℝ (gradient (objective S π x0)) y‖ ≤
      2 ^ 56 * S.a / S.lam ^ 3 * ‖x - y‖ := by
  have ha := S.ha
  have hl := S.hlam
  rw [objective_hessian, objective_hessian]
  have e : (S.a * (1 / S.lam) ^ 2) • fderiv ℝ (gradient (hardValue π)) (toUnit S x0 x) -
      (S.a * (1 / S.lam) ^ 2) • fderiv ℝ (gradient (hardValue π)) (toUnit S x0 y) =
      (S.a * (1 / S.lam) ^ 2) • (fderiv ℝ (gradient (hardValue π)) (toUnit S x0 x) -
        fderiv ℝ (gradient (hardValue π)) (toUnit S x0 y)) := by
    ext u : 1
    simp only [sub_apply, smul_apply, smul_sub]
  rw [e]
  refine (ThirdOrderAffineCalculus.norm_smul_operator_le _ _).trans ?_
  rw [abs_of_pos (by positivity)]
  have h := ThirdOrderChainLipschitz.value_hessian_lipschitz (axes_orthonormal π)
    (toUnit S x0 x) (toUnit S x0 y)
  rw [toUnit_norm_sub] at h
  calc _ ≤ S.a * (1 / S.lam) ^ 2 * (2 ^ 56 * (‖x - y‖ / S.lam)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

lemma objective_third_lipschitz (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x y : Space d) :
    ‖fderiv ℝ (fderiv ℝ (gradient (objective S π x0))) x -
        fderiv ℝ (fderiv ℝ (gradient (objective S π x0))) y‖ ≤
      2 ^ 60 * S.a / S.lam ^ 4 * ‖x - y‖ := by
  have ha := S.ha
  have hl := S.hlam
  rw [objective_third, objective_third]
  have e : (S.a * (1 / S.lam) ^ 3) • fderiv ℝ (fderiv ℝ (gradient (hardValue π))) (toUnit S x0 x) -
      (S.a * (1 / S.lam) ^ 3) • fderiv ℝ (fderiv ℝ (gradient (hardValue π))) (toUnit S x0 y) =
      (S.a * (1 / S.lam) ^ 3) • (fderiv ℝ (fderiv ℝ (gradient (hardValue π))) (toUnit S x0 x) -
        fderiv ℝ (fderiv ℝ (gradient (hardValue π))) (toUnit S x0 y)) := by
    ext u w : 2
    simp only [sub_apply, smul_apply, smul_sub]
  rw [e]
  refine (ThirdOrderAffineCalculus.norm_smul_tensor_le _ _).trans ?_
  rw [abs_of_pos (by positivity)]
  have h := ThirdOrderChainLipschitz.value_third_lipschitz (axes_orthonormal π)
    (toUnit S x0 x) (toUnit S x0 y)
  rw [toUnit_norm_sub] at h
  calc _ ≤ S.a * (1 / S.lam) ^ 3 * (2 ^ 60 * (‖x - y‖ / S.lam)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

lemma objective_gap (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 x : Space d) :
    objective S π x0 x0 - objective S π x0 x ≤ S.a * (4 * (n + 1 : ℕ)) := by
  have h0 : toUnit S x0 x0 = 0 := by simp [toUnit]
  have h := RelativeHessianLocalized.gap (axes π) (toUnit S x0 x)
  simp only [objective, h0, hardValue]
  have := mul_le_mul_of_nonneg_left h S.ha.le
  linarith

lemma toUnit_continuous (S : Scale) (x0 : Space d) : Continuous (toUnit S x0) := by
  unfold toUnit; fun_prop

lemma knownPart_continuous (S : Scale) (π : Fin (n + 1) ↪ Fin d) (m : ℕ) (x0 : Space d) :
    Continuous (knownPart S π m x0) := by
  unfold knownPart
  exact ((partGrad_continuous π (m - 1)).comp (toUnit_continuous S x0)).const_smul (S.a / S.lam)

lemma objGrad_continuous (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d) :
    Continuous (objGrad S π x0) := by
  unfold objGrad
  exact ((hardGrad_continuous π).comp (toUnit_continuous S x0)).const_smul (S.a / S.lam)

local instance : MeasurableSup₂ ℕ := ⟨measurable_of_countable _⟩

lemma stage_measurable (S : Scale) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d) :
    Measurable (fun x => stage π (toUnit S x0 x)) := by
  have hne : (Finset.univ : Finset (Fin (n + 1))).Nonempty := Finset.univ_nonempty
  have he : (fun x => stage π (toUnit S x0 x)) = Finset.univ.sup' hne
      (fun (i : Fin (n + 1)) (x : Space d) =>
        if 1 / 20 < |toUnit S x0 x (π i)| then i.val + 1 else 0) := by
    funext x
    rw [Finset.sup'_apply, Finset.sup'_eq_sup]
    rfl
  rw [he]
  apply Finset.measurable_sup'
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  apply measurableSet_lt measurable_const
  have hc : Continuous (fun x => |toUnit S x0 x (π i)|) :=
    continuous_abs.comp ((PiLp.continuous_apply 2 _ (π i)).comp (toUnit_continuous S x0))
  exact hc.measurable

lemma reply_measurable (S : Scale) (q : ℝ) (π : Fin (n + 1) ↪ Fin d) (x0 : Space d) :
    Measurable (Function.uncurry (reply S q π x0)) := by
  let G : (Space d × ℝ) × ℕ → Space d := fun p =>
    knownPart S π p.2 x0 p.1.1 +
      coin q p.1.2 • (objGrad S π x0 p.1.1 - knownPart S π p.2 x0 p.1.1)
  have hG : Measurable G := by
    apply measurable_from_prod_countable_left
    intro m
    have hk : Measurable (fun z : Space d × ℝ => knownPart S π m x0 z.1) :=
      (knownPart_continuous S π m x0).measurable.comp measurable_fst
    have ho : Measurable (fun z : Space d × ℝ => objGrad S π x0 z.1) :=
      (objGrad_continuous S π x0).measurable.comp measurable_fst
    have hc : Measurable (fun z : Space d × ℝ => coin q z.2) :=
      (coin_measurable q).comp measurable_snd
    exact hk.add (hc.smul (ho.sub hk))
  have he : Function.uncurry (reply S q π x0) =
      G ∘ (fun z : Space d × ℝ => (z, stage π (toUnit S x0 z.1))) := by
    funext z
    rfl
  rw [he]
  exact hG.comp (measurable_id.prodMk ((stage_measurable S π x0).comp measurable_fst))

end LongTails.Proofs.ThirdOrderMaskedScaling
