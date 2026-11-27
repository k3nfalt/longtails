import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory
open scoped BigOperators

namespace LongTails.Proofs.SlidingCompositeOuter

variable {S B : Type*} [MeasurableSpace S] [MeasurableSpace B]

def iter (step : S → B → S) : (k : ℕ) → S → (Fin k → B) → S
  | 0, s, _ => s
  | k + 1, s, ξ => iter step k (step s (ξ 0)) (fun i => ξ i.succ)

noncomputable def lossSum (step : S → B → S) (W : S → ℝ) : (k : ℕ) → S → (Fin k → B) → ℝ
  | 0, _, _ => 0
  | k + 1, s, ξ => W s + lossSum step W k (step s (ξ 0)) (fun i => ξ i.succ)

lemma measurable_iter {step : S → B → S} (hs : Measurable (Function.uncurry step)) (k : ℕ) :
    Measurable (fun q : S × (Fin k → B) => iter step k q.1 q.2) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
      exact ih.comp ((hs.comp (measurable_fst.prodMk
        ((measurable_pi_apply 0).comp measurable_snd))).prodMk
          (Measurable.of_eval (fun i => (measurable_pi_apply i.succ).comp measurable_snd)))

lemma measurable_lossSum {step : S → B → S} (hs : Measurable (Function.uncurry step))
    {W : S → ℝ} (hW : Measurable W) (k : ℕ) :
    Measurable (fun q : S × (Fin k → B) => lossSum step W k q.1 q.2) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      exact (hW.comp measurable_fst).add (ih.comp ((hs.comp (measurable_fst.prodMk
        ((measurable_pi_apply 0).comp measurable_snd))).prodMk
          (Measurable.of_eval (fun i => (measurable_pi_apply i.succ).comp measurable_snd))))

omit [MeasurableSpace S] [MeasurableSpace B] in
lemma lossSum_eq (step : S → B → S) (W : S → ℝ) (k : ℕ) (s : S) (ξ : Fin k → B) :
    lossSum step W k s ξ =
      ∑ j : Fin k, W (iter step j s (fun i => ξ (Fin.castLE j.isLt.le i))) := by
  induction k generalizing s with
  | zero => simp [lossSum]
  | succ k ih =>
      rw [lossSum, ih, Fin.sum_univ_succ]
      rfl

lemma lossSum_integral {step : S → B → S} (hs : Measurable (Function.uncurry step))
    {F W : S → ℝ} (hW : Measurable W) (hW0 : ∀ s, 0 ≤ W s)
    {lower r : ℝ} (hlow : ∀ s, lower ≤ F s) (ν : Measure B) [IsProbabilityMeasure ν]
    (hstep : ∀ s, Integrable (fun a => F (step s a)) ν ∧
      (∫ a, F (step s a) ∂ν) ≤ F s - W s + r)
    (k : ℕ) (s : S) :
    Integrable (fun ξ => lossSum step W k s ξ) (Measure.pi fun _ : Fin k => ν) ∧
    (∫ ξ, lossSum step W k s ξ ∂Measure.pi fun _ : Fin k => ν) ≤ F s - lower + k * r := by
  induction k generalizing s with
  | zero =>
      refine ⟨by simp [lossSum], ?_⟩
      simp only [lossSum, integral_zero, Nat.cast_zero, zero_mul, add_zero, sub_nonneg]
      exact hlow s
  | succ k ih =>
      let G := fun a : B × (Fin k → B) => lossSum step W k (step s a.1) a.2
      have hGm : Measurable G := (measurable_lossSum hs hW k).comp
        ((hs.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
      have hG0 : ∀ a, 0 ≤ G a := by
        intro a
        dsimp only [G]
        rw [lossSum_eq]
        exact Finset.sum_nonneg (fun j _ => hW0 _)
      have hNorm (a : B) : (∫ t, ‖G (a, t)‖ ∂Measure.pi (fun _ : Fin k => ν)) =
          ∫ t, G (a, t) ∂Measure.pi (fun _ : Fin k => ν) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => by
          change ‖G (a, t)‖ = G (a, t)
          rw [Real.norm_eq_abs, abs_of_nonneg (hG0 (a, t))])
      have hBound : Integrable (fun a => F (step s a) - lower + k * r) ν :=
        ((hstep s).1.sub (integrable_const _)).add (integrable_const _)
      have hOuter : Integrable (fun a => ∫ t, ‖G (a, t)‖ ∂Measure.pi (fun _ : Fin k => ν)) ν := by
        apply hBound.mono' hGm.aestronglyMeasurable.norm.integral_prod_right'
        apply Filter.Eventually.of_forall
        intro a
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun t => norm_nonneg _)), hNorm]
        exact (ih (step s a)).2
      have hGi : Integrable G (ν.prod (Measure.pi (fun _ : Fin k => ν))) :=
        (integrable_prod_iff hGm.aestronglyMeasurable).mpr
          ⟨Filter.Eventually.of_forall (fun a => (ih (step s a)).1), hOuter⟩
      have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => ν) 0).symm
      have hrew : (fun ξ : Fin (k + 1) → B => lossSum step W (k + 1) s ξ) =
          fun ξ => W s + G (ξ 0, fun i => ξ i.succ) := by
        funext ξ; rfl
      have hcomp : (fun ξ : Fin (k + 1) → B => G (ξ 0, fun i => ξ i.succ)) ∘
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => B) 0).symm = G := by
        funext a
        simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.cons_zero, Fin.cons_succ]
      have hGi' : Integrable (fun ξ : Fin (k + 1) → B => G (ξ 0, fun i => ξ i.succ))
          (Measure.pi (fun _ : Fin (k + 1) => ν)) := by
        rw [← hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _), hcomp]
        exact hGi
      have he : (∫ ξ, G (ξ 0, fun i => ξ i.succ) ∂Measure.pi (fun _ : Fin (k + 1) => ν)) =
          ∫ a, G a ∂ν.prod (Measure.pi (fun _ : Fin k => ν)) := by
        rw [← hp.integral_comp']
        exact congrArg (fun F => ∫ a, F a ∂ν.prod (Measure.pi (fun _ : Fin k => ν))) hcomp
      refine ⟨?_, ?_⟩
      · rw [hrew]; exact (integrable_const _).add hGi'
      · rw [hrew, integral_add (integrable_const _) hGi', he, integral_prod _ hGi,
          integral_const, smul_eq_mul, probReal_univ, one_mul]
        have hm := integral_mono_ae hGi.integral_prod_left hBound
          (Filter.Eventually.of_forall (fun a => (ih (step s a)).2))
        have hc : (∫ a, (F (step s a) - lower + k * r) ∂ν) =
            (∫ a, F (step s a) ∂ν) - lower + k * r := by
          have e : (fun a => F (step s a) - lower + k * r) =
              fun a => F (step s a) + (-lower + k * r) := by
            funext a; ring
          rw [e, integral_add (hstep s).1 (integrable_const _), integral_const, probReal_univ,
            one_smul]
          ring
        calc W s + ∫ a, ∫ t, G (a, t) ∂Measure.pi (fun _ : Fin k => ν) ∂ν
            ≤ W s + ∫ a, (F (step s a) - lower + k * r) ∂ν := by linarith
          _ = W s + ((∫ a, F (step s a) ∂ν) - lower + k * r) := by rw [hc]
          _ ≤ W s + (F s - W s + r - lower + k * r) := by linarith [(hstep s).2]
          _ = F s - lower + ((k + 1 : ℕ) : ℝ) * r := by push_cast; ring

end LongTails.Proofs.SlidingCompositeOuter
