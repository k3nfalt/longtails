import LongTails.Proofs.FiniteProductIteration

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.ClippedExtragradient

open ContinuizedSimilarQuasar (iterateSamples)

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

lemma measurable_iterateSamples {advance : S → Ω → S}
    (ha : Measurable (Function.uncurry advance)) (k : ℕ) :
    Measurable (fun w : S × (Fin k → Ω) => iterateSamples advance k w.1 w.2) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
      have ht : Measurable (fun w : S × (Fin (k + 1) → Ω) =>
          fun i : Fin k => w.2 i.succ) := by fun_prop
      exact ih.comp ((ha.comp (measurable_fst.prodMk
        ((measurable_pi_apply 0).comp measurable_snd))).prodMk
          ht)

lemma measurable_iterateSamples_parameter {A : Type*} [MeasurableSpace A]
    {advance : A → S → Ω → S}
    (ha : Measurable (fun w : A × S × Ω => advance w.1 w.2.1 w.2.2)) (k : ℕ) :
    Measurable (fun w : A × S × (Fin k → Ω) =>
      iterateSamples (advance w.1) k w.2.1 w.2.2) := by
  induction k with
  | zero => exact measurable_fst.comp measurable_snd
  | succ k ih =>
      have ht : Measurable (fun w : A × S × (Fin (k + 1) → Ω) =>
          fun i : Fin k => w.2.2 i.succ) := by fun_prop
      have hn : Measurable (fun w : A × S × (Fin (k + 1) → Ω) =>
          advance w.1 w.2.1 (w.2.2 0)) := ha.comp
        (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
          ((measurable_pi_apply 0).comp (measurable_snd.comp measurable_snd))))
      exact ih.comp (measurable_fst.prodMk (hn.prodMk ht))

lemma measurable_finite_replies {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] {f : A × B → C}
    (hf : Measurable f) (k : ℕ) :
    Measurable (fun w : A × (Fin k → B) => fun i => f (w.1, w.2 i)) :=
  Measurable.of_eval (fun i => hf.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma iterateSamples_invariant {advance : S → Ω → S} {Inv : S → Prop}
    (hinv : ∀ s, Inv s → ∀ ω, Inv (advance s ω)) (k : ℕ) (s : S) (hs : Inv s)
    (ξ : Fin k → Ω) : Inv (iterateSamples advance k s ξ) := by
  induction k generalizing s with
  | zero => exact hs
  | succ k ih => exact ih (advance s (ξ 0)) (hinv s hs (ξ 0)) (fun i => ξ i.succ)

lemma bounded_iterate_integral {advance : S → Ω → S}
    (ha : Measurable (Function.uncurry advance)) (P : Measure Ω) [IsProbabilityMeasure P]
    (V : S → ℝ) (hV : Measurable V) {Inv : S → Prop}
    (hinv : ∀ s, Inv s → ∀ ω, Inv (advance s ω)) {M q r : ℝ}
    (hbound : ∀ s, Inv s → ‖V s‖ ≤ M) (hq : 0 ≤ q)
    (hstep : ∀ s, Inv s → (∫ ω, V (advance s ω) ∂P) ≤ q * V s + r)
    (k : ℕ) (s : S) (hs : Inv s) :
    (∫ ξ : Fin k → Ω, V (iterateSamples advance k s ξ)
      ∂Measure.pi (fun _ : Fin k => P)) ≤
      q ^ k * V s + r * ∑ j ∈ Finset.range k, q ^ j := by
  induction k generalizing s with
  | zero => simp [iterateSamples, measureReal_def]
  | succ k ih =>
      let F : Ω × (Fin k → Ω) → ℝ := fun w =>
        V (iterateSamples advance k (advance s w.1) w.2)
      have hFm : Measurable F := (hV.comp (measurable_iterateSamples ha k)).comp
        ((ha.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
      have hFi : Integrable F (P.prod (Measure.pi fun _ : Fin k => P)) := by
        apply Integrable.of_bound hFm.aestronglyMeasurable M
        exact Filter.Eventually.of_forall (fun w =>
          hbound _ (iterateSamples_invariant hinv k _ (hinv s hs w.1) w.2))
      have hAi : Integrable (fun ω => V (advance s ω)) P := by
        apply Integrable.of_bound ((hV.comp ha).comp measurable_prodMk_left).aestronglyMeasurable M
        exact Filter.Eventually.of_forall (fun ω => hbound _ (hinv s hs ω))
      have hcond (ω : Ω) : (∫ ξ : Fin k → Ω, F (ω, ξ)
          ∂Measure.pi (fun _ : Fin k => P)) ≤
          q ^ k * V (advance s ω) + r * ∑ j ∈ Finset.range k, q ^ j :=
        ih _ (hinv s hs ω)
      have hh := integral_mono hFi.integral_prod_left
        ((hAi.const_mul (q ^ k)).add (integrable_const _)) hcond
      have hadd := integral_add (hAi.const_mul (q ^ k))
        (integrable_const (r * ∑ j ∈ Finset.range k, q ^ j))
      change (∫ x, ∫ y, F (x, y) ∂Measure.pi (fun _ : Fin k => P) ∂P) ≤
        (∫ x, q ^ k * V (advance s x) + r * ∑ j ∈ Finset.range k, q ^ j ∂P) at hh
      rw [hadd, integral_const_mul] at hh
      simp only [integral_const, probReal_univ, one_smul] at hh
      have hnext := mul_le_mul_of_nonneg_left (hstep s hs) (pow_nonneg hq k)
      have hprod : (∫ w, F w ∂P.prod (Measure.pi fun _ : Fin k => P)) ≤
          q ^ (k + 1) * V s + r * ∑ j ∈ Finset.range (k + 1), q ^ j := by
        rw [integral_prod F hFi, Finset.sum_range_succ, pow_succ]
        nlinarith
      have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => P) 0).symm
      have he : (∫ ξ : Fin (k + 1) → Ω, V (iterateSamples advance (k + 1) s ξ)
          ∂Measure.pi (fun _ : Fin (k + 1) => P)) =
          ∫ w, F w ∂P.prod (Measure.pi fun _ : Fin k => P) := by
        rw [← hp.integral_comp']
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv, Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk,
          iterateSamples, Fin.cons_zero, Fin.cons_succ, cast_eq]
        rfl
      exact he.trans_le hprod

end OracleTemplate.ClippedExtragradient
