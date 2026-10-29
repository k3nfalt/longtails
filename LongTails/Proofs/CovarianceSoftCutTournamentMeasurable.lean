import LongTails.Proofs.CovarianceSoftCutTournament
import LongTails.Proofs.CovarianceSoftCutMom

open MeasureTheory

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutTournamentMeasurable

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut
open LongTails.Proofs.CovarianceSoftCutMom

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_segmentMid (q : Params) : Measurable (segmentMid q) := by
  unfold segmentMid
  fun_prop

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_segmentDirection (q : Params) : Measurable (segmentDirection q) := by
  unfold segmentDirection
  fun_prop

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_bisectUpdate (q : Params) (a : ℝ) :
    Measurable (fun z : (Space q × Space q) × ℝ => bisectUpdate q a z.1 z.2) := by
  have hm : Measurable (fun z : (Space q × Space q) × ℝ => segmentMid q z.1) :=
    (measurable_segmentMid q).comp measurable_fst
  apply Measurable.ite (measurableSet_lt measurable_const measurable_snd)
  · exact (measurable_fst.comp measurable_fst).prodMk hm
  · apply Measurable.ite (measurableSet_lt measurable_snd measurable_const)
    · exact hm.prodMk (measurable_snd.comp measurable_fst)
    · exact hm.prodMk hm

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_bisectReplyRun (q : Params) (a : ℝ) (n m k : ℕ) :
    Measurable (fun z : (Space q × Space q) × (ℕ → Space q) => bisectReplyRun q a n m z.1 z.2 k) := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
    have hd : Measurable (fun z : (Space q × Space q) × (ℕ → Space q) =>
        segmentDirection q (bisectReplyRun q a n m z.1 z.2 k)) :=
      (measurable_segmentDirection q).comp ih
    have hr : Measurable (fun z : (Space q × Space q) × (ℕ → Space q) =>
        fun i : Fin (n*m) => z.2 (k*(n*m)+i.val)) := by fun_prop
    have hp : Measurable (fun z : (Space q × Space q) × (ℕ → Space q) =>
        (segmentDirection q (bisectReplyRun q a n m z.1 z.2 k),
          fun i : Fin (n*m) => z.2 (k*(n*m)+i.val))) := hd.prodMk hr
    have he : Measurable (fun z : (Space q × Space q) × (ℕ → Space q) =>
        directionalMomBlock q n m (segmentDirection q (bisectReplyRun q a n m z.1 z.2 k))
          (fun i => z.2 (k*(n*m)+i.val))) := by
      simpa only [Function.comp_def] using (measurable_directionalMomBlock q n m).comp hp
    have hi := ih.prodMk he
    simpa only [Function.comp_def, bisectReplyRun] using (measurable_bisectUpdate q a).comp hi

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_bisectProbe (q : Params) (a : ℝ) (n m k : ℕ) :
    Measurable (fun z : (Space q × Space q) × (ℕ → Space q) => bisectProbe q a n m z.1 z.2 k) := by
  exact ((measurable_segmentMid q).comp (measurable_bisectReplyRun q a n m k)).prodMk
    ((measurable_segmentDirection q).comp (measurable_bisectReplyRun q a n m k))

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_selectionOutput (q : Params) (a : ℝ) (K n m h : ℕ) :
    Measurable (fun z : (ℕ → Space q) × (ℕ → Space q) => selectionOutput q a K n m h z.1 z.2) := by
  induction h with
  | zero => exact (measurable_pi_apply 0).comp measurable_fst
  | succ h ih =>
    have hshift : Measurable (fun z : (ℕ → Space q) × (ℕ → Space q) =>
        ((fun i => z.1 (2^h+i)), (fun i => z.2 (selectionBlocks K h*(n*m)+i)))) := by fun_prop
    have hr : Measurable (fun z : (ℕ → Space q) × (ℕ → Space q) =>
        selectionOutput q a K n m h (fun i => z.1 (2^h+i))
          (fun i => z.2 (selectionBlocks K h*(n*m)+i))) := by
      simpa only [Function.comp_def] using ih.comp hshift
    have hp := ih.prodMk hr
    have ht : Measurable (fun z : (ℕ → Space q) × (ℕ → Space q) =>
        fun i => z.2 (2*(selectionBlocks K h*(n*m))+i)) := by fun_prop
    have hi := hp.prodMk ht
    have hh := (measurable_segmentMid q).comp ((measurable_bisectReplyRun q a n m K).comp hi)
    simpa only [Function.comp_def, selectionOutput] using hh

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_selectionProbe (q : Params) (a : ℝ) (K n m h t : ℕ) :
    Measurable (fun z : (ℕ → Space q) × (ℕ → Space q) => selectionProbe q a K n m h z.1 z.2 t) := by
  induction h generalizing t with
  | zero => exact measurable_const
  | succ h ih =>
    have hshift : Measurable (fun z : (ℕ → Space q) × (ℕ → Space q) =>
        ((fun i => z.1 (2^h+i)), (fun i => z.2 (selectionBlocks K h*(n*m)+i)))) := by fun_prop
    simp only [selectionProbe]
    split_ifs
    · exact ih t
    · simpa only [Function.comp_def] using (ih (t-selectionBlocks K h)).comp hshift
    · have hl := measurable_selectionOutput q a K n m h
      have hr : Measurable (fun z : (ℕ → Space q) × (ℕ → Space q) =>
          selectionOutput q a K n m h (fun i => z.1 (2^h+i))
            (fun i => z.2 (selectionBlocks K h*(n*m)+i))) := by
        simpa only [Function.comp_def] using hl.comp hshift
      have hp := hl.prodMk hr
      have ht : Measurable (fun z : (ℕ → Space q) × (ℕ → Space q) =>
          fun i => z.2 (2*(selectionBlocks K h*(n*m))+i)) := by fun_prop
      simpa only [Function.comp_def] using
        (measurable_bisectProbe q a n m (t-2*selectionBlocks K h)).comp (hp.prodMk ht)

end LongTails.Proofs.CovarianceSoftCutTournamentMeasurable
