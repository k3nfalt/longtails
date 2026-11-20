import LongTails.Proofs.ContaminatedParallelObservations
import LongTails.Proofs.ContaminatedTreeProbability

namespace LongTails.Proofs.ContaminatedParallelHistory

open MeasureTheory ProbabilityTheory
open LongTails.Setups.DistributedContaminatedSmoothNonconvex
open LongTails.Algorithms.ContaminatedParallelDescent
open LongTails.Algorithms
open ContaminatedParallelTrajectory ContaminatedParallelObservations ContaminatedParallelSampling

def atOp (ls : List Operation) (k : ℕ) := ls[k]?.getD (.train 0)

noncomputable def used (p : Params) (o : ℕ → Operation) : ℕ → Fin p.n → ℕ
  | 0 => fun _ => 0
  | k+1 => nextOffset p (used p o k) (o k)

noncomputable def state (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (o : ℕ → Operation) (s : Samples p) : ℕ → Model p
  | 0 => initialModel p
  | k+1 => let m := state p g o s k
           advance p m (o k) (decoded (ContaminatedParallelTrajectory.read p g s (used p o k) m (o k)))

lemma used_mono (p : Params) (o : ℕ → Operation) {j k : ℕ} (hj : j ≤ k) : used p o j ≤ used p o k :=
  monotone_nat_of_le_succ (fun _ _ => Nat.le_add_right _ _) hj

lemma agrees (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (ls : List Operation) (k : ℕ) (h : k ≤ ls.length) :
    state p g (atOp ls) s k = trajectory p g s (ls.take k) (fun _ => 0) (initialModel p) ∧
      used p (atOp ls) k = offset p (ls.take k) (fun _ => 0) := by
  induction k with
  | zero => simp [state,used,trajectory,offset]
  | succ k ih =>
    have hh : k < ls.length := by omega
    obtain ⟨hs, hu⟩ := ih hh.le
    constructor
    · rw [List.take_succ_eq_append_getElem hh, trajectory_append]
      simp [state,hs,hu,atOp,List.getElem?_eq_getElem hh,trajectory]
    · change nextOffset p (used p (atOp ls) k) (atOp ls k) = (ls.take (k+1)).foldl (nextOffset p) (fun _ => 0)
      rw [hu, List.take_succ_eq_append_getElem hh, List.foldl_append]
      simp only [List.foldl_cons,List.foldl_nil,atOp,List.getElem?_eq_getElem hh,Option.getD_some,offset]

def saved (p : Params) (m : Model p) (j : ℕ) := (m.training.history[j]?.getD (p.x0,0)).1

structure MeasurableModel {Z : Type*} (ν : MeasurableSpace Z) (p : Params) (m : Z → Model p) : Prop where
  point : Measurable[ν] (fun z => (m z).training.point)
  anchors : ∀ j, Measurable[ν] (fun z => (m z).training.anchors j)
  history : ∀ j, Measurable[ν] (fun z => saved p (m z) j)
  validation : Measurable[ν] (fun z => (m z).anchor)
  best : Measurable[ν] (fun z => (m z).best)

variable {Z : Type*} [MeasurableSpace Z]

lemma MeasurableModel.location {p : Params} {m : Z → Model p} (h : MeasurableModel (inferInstance : MeasurableSpace Z) p m) (op : Operation) :
    Measurable (fun z => location p (m z) op) := by
  cases op with
  | train => exact h.point
  | validate j _ => exact h.history j

lemma MeasurableModel.reference {p : Params} {m : Z → Model p} (h : MeasurableModel (inferInstance : MeasurableSpace Z) p m) (op : Operation) :
    Measurable (fun z => reference p (m z) op) := by
  cases op with
  | train l => exact h.anchors _
  | validate => exact h.validation

lemma MeasurableModel.advance {p : Params} {m : Z → Model p} (h : MeasurableModel (inferInstance : MeasurableSpace Z) p m)
    (op : Operation) (v : Z → Point p) (hv : Measurable v) :
    MeasurableModel (inferInstance : MeasurableSpace Z) p (fun z => advance p (m z) op (v z)) := by
  cases op with
  | train l =>
    by_cases hl : l = 0
    · subst l
      refine ⟨?_, fun j => h.anchors j, ?_, h.validation, h.best⟩
      · exact h.point.sub ((measurable_const.div hv.norm).smul hv)
      · intro j
        cases j with
        | zero => exact h.point
        | succ j => exact h.history j
    · refine ⟨?_, ?_, ?_, h.validation, h.best⟩
      · simpa only [ContaminatedParallelDescent.advance, LeonTrajectory.applyEstimate, ite_eq_right hl] using h.point
      · intro j
        by_cases hj : j = l
        · subst j; simpa [ContaminatedParallelDescent.advance, LeonTrajectory.applyEstimate, hl] using hv
        · simpa [ContaminatedParallelDescent.advance, LeonTrajectory.applyEstimate, hl, Function.update_of_ne hj] using h.anchors j
      · intro j
        simpa only [saved,ContaminatedParallelDescent.advance,LeonTrajectory.applyEstimate,ite_eq_right hl] using h.history j
  | validate j l =>
    refine ⟨h.point, h.anchors, h.history, hv, ?_⟩
    exact Measurable.ite ((measurableSet_le measurable_const h.best.snd).inter
      (measurableSet_le h.best.snd hv.norm)) h.best ((h.history j).prodMk hv.norm)

omit [MeasurableSpace Z] in
lemma MeasurableModel.mono {μ ν : MeasurableSpace Z} {p : Params} {m : Z → Model p}
    (h : MeasurableModel μ p m) (hν : μ ≤ ν) :
    @MeasurableModel Z ν p m := by
  rcases h with ⟨hpoint,hanchors,hhistory,hval,hbest⟩
  constructor
  · exact hpoint.mono hν le_rfl
  · exact fun j => (hanchors j).mono hν le_rfl
  · exact fun j => (hhistory j).mono hν le_rfl
  · exact hval.mono hν le_rfl
  · exact hbest.mono hν le_rfl

lemma measurable_round (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (m : Z → Model p) (hm : MeasurableModel (inferInstance : MeasurableSpace Z) p m)
    (op : Operation) (s : Z → Samples p) (u : Fin p.n → ℕ)
    (hs : ∀ i k, k < (batch p (op.precision p) i : ℕ) → Measurable (fun z => s z i (u i+k))) :
    Measurable (fun z => decoded (ContaminatedParallelTrajectory.read p g (s z) u (m z) op)) := by
  let r := fun z => ContaminatedParallelTrajectory.read p g (s z) u (m z) op
  have hv (i) : Measurable (fun z => estimate p (op.precision p) i ((r z).values i)) :=
    measurable_local p _ g hg _ (hm.location op) (fun z => freshSamples p u (s z)) hs i
  have hcodes : Measurable (fun z => rawCodes (r z)) := by
    apply Measurable.of_eval
    intro j
    apply Finset.measurable_fun_sum
    intro i _
    have hc := (DashaQuantization.measurable_indices p.d false (LeonTuning.spacing (network p))).comp
      (((hv i).sub (hm.reference op)).prodMk (measurable_const (a := fun _ : Fin p.d => (0:ℝ))))
    exact (measurable_pi_apply j).comp hc
  exact LeonMeasurability.measurable_decode (network p) op.level _ _ (hm.reference op) hcodes

lemma measurable_state (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (o : ℕ → Operation) (k : ℕ) :
    @MeasurableModel (Samples p) (past p (used p o k)) p (fun s => state p g o s k) := by
  induction k with
  | zero =>
    let _ := past p (used p o 0)
    exact ⟨measurable_const, fun _ => measurable_const, fun _ => measurable_const,
      measurable_const, measurable_const⟩
  | succ k ih =>
    let _ := past p (used p o (k+1))
    have hm := ih.mono (ν := past p (used p o (k+1))) (past_mono p (used_mono p o (Nat.le_succ k)))
    apply hm.advance
    apply @measurable_round (Samples p) (past p (used p o (k+1))) p g hg _ hm (o k) id (used p o k)
    intro i j h
    exact past_eval p _ i _ (Nat.add_lt_add_left h _)

end LongTails.Proofs.ContaminatedParallelHistory
