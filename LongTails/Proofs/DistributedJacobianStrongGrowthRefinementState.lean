import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementReference
import LongTails.Proofs.DistributedJacobianStrongGrowthSampleReference

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRefinementState

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthWorkerReference
open DistributedJacobianStrongGrowthRefinementReference

noncomputable def RefinementState (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (i : Fin p.n) (s : State p) : Prop :=
  (∀ epoch, s.phase = .refinement epoch → s.current = refinementPoint p g samples epoch ∧
    match s.work with
    | some work => ∃ used, used ≤ 2 * localDepth p ∧
        work = extraWork p (localDepth p) (g i) (refinementPoint p g samples epoch)
          (refinementSamples p samples epoch i) used
    | none => s.own = refinementValues p g samples epoch i) ∧
  (s.phase = .done → s.current = refinementPoint p g samples (refinementCount p (localDepth p)))

lemma refinementState_initial (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (i : Fin p.n)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    RefinementState p g samples i (initialState p i) := by
  simp [RefinementState, initialState, not_le.mpr hε, hrich]

lemma refinementState_start (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (i : Fin p.n)
    (s : State p) (epoch : ℕ) (he : epoch ≤ refinementCount p (localDepth p))
    (hx : s.current = refinementPoint p g samples epoch) :
    RefinementState p g samples i (startRefinement p epoch s) := by
  unfold startRefinement
  split_ifs with hk
  · constructor
    · intro e hs
      have heq : epoch = e := Phase.refinement.inj hs
      subst e
      refine ⟨hx, 0, by omega, ?_⟩
      simp only [extraWork_initial, hx]
    · intro hs
      cases hs
  · have heq : epoch = refinementCount p (localDepth p) := by omega
    constructor
    · intro e hs
      cases hs
    · intro _
      simpa only [heq] using hx

lemma extraWork_endpoint (p : Params) (T : ℕ) (g : Point p → p.Ω → Point p)
    (x : Point p) (samples : ℕ → p.Ω) (used : ℕ) (hu : used ≤ 2 * T)
    (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query (extraWork p T g x samples used) = none) :
    LongTails.Algorithms.DistributedLocalExtragradientWorker.point (extraWork p T g x samples used) =
      LongTails.Algorithms.LocalNonlinearExtragradient.run (1 / (4 * p.L)) g x samples T := by
  have hh := (DistributedJacobianStrongGrowthWorker.query_none_iff p _).mp hq
  rw [extraWork_remaining p T g x samples used hu] at hh
  have he : used = 2 * T := by omega
  rw [he, extraWork_final]
  rfl

lemma refinementState_finishLocal (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (i : Fin p.n)
    (s : State p) (work : LongTails.Algorithms.DistributedLocalExtragradientWorker.Work p)
    (h : RefinementState p g samples i s) (hn : s.phase ≠ .baseline)
    (hw : s.work = some work) (hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work = none) :
    RefinementState p g samples i
      (finishLocal p s (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work)) := by
  cases hs : s.phase with
  | baseline => exact False.elim (hn hs)
  | warming => simp [RefinementState, finishLocal, hs, startMedian]
  | median remaining => simp [RefinementState, finishLocal, hs]
  | done => simpa [RefinementState, finishLocal, hs] using h.2 hs
  | refinement epoch =>
      have hh := h.1 epoch hs
      have hwref : ∃ used, used ≤ 2 * localDepth p ∧
          work = extraWork p (localDepth p) (g i) (refinementPoint p g samples epoch)
            (refinementSamples p samples epoch i) used := by simpa only [hw] using hh.2
      obtain ⟨used, hu, he⟩ := hwref
      have hend := extraWork_endpoint p (localDepth p) (g i) (refinementPoint p g samples epoch)
        (refinementSamples p samples epoch i) used hu (by simpa only [← he] using hq)
      rw [← he] at hend
      constructor
      · intro e hphase
        have heq : epoch = e := by simpa only [finishLocal, hs, Phase.refinement.injEq] using hphase
        subst e
        constructor
        · simpa only [finishLocal, hs] using hh.1
        · rw [show (finishLocal p s (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work)).work = none by
            simp [finishLocal, hs]]
          rw [hend]
          exact refinement_finishLocal_own p g samples i s epoch hs hh.1
      · intro hphase
        simp only [finishLocal, hs, reduceCtorEq] at hphase

lemma refinementState_congr (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (i : Fin p.n)
    (s t : State p) (hphase : t.phase = s.phase) (hx : t.current = s.current)
    (hw : t.work = s.work) (hown : t.own = s.own) (h : RefinementState p g samples i s) :
    RefinementState p g samples i t := by
  simpa only [RefinementState, hphase, hx, hw, hown] using h

lemma refinement_computed_fields (p : Params) (i : Fin p.n) (s : State p) (value : Point p) :
    (update p i s (.computed value)).phase = s.phase ∧
    (update p i s (.computed value)).current = s.current := by
  cases hw : s.work <;> cases hb : s.busy <;> simp [update, hw, hb]

lemma refinementState_computed (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (S : Sampling p)
    (i : Fin p.n) (s : State p) (oracle next : ComputationState p)
    (time : DistributedTemplate.Time) (value : Point p)
    (h : RefinementState p g samples i s)
    (ha : DistributedJacobianStrongGrowthQueryAccounting.Accounted p s oracle.used)
    (hm : DistributedJacobianStrongGrowthExecution.PendingMatches p s oracle)
    (hsamples : oracle.samples = samples)
    (hanswer : (computation p g S).answer i oracle time = some (value, next)) :
    RefinementState p g samples i (update p i s (.computed value)) := by
  have hf := refinement_computed_fields p i s value
  constructor
  · intro epoch hsnew
    have hs : s.phase = .refinement epoch := hf.1.symm.trans hsnew
    have hh := h.1 epoch hs
    refine ⟨hf.2.trans hh.1, ?_⟩
    obtain ⟨finish, point, hpending, _, _, _⟩ :=
      DistributedJacobianStrongGrowthOracle.computation_received_data p g S i oracle next time value hanswer
    obtain ⟨work, hwork, hquery⟩ := hm.2 finish point hpending
    have hwref : ∃ used, used ≤ 2 * localDepth p ∧
        work = extraWork p (localDepth p) (g i) (refinementPoint p g samples epoch)
          (refinementSamples p samples epoch i) used := by simpa only [hwork] using hh.2
    obtain ⟨used, hu, he⟩ := hwref
    have hlt : used < 2 * localDepth p := by
      by_contra hn
      have heq : used = 2 * localDepth p := by omega
      rw [he, heq, extraWork_final, LongTails.Algorithms.DistributedLocalExtragradientWorker.query] at hquery
      cases hquery
    have hw' : s.work = some (extraWork p (localDepth p) (g i) (refinementPoint p g samples epoch)
        (refinementSamples p samples epoch i) used) := hwork.trans (congrArg some he)
    have hnext := DistributedJacobianStrongGrowthSampleReference.refinement_answer_work p g S i s oracle next
      epoch used (refinementPoint p g samples epoch) value time hs
      (by unfold refinementSamples at hw'; simpa only [hsamples] using hw') hlt ha hm hanswer
    have hn : (update p i s (.computed value)).work = some (extraWork p (localDepth p) (g i)
        (refinementPoint p g samples epoch) (refinementSamples p samples epoch i) (used + 1)) := by
      unfold refinementSamples
      simpa only [hsamples] using hnext
    rw [hn]
    exact ⟨used + 1, by omega, rfl⟩
  · intro hs
    exact hf.2.trans (h.2 (hf.1.symm.trans hs))

end LongTails.Proofs.DistributedJacobianStrongGrowthRefinementState
