import LongTails.Proofs.DistributedJacobianStrongGrowthNetworkExecution

namespace LongTails.Proofs.DistributedJacobianStrongGrowthPhaseProgress

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning

def PhaseBounds (p : Params) (phase : Phase) : Prop :=
  match phase with
  | .median remaining => 1 ≤ remaining ∧ remaining ≤ warmWidth p (localDepth p)
  | .refinement epoch => epoch < refinementCount p (localDepth p)
  | _ => True

noncomputable def epochIndex (p : Params) (phase : Phase) : ℕ :=
  match phase with
  | .median remaining => warmWidth p (localDepth p) - remaining
  | .refinement epoch => warmWidth p (localDepth p) + epoch
  | .done => warmWidth p (localDepth p) + refinementCount p (localDepth p)
  | _ => 0

lemma warmWidth_pos (p : Params) : 1 ≤ warmWidth p (localDepth p) := by
  unfold warmWidth
  omega

lemma phaseBounds_initial (p : Params) (v : Fin p.n) : PhaseBounds p (initialState p v).phase := by
  unfold initialState
  split_ifs <;> trivial

lemma phaseBounds_startRefinement (p : Params) (epoch : ℕ) (s : State p) :
    PhaseBounds p (startRefinement p epoch s).phase := by
  unfold startRefinement
  split_ifs with h
  · exact h
  · trivial

lemma phaseBounds_finishLocal (p : Params) (s : State p) (x : Point p)
    (h : PhaseBounds p s.phase) : PhaseBounds p (finishLocal p s x).phase := by
  cases hs : s.phase with
  | baseline => simp [finishLocal, hs, PhaseBounds]
  | warming =>
      simpa [finishLocal, hs, startMedian, PhaseBounds] using And.intro (warmWidth_pos p) (le_refl (warmWidth p (localDepth p)))
  | median remaining => simpa [finishLocal, hs] using h
  | refinement epoch => simpa [finishLocal, hs] using h
  | done => simp [finishLocal, hs, PhaseBounds]

lemma phaseBounds_finishBroadcast (p : Params) (s : State p) (values : Fin p.d → ℕ)
    (h : PhaseBounds p s.phase) : PhaseBounds p (finishBroadcast p s values).phase := by
  cases hs : s.phase with
  | baseline => simpa [finishBroadcast, hs] using h
  | warming => simpa [finishBroadcast, hs] using h
  | done => simpa [finishBroadcast, hs] using h
  | refinement epoch =>
      simp only [finishBroadcast, hs]
      exact phaseBounds_startRefinement _ _ _
  | median remaining =>
      have hb : 1 ≤ remaining ∧ remaining ≤ warmWidth p (localDepth p) := by simpa [PhaseBounds, hs] using h
      simp only [finishBroadcast, hs]
      split_ifs with hr
      · change 1 ≤ remaining - 1 ∧ remaining - 1 ≤ warmWidth p (localDepth p)
        omega
      · exact phaseBounds_startRefinement _ _ _

lemma epochIndex_finishBroadcast (p : Params) (s : State p) (values : Fin p.d → ℕ)
    (h : PhaseBounds p s.phase) (ha : DistributedJacobianStrongGrowthPhases.Active s.phase) :
    epochIndex p (finishBroadcast p s values).phase = epochIndex p s.phase + 1 := by
  cases hs : s.phase <;> simp only [hs, DistributedJacobianStrongGrowthPhases.Active] at ha
  · rename_i remaining
    have hb : 1 ≤ remaining ∧ remaining ≤ warmWidth p (localDepth p) := by simpa only [PhaseBounds, hs] using h
    simp only [finishBroadcast, hs]
    split_ifs with hr
    · simp only [startMedian, epochIndex]
      omega
    · unfold startRefinement
      split_ifs with hk <;> simp only [epochIndex]
      · omega
      · omega
  · rename_i epoch
    have hb : epoch < refinementCount p (localDepth p) := by simpa only [PhaseBounds, hs] using h
    simp only [finishBroadcast, hs]
    unfold startRefinement
    split_ifs with hk <;> simp only [epochIndex] <;> omega

lemma phaseBounds_update (p : Params) (v : Fin p.n) (s : State p)
    (notification : DistributedTemplate.Event (Point p) (CommReply p))
    (h : PhaseBounds p s.phase) : PhaseBounds p (update p v s notification).phase := by
  cases notification with
  | wake => exact h
  | computed value =>
      simp only [update]
      split
      · split_ifs <;> exact h
      · exact h
  | received message =>
      simp only [update]
      split_ifs
      · exact phaseBounds_finishBroadcast _ _ _ h
      · exact h

lemma phaseBounds_query (p : Params) (v : Fin p.n) (s : State p)
    (h : PhaseBounds p s.phase) : PhaseBounds p (query p v s).2.phase := by
  unfold query
  split
  · exact h
  · split
    · split_ifs
      · exact h
      · split
        · exact h
        · exact phaseBounds_finishLocal _ _ _ h
    · split_ifs
      · exact phaseBounds_finishBroadcast _ _ _ h
      · exact h
      · exact h

lemma phaseBounds_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : DistributedTemplate.Time) (k : ℕ)
    (c : DistributedTemplate.ExecutionState (system p g S) (algorithm p idle))
    (h : ∀ v, PhaseBounds p (c.workers v).phase) :
    ∀ v, PhaseBounds p ((DistributedTemplate.run (system p g S) (algorithm p idle) k c).workers v).phase := by
  induction k generalizing c with
  | zero => exact h
  | succ k ih =>
      cases hs : DistributedTemplate.step (system p g S) (algorithm p idle) c with
      | none => simpa only [DistributedTemplate.run, hs] using h
      | some next =>
          have hn := DistributedJacobianStrongGrowthPhases.statePredicate_step p g S idle
            (fun s => PhaseBounds p s.phase) (phaseBounds_update p)
            (fun v s next action h hq => by
              have hh := phaseBounds_query p v s h
              simpa only [hq] using hh) c next h hs
          simpa only [DistributedTemplate.run, hs] using ih next hn

lemma phaseBounds_initial_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle deadline : DistributedTemplate.Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ) (v : Fin p.n) :
    PhaseBounds p ((DistributedTemplate.run (system p g S) (algorithm p idle) k
      (DistributedTemplate.initial (system p g S) (algorithm p idle) deadline seed)).workers v).phase :=
  phaseBounds_run p g S idle k _ (fun i => phaseBounds_initial p i) v

lemma epochIndex_finishLocal (p : Params) (s : State p) (x : Point p)
    (h : s.phase ≠ .baseline) :
    epochIndex p (finishLocal p s x).phase = epochIndex p s.phase := by
  cases hs : s.phase with
  | baseline => exact False.elim (h hs)
  | warming => simp [finishLocal, hs, startMedian, epochIndex]
  | median remaining => simp [finishLocal, hs]
  | refinement epoch => simp [finishLocal, hs]
  | done => simp [finishLocal, hs]

lemma noBaseline_startRefinement (p : Params) (epoch : ℕ) (s : State p) :
    (startRefinement p epoch s).phase ≠ .baseline := by
  unfold startRefinement
  split_ifs <;> simp

lemma noBaseline_finishLocal (p : Params) (s : State p) (x : Point p) :
    (finishLocal p s x).phase ≠ .baseline := by
  cases hs : s.phase <;> simp [finishLocal, hs, startMedian]

lemma noBaseline_finishBroadcast (p : Params) (s : State p) (values : Fin p.d → ℕ)
    (h : s.phase ≠ .baseline) : (finishBroadcast p s values).phase ≠ .baseline := by
  cases hs : s.phase with
  | baseline => exact False.elim (h hs)
  | warming => simp [finishBroadcast, hs]
  | done => simp [finishBroadcast, hs]
  | refinement epoch =>
      simp only [finishBroadcast, hs]
      exact noBaseline_startRefinement _ _ _
  | median remaining =>
      simp only [finishBroadcast, hs]
      split_ifs
      · simp [startMedian]
      · exact noBaseline_startRefinement _ _ _

lemma noBaseline_initial (p : Params) (v : Fin p.n)
    (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    (initialState p v).phase ≠ .baseline := by
  unfold initialState
  split_ifs <;> simp_all

lemma noBaseline_update (p : Params) (v : Fin p.n) (s : State p)
    (notification : DistributedTemplate.Event (Point p) (CommReply p))
    (h : s.phase ≠ .baseline) : (update p v s notification).phase ≠ .baseline := by
  cases notification with
  | wake => exact h
  | computed value =>
      simp only [update]
      split
      · split_ifs <;> exact h
      · exact h
  | received message =>
      simp only [update]
      split_ifs
      · exact noBaseline_finishBroadcast _ _ _ h
      · exact h

lemma noBaseline_query (p : Params) (v : Fin p.n) (s : State p)
    (h : s.phase ≠ .baseline) : (query p v s).2.phase ≠ .baseline := by
  unfold query
  split
  · exact h
  · split
    · split_ifs
      · exact h
      · split
        · exact h
        · exact noBaseline_finishLocal _ _ _
    · split_ifs
      · exact noBaseline_finishBroadcast _ _ _ h
      · exact h
      · exact h

lemma noBaseline_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle : DistributedTemplate.Time) (k : ℕ)
    (c : DistributedTemplate.ExecutionState (system p g S) (algorithm p idle))
    (h : ∀ v, (c.workers v).phase ≠ .baseline) :
    ∀ v, ((DistributedTemplate.run (system p g S) (algorithm p idle) k c).workers v).phase ≠ .baseline := by
  induction k generalizing c with
  | zero => exact h
  | succ k ih =>
      cases hs : DistributedTemplate.step (system p g S) (algorithm p idle) c with
      | none => simpa only [DistributedTemplate.run, hs] using h
      | some next =>
          have hn := DistributedJacobianStrongGrowthPhases.statePredicate_step p g S idle
            (fun s => s.phase ≠ .baseline) (noBaseline_update p)
            (fun v s next action h hq => by
              have hh := noBaseline_query p v s h
              simpa only [hq] using hh) c next h hs
          simpa only [DistributedTemplate.run, hs] using ih next hn

lemma noBaseline_initial_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p)
    (S : Sampling p) (idle deadline : DistributedTemplate.Time)
    (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ) (v : Fin p.n)
    (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    ((DistributedTemplate.run (system p g S) (algorithm p idle) k
      (DistributedTemplate.initial (system p g S) (algorithm p idle) deadline seed)).workers v).phase ≠ .baseline :=
  noBaseline_run p g S idle k _ (fun i => noBaseline_initial p i hrich) v

end LongTails.Proofs.DistributedJacobianStrongGrowthPhaseProgress
