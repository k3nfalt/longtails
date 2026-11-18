import LongTails.Proofs.DistributedJacobianStrongGrowthRouting

namespace LongTails.Proofs.DistributedJacobianStrongGrowthLiveShape

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol

def LiveShape (p : Params) (s : State p) : Prop :=
  match s.phase with
  | .baseline | .warming => s.work.isSome
  | .median _ => s.ready = true
  | .refinement _ => s.work.isSome ∨ s.ready = true
  | .done => True

lemma liveShape_initial (p : Params) (v : Fin p.n) : LiveShape p (initialState p v) := by
  unfold initialState
  split_ifs <;> simp [LiveShape]

lemma liveShape_startMedian (p : Params) (remaining : ℕ) (s : State p) :
    LiveShape p (startMedian p remaining s) := by
  simp [LiveShape, startMedian]

lemma liveShape_startRefinement (p : Params) (epoch : ℕ) (s : State p) :
    LiveShape p (startRefinement p epoch s) := by
  unfold startRefinement
  split_ifs <;> simp [LiveShape]

lemma liveShape_finishLocal (p : Params) (s : State p) (x : Point p) (h : LiveShape p s) :
    LiveShape p (finishLocal p s x) := by
  cases hs : s.phase <;> simp_all [LiveShape, finishLocal, startMedian]

lemma liveShape_finishBroadcast (p : Params) (s : State p) (values : Fin p.d → ℕ)
    (h : LiveShape p s) : LiveShape p (finishBroadcast p s values) := by
  cases hs : s.phase with
  | baseline => simpa [finishBroadcast, hs] using h
  | warming => simpa [finishBroadcast, hs] using h
  | done => simp [finishBroadcast, hs, LiveShape]
  | median remaining =>
      simp only [finishBroadcast, hs]
      split_ifs
      · exact liveShape_startMedian _ _ _
      · exact liveShape_startRefinement _ _ _
  | refinement epoch =>
      simp only [finishBroadcast, hs]
      exact liveShape_startRefinement _ _ _

lemma liveShape_congr (p : Params) (s next : State p) (h : LiveShape p s)
    (hp : next.phase = s.phase) (hw : next.work.isSome = s.work.isSome) (hr : next.ready = s.ready) :
    LiveShape p next := by
  simpa only [LiveShape, hp, hw, hr] using h

lemma liveShape_update (p : Params) (v : Fin p.n) (s : State p)
    (notification : Event (Point p) (CommReply p)) (h : LiveShape p s) :
    LiveShape p (update p v s notification) := by
  cases notification with
  | wake => exact h
  | computed value =>
      cases hw : s.work <;> cases hb : s.busy
      all_goals
        apply liveShape_congr p s _ h <;> simp [update, hw, hb]
  | received message =>
      simp only [update]
      split_ifs
      · exact liveShape_finishBroadcast p s _ h
      · exact liveShape_congr p s _ h rfl rfl rfl

lemma liveShape_query (p : Params) (v : Fin p.n) (s : State p) (h : LiveShape p s) :
    LiveShape p (query p v s).2 := by
  unfold query
  split
  · exact liveShape_congr p s _ h rfl rfl rfl
  · split
    · split_ifs
      · exact h
      · split
        · exact liveShape_congr p s _ h rfl rfl rfl
        · exact liveShape_finishLocal p s _ h
    · split_ifs
      · exact liveShape_finishBroadcast p s _ h
      · exact liveShape_congr p s _ h rfl rfl rfl
      · exact h

lemma liveShape_unfinished (p : Params) (s : State p) (h : LiveShape p s)
    (hn : s.phase ≠ .done) (hw : s.work = none) : s.ready = true := by
  cases hs : s.phase <;> simp_all [LiveShape]

lemma liveShape_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle : Time) (k : ℕ) (c : ExecutionState (system p g S) (algorithm p idle))
    (h : ∀ v, LiveShape p (c.workers v)) :
    ∀ v, LiveShape p ((run (system p g S) (algorithm p idle) k c).workers v) := by
  induction k generalizing c with
  | zero => exact h
  | succ k ih =>
      cases hs : step (system p g S) (algorithm p idle) c with
      | none => simpa only [run, hs] using h
      | some next =>
          have hn := DistributedJacobianStrongGrowthRouting.workerPredicate_step p g S idle (fun _ => LiveShape p)
            (liveShape_update p)
            (fun v s next action h hq => by simpa only [hq] using liveShape_query p v s h) c next h hs
          simpa only [run, hs] using ih next hn

lemma liveShape_initial_run (p : Params) (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (idle deadline : Time) (seed : (algorithm p idle).Seed × (system p g S).Seed) (k : ℕ) :
    ∀ v, LiveShape p ((run (system p g S) (algorithm p idle) k
      (initial (system p g S) (algorithm p idle) deadline seed)).workers v) :=
  liveShape_run p g S idle k _ (liveShape_initial p)

end LongTails.Proofs.DistributedJacobianStrongGrowthLiveShape
