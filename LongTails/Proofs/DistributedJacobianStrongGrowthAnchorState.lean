import LongTails.Proofs.DistributedJacobianStrongGrowthMedianAnchor

namespace LongTails.Proofs.DistributedJacobianStrongGrowthAnchorState

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradient
open LongTails.Algorithms.DistributedLocalExtragradientWarmStart
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthMedianState
open DistributedJacobianStrongGrowthMedianContent
open DistributedJacobianStrongGrowthMedianAnchor

noncomputable def medianCenter (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) : Point p :=
  projectBall p p.x0 p.R (p.x0 + reconstruct (warmSpacing p (localDepth p)) (medianGrid codes))

def AnchorState (p : Params) (center : Point p) (s : State p) : Prop :=
  match s.phase with
  | .refinement _ => s.anchor = center
  | .done => s.anchor = center
  | _ => True

lemma anchorState_initial (p : Params) (center : Point p) (v : Fin p.n)
    (hε : p.ε < p.R) (hrich : 64 * (p.L / p.μ) * growth p ≤ (p.n : ℝ)) :
    AnchorState p center (initialState p v) := by
  simp [AnchorState, initialState, not_le.mpr hε, hrich]

lemma anchorState_congr (p : Params) (center : Point p) (s t : State p)
    (hphase : t.phase = s.phase) (hanchor : t.anchor = s.anchor)
    (h : AnchorState p center s) : AnchorState p center t := by
  cases hs : s.phase <;> simp_all [AnchorState]

lemma anchorState_startRefinement (p : Params) (center : Point p) (s : State p)
    (epoch : ℕ) (ha : s.anchor = center) : AnchorState p center (startRefinement p epoch s) := by
  unfold startRefinement
  split_ifs <;> simpa only [AnchorState] using ha

lemma anchorState_finishLocal (p : Params) (center : Point p) (s : State p) (x : Point p)
    (hn : s.phase ≠ .baseline) (h : AnchorState p center s) :
    AnchorState p center (finishLocal p s x) := by
  cases hs : s.phase <;> simp_all [AnchorState, finishLocal, startMedian]

lemma anchorState_computed (p : Params) (center : Point p) (v : Fin p.n) (s : State p)
    (value : Point p) (h : AnchorState p center s) : AnchorState p center (update p v s (.computed value)) := by
  cases hw : s.work <;> cases hb : s.busy <;> simpa [update, hw, hb, AnchorState] using h

lemma anchorState_finishBroadcast (p : Params) (center : Point p) (s : State p)
    (values : Fin p.d → ℕ) (h : AnchorState p center s) (hb : PhaseBounds p s.phase)
    (hfinal : s.phase = .median 1 → (finishBroadcast p s values).anchor = center) :
    AnchorState p center (finishBroadcast p s values) := by
  cases hs : s.phase with
  | baseline => simpa [finishBroadcast, hs] using h
  | warming => simp [finishBroadcast, hs, AnchorState]
  | done => simpa [finishBroadcast, hs] using h
  | refinement epoch =>
      simp only [finishBroadcast, hs]
      apply anchorState_startRefinement
      simpa only [AnchorState, hs] using h
  | median remaining =>
      by_cases hr : 1 < remaining
      · simp [finishBroadcast, hs, hr, startMedian, AnchorState]
      · have he : remaining = 1 := by
          have hp : 1 ≤ remaining := (show 1 ≤ remaining ∧ remaining ≤ warmWidth p (localDepth p) from by
            simpa only [hs, PhaseBounds] using hb).1
          omega
        subst remaining
        have ha := hfinal hs
        simp only [finishBroadcast, hs, ite_eq_right hr] at ha ⊢
        have ha' := ha
        rw [DistributedJacobianStrongGrowthProtocol.startRefinement_anchor] at ha'
        exact anchorState_startRefinement p center _ 0 ha'

lemma anchorState_query (p : Params) (hp : valid p)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p)))
    (workers : Fin p.n → State p) (network : CommunicationState p)
    (hcontent : MedianContent p codes workers network) (i : Fin p.n)
    (h : AnchorState p (medianCenter p codes) (workers i))
    (hb : PhaseBounds p (workers i).phase) (hn : (workers i).phase ≠ .baseline) :
    AnchorState p (medianCenter p codes) (query p i (workers i)).2 := by
  classical
  cases hqueue : (workers i).queue with
  | cons packet rest => simpa [query, hqueue, AnchorState] using h
  | nil =>
      cases hw : (workers i).work with
      | some work =>
          cases hbusy : (workers i).busy with
          | true => simpa [query, hqueue, hw, hbusy] using h
          | false =>
              cases hq : LongTails.Algorithms.DistributedLocalExtragradientWorker.query work with
              | some x => simpa [query, hqueue, hw, hbusy, hq, AnchorState] using h
              | none =>
                  simpa [query, hqueue, hw, hbusy, hq] using anchorState_finishLocal p (medianCenter p codes)
                    (workers i) (LongTails.Algorithms.DistributedLocalExtragradientWorker.point work) hn h
      | none =>
          by_cases hr : (workers i).ready ∧ ¬ (workers i).sent ∧
              LongTails.Algorithms.DistributedLocalExtragradientTree.children p i ⊆ (workers i).collector.seen
          · by_cases hi : i = p.root
            · subst i
              have hf := anchorState_finishBroadcast p (medianCenter p codes) (workers p.root)
                (broadcastValues p (workers p.root).phase
                  (fun j => (workers p.root).own j + (workers p.root).collector.total j)) h hb (by
                    intro hs
                    exact median_root_anchor p hp codes workers network hcontent hs hr.2.2)
              simpa [query, hqueue, hw, hr, AnchorState, relay] using hf
            · simpa [query, hqueue, hw, hr, hi, AnchorState] using h
          · simpa only [query, hqueue, hw, ite_eq_right hr] using h

lemma anchorState_received (p : Params) (center : Point p) (v : Fin p.n) (s : State p)
    (message : CommReply p) (h : AnchorState p center s) (hb : PhaseBounds p s.phase)
    (hfinal : v ≠ p.root ∧ message.source = p.parent v → s.phase = .median 1 →
      (finishBroadcast p s
        (LongTails.Algorithms.LocalExtragradientQuantization.receiveNaturals p.d (downWidth p s.phase) message.bits)).anchor = center) :
    AnchorState p center (update p v s (.received message)) := by
  simp only [update]
  split_ifs with hp
  · exact anchorState_finishBroadcast p center s _ h hb (hfinal hp)
  · exact h

end LongTails.Proofs.DistributedJacobianStrongGrowthAnchorState
