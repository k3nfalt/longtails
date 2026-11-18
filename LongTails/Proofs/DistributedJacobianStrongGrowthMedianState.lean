import LongTails.Proofs.DistributedJacobianStrongGrowthMedianReference

namespace LongTails.Proofs.DistributedJacobianStrongGrowthMedianState

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthPayload
open DistributedJacobianStrongGrowthMedianReference

noncomputable def MedianState (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (i : Fin p.n) (s : State p) : Prop :=
  ∀ remaining, s.phase = .median remaining →
    s.lower = lowerAfter codes (warmWidth p (localDepth p) - remaining) ∧
    s.own = medianValues p codes (warmWidth p (localDepth p) - remaining) i

lemma medianState_initial (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (i : Fin p.n) :
    MedianState p codes i (initialState p i) := by
  intro remaining hs
  unfold initialState at hs
  split_ifs at hs

lemma medianState_startRefinement (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (i : Fin p.n)
    (epoch : ℕ) (s : State p) : MedianState p codes i (startRefinement p epoch s) := by
  intro remaining hs
  unfold startRefinement at hs
  split_ifs at hs

lemma medianState_startMedian (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (i : Fin p.n)
    (remaining : ℕ) (s : State p) (hpos : 0 < remaining)
    (hle : remaining ≤ warmWidth p (localDepth p))
    (hlower : s.lower = lowerAfter codes (warmWidth p (localDepth p) - remaining))
    (hcodes : s.warmCodes = fun j => (codes i j).val) :
    MedianState p codes i (startMedian p remaining s) := by
  intro r hs
  have he : remaining = r := Phase.median.inj hs
  subst r
  constructor
  · exact hlower
  · have hr : warmWidth p (localDepth p) -
        (warmWidth p (localDepth p) - remaining + 1) = remaining - 1 := by omega
    funext j
    simp only [startMedian, medianValues, hlower, hcodes, hr]

lemma medianState_broadcast (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (i : Fin p.n)
    (remaining : ℕ) (s : State p) (hs : s.phase = .median remaining)
    (hle : remaining ≤ warmWidth p (localDepth p))
    (hstate : MedianState p codes i s)
    (hcodes : s.warmCodes = fun j => (codes i j).val) :
    MedianState p codes i (finishBroadcast p s (broadcastValues p s.phase
      (fun j => LongTails.Algorithms.DistributedLocalExtragradientMedianSearch.countBelow
        codes j (s.lower j + 2 ^ (remaining - 1))))) := by
  have hl := (hstate remaining hs).1
  by_cases hr : 1 < remaining
  · intro r hphase
    have he : remaining - 1 = r := by
      simpa only [finishBroadcast, hs, ite_eq_left hr, startMedian, Phase.median.injEq] using hphase
    subst r
    constructor
    · exact median_broadcast_lower p s remaining codes hs hr hle hl
    · have h := median_broadcast_own p s remaining i codes hs hr hle hl hcodes
      have he : warmWidth p (localDepth p) -
          (warmWidth p (localDepth p) - (remaining - 1) + 1) = remaining - 1 - 1 := by omega
      funext j
      simpa only [medianValues, he] using congrFun h j
  · simp only [finishBroadcast, hs, ite_eq_right hr]
    exact medianState_startRefinement p codes i 0 _

lemma medianState_congr (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (i : Fin p.n)
    (s t : State p) (hphase : t.phase = s.phase) (hlower : t.lower = s.lower)
    (hown : t.own = s.own) (h : MedianState p codes i s) : MedianState p codes i t := by
  intro remaining hs
  simpa only [hlower, hown] using h remaining (hphase.symm.trans hs)

lemma medianState_computed (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (i : Fin p.n)
    (s : State p) (value : Point p) (h : MedianState p codes i s) :
    MedianState p codes i (update p i s (.computed value)) := by
  cases hw : s.work <;> cases hb : s.busy <;> simpa [update, hw, hb, MedianState] using h

lemma medianState_child (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (i : Fin p.n)
    (s : State p) (message : CommReply p) (h : MedianState p codes i s)
    (hn : ¬ (i ≠ p.root ∧ message.source = p.parent i)) :
    MedianState p codes i (update p i s (.received message)) := by
  simpa [update, hn, MedianState] using h

lemma medianState_finishLocal_warming (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (i : Fin p.n)
    (s : State p) (x : Point p) (hs : s.phase = .warming)
    (hcodes : (finishLocal p s x).warmCodes = fun j => (codes i j).val) :
    MedianState p codes i (finishLocal p s x) := by
  intro remaining hr
  have he : warmWidth p (localDepth p) = remaining := by
    simpa only [finishLocal, hs, startMedian, Phase.median.injEq] using hr
  subst remaining
  constructor
  · simp [finishLocal, hs, startMedian, lowerAfter]
  · rw [finishLocal_warming_own p s x hs, hcodes]
    funext j
    simp only [medianValues, Nat.sub_self, lowerAfter, Nat.zero_add]

lemma medianState_received_packet (p : Params)
    (codes : Fin p.n → Grid p.d (warmWidth p (localDepth p))) (i : Fin p.n)
    (remaining : ℕ) (s : State p) (hs : s.phase = .median remaining)
    (hle : remaining ≤ warmWidth p (localDepth p))
    (hstate : MedianState p codes i s)
    (hcodes : s.warmCodes = fun j => (codes i j).val)
    (hi : i ≠ p.root) (padding : List Bool) :
    MedianState p codes i (update p i s (.received ⟨p.parent i,
      LongTails.Algorithms.LocalExtragradientQuantization.naturalMessage 1
        (broadcastValues p s.phase (fun j =>
          LongTails.Algorithms.DistributedLocalExtragradientMedianSearch.countBelow codes j
            (s.lower j + 2 ^ (remaining - 1)))) ++ padding⟩)) := by
  let values := broadcastValues p s.phase (fun j =>
    LongTails.Algorithms.DistributedLocalExtragradientMedianSearch.countBelow codes j
      (s.lower j + 2 ^ (remaining - 1)))
  have hfit : ∀ j, values j < 2 ^ 1 := by
    intro j
    simp only [values, hs, broadcastValues]
    split_ifs <;> decide
  have hd := LongTails.Proofs.LocalExtragradientQuantization.receiveNaturals_message
    1 values hfit padding
  change MedianState p codes i (update p i s (.received ⟨p.parent i,
    LongTails.Algorithms.LocalExtragradientQuantization.naturalMessage 1 values ++ padding⟩))
  simp only [update]
  rw [ite_eq_left (show i ≠ p.root ∧ True from ⟨hi, trivial⟩)]
  change MedianState p codes i (finishBroadcast p s
    (LongTails.Algorithms.LocalExtragradientQuantization.receiveNaturals p.d
      (downWidth p s.phase)
      (LongTails.Algorithms.LocalExtragradientQuantization.naturalMessage 1 values ++ padding)))
  rw [show downWidth p s.phase = 1 by simp [downWidth, hs], hd]
  exact medianState_broadcast p codes i remaining s hs hle hstate hcodes

end LongTails.Proofs.DistributedJacobianStrongGrowthMedianState
