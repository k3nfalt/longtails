import LongTails.Proofs.DistributedJacobianStrongGrowthPhaseProgress
import LongTails.Proofs.DistributedJacobianStrongGrowthQueryAccounting

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTerminationRank

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthQueryAccounting

lemma termination_of_lex {n : ℕ} {ComputeQuery ComputeReply CommReply Output : Type}
    (O : Oracle ComputeQuery ComputeReply CommReply n)
    (A : Algorithm ComputeQuery ComputeReply CommReply Output n)
    (Inv : ExecutionState O A → Prop) (stage rank : ExecutionState O A → ℕ)
    (hnext : ∀ c next, Inv c → step O A c = some next → Inv next ∧
      (stage next < stage c ∨ stage next = stage c ∧ rank next < rank c))
    (c : ExecutionState O A) (hc : Inv c) :
    ∃ k, step O A (run O A k c) = none := by
  have hall : ∀ a b, ∀ c : ExecutionState O A, stage c = a → rank c = b → Inv c →
      ∃ k, step O A (run O A k c) = none := by
    intro a
    induction a using Nat.strong_induction_on with
    | h a iha =>
      intro b
      induction b using Nat.strong_induction_on with
      | h b ihb =>
        intro c ha hb hc
        cases hs : step O A c with
        | none => exact ⟨0, hs⟩
        | some next =>
          obtain ⟨hn, hd⟩ := hnext c next hc hs
          have hex : ∃ k, step O A (run O A k next) = none := by
            rcases hd with hd | ⟨he, hd⟩
            · exact iha (stage next) (by omega) (rank next) next rfl rfl hn
            · exact ihb (rank next) (by omega) next (he.trans ha) rfl hn
          obtain ⟨k, hk⟩ := hex
          exact ⟨k + 1, by simpa [run, hs] using hk⟩
  exact hall (stage c) (rank c) c rfl rfl hc

noncomputable def stagesRemaining (p : Params) : Phase → ℕ
  | .baseline => 1
  | .warming => warmWidth p (localDepth p) + refinementCount p (localDepth p) + 1
  | .median remaining => remaining + refinementCount p (localDepth p)
  | .refinement epoch => refinementCount p (localDepth p) - epoch
  | .done => 0

lemma stagesRemaining_startRefinement (p : Params) (epoch : ℕ) (s : State p) :
    stagesRemaining p (startRefinement p epoch s).phase = refinementCount p (localDepth p) - epoch := by
  unfold startRefinement
  split_ifs with h <;> simp only [stagesRemaining]
  omega

lemma stagesRemaining_finishBroadcast (p : Params) (s : State p) (values : Fin p.d → ℕ)
    (hb : PhaseBounds p s.phase) (ha : DistributedJacobianStrongGrowthPhases.Active s.phase) :
    stagesRemaining p (finishBroadcast p s values).phase + 1 = stagesRemaining p s.phase := by
  cases hs : s.phase <;> simp only [hs, DistributedJacobianStrongGrowthPhases.Active] at ha
  · rename_i remaining
    have hr : 1 ≤ remaining := (show 1 ≤ remaining ∧ remaining ≤ warmWidth p (localDepth p) from
      by simpa only [hs, PhaseBounds] using hb).1
    simp only [finishBroadcast, hs]
    split_ifs with h
    · simp only [startMedian, stagesRemaining]
      omega
    · rw [stagesRemaining_startRefinement]
      simp only [stagesRemaining]
      omega
  · rename_i epoch
    have he : epoch < refinementCount p (localDepth p) := by simpa only [hs, PhaseBounds] using hb
    simp only [finishBroadcast, hs]
    rw [stagesRemaining_startRefinement]
    simp only [stagesRemaining]
    omega

lemma stagesRemaining_finishLocal (p : Params) (s : State p) (x : Point p) :
    stagesRemaining p (finishLocal p s x).phase ≤ stagesRemaining p s.phase := by
  cases hs : s.phase <;> simp [finishLocal, hs, startMedian, stagesRemaining]

lemma stagesRemaining_finishLocal_warming (p : Params) (s : State p) (x : Point p)
    (hs : s.phase = .warming) :
    stagesRemaining p (finishLocal p s x).phase + 1 = stagesRemaining p s.phase := by
  simp [finishLocal, hs, startMedian, stagesRemaining]

lemma stagesRemaining_update (p : Params) (v : Fin p.n) (s : State p)
    (notification : Event (Point p) (CommReply p)) (hb : PhaseBounds p s.phase)
    (ha : v ≠ p.root → ∀ bits,
      notification = .received ⟨p.parent v, bits⟩ → DistributedJacobianStrongGrowthPhases.Active s.phase) :
    stagesRemaining p (update p v s notification).phase ≤ stagesRemaining p s.phase := by
  cases notification with
  | wake => exact le_rfl
  | computed value =>
      simp only [update]
      split
      · split_ifs <;> exact le_rfl
      · exact le_rfl
  | received message =>
      simp only [update]
      split_ifs with h
      · have hactive := ha h.1 message.bits (by cases message; simp_all)
        have he := stagesRemaining_finishBroadcast p s
          (LongTails.Algorithms.LocalExtragradientQuantization.receiveNaturals p.d
            (downWidth p s.phase) message.bits) hb hactive
        change stagesRemaining p (finishBroadcast p s _).phase ≤ _
        omega
      · exact le_rfl

end LongTails.Proofs.DistributedJacobianStrongGrowthTerminationRank
