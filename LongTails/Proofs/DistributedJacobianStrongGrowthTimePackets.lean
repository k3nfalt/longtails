import LongTails.Proofs.DistributedJacobianStrongGrowthTimeSchedule

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimePackets

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientMedianSearch
open LongTails.Algorithms.LocalExtragradientQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPhases
open DistributedJacobianStrongGrowthTimeSchedule

lemma up_packet_time (p : Params) (phase : Phase) (values : Fin p.d → ℕ)
    (hb : PhaseBounds p phase) (ha : Active phase) :
    p.l + p.β * (naturalMessage (upWidth p phase) values ++ List.replicate clockBits false).length =
      roundComm p (epochIndex p phase) := by
  rw [LocalExtragradientQuantization.naturalMessage_packet_length]
  cases phase with
  | baseline => cases ha
  | warming => cases ha
  | done => cases ha
  | median remaining =>
      have he : warmWidth p (localDepth p) - remaining < warmWidth p (localDepth p) := by
        simp only [PhaseBounds] at hb
        omega
      simp only [upWidth, epochIndex, roundComm, medianTime]
      exact (ite_eq_left he).symm
  | refinement epoch =>
      have he : ¬ warmWidth p (localDepth p) + epoch < warmWidth p (localDepth p) := by omega
      simp only [upWidth, epochIndex, roundComm, refinementTime]
      exact (ite_eq_right he).symm

lemma down_packet_time (p : Params) (phase : Phase) (values : Fin p.d → ℕ)
    (hb : PhaseBounds p phase) (ha : Active phase) :
    p.l + p.β * (naturalMessage (downWidth p phase) values ++ List.replicate clockBits false).length ≤
      roundComm p (epochIndex p phase) := by
  rw [LocalExtragradientQuantization.naturalMessage_packet_length]
  cases phase with
  | baseline => cases ha
  | warming => cases ha
  | done => cases ha
  | median remaining =>
      have he : warmWidth p (localDepth p) - remaining < warmWidth p (localDepth p) := by
        simp only [PhaseBounds] at hb
        omega
      have hcomm : roundComm p (epochIndex p (.median remaining)) = medianTime p := ite_eq_left he
      rw [hcomm]
      simp only [downWidth, medianTime]
      have hw : 1 ≤ countWidth p.n := by unfold countWidth; omega
      have hl : p.d * 1 + 64 ≤ p.d * countWidth p.n + 64 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left p.d hw) 64
      have hc : ((p.d * 1 + 64 : ℕ) : Time) ≤ (p.d * countWidth p.n + 64 : ℕ) := by exact_mod_cast hl
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hc zero_le)
  | refinement epoch =>
      have he : ¬ warmWidth p (localDepth p) + epoch < warmWidth p (localDepth p) := by omega
      have hcomm : roundComm p (epochIndex p (.refinement epoch)) = refinementTime p := ite_eq_right he
      rw [hcomm]
      exact le_rfl

lemma relay_packet_time (p : Params) (v : Fin p.n) (s : State p) (values : Fin p.d → ℕ)
    (packet : Fin p.n × List Bool) (hpacket : packet ∈ (relay p v s values).queue)
    (hb : PhaseBounds p s.phase) (ha : Active s.phase) :
    p.l + p.β * (packet.2 ++ List.replicate clockBits false).length ≤
      roundComm p (epochIndex p s.phase) := by
  rw [(DistributedJacobianStrongGrowthProtocol.relay_packet p v s values packet hpacket).2]
  exact down_packet_time p s.phase values hb ha

end LongTails.Proofs.DistributedJacobianStrongGrowthTimePackets
