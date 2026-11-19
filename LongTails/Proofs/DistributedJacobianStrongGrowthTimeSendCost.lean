import LongTails.Proofs.DistributedJacobianStrongGrowthTimeQueue

namespace LongTails.Proofs.DistributedJacobianStrongGrowthTimeSendCost

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.LocalExtragradientQuantization
open DistributedJacobianStrongGrowthPhaseProgress
open DistributedJacobianStrongGrowthPhases
open DistributedJacobianStrongGrowthTimeSchedule
open DistributedJacobianStrongGrowthTimePackets
open DistributedJacobianStrongGrowthTimeState
open DistributedJacobianStrongGrowthHandshake
open DistributedJacobianStrongGrowthEpochOrdering

lemma queued_epoch (p : Params) (workers : Fin p.n → State p) (network : CommunicationState p)
    (hh : Handshake p workers network) (ho : EpochOrdering p workers network)
    (v : Fin p.n) (hv : v ≠ p.root) (bits : List Bool) (rest : List (Fin p.n × List Bool))
    (hq : (workers (p.parent v)).queue = (v, bits) :: rest) :
    epochIndex p (workers (p.parent v)).phase = epochIndex p (workers v).phase + 1 := by
  have hpos : 0 < (workers (p.parent v)).queue.countP (fun packet => decide (packet.1 = v)) := by simp [hq]
  have hf := down_free_of_queued p workers network hh v hv hpos
  have hb := hh v hv
  unfold edgeLoad at hb
  have hcount : (workers (p.parent v)).queue.countP (fun packet => decide (packet.1 = v)) = 1 := by
    cases hsent : (workers v).sent <;> simp only [hsent, Bool.toNat_false, Bool.toNat_true] at hb <;> omega
  simpa only [downLoad, hcount, hf, Option.isSome_none, Bool.toNat_false, Nat.add_zero] using ho v hv

lemma up_send_finish (p : Params) (hp : valid p) (v : Fin p.n) (hv : v ≠ p.root)
    (s : State p) (time : Time) (values : Fin p.d → ℕ) (hb : PhaseBounds p s.phase) (ha : Active s.phase)
    (hq : s.queue = []) (hw : s.work = none) (ht : WakeFits p v s time) :
    time + p.l + p.β * (naturalMessage (upWidth p s.phase) values ++ List.replicate clockBits false).length ≤
      upDeadline p (epochIndex p s.phase) (p.parent v) := by
  have htime : time ≤ upDeadline p (epochIndex p s.phase) v := by
    have hh : Active s.phase → time ≤ upDeadline p (epochIndex p s.phase) v := by
      simpa only [WakeFits, hq, ite_true, hw] using ht
    exact hh ha
  calc
    _ = time + (p.l + p.β * (naturalMessage (upWidth p s.phase) values ++ List.replicate clockBits false).length) := by ring
    _ = time + roundComm p (epochIndex p s.phase) := by rw [up_packet_time p s.phase values hb ha]
    _ ≤ upDeadline p (epochIndex p s.phase) v + roundComm p (epochIndex p s.phase) := add_le_add htime le_rfl
    _ = _ := upDeadline_parent p hp _ v hv

lemma queued_send_finish (p : Params) (hp : valid p) (workers : Fin p.n → State p)
    (network : CommunicationState p) (hh : Handshake p workers network) (ho : EpochOrdering p workers network)
    (v : Fin p.n) (hv : v ≠ p.root) (bits : List Bool) (rest : List (Fin p.n × List Bool)) (time : Time)
    (hq : (workers (p.parent v)).queue = (v, bits) :: rest)
    (ht : WakeFits p (p.parent v) (workers (p.parent v)) time)
    (hcost : p.l + p.β * (bits ++ List.replicate clockBits false).length ≤
      roundComm p (epochIndex p (workers (p.parent v)).phase - 1)) :
    time + p.l + p.β * (bits ++ List.replicate clockBits false).length ≤
      downDeadline p (epochIndex p (workers v).phase) v := by
  have he := queued_epoch p workers network hh ho v hv bits rest hq
  have htime : time ≤ downDeadline p (epochIndex p (workers v).phase) (p.parent v) := by
    simpa only [WakeFits, hq, List.cons_ne_nil, ite_false, he, Nat.add_sub_cancel] using ht
  have hcost' : p.l + p.β * (bits ++ List.replicate clockBits false).length ≤
      roundComm p (epochIndex p (workers v).phase) := by simpa only [he, Nat.add_sub_cancel] using hcost
  calc
    _ = time + (p.l + p.β * (bits ++ List.replicate clockBits false).length) := by ring
    _ ≤ downDeadline p (epochIndex p (workers v).phase) (p.parent v) + roundComm p (epochIndex p (workers v).phase) :=
      add_le_add htime hcost'
    _ = _ := downDeadline_child p hp _ v hv

end LongTails.Proofs.DistributedJacobianStrongGrowthTimeSendCost
