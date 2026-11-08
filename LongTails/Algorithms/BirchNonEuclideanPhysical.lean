import LongTails.Algorithms.BirchNonEuclideanProfiles

namespace LongTails.Algorithms.BirchNonEuclideanPhysical

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies

structure Packet (m : ℕ) where
  worker : Fin m
  source : ℕ
  serial : ℕ

structure PacketSchedule (m : ℕ) where
  accepted : List (Packet m) := []
  rejected : List (Packet m) := []
  completed : List (Packet m) := []
  source : Fin m → ℕ := fun _ => 0
  serial : Fin m → ℕ := fun _ => 0
  last : Option (Fin m) := none

def scheduleStep {m : ℕ} (K R : ℕ) (w : Fin m) (s : PacketSchedule m) : PacketSchedule m :=
  if s.accepted.length < K then
    let job : Packet m := ⟨w, s.source w, s.serial w⟩
    if s.accepted.length - s.source w ≤ R then
      { accepted := s.accepted ++ [job]
        rejected := s.rejected
        completed := s.completed ++ [job]
        source := Function.update s.source w (s.accepted.length + 1)
        serial := Function.update s.serial w (s.serial w + 1)
        last := some w }
    else
      { accepted := s.accepted
        rejected := s.rejected ++ [job]
        completed := s.completed ++ [job]
        source := Function.update s.source w s.accepted.length
        serial := Function.update s.serial w (s.serial w + 1)
        last := some w }
  else s

def scheduleRun {m : ℕ} (K R : ℕ) (word : ℕ → Fin m) : ℕ → PacketSchedule m
  | 0 => {}
  | n + 1 => scheduleStep K R (word n) (scheduleRun K R word n)

def completionLimit (m K R : ℕ) : ℕ := K + (m - 1) * (K - 1) / (R + 1)

def packetCutoff (H B : ℕ) : ℕ := B / (8 * H)

def finalSchedule {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) : PacketSchedule m :=
  scheduleRun K (packetCutoff H B) word (completionLimit m K (packetCutoff H B))

def pending {m : ℕ} (s : PacketSchedule m) : List (Packet m) :=
  ((List.finRange m).filter (fun i => some i != s.last)).map
    (fun i => ⟨i, s.source i, s.serial i⟩)

def ignored {m : ℕ} (s : PacketSchedule m) : List (Packet m) := s.rejected ++ pending s

def packetSource {m : ℕ} (jobs : List (Packet m)) (k : ℕ) : ℕ :=
  ((jobs[k]?).map Packet.source).getD k

def packetWorker {m : ℕ} (jobs : List (Packet m)) (k : ℕ) : ℕ :=
  ((jobs[k]?).map (fun p => p.worker.val + 1)).getD 0

noncomputable def pairedCode (H : ℕ) (dispatch worker : ℕ → ℕ) (K B : ℕ) :
    StateM CodeState ((ℕ → ℕ) × (ℕ → ℕ)) := do
  let mut points := fun _ : ℕ => 0
  let initial ← localBatch 0 0 B
  let mut momenta := fun _ : ℕ => initial
  for k in List.range K do
    let src := dispatch k
    let w := worker k
    let _ ← emit (.sendPoint 0 w (points src))
    let _ ← emit (.sendVector 0 w (momenta src))
    let packet ← localMomentum w (points src) (momenta src) H k
    let dx ← emit (.difference w packet.1 (points src))
    let dm ← emit (.mix w [(.constant 1, packet.2), (.constant (-1), momenta src)])
    let _ ← emit (.sendVector w 0 dx)
    let _ ← emit (.sendVector w 0 dm)
    let x ← emit (.move 0 (points k) dx (.constant 1))
    let v ← emit (.mix 0 [(.constant 1, momenta k), (.constant 1, dm)])
    points := Function.update points (k + 1) x
    momenta := Function.update momenta (k + 1) v
  return (points, momenta)

noncomputable def unusedPacket (w x v H round : ℕ) : StateM CodeState Unit := do
  let _ ← emit (.sendPoint 0 w x)
  let _ ← emit (.sendVector 0 w v)
  let packet ← localMomentum w x v H round
  let dx ← emit (.difference w packet.1 x)
  let dm ← emit (.mix w [(.constant 1, packet.2), (.constant (-1), v)])
  let _ ← emit (.sendVector w 0 dx)
  let _ ← emit (.sendVector w 0 dm)
  return ()

noncomputable def physicalLocalCode {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) :
    StateM CodeState (ℕ → ℕ) := do
  let schedule := finalSchedule H K B word
  let state ← pairedCode H (packetSource schedule.accepted) (packetWorker schedule.accepted) K B
  for job in ignored schedule do
    unusedPacket (job.worker.val + 1) (state.1 job.source) (state.2 job.source) H 0
  return state.1

noncomputable def physicalLocalFamily {m : ℕ} (H : ℕ) (word : ℕ → ℕ → ℕ → Fin m) : ProtocolFamily where
  template K B := makeTemplate K (physicalLocalCode H K B (word K B))

noncomputable def physicalLocalProfile (H : ℕ) : StructuralProfile where
  minimumBatch := 8 * H
  driftConstant := 2
  driftLinear := 3 / (H : ℝ)
  noiseLinear := 1
  noiseQuadratic := 0

def physicalLocalCalls {m : ℕ} (H : ℕ) (word : ℕ → ℕ → ℕ → Fin m) (K B : ℕ) : ℕ :=
  B + H * (K + (ignored (finalSchedule H K B (word K B))).length)

end LongTails.Algorithms.BirchNonEuclideanPhysical
