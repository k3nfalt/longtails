import LongTails.Algorithms.BirchCausalPackets
import LongTails.Algorithms.BirchNonEuclideanPhysical

namespace LongTails.Algorithms.BirchCausalPhysical

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanPhysical
open LongTails.Algorithms.BirchCausalPackets

def packetExpr {m : ℕ} (recipe : Packet m → PacketExpr) (fallback : Packet m)
    (jobs : List (Packet m)) (k : ℕ) : PacketExpr := recipe ((jobs[k]?).getD fallback)

noncomputable def drainGraph {m : ℕ} (H : ℕ) (recipe : Packet m → PacketExpr)
    (state : GraphState) (main : ℕ → ℕ) (job : Packet m) : StateM CodeState Unit := do
  let root := state.states (main job.source)
  let block := (recipe job).compile 0 1
  let _ ← graphCode H 0 block.nodes block.output root.worker root.point root.momentum
  return ()

noncomputable def drainGraphs {m : ℕ} (H : ℕ) (recipe : Packet m → PacketExpr)
    (state : GraphState) (main : ℕ → ℕ) : List (Packet m) → StateM CodeState Unit
  | [] => pure ()
  | job :: rest => do
      drainGraph H recipe state main job
      drainGraphs H recipe state main rest

def physicalPlan {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m) (recipe : Packet m → PacketExpr) : GraphPlan :=
  let jobs := (finalSchedule H K B word).accepted
  planRun (packetExpr recipe ⟨word 0, 0, 0⟩ jobs) (packetSource jobs) K

noncomputable def physicalGraphCode {m : ℕ} (H K B : ℕ) (word : ℕ → Fin m)
    (recipe : Packet m → PacketExpr) : StateM CodeState (ℕ → ℕ) := do
  let schedule := finalSchedule H K B word
  let plan := physicalPlan H K B word recipe
  let initial ← localBatch 0 0 B
  let state ← graphRun H 0 plan.nodes ⟨fun _ => ⟨0, 0, initial⟩, 1, 0⟩
  sendMainPoints K state plan.main
  drainGraphs H recipe state plan.main (ignored schedule)
  return fun k => (state.states (plan.main k)).point

noncomputable def physicalGraphFamily {m : ℕ} (H : ℕ)
    (word : ℕ → ℕ → ℕ → Fin m) (recipe : ℕ → ℕ → Packet m → PacketExpr) : ProtocolFamily where
  template K B := makeTemplate K (physicalGraphCode H K B (word K B) (recipe K B))

end LongTails.Algorithms.BirchCausalPhysical
