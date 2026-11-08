import LongTails.Proofs.BirchResourceComplexity
import LongTails.Proofs.BirchCollectionVanilla
import LongTails.Proofs.BirchCollectionRennala
import LongTails.Proofs.BirchCollectionDelayed
import LongTails.Proofs.BirchCollectionLocal
import LongTails.Proofs.BirchCollectionCycle
import LongTails.Proofs.BirchCollectionAsyncLocal
import LongTails.Proofs.BirchCollectionAsyncBatch
import LongTails.Proofs.BirchCollectionLocalAsync
import LongTails.Proofs.BirchCollectionNested
import LongTails.Proofs.BirchCollectionMeta
import LongTails.Proofs.BirchCollectionDualPool
import LongTails.Proofs.BirchCollectionRetainedQuota
import LongTails.Theorems.BirchWindow
import Lean.Util.FoldConsts

open Lean Elab Command

private def projectConst (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "LongTails." || s.startsWith "OracleTemplate." ||
    s.startsWith "_private.LongTails."

private partial def findProofChain (env : Environment) (target : Name)
    (todo : List (Name × List Name)) (seen : NameSet) : Option (List Name) :=
  match todo with
  | [] => none
  | (n, path) :: rest =>
    if n == target then some ((n :: path).reverse)
    else if seen.contains n then findProofChain env target rest seen
    else
      let names := ((env.find? n).bind (fun info => info.value? true)).map
        (fun value => value.getUsedConstants.toList.filter projectConst)
      let work := (names.getD []).map (fun c => (c, n :: path))
      findProofChain env target (work ++ rest) (seen.insert n)

set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let target := `LongTails.Proofs.BirchTraceDescent.convergence
  for n in [`LongTails.Theorems.BirchRoutedTime.result,
    `LongTails.Theorems.BirchPowerTime.result,
    `LongTails.Proofs.BirchResourceTimedTrace.routed_timed,
    `LongTails.Proofs.BirchResourceTimedTrace.power_timed,
    `OracleTemplate.BirchSgd.assembly,
    `OracleTemplate.BirchSgd.main_theorem,
    `OracleTemplate.BirchSgd.result,
    `LongTails.Proofs.BirchCollectionEuclidean.paper_prefix_rate,
    `LongTails.Proofs.BirchCollectionEuclidean.recovered_success,
    `LongTails.Proofs.BirchRetainedEnergy.trajectory_energy,
    `LongTails.Theorems.BirchCollections.result,
    `LongTails.Proofs.BirchCollectionVanilla.vanilla_success,
    `LongTails.Proofs.BirchCollectionRennala.rennala_success,
    `LongTails.Proofs.BirchCollectionDelayed.delayed_success,
    `LongTails.Proofs.BirchCollectionLocal.local_success,
    `LongTails.Proofs.BirchCollectionCycle.cycle_success,
    `LongTails.Proofs.BirchCollectionAsyncLocal.async_local_success,
    `LongTails.Proofs.BirchCollectionAsyncBatch.async_batch_success,
    `LongTails.Proofs.BirchCollectionLocalAsync.local_async_success,
    `LongTails.Proofs.BirchCollectionNested.nested_success,
    `LongTails.Proofs.BirchCollectionMeta.meta_success,
    `LongTails.Proofs.BirchCollectionDualPool.dual_success,
    `LongTails.Proofs.BirchCollectionRetainedQuota.retained_quota_success,
    `LongTails.Proofs.BirchWindow.trajectory,
    `LongTails.Proofs.BirchWindow.expected_window,
    `LongTails.Theorems.BirchWindow.result] do
    match findProofChain env target [(n, [])] {} with
    | none => throwError "No proof dependency from {n} to {target}"
    | some path => logInfo (String.intercalate " -> " (path.map Name.toString))
