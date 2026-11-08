import LongTails.Proofs.BirchCollectionRetainedQuotaLedger
import LongTails.Proofs.BirchCollectionBounds

namespace LongTails.Proofs.BirchCollectionRetainedQuota

open Finset OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionNested (Layout)
open LongTails.Algorithms.BirchCollectionRetainedQuota
open LongTails.Algorithms.BirchCollections (program algorithm)
open LongTails.Algorithms.BirchCollectionRetune (retune)
open LongTails.Proofs.BirchCollectionRetainedQuotaHistory
open LongTails.Proofs.BirchCollectionRetainedQuotaStructure
open LongTails.Proofs.BirchCollectionRetainedQuotaLedger
open LongTails.Proofs.BirchCollectionExecution (program_calls run_raw)
open LongTails.Proofs.BirchCollectionBounds (budget_tuned)
open LongTails.Proofs.BirchCollectionSuccess (execute_success)
open LongTails.Theorems.BirchCollections (budget)

lemma retained_quota_valid {m : ℕ} (p : Params) (layout : Layout m) (schedule : ℕ → Phase m)
    (hdef : ∀ x, p.N x = 0 → x = 0) (hcont : Continuous p.N)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (hregular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ)
    (hc : Complete schedule (batchSize (retainedQuota p layout schedule))
      (horizon (retainedQuota p layout schedule))) :
    spec.valid (retainedQuota p layout schedule) := by
  let q := retainedQuota p layout schedule
  let B := batchSize q
  let K := horizon q
  let s := rounds layout B schedule K
  have hB : 0 < B := by unfold B batchSize; omega
  have hK : 0 < K := by unfold K horizon; omega
  have hs : History s schedule B K := rounds_history layout schedule hB K hc
  refine ⟨hdef, hcont, hL, hσ, hε, hΔ, Nat.zero_lt_succ _, hregular, mapped_legal hs, ?_⟩
  change Structural (run (s.events.map (retune gain))) (ordering schedule K)
    (controls (waste layout B schedule K)) K B
  rw [mapped_run hs]
  exact structural hs hc hB hK (waste_exact layout schedule hB hK hc).le

lemma retained_quota_calls {m : ℕ} (p : Params) (layout : Layout m) (schedule : ℕ → Phase m)
    (hc : Complete schedule (batchSize (retainedQuota p layout schedule))
      (horizon (retainedQuota p layout schedule))) :
    let q := retainedQuota p layout schedule
    (program q).oracleCalls = (∑ k ∈ range (horizon q), volume schedule (batchSize q) k) + q.controls.waste := by
  let q := retainedQuota p layout schedule
  let B := batchSize q
  let K := horizon q
  let s := rounds layout B schedule K
  have hB : 0 < B := by unfold B batchSize; omega
  have hs : History s schedule B K := rounds_history layout schedule hB K hc
  change (program q).oracleCalls = _
  rw [program_calls, ← run_raw]
  change (run (s.events.map (retune gain))).nextRaw =
    (∑ k ∈ range K, volume schedule B k) + waste layout B schedule K
  rw [mapped_run hs]
  exact rounds_raw layout schedule K hB hc

lemma retained_quota_budget {m : ℕ} (p : Params) (layout : Layout m) (schedule : ℕ → Phase m) :
    let q := retainedQuota p layout schedule
    budget q 0 = q.controls.waste + batchSize q * horizon q := by
  let q := retainedQuota p layout schedule
  change budget q 0 = _
  rw [budget_tuned]
  change 0 + q.controls.waste + ⌈(batchSize q : ℝ) * 8 * ((horizon q : ℝ) * (1 / 8))⌉₊ = _
  have h : (batchSize q : ℝ) * 8 * ((horizon q : ℝ) * (1 / 8)) =
      ((batchSize q * horizon q : ℕ) : ℝ) := by push_cast; ring
  rw [zero_add, h, Nat.ceil_natCast]

lemma retained_quota_calls_le {m : ℕ} (p : Params) (layout : Layout m) (schedule : ℕ → Phase m)
    (hc : Complete schedule (batchSize (retainedQuota p layout schedule))
      (horizon (retainedQuota p layout schedule))) :
    let q := retainedQuota p layout schedule
    (program q).oracleCalls ≤ budget q 0 := by
  dsimp only
  rw [retained_quota_calls p layout schedule hc, retained_quota_budget]
  exact (Nat.add_le_add_right (volume_upper hc) _).trans_eq (Nat.add_comm _ _)

lemma retained_quota_success {m : ℕ} (p : Params) (layout : Layout m) (schedule : ℕ → Phase m)
    (hp : spec.valid (retainedQuota p layout schedule))
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : spec.admissible (retainedQuota p layout schedule) I O) :
    let q := retainedQuota p layout schedule
    let C := (program q).oracleCalls
    spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm q) (fun _ => C) z.1 z.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ :=
  execute_success (retainedQuota p layout schedule) hp _ le_rfl I O hI

end LongTails.Proofs.BirchCollectionRetainedQuota
