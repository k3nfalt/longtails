import LongTails.Algorithms.BirchCollectionCycle
import LongTails.Proofs.BirchCollectionCycleTrace
import LongTails.Proofs.BirchCollectionBounds

namespace LongTails.Proofs.BirchCollectionCycle

open LongTails.Algorithms.BirchCollectionCycle

open OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections (Params spec horizon batchSize)
open LongTails.Algorithms.BirchCollectionWorkerPools
open LongTails.Algorithms.BirchCollections (algorithm program)
open LongTails.Proofs.BirchCollectionCycleTrace
open LongTails.Proofs.BirchCollectionCycleTimer (group_count)
open LongTails.Proofs.BirchCollectionPoolCertificate (pool_certificate)
open LongTails.Algorithms.BirchCollectionProfiles (controls divisor)
open LongTails.Algorithms.BirchCollectionProfiles (resetOrdering)
open LongTails.Proofs.BirchCollectionSuccess (execute_success)
open LongTails.Proofs.BirchCollectionBounds (scaled_budget)
open LongTails.Theorems.BirchCollections (budget)

lemma upper_pos (m size : ℕ) (hm : 0 < m) : 0 < upper m size := by
  unfold upper
  apply Nat.mul_pos hm
  rw [group_count m size hm]
  exact Nat.zero_lt_succ _

lemma cycle_valid (p : Params) (m size : ℕ) (hm : 0 < m) (hsize : 0 < size)
    (hdef : ∀ x, p.N x = 0 → x = 0) (hcont : Continuous p.N)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (hregular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ) :
    spec.valid (cycleSgd p m size) := by
  let q := tuned p m size
  let U := upper m size
  let W := window m size
  let B := batchSize q
  let K := horizon q
  let move : ℝ := 1 / divisor U W
  let s := cycle m size B K move
  have hK : 0 < K := by unfold K horizon; omega
  have hB : 0 < B := by unfold B batchSize; omega
  have hU : 0 < U := upper_pos m size hm
  have hc : (1 : ℝ) ≤ divisor U W := by
    exact_mod_cast (show 1 ≤ divisor U W by unfold divisor; omega)
  have hc' : (0 : ℝ) < divisor U W := by linarith
  obtain ⟨hs, hb⟩ := cycle_data m size B K move hm hsize hB (by positivity) ((div_le_one hc').2 hc)
  exact ⟨hdef, hcont, hL, hσ, hε, hΔ, Nat.zero_lt_succ _, hregular, hs.legal,
    pool_certificate s hs hK Nat.one_pos hU hb.cuts⟩

lemma cycle_budget (p : Params) (m size : ℕ) (hm : 0 < m) :
    let q := cycleSgd p m size
    budget q 0 = q.controls.waste + batchSize q * (horizon q * upper m size) := by
  let q := cycleSgd p m size
  exact scaled_budget q 1 (upper m size) (window m size) q.controls.waste (upper_pos m size hm) rfl

lemma cycle_success (p : Params) (m size : ℕ) (hp : spec.valid (cycleSgd p m size))
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : spec.admissible (cycleSgd p m size) I O) :
    let q := cycleSgd p m size
    let C := (program q).oracleCalls
    spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm q) (fun _ => C) z.1 z.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ :=
  execute_success (cycleSgd p m size) hp _ le_rfl I O hI

end LongTails.Proofs.BirchCollectionCycle
