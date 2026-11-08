import LongTails.Proofs.BirchCollectionDualPoolRounds
import LongTails.Proofs.BirchCollectionBounds

namespace LongTails.Proofs.BirchCollectionDualPool

open OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections (Params spec horizon batchSize)
open LongTails.Algorithms.BirchCollectionWorkerPools (ordering)
open LongTails.Algorithms.BirchCollectionDualPool
open LongTails.Algorithms.BirchCollections (algorithm program)
open LongTails.Proofs.BirchCollectionDualPoolRounds
open LongTails.Proofs.BirchCollectionPoolCertificate (pool_certificate)
open LongTails.Proofs.BirchCollectionPoolTrace (initial_data)
open LongTails.Algorithms.BirchCollectionProfiles (controls divisor)
open LongTails.Algorithms.BirchCollectionProfiles (resetOrdering)
open LongTails.Proofs.BirchCollectionSuccess (execute_success)
open LongTails.Proofs.BirchCollectionBounds (scaled_budget)
open LongTails.Theorems.BirchCollections (budget)

lemma dual_valid (p : Params) (m Q : ℕ) (events : List (List (Action m)))
    (hQ : 0 < Q) (hdef : ∀ x, p.N x = 0 → x = 0) (hcont : Continuous p.N)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (hregular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ)
    (he : Complete p m Q events) : spec.valid (dualProcess p m Q events) := by
  let q := tuned p m Q
  let B := batchSize q
  let K := horizon q
  let move : ℝ := 1 / divisor Q (Q - 1)
  let s := runRounds B move events
  have hK : 0 < K := by unfold K horizon; omega
  have hB : 0 < B := by unfold B batchSize; omega
  have hc : (1 : ℝ) ≤ divisor Q (Q - 1) := by
    exact_mod_cast (show 1 ≤ divisor Q (Q - 1) by unfold divisor; omega)
  have hc' : (0 : ℝ) < divisor Q (Q - 1) := by linarith
  have hi : AfterRound (m := m) {} 0 B Q move :=
    ⟨initial_data m B Q Q (Q - 1) move, fun _ => rfl, fun _ => rfl, rfl⟩
  have hs : AfterRound s K B Q move := by
    have h := run_rounds {} events hi hQ hB (show 0 ≤ move by positivity) ((div_le_one hc').2 hc) he.2
    simpa only [s, K, runRounds, zero_add, he.1] using h
  exact ⟨hdef, hcont, hL, hσ, hε, hΔ, Nat.zero_lt_succ _, hregular, hs.pool.legal,
    pool_certificate s hs.pool hK hQ le_rfl hs.cuts⟩

lemma dual_budget (p : Params) (m Q : ℕ) (events : List (List (Action m))) (hQ : 0 < Q) :
    let q := dualProcess p m Q events
    budget q 0 = q.controls.waste + batchSize q * (horizon q * Q) := by
  let q := dualProcess p m Q events
  exact scaled_budget q Q Q (Q - 1) q.controls.waste hQ rfl

lemma dual_success (p : Params) (m Q : ℕ) (events : List (List (Action m)))
    (hp : spec.valid (dualProcess p m Q events))
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : spec.admissible (dualProcess p m Q events) I O) :
    let q := dualProcess p m Q events
    let C := (program q).oracleCalls
    spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm q) (fun _ => C) z.1 z.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ :=
  execute_success (dualProcess p m Q events) hp _ le_rfl I O hI

end LongTails.Proofs.BirchCollectionDualPool
