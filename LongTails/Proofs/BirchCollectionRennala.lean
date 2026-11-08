import LongTails.Proofs.BirchCollectionRennalaReply
import LongTails.Proofs.BirchCollectionSerialCertificate
import LongTails.Theorems.BirchCollections

namespace LongTails.Proofs.BirchCollectionRennala

open OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionRennala
open LongTails.Algorithms.BirchCollections (algorithm program)
open LongTails.Proofs.BirchCollectionExecution (run_raw program_calls)
open LongTails.Proofs.BirchCollectionRennalaLedger
open LongTails.Proofs.BirchCollectionRennalaTrace
open LongTails.Proofs.BirchCollectionRennalaReply
open LongTails.Proofs.BirchCollectionSerialCertificate (serial_structural)
open LongTails.Proofs.BirchCollectionSuccess (execute_success)

local notation "orun" => LongTails.Algorithms.BirchNonEuclideanRennala.run
local notation "CompleteTrace" => LongTails.Algorithms.BirchNonEuclideanRennala.CompleteTrace

abbrev Complete (p : Params) (m : ℕ) (events : List (OriginalEvent m)) : Prop :=
  let q := rennala p m events
  CompleteTrace (horizon q) (batchSize q) events

lemma rennala_exact (p : Params) (m : ℕ) (events : List (OriginalEvent m)) (he : Complete p m events) :
    let q := rennala p m events
    (program q).oracleCalls = batchSize q * horizon q + q.controls.waste := by
  let q := rennala p m events
  let K := horizon q
  let B := batchSize q
  let t := translate K B events
  change (program q).oracleCalls = B * K + (t.original.stale.length + t.original.drained.length)
  have hK : 0 < K := by unfold K horizon; omega
  have hB : 0 < B := by unfold B batchSize; omega
  have hrun := (translate_ledger K B events).1
  have hd := (LongTails.Proofs.BirchNonEuclideanRennalaScheduling.run_invariant K B events hK hB he.1).stopped_drain he.2.1
  rw [he.2.2, Finset.card_empty, Nat.add_zero] at hd
  rw [program_calls]
  change calls t.events = _
  rw [translate_calls K B events hK hB he, show t.original = orun K B events from hrun,
    hd, Nat.mul_comm B K, Nat.add_assoc]

lemma rennala_calls_bound (p : Params) (m : ℕ) (events : List (OriginalEvent m)) (hm : 0 < m)
    (he : Complete p m events) :
    let q := rennala p m events
    (program q).oracleCalls ≤ horizon q * (batchSize q + m - 1) := by
  let q := rennala p m events
  let K := horizon q
  let B := batchSize q
  have hK : 0 < K := by unfold K horizon; omega
  have hB : 0 < B := by unfold B batchSize; omega
  change (program q).oracleCalls ≤ K * (B + m - 1)
  rw [program_calls]
  exact translate_calls_bound K B events hm hK hB he

lemma rennala_valid (p : Params) (m : ℕ) (events : List (OriginalEvent m))
    (hdef : ∀ x, p.N x = 0 → x = 0) (hcont : Continuous p.N)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (hregular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ)
    (he : Complete p m events) : spec.valid (rennala p m events) := by
  let q := rennala p m events
  let K := horizon q
  let B := batchSize q
  let t := translate K B events
  have hK : 0 < K := by unfold K horizon; omega
  have hB : 0 < B := by unfold B batchSize; omega
  have ht := data_translate events hK hB he.1
  have hm : LongTails.Proofs.BirchCollectionRennalaTrace.MainData (run t.events) B K := by
    have hr : t.original.round = K := by
      change (translate K B events).original.round = K
      rw [(translate_ledger K B events).1]
      exact he.2.1
    rw [ht.represented]
    simpa only [hr] using (show LongTails.Proofs.BirchCollectionRennalaTrace.MainData
      t.trace B t.original.round from ht.main)
  have hcount : (run t.events).nextRaw = B * K + q.controls.waste := by
    rw [run_raw]
    exact (program_calls q).symm.trans (rennala_exact p m events he)
  have hstruct := serial_structural (m + 1) B K q.controls.waste t.events hK ht.legal
    ⟨hm.states, hm.directions, hm.markers, hm.history, hm.direction⟩ hcount.le
  exact ⟨hdef, hcont, hL, hσ, hε, hΔ, Nat.zero_lt_succ _, hregular, ht.legal, hstruct⟩

lemma rennala_success (p : Params) (m : ℕ) (events : List (OriginalEvent m))
    (he : Complete p m events) (hp : spec.valid (rennala p m events))
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : spec.admissible (rennala p m events) I O) :
    let q := rennala p m events
    let Q := batchSize q * horizon q + q.controls.waste
    spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm q) (fun _ => Q) z.1 z.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ :=
  execute_success (rennala p m events) hp _ (rennala_exact p m events he).le I O hI

end LongTails.Proofs.BirchCollectionRennala
