import LongTails.Algorithms.BirchCollectionAsyncBatch
import LongTails.Proofs.BirchCollectionDelayed

namespace LongTails.Proofs.BirchCollectionAsyncBatch

open LongTails.Algorithms.BirchCollectionAsyncBatch

open OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionDelayed
open LongTails.Algorithms.BirchCollectionRennala (OriginalEvent)
open LongTails.Algorithms.BirchCollections (algorithm program)
open LongTails.Proofs.BirchCollectionDelayedTrace
open LongTails.Proofs.BirchCollectionDelayed (delayed_ordering delayed_calls launches)
open LongTails.Proofs.BirchCollectionExecution (program_calls)
open LongTails.Algorithms.BirchCollectionProfiles (packetControls divisor)
open LongTails.Proofs.BirchCollectionScaledReset (packet_window_structural)
open LongTails.Algorithms.BirchCollectionProfiles (resetOrdering)
open LongTails.Proofs.BirchCollectionBounds (packet_budget)
open LongTails.Proofs.BirchCollectionSuccess (execute_success)
open LongTails.Theorems.BirchCollections (budget)

lemma age_guard (G M d : ℕ) (hG : 0 < G) (hM : 0 < M) :
    d ≤ delayWindow G M ↔ d * M < G := by
  unfold delayWindow
  rw [Nat.le_div_iff_mul_le hM]
  omega

lemma async_batch_valid (p : Params) (m G M : ℕ) (events : List (OriginalEvent m))
    (hM : 0 < M) (hdef : ∀ x, p.N x = 0 → x = 0) (hcont : Continuous p.N)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (hregular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ)
    (he : Complete p m G M events) : spec.valid (asyncBatch p m G M events) := by
  let q := tuned p m G M
  let K := horizon q
  let B := batchSize q
  let W := delayWindow G M
  let move : ℝ := 1 / divisor 1 W
  let s := runController K (B * M) W move events
  have hK : 0 < K := by unfold K horizon; omega
  have hB : 0 < B := by unfold B batchSize; omega
  have hc : (1 : ℝ) ≤ divisor 1 W := by
    exact_mod_cast (show 1 ≤ divisor 1 W by unfold divisor; omega)
  have hcp : (0 : ℝ) < divisor 1 W := by linarith
  have hs : Data (B * M) W move s :=
    data_run move events (Nat.mul_pos hB hM) (by positivity) ((div_le_one hcp).2 hc) he.1
  have hround : s.trace.nextDirection = K := he.2
  have hp : 0 < s.trace.nextDirection := hround.symm ▸ hK
  obtain ⟨ho, hf, hm⟩ := delayed_ordering hs.path hp
  let o := delayedOrdering s.frontiers
  have ho' : o.Valid s.trace K := hround ▸ ho
  have hlen : o.labels.length = K := List.length_range.trans (hs.path.size.symm.trans hround)
  let D := s.trace.nextRaw - B * M * K
  have hs' : Structural s.trace (resetOrdering o) (packetControls 1 1 W D M) K B := by
    have h := packet_window_structural (m + 1) K B 1 1 W D M s.events o hs.legal
      (hs.represented.symm ▸ ho') Nat.one_pos le_rfl hM
    rw [hs.represented] at h
    refine h hf ?_ (fun n hn => (hm n hn).1) (fun n hn => (hm n hn).2.1)
      (fun n hn => (hm n hn).2.2) ?_
    · intro k _
      change 1 ≤ k + 1 - k ∧ k + 1 - k ≤ 1
      omega
    · rw [hlen]
      dsimp [D]
      omega
  exact ⟨hdef, hcont, hL, hσ, hε, hΔ, Nat.zero_lt_succ _, hregular, hs.legal,
    hs.represented.symm ▸ hs'⟩

lemma async_batch_budget (p : Params) (m G M : ℕ) (events : List (OriginalEvent m)) :
    let q := asyncBatch p m G M events
    budget q 0 = q.controls.waste + (batchSize q * M) * horizon q := by
  let q := asyncBatch p m G M events
  change budget q 0 = _
  have h := packet_budget q 1 1 (delayWindow G M) q.controls.waste M Nat.one_pos rfl
  simpa only [Nat.mul_one] using h

lemma async_batch_calls (p : Params) (m G M : ℕ) (events : List (OriginalEvent m)) :
    let q := asyncBatch p m G M events
    (program q).oracleCalls = (batchSize q * M) * launches events := by
  let q := asyncBatch p m G M events
  change (program q).oracleCalls = _
  rw [program_calls]
  exact delayed_calls (K := horizon q) (B := batchSize q * M) (window := delayWindow G M)
    (1 / (divisor 1 (delayWindow G M) : ℝ)) events

lemma async_batch_success (p : Params) (m G M : ℕ) (events : List (OriginalEvent m))
    (hp : spec.valid (asyncBatch p m G M events))
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : spec.admissible (asyncBatch p m G M events) I O) :
    let q := asyncBatch p m G M events
    let Q := (batchSize q * M) * launches events
    spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm q) (fun _ => Q) z.1 z.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ :=
  execute_success (asyncBatch p m G M events) hp _ (async_batch_calls p m G M events).le I O hI

end LongTails.Proofs.BirchCollectionAsyncBatch
