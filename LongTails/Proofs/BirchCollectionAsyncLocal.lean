import LongTails.Proofs.BirchCollectionAsyncLocalPublish
import LongTails.Proofs.BirchCollectionBounds

namespace LongTails.Proofs.BirchCollectionAsyncLocal

open OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections (Params TraceState ValidFrom run Structural spec batchSize horizon Ordering)
open LongTails.Algorithms.BirchCollectionAsyncLocal
open LongTails.Algorithms.BirchCollections (algorithm program)
open LongTails.Proofs.BirchCollectionAsyncLocalTrace
open LongTails.Proofs.BirchCollectionAsyncLocalPublish
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Proofs.BirchCollectionAcceptedOrder
open LongTails.Algorithms.BirchCollectionProfiles (controls divisor)
open LongTails.Proofs.BirchCollectionScaledReset (window_structural)
open LongTails.Algorithms.BirchCollectionProfiles (resetOrdering)
open LongTails.Proofs.BirchCollectionSuccess (execute_success)
open LongTails.Proofs.BirchCollectionBounds (scaled_budget)
open LongTails.Theorems.BirchCollections (budget)

lemma ordering_data {m G M B : ℕ} {s : Controller m} {move : ℝ}
    (hs : Data s G M B move) (hK : 0 < s.rounds) (hM : 0 < M) :
    let o := ordering M s
    LogData s.trace o s.rounds (delayWindow G M) ∧
      (∀ n, n < o.labels.length → o.refresh s.trace n = 1 ∧ o.movement s.trace n = move ∧
        (s.trace.directions (o.label n)).raw.length = B) := by
  let o := ordering M s
  have hlen : o.labels.length = s.rounds * M := hs.main.count
  have hpos : 0 < o.labels.length := hlen.symm ▸ Nat.mul_pos hK hM
  have hlabel (n : ℕ) (hn : n < s.accepted.length) : o.label n = s.accepted[n] :=
    label_eq_getElem o n hn
  change LogData s.trace o s.rounds (delayWindow G M) ∧ _
  refine ⟨⟨hpos, hs.main.unique, hs.main.markerCount, Nat.zero_mul _, hlen.symm,
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro k _
    change k * M < (k + 1) * M
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · intro k hk
    change k * M ≤ o.labels.length
    rw [hlen]
    exact Nat.mul_le_mul_right M hk
  · intro n hn
    rw [hlabel n hn]
    exact hs.main.labels _ (List.getElem_mem hn)
  · exact hs.main.markers
  · intro n hn
    rw [hlabel n hn]
    exact (hs.main.directions n hn).prior
  · intro n hn
    have hd := hs.main.directions n hn
    exact ⟨hd.frontierBound, hd.delayBound, by rw [hlabel n hn]; exact hd.includes⟩
  · intro n hn
    have hd := hs.main.directions n hn
    change o.refresh s.trace n = 1 ∧ o.movement s.trace n = move ∧
      (s.trace.directions (o.label n)).raw.length = B
    have hlength : o.labels.length = s.accepted.length := rfl
    have hn' : n < s.accepted.length := hn
    simp only [Ordering.refresh, Ordering.movement, hlength, ite_eq_left hn', hlabel n hn']
    exact ⟨hd.refresh, hd.movement, hd.raw⟩

lemma async_local_valid (p : Params) (m G M : ℕ) (events : List (Event m))
    (hG : 0 < G) (hM : 0 < M)
    (hdef : ∀ x, p.N x = 0 → x = 0) (hcont : Continuous p.N)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (hregular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ)
    (he : Complete p m G M events) : spec.valid (asyncLocal p m G M events) := by
  let q := tuned p m G M
  let B := batchSize q
  let K := horizon q
  let W := delayWindow G M
  let move : ℝ := 1 / divisor M W
  let s := controller B G M move events
  have hK : 0 < K := by unfold K horizon; omega
  have hB : 0 < B := by unfold B batchSize; omega
  have hc : (1 : ℝ) ≤ divisor M W := by
    exact_mod_cast (show 1 ≤ divisor M W by unfold divisor; omega)
  have hc' : (0 : ℝ) < divisor M W := by linarith
  have hs : Data s G M B move := data_run move events hG hM hB (by positivity) ((div_le_one hc').2 hc) he.1
  have hround : s.rounds = K := he.2
  obtain ⟨ho, hd⟩ := ordering_data hs (hround.symm ▸ hK) hM
  let o := ordering M s
  let D := s.trace.nextRaw - B * (K * M)
  have hlog : LogData s.trace o K W := hround ▸ ho
  have hlen : o.labels.length = K * M := hs.main.count.trans (congrArg (· * M) hround)
  have hstruct : Structural (run s.events) (resetOrdering o) (controls M M W D) K B := by
    apply window_structural (m + 1) K B M M W D s.events o hs.legal
      (hs.represented.symm ▸ hlog.valid) hM le_rfl
    · rw [hs.represented]
      exact hlog.frontier
    · intro k _
      change M ≤ (k + 1) * M - k * M ∧ (k + 1) * M - k * M ≤ M
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
      exact ⟨le_rfl, le_rfl⟩
    · rw [hs.represented]
      exact fun n hn => (hd n hn).1
    · rw [hs.represented]
      exact fun n hn => (hd n hn).2.1
    · rw [hs.represented]
      exact fun n hn => (hd n hn).2.2
    · rw [hs.represented, hlen]
      dsimp only [D]
      omega
  exact ⟨hdef, hcont, hL, hσ, hε, hΔ, Nat.zero_lt_succ _, hregular, hs.legal, hstruct⟩

lemma async_local_budget (p : Params) (m G M : ℕ) (events : List (Event m)) (hM : 0 < M) :
    let q := asyncLocal p m G M events
    budget q 0 = q.controls.waste + batchSize q * (horizon q * M) := by
  let q := asyncLocal p m G M events
  exact scaled_budget q M M (delayWindow G M) q.controls.waste hM rfl

lemma async_local_success (p : Params) (m G M : ℕ) (events : List (Event m))
    (hp : spec.valid (asyncLocal p m G M events))
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : spec.admissible (asyncLocal p m G M events) I O) :
    let q := asyncLocal p m G M events
    let Q := (program q).oracleCalls
    spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm q) (fun _ => Q) z.1 z.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ :=
  execute_success (asyncLocal p m G M events) hp _ le_rfl I O hI

end LongTails.Proofs.BirchCollectionAsyncLocal
