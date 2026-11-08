import LongTails.Proofs.BirchCollectionLocalRounds
import LongTails.Proofs.BirchCollectionSerialCertificate
import LongTails.Proofs.BirchCollectionBounds

namespace LongTails.Proofs.BirchCollectionLocal

open Finset OracleTemplate MeasureTheory
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal
open LongTails.Algorithms.BirchCollectionRennala (OriginalEvent)
open LongTails.Algorithms.BirchCollections (algorithm program)
open LongTails.Proofs.BirchCollectionLocalRounds
open LongTails.Proofs.BirchCollectionExecution (run_raw program_calls)
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Proofs.BirchCollectionSerialCertificate (vanilla_label)
open LongTails.Algorithms.BirchCollectionProfiles (controls divisor)
open LongTails.Proofs.BirchCollectionScaledReset (window_structural)
open LongTails.Algorithms.BirchCollectionProfiles (resetOrdering)
open LongTails.Proofs.BirchCollectionSuccess (execute_success)
open LongTails.Proofs.BirchCollectionBounds (scaled_budget)
open LongTails.Theorems.BirchCollections (budget)

lemma local_ordering {m K Q B : ℕ} {move : ℝ} {s : Round m}
    (hs : History s K Q B move) (hK : 0 < K) (hQ : 0 < Q) :
    let o := localOrdering Q K
    o.Valid s.trace K ∧
      (∀ n, n < o.labels.length → o.frontier n ≤ n ∧ n - o.frontier n ≤ Q - 1 ∧
        range (o.frontier n) ⊆ o.history s.trace n) ∧
      (∀ n, n < o.labels.length → o.refresh s.trace n = 1 ∧ o.movement s.trace n = move ∧
        (s.trace.directions (o.label n)).raw.length = B) := by
  let o := localOrdering Q K
  have hlen : o.labels.length = K * Q := List.length_range
  have hlabel (n : ℕ) (hn : n < K * Q) : o.label n = n :=
    vanilla_label (K * Q) n hn
  change o.Valid s.trace K ∧ _
  refine ⟨⟨hlen.symm ▸ Nat.mul_pos hK hQ, List.nodup_range, hs.markers,
    Nat.zero_mul Q, hlen.symm, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro k _
    change k * Q < (k + 1) * Q
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · intro n hn
    have hn' := hlen ▸ hn
    rw [hlabel n hn', hs.directions]
    exact hn'
  · intro k hk
    change (s.trace.states (s.trace.markers[k]?.getD 0)).history = (range (k * Q)).image o.label
    rw [hs.history k hk]
    ext i
    have hi (j : ℕ) (hj : j ∈ range (k * Q)) : j < K * Q :=
      (mem_range.mp hj).trans_le (Nat.mul_le_mul_right Q hk)
    constructor
    · intro hin
      exact mem_image.mpr ⟨i, hin, hlabel i (hi i hin)⟩
    · intro hin
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hin
      simpa only [hlabel j (hi j hj)] using hj
  · intro n
    by_cases hn : n < o.labels.length
    · have hn' := hlen ▸ hn
      intro j hj
      obtain ⟨hjl, hjp⟩ := (ordering_history_mem s.trace o n j hn).mp hj
      rw [hlabel n hn', hlabel j (hlen ▸ hjl)] at hjp
      exact (hs.direction n hn').2.1 hjp
    · rw [Ordering.history, ite_eq_right hn]
  · intro n hn
    have hn' := hlen ▸ hn
    change (n / Q) * Q ≤ n ∧ n - (n / Q) * Q ≤ Q - 1 ∧
      range ((n / Q) * Q) ⊆ o.history s.trace n
    have hmod := Nat.mod_add_div n Q
    rw [Nat.mul_comm Q (n / Q)] at hmod
    have hml := Nat.mod_lt n hQ
    refine ⟨by omega, by omega, ?_⟩
    intro j hj
    have hjK : j < K * Q := (mem_range.mp hj).trans_le (show (n / Q) * Q ≤ n by omega)
      |>.trans hn'
    apply (ordering_history_mem s.trace o n j hn).2
    rw [hlabel n hn', hlabel j hjK]
    exact ⟨hlen.symm ▸ hjK, (hs.direction n hn').1 hj⟩
  · intro n hn
    have hn' := hlen ▸ hn
    change o.refresh s.trace n = 1 ∧ o.movement s.trace n = move ∧
      (s.trace.directions (o.label n)).raw.length = B
    simp only [Ordering.refresh, Ordering.movement, hlen, ite_eq_left hn', hlabel n hn']
    exact (hs.direction n hn').2.2

lemma history_structural {m K Q B : ℕ} {s : Round m}
    (hs : History s K Q B (1 / (divisor Q (Q - 1) : ℝ))) (hK : 0 < K) (hQ : 0 < Q) :
    Structural (run s.events) (resetOrdering (localOrdering Q K))
      (controls Q Q (Q - 1) (s.trace.nextRaw - B * (K * Q))) K B := by
  obtain ⟨ho, hf, hb⟩ := local_ordering hs hK hQ
  let o := localOrdering Q K
  let D := s.trace.nextRaw - B * (K * Q)
  have hblocks : ∀ k, k < K → Q ≤ o.cut (k + 1) - o.cut k ∧ o.cut (k + 1) - o.cut k ≤ Q := by
    intro k _
    change Q ≤ (k + 1) * Q - k * Q ∧ (k + 1) * Q - k * Q ≤ Q
    rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
    exact ⟨le_rfl, le_rfl⟩
  have hstruct : Structural (run s.events) (resetOrdering o) (controls Q Q (Q - 1) D) K B := by
    apply window_structural (m + 1) K B Q Q (Q - 1) D s.events o hs.legal
      (hs.represented.symm ▸ ho) hQ le_rfl
    · rw [hs.represented]
      exact hf
    · exact hblocks
    · rw [hs.represented]
      exact fun n hn => (hb n hn).1
    · rw [hs.represented]
      exact fun n hn => (hb n hn).2.1
    · rw [hs.represented]
      exact fun n hn => (hb n hn).2.2
    · rw [hs.represented, show o.labels.length = K * Q from List.length_range]
      dsimp only [D]
      omega
  exact hstruct

lemma local_valid (p : Params) (m Q : ℕ) (rounds : List (List (OriginalEvent m)))
    (hQ : 0 < Q) (hdef : ∀ x, p.N x = 0 → x = 0) (hcont : Continuous p.N)
    (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (hregular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ)
    (he : Complete p m Q rounds) : spec.valid (localSgd p m Q rounds) := by
  let q := tuned p m Q
  let K := horizon q
  let B := batchSize q
  let move : ℝ := 1 / divisor Q (Q - 1)
  let s := runRounds B move rounds
  have hK : 0 < K := by unfold K horizon; omega
  have hB : 0 < B := by unfold B batchSize; omega
  have hc : (1 : ℝ) ≤ divisor Q (Q - 1) := by
    exact_mod_cast (show 1 ≤ divisor Q (Q - 1) by unfold divisor; omega)
  have hc' : (0 : ℝ) < divisor Q (Q - 1) := by linarith
  have hs : History s K Q B move := by
    have h := history_run rounds hQ hB (show 0 ≤ move by positivity) ((div_le_one hc').2 hc) he.2
    rwa [he.1] at h
  exact ⟨hdef, hcont, hL, hσ, hε, hΔ, Nat.zero_lt_succ _, hregular, hs.legal, history_structural hs hK hQ⟩

lemma local_budget (p : Params) (m Q : ℕ) (rounds : List (List (OriginalEvent m))) (hQ : 0 < Q) :
    let q := localSgd p m Q rounds
    budget q 0 = q.controls.waste + batchSize q * (horizon q * Q) := by
  let q := localSgd p m Q rounds
  exact scaled_budget q Q Q (Q - 1) q.controls.waste hQ rfl

lemma local_success (p : Params) (m Q : ℕ) (rounds : List (List (OriginalEvent m)))
    (hp : spec.valid (localSgd p m Q rounds))
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : spec.admissible (localSgd p m Q rounds) I O) :
    let q := localSgd p m Q rounds
    let C := (program q).oracleCalls
    spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (algorithm q) (fun _ => C) z.1 z.2)
      ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ :=
  execute_success (localSgd p m Q rounds) hp _ le_rfl I O hI

end LongTails.Proofs.BirchCollectionLocal
