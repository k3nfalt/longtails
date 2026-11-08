import LongTails.Proofs.BirchResourceNativeTrace
import LongTails.Proofs.BirchResourceDispatch
import LongTails.Proofs.BirchResourcePlans
import LongTails.Proofs.BirchCollectionSuccess

namespace LongTails.Proofs.BirchResourceNativePlan

open Finset MeasureTheory OracleTemplate
open OracleTemplate.Rennala (Point Instance)
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchResourceNative
open LongTails.Proofs.BirchResourceNativeTrace
open LongTails.Proofs.BirchResourceDispatch
open LongTails.Proofs.BirchResourceNativeCertificate (structural)
open LongTails.Algorithms.BirchCollections (program algorithm)
open LongTails.Proofs.BirchCollectionSuccess (execute_success)
open LongTails.Proofs.BirchCollectionExecution (program_calls run_raw)

lemma cut_succ {Q : ℕ} (p : Layout Q) (hQ : 0 < Q) (B k : ℕ) :
    (plan p hQ B).cut (k + 1) = 1 + k * Q := by simp [plan]

lemma slot_add {Q : ℕ} (hQ : 0 < Q) (k : ℕ) (i : Fin Q) :
    slot hQ (1 + k * Q + i) = i := by
  apply Fin.ext
  change (1 + k * Q + i.val - 1) % Q = i.val
  have he : 1 + k * Q + i.val - 1 = k * Q + i.val := by omega
  rw [he, Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt i.isLt]

lemma fixed_valid {Q : ℕ} (p : Layout Q) (hQ : 0 < Q) (B K : ℕ) (hB : 0 < B)
    (hK : 0 < K) (hp : p.Valid B) : Plan.Valid (plan p hQ B) B K := by
  let a := plan p hQ B
  have hc0 : a.cut 0 = 0 := rfl
  have hc1 : a.cut 1 = 1 := by rw [cut_succ]; simp
  have hKcut : a.cut K = 1 + (K - 1) * Q := by simp [a, plan, Nat.ne_of_gt hK]
  have hb (i : Fin Q) : p.accepted i ≤ B := by
    rw [← hp.quota]
    exact single_le_sum (f := p.accepted) (fun _ _ => Nat.zero_le _) (mem_univ i)
  have hpaid : B ≤ ∑ i, p.paid i := by rw [← hp.quota]; exact sum_le_sum (fun i _ => (hp.count i).2)
  have hphase (n : ℕ) (hn : 0 < n) :
      a.cut (a.phase n) = offset Q n ∧
        a.cut (a.phase n + 1) = offset Q n + Q := by
    have he : a.phase n = (n - 1) / Q + 1 := by simp [a, plan, Nat.ne_of_gt hn, add_comm]
    rw [he, cut_succ, cut_succ, Nat.add_mul, Nat.one_mul]
    simp [offset, Nat.add_assoc]
  have hspan (n : ℕ) (hn : 0 < n) :
      offset Q n ≤ n ∧ n < offset Q n + Q := by
    have he := Nat.mod_add_div (n - 1) Q
    rw [Nat.mul_comm] at he
    have hi := Nat.mod_lt (n - 1) hQ
    unfold offset
    omega
  refine ⟨hc0, hc1, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro k hk
    by_cases hz : k = 0
    · subst k
      rw [hc0, hc1]
      decide
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
      rw [cut_succ, cut_succ, Nat.add_mul, Nat.one_mul]
      omega
  · intro n hn
    by_cases hz : n = 0
    · subst n
      change 0 < K ∧ a.cut 0 ≤ 0 ∧ 0 < a.cut 1
      rw [hc0, hc1]
      exact ⟨hK, le_rfl, Nat.one_pos⟩
    · have hpos := Nat.pos_of_ne_zero hz
      have hs := hspan n hpos
      have ht := hphase n hpos
      have hlt : (n - 1) / Q < K - 1 := by
        apply (Nat.div_lt_iff_lt_mul hQ).2
        rw [hKcut] at hn
        omega
      refine ⟨?_, ht.1.symm ▸ hs.1, ht.2.symm ▸ hs.2⟩
      change (if n = 0 then 0 else 1 + (n - 1) / Q) < K
      rw [ite_eq_right hz]
      omega
  · intro n _ j hj
    by_cases hz : n = 0
    · simp [plan, hz] at hj
    · have hpos := Nat.pos_of_ne_zero hz
      change (if n = 0 then none else (p.parent (slot hQ n)).map (fun i => offset Q n + i.val)) =
        some j at hj
      rw [ite_eq_right hz] at hj
      obtain ⟨i, hi, he⟩ := Option.map_eq_some_iff.mp hj
      subst j
      have hrel := hp.earlier (slot hQ n) i hi
      have hsum := Nat.mod_add_div (n - 1) Q
      rw [Nat.mul_comm] at hsum
      have hjn : offset Q n + i.val < n := by
        change i.val < (n - 1) % Q at hrel
        dsimp [offset]
        omega
      have hj0 : offset Q n + i.val ≠ 0 := by unfold offset; omega
      have hquot : (offset Q n + i.val - 1) / Q = (n - 1) / Q := by
        have he' : offset Q n + i.val - 1 = i.val + ((n - 1) / Q) * Q := by unfold offset; omega
        rw [he', Nat.mul_comm ((n - 1) / Q) Q, Nat.add_mul_div_left _ _ hQ, Nat.div_eq_of_lt i.isLt, zero_add]
      refine ⟨hjn, ?_⟩
      change (if offset Q n + i.val = 0 then 0 else 1 + (offset Q n + i.val - 1) / Q) =
        (if n = 0 then 0 else 1 + (n - 1) / Q)
      rw [ite_eq_right hj0, ite_eq_right hz, hquot]
  · intro n _
    by_cases hz : n = 0
    · subst n
      exact ⟨hB, hpaid, le_rfl⟩
    · simpa only [a, plan, ite_eq_right hz] using ⟨(hp.count (slot hQ n)).1,
        (hp.count (slot hQ n)).2, hb (slot hQ n)⟩
  · intro k _
    by_cases hz : k = 0
    · subst k
      change ∑ n ∈ Ico (a.cut 0) (a.cut 1), a.accepted n = B
      rw [hc0, hc1]
      simp [a, plan]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
      change ∑ n ∈ Ico (a.cut (j + 1)) (a.cut (j + 1 + 1)), a.accepted n = B
      rw [cut_succ, cut_succ, Nat.add_mul, Nat.one_mul, sum_Ico_eq_sum_range, ← Nat.add_assoc,
        Nat.add_sub_cancel_left, ← Fin.sum_univ_eq_sum_range]
      calc
        _ = ∑ i, p.accepted i := by
          apply sum_congr rfl
          intro i _
          have hne : 1 + j * Q + i.val ≠ 0 := by omega
          change (if 1 + j * Q + i.val = 0 then B else p.accepted (slot hQ (1 + j * Q + i))) = _
          rw [ite_eq_right hne, slot_add hQ]
        _ = _ := hp.quota

lemma paid_phase {Q : ℕ} (p : Layout Q) (hQ : 0 < Q) (B k : ℕ) :
    let a := plan p hQ B
    ∑ n ∈ Ico (a.cut k) (a.cut (k + 1)), a.paid n = ∑ i, p.paid i := by
  let a := plan p hQ B
  by_cases hz : k = 0
  · subst k
    change ∑ n ∈ Ico (a.cut 0) (a.cut 1), a.paid n = _
    rw [show a.cut 0 = 0 from rfl, cut_succ]
    simp [a, plan]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
    change ∑ n ∈ Ico (a.cut (j + 1)) (a.cut (j + 1 + 1)), a.paid n = _
    rw [cut_succ, cut_succ, Nat.add_mul, Nat.one_mul, sum_Ico_eq_sum_range, ← Nat.add_assoc,
      Nat.add_sub_cancel_left, ← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    have hne : 1 + j * Q + i.val ≠ 0 := by omega
    change (if 1 + j * Q + i.val = 0 then ∑ i, p.paid i else p.paid (slot hQ (1 + j * Q + i))) = _
    rw [ite_eq_right hne, slot_add hQ]

lemma sum_blocks (cut : ℕ → ℕ) (K : ℕ) (v : ℕ → ℕ) (c : ℕ)
    (hz : cut 0 = 0) (hm : ∀ k < K, cut k ≤ cut (k + 1))
    (hv : ∀ k < K, ∑ n ∈ Ico (cut k) (cut (k + 1)), v n = c) :
    (∑ n ∈ range (cut K), v n) = K * c := by
  induction K with
  | zero => simp [hz]
  | succ K ih =>
    rw [← sum_range_add_sum_Ico (f := v) (hm K (by omega)),
      ih (fun k hk => hm k (by omega)) (fun k hk => hv k (by omega)), hv K (by omega),
      Nat.add_mul, Nat.one_mul]

open LongTails.Proofs.BirchCollectionStructure (rawLedger_run completedLedger_run)
open LongTails.Proofs.BirchCollectionOrdering (ordering_raw_ledger)

lemma checked {Q : ℕ} (p : Params) (l : Layout Q) (hQ : 0 < Q) (hl : l.Valid (batchSize (tuned p))) :
    let q := compiledParams p l hQ
    let B := batchSize q
    let K := horizon q
    (program q).oracleCalls = K * (∑ i, l.paid i) ∧
      ValidFrom q.workers {} q.events ∧ Structural (run q.events) q.ordering q.controls K B := by
  let q := compiledParams p l hQ
  let B := batchSize q
  let K := horizon q
  let a := plan l hQ B
  have hB : 0 < B := by unfold B batchSize; omega
  have hK : 0 < K := by unfold K horizon; omega
  have hp := fixed_valid l hQ B K hB hK hl
  have hm := code_marked hp hB K le_rfl
  have hf := profile hp hB hK
  let s := run q.events
  let o := q.ordering
  have hlegal : ValidFrom q.workers {} q.events := hm.prefixData.legal
  have hwork : s.nextRaw = K * (∑ i, l.paid i) := by
    change (run (code a B K)).nextRaw = _
    rw [hm.prefixData.work]
    exact sum_blocks a.cut K a.paid _ hp.zero (fun k hk => (hp.strict k hk).le)
      (fun k _ => paid_phase l hQ B k)
  have hraw : (∑ n ∈ range o.labels.length, (o.raw s n).card) = K * B := by
    have hcut : o.cut K = o.labels.length := hf.ordered.2.2.2.2.1
    rw [← hcut]
    exact sum_blocks o.cut K (fun n => (o.raw s n).card) B hf.ordered.2.2.2.1
      (fun k hk => (hf.ordered.2.2.2.2.2.1 k hk).le) hf.quota
  have hledger := ordering_raw_ledger s o K (rawLedger_run q.workers q.events hlegal)
    (completedLedger_run q.workers q.events hlegal) hf.ordered
  have he : s.nextRaw - ((range o.labels.length).biUnion (o.raw s)).card ≤ q.controls.waste := by
    change s.nextRaw - ((range o.labels.length).biUnion (o.raw s)).card ≤
      K * ((∑ i, l.paid i) - B)
    rw [hwork, hraw] at hledger
    rw [Nat.mul_sub]
    omega
  refine ⟨?_, hlegal, structural hf hB he⟩
  rw [program_calls, ← run_raw]
  exact hwork

lemma native_success {Q : ℕ} (p : Params) (l : Layout Q) (hQ : 0 < Q)
    (hl : l.Valid (batchSize (tuned p))) (hdef : ∀ x, p.N x = 0 → x = 0)
    (hcont : Continuous p.N) (hL : 0 < p.L) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hΔ : 0 ≤ p.Δ)
    (hregular : LongTails.Setups.BirchNonEuclidean.DualRegular p.N p.κ)
    (I : Instance p.d) (O : Oracle (Point p.d) (Point p.d))
    (hI : spec.admissible (compiledParams p l hQ) I O) :
    let q := compiledParams p l hQ
    let C := horizon q * (∑ i, l.paid i)
    (program q).oracleCalls = C ∧
      spec.successful q I (fun z : (algorithm q).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (algorithm q) (fun _ => C) z.1 z.2)
        ⟨((algorithm q).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let q := compiledParams p l hQ
  obtain ⟨hc, hv, hs⟩ := checked p l hQ hl
  have hq : spec.valid q :=
    ⟨hdef, hcont, hL, hσ, hε, hΔ, show (0 : ℕ) < 1 from Nat.one_pos, hregular, hv, hs⟩
  exact ⟨hc, execute_success q hq _ hc.le I O hI⟩

end LongTails.Proofs.BirchResourceNativePlan
