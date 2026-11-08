import LongTails.Algorithms.BirchNonEuclideanRennala
import LongTails.Proofs.BirchNonEuclideanScheduling

namespace LongTails.Proofs.BirchNonEuclideanRennalaScheduling

open LongTails.Algorithms.BirchNonEuclideanRennala

lemma legalFrom_append {m : ℕ} (K B : ℕ) (s : State m) (xs ys : List (Event m)) :
    LegalFrom K B s (xs ++ ys) ↔ LegalFrom K B s xs ∧ LegalFrom K B (xs.foldl (step K B) s) ys := by
  induction xs generalizing s with
  | nil => simp [LegalFrom]
  | cons x xs ih => simp [LegalFrom, ih, and_assoc]

lemma run_append {m : ℕ} (K B : ℕ) (xs ys : List (Event m)) :
    run K B (xs ++ ys) = ys.foldl (step K B) (run K B xs) := by simp [run]

lemma legalFrom_invariant {m : ℕ} (K B : ℕ) (P : State m → Prop)
    (hp : ∀ s e, P s → e.Enabled s → P (step K B s e)) (s : State m)
    (events : List (Event m)) (hs : P s) (he : LegalFrom K B s events) :
    P (events.foldl (step K B) s) := by
  induction events generalizing s with
  | nil => exact hs
  | cons e events ih => exact ih _ (hp s e hs he.1) he.2

structure Invariant {m : ℕ} (K B : ℕ) (s : State m) : Prop where
  round_le : s.round ≤ K
  batch_lt : s.batch < B
  stopped_batch : s.round = K → s.batch = 0
  accepted_count : s.accepted.length = s.round * B + s.batch
  source_le : ∀ w, s.source w ≤ s.round
  active_live : s.round < K → s.live = Finset.univ
  ready_live : s.ready ⊆ s.live
  query_balance : s.queries.length = s.accepted.length + s.stale.length + s.drained.length + s.ready.card
  active_drain : s.round < K → s.drained = []
  stopped_drain : s.round = K → s.drained.length + s.live.card = m - 1

lemma invariant_initial {m : ℕ} (K B : ℕ) (hK : 0 < K) (hB : 0 < B) :
    Invariant (m := m) K B {} := by
  constructor <;> simp_all
  omega

lemma update_source_le {m : ℕ} (s : State m) (w : Fin m) (a : ℕ)
    (hs : ∀ v, s.source v ≤ s.round) (ha : s.round ≤ a) :
    ∀ v, Function.update s.source w a v ≤ a := by
  intro v
  by_cases hv : v = w
  · subst v
    simp
  · simpa only [Function.update_of_ne hv] using (hs v).trans ha

lemma invariant_query {m : ℕ} (K B : ℕ) (s : State m) (w : Fin m)
    (hs : Invariant K B s) (he : (Event.query w).Enabled s) :
    Invariant K B (step K B s (.query w)) := by
  refine { hs with ready_live := ?_, query_balance := ?_ }
  · exact Finset.insert_subset he.1 hs.ready_live
  · simp only [step, List.length_append, List.length_singleton, Finset.card_insert_of_notMem he.2]
    have := hs.query_balance
    omega

lemma invariant_reply {m : ℕ} (K B : ℕ) (s : State m) (w : Fin m)
    (hs : Invariant K B s) (he : (Event.reply w).Enabled s) :
    Invariant K B (step K B s (.reply w)) := by
  have hbalance := hs.query_balance
  have hcount0 := hs.accepted_count
  have hbatch := hs.batch_lt
  have hready : s.ready.card = (s.ready.erase w).card + 1 :=
    (Finset.card_erase_add_one he.2).symm
  have hlive : s.live.card = (s.live.erase w).card + 1 :=
    (Finset.card_erase_add_one he.1).symm
  have hsubset : s.ready.erase w ⊆ s.live.erase w := Finset.erase_subset_erase w hs.ready_live
  have hsubset' : s.ready.erase w ⊆ s.live := (Finset.erase_subset w s.ready).trans hs.ready_live
  by_cases ha : s.round < K
  · have hl := hs.active_live ha
    have hd := hs.active_drain ha
    have hcard : s.live.card = m := by simp [hl]
    by_cases hf : fresh s w
    · by_cases hc : commits B s w
      · have hb : s.batch + 1 = B := hc.2
        have hr : s.round + 1 ≤ K := by omega
        have hcount : s.accepted.length + 1 = (s.round + 1) * B := by
          have hx := hs.accepted_count
          rw [Nat.add_mul, Nat.one_mul]
          omega
        simp only [step, ite_eq_left ha, ite_eq_left hc, ite_eq_left hf]
        refine {
          round_le := hr
          batch_lt := by change 0 < B; omega
          stopped_batch := fun _ => rfl
          accepted_count := by simpa using hcount
          source_le := update_source_le s w _ hs.source_le (by omega)
          active_live := ?_
          ready_live := ?_
          query_balance := ?_
          active_drain := fun _ => hd
          stopped_drain := ?_ }
        · intro hactive
          simpa only [ite_eq_left hactive] using hl
        · split_ifs <;> assumption
        · simp only [List.length_append, List.length_singleton]
          omega
        · intro hstop
          change s.round + 1 = K at hstop
          rw [ite_eq_right (by omega), hd]
          simp only [List.length_nil, zero_add]
          omega
      · have hb : s.batch + 1 < B := by
          have hbne : s.batch + 1 ≠ B := fun h => hc ⟨hf, h⟩
          omega
        simp only [step, ite_eq_left ha, ite_eq_right hc, ite_eq_left hf, Nat.add_zero]
        refine {
          round_le := hs.round_le
          batch_lt := hb
          stopped_batch := by change s.round = K → s.batch + 1 = 0; omega
          accepted_count := ?_
          source_le := update_source_le s w _ hs.source_le le_rfl
          active_live := fun _ => by simpa only [ite_eq_left ha] using hl
          ready_live := by simpa only [ite_eq_left ha] using hsubset'
          query_balance := ?_
          active_drain := fun _ => hd
          stopped_drain := by intro hk; change s.round = K at hk; omega }
        · simp only [List.length_append, List.length_singleton]
          omega
        · simp only [List.length_append, List.length_singleton]
          omega
    · have hc : ¬commits B s w := fun h => hf h.1
      simp only [step, ite_eq_left ha, ite_eq_right hc, ite_eq_right hf, Nat.add_zero]
      refine {
        round_le := hs.round_le
        batch_lt := hs.batch_lt
        stopped_batch := hs.stopped_batch
        accepted_count := hs.accepted_count
        source_le := update_source_le s w _ hs.source_le le_rfl
        active_live := fun _ => by simpa only [ite_eq_left ha] using hl
        ready_live := by simpa only [ite_eq_left ha] using hsubset'
        query_balance := ?_
        active_drain := fun _ => hd
        stopped_drain := by intro hk; change s.round = K at hk; omega }
      simp only [List.length_append, List.length_singleton]
      omega
  · have hk : s.round = K := by have := hs.round_le; omega
    simp only [step, ite_eq_right ha]
    refine {
      round_le := hs.round_le
      batch_lt := hs.batch_lt
      stopped_batch := hs.stopped_batch
      accepted_count := hs.accepted_count
      source_le := hs.source_le
      active_live := by intro hx; change s.round < K at hx; omega
      ready_live := hsubset
      query_balance := ?_
      active_drain := by intro hx; change s.round < K at hx; omega
      stopped_drain := ?_ }
    · simp only [List.length_append, List.length_singleton]
      omega
    · intro _
      have hd := hs.stopped_drain hk
      simp only [List.length_append, List.length_singleton]
      omega

lemma step_invariant {m : ℕ} (K B : ℕ) (s : State m) (e : Event m)
    (hs : Invariant K B s) (he : e.Enabled s) : Invariant K B (step K B s e) := by
  cases e with
  | query w => exact invariant_query K B s w hs he
  | reply w => exact invariant_reply K B s w hs he

lemma run_invariant {m : ℕ} (K B : ℕ) (events : List (Event m)) (hK : 0 < K) (hB : 0 < B)
    (he : LegalFrom K B {} events) : Invariant K B (run K B events) :=
  legalFrom_invariant K B (Invariant K B) (step_invariant K B) {} events (invariant_initial K B hK hB) he

def agePotential {m : ℕ} (s : State m) : ℤ := ∑ w : Fin m, ((s.round : ℤ) - s.source w)

def Credit {m : ℕ} (s : State m) : Prop :=
  (s.stale.length : ℤ) + agePotential s ≤ ((m : ℤ) - 1) * s.round

lemma agePotential_nonneg {m : ℕ} (s : State m) (hs : ∀ w, s.source w ≤ s.round) :
    0 ≤ agePotential s := by
  apply Finset.sum_nonneg
  intro w _
  exact sub_nonneg.mpr (by exact_mod_cast hs w)

lemma step_credit {m : ℕ} (K B : ℕ) (s : State m) (e : Event m)
    (hs : Invariant K B s) (hc : Credit s) : Credit (step K B s e) := by
  cases e with
  | query w => exact hc
  | reply w =>
      by_cases ha : s.round < K
      · by_cases hf : fresh s w
        · by_cases hcommit : commits B s w
          · simp only [Credit, step, ite_eq_left ha, ite_eq_left hf, ite_eq_left hcommit, agePotential]
            rw [LongTails.Proofs.BirchNonEuclideanScheduling.age_update s.round (s.round + 1)]
            simp only [Nat.cast_add, Nat.cast_one]
            have hsource : (s.source w : ℤ) = s.round := by exact_mod_cast hf
            dsimp [Credit, agePotential] at hc
            nlinarith
          · simp only [Credit, step, ite_eq_left ha, ite_eq_left hf, ite_eq_right hcommit, Nat.add_zero, agePotential]
            rw [LongTails.Proofs.BirchNonEuclideanScheduling.age_update s.round s.round]
            have hsource : (s.source w : ℤ) = s.round := by exact_mod_cast hf
            dsimp [Credit, agePotential] at hc
            linarith
        · have hcommit : ¬commits B s w := fun h => hf h.1
          simp only [Credit, step, ite_eq_left ha, ite_eq_right hf, ite_eq_right hcommit, Nat.add_zero,
            agePotential, List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
          rw [LongTails.Proofs.BirchNonEuclideanScheduling.age_update s.round s.round]
          have hsource : (s.source w : ℤ) + 1 ≤ s.round := by
            have hx := hs.source_le w
            have hn : s.source w ≠ s.round := hf
            exact_mod_cast (show s.source w + 1 ≤ s.round by omega)
          dsimp [Credit, agePotential] at hc
          linarith
      · simpa only [Credit, step, ite_eq_right ha, agePotential] using hc

lemma run_credit {m : ℕ} (K B : ℕ) (events : List (Event m)) (hK : 0 < K) (hB : 0 < B)
    (he : LegalFrom K B {} events) : Credit (run K B events) := by
  have hi : Invariant K B ({} : State m) ∧ Credit ({} : State m) :=
    ⟨invariant_initial K B hK hB, by simp [Credit, agePotential]⟩
  exact (legalFrom_invariant K B (fun s => Invariant K B s ∧ Credit s)
    (fun s e hs he => ⟨step_invariant K B s e hs.1 he, step_credit K B s e hs.1 hs.2⟩) {} events hi he).2

lemma stale_le_round {m : ℕ} (s : State m) (hm : 0 < m) (hs : ∀ w, s.source w ≤ s.round)
    (hc : Credit s) : s.stale.length ≤ (m - 1) * s.round := by
  have hn := agePotential_nonneg s hs
  have hh : (s.stale.length : ℤ) ≤ ((m : ℤ) - 1) * s.round := by dsimp [Credit] at hc; linarith
  have hm1 : (1 : ℕ) ≤ m := hm
  exact_mod_cast hh

lemma run_stale_bound {m : ℕ} (K B : ℕ) (events : List (Event m)) (hm : 0 < m)
    (hK : 0 < K) (hB : 0 < B) (he : LegalFrom K B {} events) :
    (run K B events).stale.length ≤ (m - 1) * (K - 1) := by
  let P := fun s : State m => Invariant K B s ∧ Credit s ∧ s.stale.length ≤ (m - 1) * (K - 1)
  have hi : P {} := ⟨invariant_initial K B hK hB, by simp [Credit, agePotential], by simp⟩
  have hp : ∀ s e, P s → e.Enabled s → P (step K B s e) := by
    intro s e hs hen
    have hn := step_invariant K B s e hs.1 hen
    have hc := step_credit K B s e hs.1 hs.2.1
    refine ⟨hn, hc, ?_⟩
    cases e with
    | query w => exact hs.2.2
    | reply w =>
        by_cases ha : s.round < K
        · by_cases hf : fresh s w
          · simpa only [step, ite_eq_left ha, ite_eq_left hf] using hs.2.2
          · have hb := stale_le_round (step K B s (.reply w)) hm hn.source_le hc
            have hcommit : ¬commits B s w := fun h => hf h.1
            have hr : (step K B s (.reply w)).round = s.round := by
              simp only [step, ite_eq_left ha, ite_eq_right hcommit, Nat.add_zero]
            rw [hr] at hb
            exact hb.trans (Nat.mul_le_mul_left (m - 1) (by omega))
        · simpa only [step, ite_eq_right ha] using hs.2.2
  exact (legalFrom_invariant K B P hp {} events hi he).2.2

lemma completeTrace_query_count {m : ℕ} (K B : ℕ) (events : List (Event m))
    (hK : 0 < K) (hB : 0 < B) (he : CompleteTrace K B events) :
    (run K B events).queries.length = K * B + (run K B events).stale.length + (m - 1) := by
  have hi := run_invariant K B events hK hB he.1
  have hb := hi.stopped_batch he.2.1
  have ha := hi.accepted_count
  have hd := hi.stopped_drain he.2.1
  have hready : (run K B events).ready = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hx := hi.ready_live hw
    simp [he.2.2] at hx
  have hq := hi.query_balance
  rw [he.2.1, hb, Nat.add_zero] at ha
  rw [he.2.2, Finset.card_empty, Nat.add_zero] at hd
  rw [ha, hd, hready, Finset.card_empty, Nat.add_zero] at hq
  exact hq

lemma completeTrace_query_bound {m : ℕ} (K B : ℕ) (events : List (Event m))
    (hm : 0 < m) (hK : 0 < K) (hB : 0 < B) (he : CompleteTrace K B events) :
    (run K B events).queries.length ≤ K * (B + m - 1) := by
  rw [completeTrace_query_count K B events hK hB he]
  have hs := run_stale_bound K B events hm hK hB he.1
  have heq : K * B + (m - 1) * (K - 1) + (m - 1) = K * (B + m - 1) := by
    have hsum : B + m - 1 = B + (m - 1) := by omega
    calc
      _ = K * B + (m - 1) * ((K - 1) + 1) := by ring
      _ = K * B + (m - 1) * K := by rw [Nat.sub_add_cancel hK]
      _ = _ := by rw [hsum]; ring
  omega

end LongTails.Proofs.BirchNonEuclideanRennalaScheduling
