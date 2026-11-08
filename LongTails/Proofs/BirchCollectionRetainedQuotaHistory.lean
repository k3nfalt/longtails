import LongTails.Algorithms.BirchCollectionRetainedQuota
import LongTails.Proofs.BirchCollectionAlternatingHistory

namespace LongTails.Proofs.BirchCollectionRetainedQuotaHistory

open Finset
open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollectionLocal (Round)
open LongTails.Algorithms.BirchCollectionNested (Layout)
open LongTails.Algorithms.BirchCollectionRetainedQuota
open LongTails.Proofs.BirchCollectionAlternatingHistory (reset_block)
open LongTails.Proofs.BirchCollectionNestedRounds (BlockEffect nested_block)
open LongTails.Proofs.BirchCollectionBatches (RetiredPast)
open LongTails.Proofs.BirchCollectionOrdering (markers_bound_run)

lemma leaf_bounds {m B : ℕ} {phase : Phase m} (hB : 0 < B) (hp : phase.Valid B) :
    0 ≤ leafGain B phase.batch ∧ leafGain B phase.batch ≤ 1 / 8 := by
  have hb : phase.batch ≤ B := by
    have h := Nat.mul_le_mul_left phase.batch hp.2.1
    rw [Nat.mul_one] at h
    exact h.trans hp.2.2.2
  have hR : (phase.batch : ℝ) ≤ B := by exact_mod_cast hb
  exact ⟨by unfold leafGain; positivity, (div_le_iff₀ (by positivity)).2 (by linarith)⟩

def batch {m : ℕ} (schedule : ℕ → Phase m) (B k : ℕ) : ℕ :=
  if k = 0 then B else (schedule k).batch

noncomputable def movement {m : ℕ} (schedule : ℕ → Phase m) (B k : ℕ) : ℝ :=
  if k = 0 then 1 / 2 else leafGain B (schedule k).batch

lemma cut_lt {m B K : ℕ} {schedule : ℕ → Phase m} (hs : Complete schedule B K)
    {k : ℕ} (hk : k < K) : cut schedule k < cut schedule (k + 1) := by
  rw [cut]
  by_cases h : k = 0
  · simp [h]
  · simp only [ite_eq_right h]
    have hh := (hs k (Nat.pos_of_ne_zero h) hk).2.1
    omega

lemma cut_le {m B K : ℕ} {schedule : ℕ → Phase m} (hs : Complete schedule B K)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ K) : cut schedule i ≤ cut schedule j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (cut_lt hs (by omega : j < K)).le

structure History {m : ℕ} (s : Round m) (schedule : ℕ → Phase m) (B K : ℕ) : Prop where
  represented : run s.events = s.trace
  legal : ValidFrom (m + 1) {} s.events
  retired : RetiredPast s.trace
  count : s.trace.nextDirection = cut schedule K
  markers : s.trace.markers.length = K + 1
  last : s.trace.markers.getLast?.getD 0 < s.trace.nextState ∧
    (s.trace.states (s.trace.markers.getLast?.getD 0)).history = range (cut schedule K)
  mark : ∀ k ≤ K, (s.trace.states (s.trace.markers[k]?.getD 0)).history = range (cut schedule k)
  direction : ∀ k < K, ∀ n ∈ Ico (cut schedule k) (cut schedule (k + 1)),
    range (cut schedule k) ⊆ (s.trace.directions n).history ∧
    (s.trace.directions n).history ⊆ range n ∧
    (s.trace.directions n).movement = movement schedule B k ∧
    (s.trace.directions n).raw.length = batch schedule B k

lemma extend_history {m B K Q b : ℕ} {w : ℝ} {s t : Round m} {schedule : ℕ → Phase m}
    (hs : History s schedule B K) (ht : BlockEffect s t Q b w)
    (hc : Complete schedule B K) (hcut : cut schedule (K + 1) = cut schedule K + Q)
    (hb : b = batch schedule B K) (hw : w = movement schedule B K) :
    History t schedule B (K + 1) := by
  have hcount : t.trace.nextDirection = cut schedule (K + 1) := by rw [ht.count, hs.count, hcut]
  obtain ⟨head, hhead, hm, hh⟩ := ht.mark
  refine ⟨ht.represented, ht.legal, ht.retired, hcount, by simp [hm, hs.markers], ?_, ?_, ?_⟩
  · rw [show t.trace.markers.getLast?.getD 0 = head by simp [hm]]
    exact ⟨hhead, hh.trans (congrArg range hcount)⟩
  · intro k hk
    by_cases h : k ≤ K
    · have hi : k < s.trace.markers.length := by rw [hs.markers]; omega
      have hmem : s.trace.markers[k]?.getD 0 ∈ s.trace.markers := by simp [hi]
      have hb' := markers_bound_run (m + 1) s.events hs.legal
      rw [hs.represented] at hb'
      rw [hm, List.getElem?_append_left hi, ht.extension.oldState _ (hb' _ hmem)]
      exact hs.mark k h
    · have hk' : k = K + 1 := by omega
      rw [hm, hk', show K + 1 = s.trace.markers.length from hs.markers.symm]
      simp only [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      exact hh.trans (congrArg range (by rw [hcount, hs.markers]))
  · intro k hk n hn
    obtain ⟨hnl, hnu⟩ := mem_Ico.mp hn
    by_cases h : k < K
    · have hn' : n < s.trace.nextDirection := by
        rw [hs.count]
        exact hnu.trans_le (cut_le hc (by omega) le_rfl)
      rw [ht.extension.oldDirection _ hn']
      exact hs.direction k h n hn
    · have hk' : k = K := by omega
      subst k
      obtain ⟨ha, hp, _, hm', hb'⟩ := ht.direction n (hs.count.symm ▸ hnl) (hcount.symm ▸ hnu)
      exact ⟨hs.count ▸ ha, hp, hm'.trans hw, hb'.trans hb⟩

lemma rounds_history {m B : ℕ} (layout : Layout m) (schedule : ℕ → Phase m)
    (hB : 0 < B) (K : ℕ) (hc : Complete schedule B K) :
    History (rounds layout B schedule K) schedule B K := by
  induction K with
  | zero =>
    refine ⟨rfl, trivial, by simp [RetiredPast, rounds, Round.initial], rfl, rfl, ?_, ?_, ?_⟩
    · exact ⟨Nat.one_pos, by simp [rounds, Round.initial, cut]⟩
    · intro k hk
      have : k = 0 := by omega
      subst k
      simp [rounds, Round.initial, cut]
    · simp
  | succ k ih =>
    let s := rounds layout B schedule k
    have hc' : Complete schedule B k := fun j hj hl => hc j hj (by omega)
    have hs : History s schedule B k := ih hc'
    have hh := hs.last.2
    rw [← hs.count] at hh
    by_cases h : k = 0
    · subst k
      simp only [rounds, stepRound, ite_true]
      have ht := reset_block (move := 1 / 2) s hB (by norm_num) (by norm_num)
        hs.represented hs.legal hs.retired hs.last.1 hh
      exact extend_history hs ht hc' (by simp [cut]) (by simp [batch]) (by simp [movement])
    · simp only [rounds, stepRound, h, ite_false]
      have hp := hc k (Nat.pos_of_ne_zero h) (by omega)
      have hg := leaf_bounds hB hp
      exact extend_history hs (nested_block layout s (schedule k).arrivals hs.represented hs.legal
        hs.retired hs.last.1 hh hp.1 hg.1 (hg.2.trans (by norm_num)) rfl) hc'
        (by simp [cut, h]) (by simp [batch, h]) (by simp [movement, h])

end LongTails.Proofs.BirchCollectionRetainedQuotaHistory
