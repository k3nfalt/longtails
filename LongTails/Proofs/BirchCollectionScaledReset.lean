import LongTails.Algorithms.BirchCollectionProfiles
import LongTails.Proofs.BirchCollectionReset
import LongTails.Proofs.BirchCollectionOrdering

namespace LongTails.Proofs.BirchCollectionScaledReset

open Finset
open LongTails.Algorithms.BirchCollectionProfiles
open LongTails.Setups.BirchCollections
open LongTails.Proofs.BirchCollectionOrdering
open LongTails.Proofs.BirchCollectionStructure
open LongTails.Proofs.BirchCollectionReset

lemma controls_valid (lower upper window waste : ℕ) (hl : 0 < lower) (hu : lower ≤ upper) :
    (controls lower upper window waste).Valid := by
  have hcN : 0 < divisor upper window := by unfold divisor; omega
  have hc : (0 : ℝ) < divisor upper window := Nat.cast_pos.mpr hcN
  have hlR : (0 : ℝ) < lower := Nat.cast_pos.mpr hl
  have huR : (lower : ℝ) ≤ upper := by exact_mod_cast hu
  have hUC : (upper : ℝ) ≤ divisor upper window := by
    exact_mod_cast (show upper ≤ divisor upper window by unfold divisor; omega)
  refine ⟨div_pos hlR hc, div_le_div_of_nonneg_right huR hc.le, (div_le_one hc).2 hUC, ?_, hc⟩
  change (upper : ℝ) / divisor upper window ≤
    (upper : ℝ) / lower * ((lower : ℝ) / divisor upper window)
  have hh : (upper : ℝ) / lower * ((lower : ℝ) / divisor upper window) =
      (upper : ℝ) / divisor upper window := by field_simp
  rw [hh]

lemma packetControls_valid (lower upper window waste factor : ℕ) (hl : 0 < lower) (hu : lower ≤ upper)
    (hf : 0 < factor) : (packetControls lower upper window waste factor).Valid := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := controls_valid lower upper window waste hl hu
  exact ⟨h₁, h₂, h₃, h₄, mul_pos h₅ (Nat.cast_pos.mpr hf)⟩

@[simp] lemma packetControls_one (lower upper window D : ℕ) :
    packetControls lower upper window D 1 = controls lower upper window D := by
  simp [packetControls, controls]

lemma packet_window_structural (workers K B lower upper window D factor : ℕ) (events : List Event)
    (o : LongTails.Setups.BirchCollections.Ordering)
    (hv : ValidFrom workers {} events) (ho : o.Valid (run events) K)
    (hl : 0 < lower) (hu : lower ≤ upper) (hf : 0 < factor)
    (hp : ∀ n, n < o.labels.length →
      o.frontier n ≤ n ∧ n - o.frontier n ≤ window ∧
        range (o.frontier n) ⊆ o.history (run events) n)
    (hblocks : ∀ k, k < K → lower ≤ o.cut (k + 1) - o.cut k ∧
      o.cut (k + 1) - o.cut k ≤ upper)
    (hrefresh : ∀ n, n < o.labels.length → o.refresh (run events) n = 1)
    (hmovement : ∀ n, n < o.labels.length →
      o.movement (run events) n = 1 / (divisor upper window : ℝ))
    (hsize : ∀ n, n < o.labels.length → ((run events).directions (o.label n)).raw.length = B * factor)
    (hbudget : (run events).nextRaw ≤ (B * factor) * o.labels.length + D) :
    Structural (run events) (resetOrdering o) (packetControls lower upper window D factor) K B := by
  let s := run events
  let C : ℝ := divisor upper window
  have hcN : 0 < divisor upper window := by unfold divisor; omega
  have hc : 0 < C := Nat.cast_pos.mpr hcN
  have hwindow : (4 : ℝ) * window ≤ C := by
    change (4 : ℝ) * window ≤ divisor upper window
    exact_mod_cast (show 4 * window ≤ divisor upper window by unfold divisor; omega)
  have hcut := ho.2.2.2.2.2.1
  have hend := ho.2.2.2.2.1
  have hcut_le : ∀ k ≤ K, o.cut k ≤ o.labels.length := by
    have hmono : MonotoneOn o.cut (Set.Iic K) := by
      apply monotoneOn_of_le_succ
      · exact Set.ordConnected_Iic
      · intro j _ _ hj
        exact (hcut j (Set.mem_Iic.mp hj)).le
    intro k hk
    rw [← hend]
    exact hmono (Set.mem_Iic.mpr hk) (Set.mem_Iic.mpr le_rfl) hk
  have hsum (a b : ℕ) (hb : b ≤ o.labels.length) :
      ∑ n ∈ Ico a b, o.movement s n = ((b - a : ℕ) : ℝ) / C := by
    calc
      _ = ∑ _ ∈ Ico a b, (1 : ℝ) / C :=
        sum_congr rfl fun n hn => hmovement n ((mem_Ico.mp hn).2.trans_le hb)
      _ = _ := by simp [Nat.card_Ico, div_eq_mul_inv]
  have hraw := rawLedger_run workers events hv
  have hcompleted := completedLedger_run workers events hv
  have hcard (n : ℕ) (hn : n < o.labels.length) : (o.raw s n).card = B * factor := by
    have hlabel := ho.2.2.2.2.2.2.1 n hn
    have hnd := (completed_raw s hraw hcompleted (o.label n) hlabel).1
    rw [Ordering.raw, List.toFinset_card_of_nodup hnd]
    exact hsize n hn
  have hledger := ordering_raw_ledger s o K hraw hcompleted ho
  have hsumRaw : (∑ n ∈ range o.labels.length, (o.raw s n).card) = (B * factor) * o.labels.length := by
    calc
      _ = ∑ _ ∈ range o.labels.length, B * factor := sum_congr rfl fun n hn => hcard n (mem_range.mp hn)
      _ = _ := by simp [Nat.mul_comm]
  have hwaste : s.nextRaw - ((range o.labels.length).biUnion (o.raw s)).card ≤ D := by
    rw [hsumRaw] at hledger
    change s.nextRaw ≤ (B * factor) * o.labels.length + D at hbudget
    omega
  refine reset_structural s o (packetControls lower upper window D factor) K B ho
    (packetControls_valid lower upper window D factor hl hu hf) hrefresh ?_ ?_ ?_ ?_ ?_ hwaste
  · intro n hn
    obtain ⟨h₁, h₂, h₃⟩ := hp n hn
    refine ⟨h₁, h₃, ?_⟩
    rw [hsum _ _ hn.le]
    apply (div_le_iff₀ hc).2
    have hh : ((n - o.frontier n : ℕ) : ℝ) ≤ window := by exact_mod_cast h₂
    linarith
  · intro k hk
    rw [hsum _ _ (hcut_le (k + 1) hk)]
    apply div_le_div_of_nonneg_right _ hc.le
    exact_mod_cast (hblocks k hk).1
  · intro k hk
    rw [hsum _ _ (hcut_le (k + 1) hk)]
    apply div_le_div_of_nonneg_right _ hc.le
    exact_mod_cast (hblocks k hk).2
  · intro n hn
    rw [hcard n hn]
    exact Nat.le_mul_of_pos_right B hf
  · intro n hn
    rw [hcard n hn, hmovement n hn]
    change ((B * factor : ℕ) : ℝ) ≤ (B : ℝ) * (C * factor) * (1 / C)
    have he : (B : ℝ) * (C * factor) * (1 / C) = ((B * factor : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [he]

lemma window_structural (workers K B lower upper window D : ℕ) (events : List Event)
    (o : LongTails.Setups.BirchCollections.Ordering)
    (hv : ValidFrom workers {} events) (ho : o.Valid (run events) K)
    (hl : 0 < lower) (hu : lower ≤ upper)
    (hp : ∀ n, n < o.labels.length →
      o.frontier n ≤ n ∧ n - o.frontier n ≤ window ∧
        range (o.frontier n) ⊆ o.history (run events) n)
    (hblocks : ∀ k, k < K → lower ≤ o.cut (k + 1) - o.cut k ∧
      o.cut (k + 1) - o.cut k ≤ upper)
    (hrefresh : ∀ n, n < o.labels.length → o.refresh (run events) n = 1)
    (hmovement : ∀ n, n < o.labels.length →
      o.movement (run events) n = 1 / (divisor upper window : ℝ))
    (hsize : ∀ n, n < o.labels.length → ((run events).directions (o.label n)).raw.length = B)
    (hbudget : (run events).nextRaw ≤ B * o.labels.length + D) :
    Structural (run events) (resetOrdering o) (controls lower upper window D) K B := by
  have h := packet_window_structural workers K B lower upper window D 1 events o hv ho hl hu
    Nat.one_pos hp hblocks hrefresh hmovement (by simpa only [Nat.mul_one] using hsize)
    (by simpa only [Nat.mul_one] using hbudget)
  simpa only [packetControls_one] using h

end LongTails.Proofs.BirchCollectionScaledReset
