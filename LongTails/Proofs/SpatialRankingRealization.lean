import LongTails.Proofs.SpatialRankingDictionary

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpatialRankingRealization

open LongTails.Setups.SpatialRankingLogistic
open LongTails.Proofs.SpatialRankingPixels
open LongTails.Proofs.SpatialRankingDictionary

lemma cov_cross {g h : Bool} (H : g ≠ h) (r : Bool) (a b : Packet) : cov r g h a b = 0 := by
  have he : h = !g := by cases g <;> cases h <;> simp_all
  simp [he, cov, cross_table]

lemma private_le (n : ℕ) (e : Bool) : privateBlock n e ≤ n := by
  cases e <;> simp [privateBlock]

lemma private_ge (n : ℕ) (e : Bool) : n-1 ≤ privateBlock n e := by
  cases e <;> simp [privateBlock]

lemma private_iff {n : ℕ} (hn : 8 ≤ n) (e f : Bool) :
    privateBlock n e = privateBlock n f ↔ e=f := by
  cases e <;> cases f <;> simp [privateBlock, show n ≠ n-1 by omega, show n-1 ≠ n by omega]

lemma private_spine {p : Params} (hd : 32*(p.n+1) ≤ p.d) (r g h e : Bool)
    (a : Packet) (x : ℕ → ℝ) :
    form r (filler p g e) (spine p h a x) = 0 ∧ form r (spine p h a x) (filler p g e) = 0 := by
  simp [filler, form_add_left, form_add_right, form_smul_left, form_smul_right,
    atom_spine hd _ _ _ _ _ _ (private_le _ _), spine_atom hd _ _ _ _ _ _ (private_le _ _),
    Nat.not_lt.mpr (private_ge _ _)]

lemma private_item {p : Params} (hd : 32*(p.n+1) ≤ p.d) (r g h e : Bool) {i : ℕ}
    (hi : 0 < i) (hr : i < p.n) :
    form r (filler p g e) (item p h i) = 0 ∧ form r (item p h i) (filler p g e) = 0 := by
  have hne : privateBlock p.n e ≠ i-1 := by have := private_ge p.n e; omega
  simp [filler, item, form_add_left, form_add_right, form_smul_left, form_smul_right,
    atom_form hd _ _ _ _ _ (private_le _ _) (by omega : i-1 ≤ p.n),
    atom_form hd _ _ _ _ _ (by omega : i-1 ≤ p.n) (private_le _ _), hne, Ne.symm hne]

lemma private_private {p : Params} (hd : 32*(p.n+1) ≤ p.d) (hn : 8 ≤ p.n) (r g h e f : Bool) :
    form r (filler p g e) (filler p h f) = if g=h ∧ e=f then
      if r then (population g).anchorLag else 1-power p.n g else 0 := by
  simp only [filler, form_add_left, form_add_right, form_smul_left, form_smul_right,
    atom_form hd _ _ _ _ _ (private_le _ _) (private_le _ _), private_iff hn]
  by_cases H : g=h
  · subst h
    obtain ⟨_,_,_,_,hcc,hci,hic,hii⟩ := packet_table g r e f
    by_cases E : e=f
    · simp only [E, ite_true, true_and, cov, hcc, hci, hic, hii, Int.cast_zero]
      have hs := remnant_sq hn g
      cases r <;> cases g <;> norm_num [capSign, population, first, second] at * <;> linarith
    · simp [E]
  · simp [H, cov_cross H]

lemma endpoint_form {p : Params} (hd : 32*(p.n+1) ≤ p.d) (hn : 8 ≤ p.n) (r g h e f : Bool) :
    form r (endpoint p g e) (endpoint p h f) =
      if g=h ∧ e=f then if r then (population g).anchorLag else 1 else 0 := by
  simp only [endpoint, form_add_left, form_add_right, (private_spine hd _ _ _ _ _ _).1,
    (private_spine hd _ _ _ _ _ _).2, private_private hd hn, spine_form hd]
  by_cases H : g=h
  · subst h
    by_cases E : e=f
    · subst f
      cases r <;> simp [power, cov, (packet_table g _ e e).2.2.2.1]
    · cases r <;> simp [E, cov, (packet_table g _ e f).2.2.2.1]
  · simp [H, cov_cross H]

lemma item_item {p : Params} (hd : 32*(p.n+1) ≤ p.d) (r g h : Bool) {i j : ℕ}
    (hil : 0 < i) (hir : i < p.n) (hjl : 0 < j) (hjr : j < p.n) :
    form r (item p g i) (item p h j) = if g=h ∧ i=j then
      if r then (population g).itemLag else 1 else 0 := by
  simp only [item, form_smul_left, form_smul_right, atom_form hd _ _ _ _ _
    (by omega : i-1 ≤ p.n) (by omega : j-1 ≤ p.n)]
  by_cases H : g=h
  · subst h
    obtain ⟨hrr,_⟩ := packet_table g r false false
    by_cases E : i=j
    · subst j
      simp only [cov, hrr, ite_true, true_and]
      have hs := width_sq g
      have hp := width_pos g
      cases r <;> cases g <;> norm_num [energy, population, first, second] at * <;>
        field_simp <;> nlinarith
    · simp [E, show i-1 ≠ j-1 by omega]
  · simp [H, cov_cross H]

lemma item_endpoint {p : Params} (hd : 32*(p.n+1) ≤ p.d) (r g h e : Bool) {i : ℕ}
    (hi : 0 < i) (hr : i < p.n) :
    form r (item p g i) (endpoint p h e) =
      if g=h ∧ r ∧ !e then traceValue p.n g i else 0 := by
  rw [endpoint, form_add_right, (private_item hd r h g e hi hr).2, add_zero]
  simp only [item, form_smul_left, atom_spine hd _ _ _ _ _ _ (by omega : i-1 ≤ p.n),
    ite_eq_left (by omega : i-1 < p.n-1), amp, show i-1+1=i by omega]
  by_cases H : g=h
  · subst h
    have hh := (packet_table g r e e).2.1
    have hw := (width_pos g).ne'
    cases e <;> cases r <;> simp [cov, hh, hw, mul_comm]
  · simp [H, cov_cross H]

lemma endpoint_item {p : Params} (hd : 32*(p.n+1) ≤ p.d) (r g h e : Bool) {i : ℕ}
    (hi : 0 < i) (hr : i < p.n) :
    form r (endpoint p g e) (item p h i) =
      if g=h ∧ r ∧ e then -traceValue p.n g i else 0 := by
  rw [endpoint, form_add_left, (private_item hd r g h e hi hr).1, add_zero]
  simp only [item, form_smul_right, spine_atom hd _ _ _ _ _ _ (by omega : i-1 ≤ p.n),
    ite_eq_left (by omega : i-1 < p.n-1), amp, show i-1+1=i by omega]
  by_cases H : g=h
  · subst h
    have hh := (packet_table g r e e).2.2.1
    have hw := (width_pos g).ne'
    cases e <;> cases r <;> simp [cov, hh, hw, mul_comm]
  · simp [H, cov_cross H]

lemma realizes (p : Params) (hn : 8 ≤ p.n) (hd : 32*(p.n+1) ≤ p.d) : Geometry p (dictionary p) := by
  have H (r g h : Bool) (i j : Fin (p.n+1)) :
      form r (dictionary p g i) (dictionary p h j) =
        if g=h then if r then lagEntry p.n g i.val j.val else
          (if i=j then 1 else 0) else 0 := by
    have hi := i.isLt
    have hj := j.isLt
    unfold dictionary
    split_ifs
    all_goals first
      | rw [endpoint_form hd hn]
      | rw [item_item hd _ _ _ (by omega) (by omega) (by omega) (by omega)]
      | rw [endpoint_item hd _ _ _ _ (by omega) (by omega)]
      | rw [item_endpoint hd _ _ _ _ (by omega) (by omega)]
    all_goals try simp only [lagEntry, Fin.ext_iff] at *
    all_goals split_ifs <;> first | omega | simp_all
  constructor
  · intro g h i j
    have hh := H false g h i j
    simp [form, spatialLag] at hh
    rw [hh]
    by_cases he : g=h <;> simp [he]
  · intro g h i j
    exact H true g h i j

end LongTails.Proofs.SpatialRankingRealization
