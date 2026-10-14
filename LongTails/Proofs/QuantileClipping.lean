import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OracleTemplate.QuantileClipping

noncomputable def insert {K : ℕ} (b : Fin K → ℝ) (i : Fin K) (v : ℝ) : Fin K → ℝ :=
  Function.update b i (max (b i) v)

noncomputable def cappedMass {K : ℕ} (b : Fin K → ℝ) (A : ℝ) : ℝ :=
  ∑ i, min (b i) A

lemma capped_scalar (x v A : ℝ) :
    min (max x v) A = min x A + max 0 (min v A - min x A) := by
  rcases le_total x v with h | h
  · rw [max_eq_right h]
    have hm : min x A ≤ min v A := min_le_min_right A h
    rw [max_eq_right (sub_nonneg.mpr hm)]
    ring
  · rw [max_eq_left h]
    have hm : min v A ≤ min x A := min_le_min_right A h
    rw [max_eq_left (sub_nonpos.mpr hm)]
    ring

lemma cappedMass_insert {K : ℕ} (b : Fin K → ℝ) (i : Fin K) (v A : ℝ) :
    cappedMass (insert b i v) A =
      cappedMass b A + max 0 (min v A - min (b i) A) := by
  classical
  have hf : (fun j => min (insert b i v j) A) =
      Function.update (fun j => min (b j) A) i (min (max (b i) v) A) := by
    funext j
    by_cases h : j = i
    · subst j
      simp [insert]
    · simp [insert, h]
  unfold cappedMass
  rw [hf, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [capped_scalar, Finset.sdiff_singleton_eq_erase]
  have hs := Finset.sum_erase_add Finset.univ (fun j => min (b j) A) (Finset.mem_univ i)
  linarith

lemma cappedMass_le {K : ℕ} (b : Fin K → ℝ) (A : ℝ) :
    cappedMass b A ≤ K * A := by
  calc
    cappedMass b A ≤ ∑ _ : Fin K, A := Finset.sum_le_sum (fun _ _ => min_le_right _ _)
    _ = K * A := by simp

lemma insert_nonneg {K : ℕ} (b : Fin K → ℝ) (i : Fin K) (v : ℝ)
    (hb : ∀ j, 0 ≤ b j) : ∀ j, 0 ≤ insert b i v j := by
  intro j
  by_cases h : j = i
  · subst j
    simpa [insert] using (hb i).trans (le_max_left (b i) v)
  · simpa [insert, Function.update_of_ne h] using hb j

lemma insert_minimum {K : ℕ} (b : Fin K → ℝ) (i : Fin K) (v : ℝ)
    (hi : ∀ j, b i ≤ b j) : ∀ j, b i ≤ insert b i v j := by
  intro j
  by_cases h : j = i
  · subst j
    simp [insert]
  · simpa [insert, Function.update_of_ne h] using hi j

noncomputable def evolve {K : ℕ} (select : (Fin K → ℝ) → Fin K)
    (v : ℕ → ℝ) : ℕ → Fin K → ℝ
  | 0 => fun _ => 0
  | n + 1 => insert (evolve select v n) (select (evolve select v n)) (v n)

lemma capped_excess_sum {K : ℕ} (select : (Fin K → ℝ) → Fin K)
    (v : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A) (N : ℕ) :
    (∑ n ∈ Finset.range N, max 0 (min (v n) A -
      min (evolve select v n (select (evolve select v n))) A)) =
        cappedMass (evolve select v N) A := by
  induction N with
  | zero => simp [evolve, cappedMass, min_eq_left hA]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, evolve, cappedMass_insert]

lemma capped_excess_sum_le {K : ℕ} (select : (Fin K → ℝ) → Fin K)
    (v : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A) (N : ℕ) :
    (∑ n ∈ Finset.range N, max 0 (min (v n) A -
      min (evolve select v n (select (evolve select v n))) A)) ≤ K * A := by
  rw [capped_excess_sum select v hA N]
  exact cappedMass_le _ _

noncomputable def exceedCount {K : ℕ} (b : Fin K → ℝ) (A : ℝ) : ℕ :=
  ∑ i, if A < b i then 1 else 0

lemma exceedCount_insert_le {K : ℕ} (b : Fin K → ℝ) (i : Fin K) (v A : ℝ) :
    exceedCount (insert b i v) A ≤ exceedCount b A + if A < v then 1 else 0 := by
  classical
  have hf : (fun j => if A < insert b i v j then 1 else 0 : Fin K → ℕ) =
      Function.update (fun j => if A < b j then 1 else 0) i
        (if A < max (b i) v then 1 else 0) := by
    funext j
    by_cases h : j = i
    · subst j
      simp [insert]
    · simp [insert, h]
  unfold exceedCount
  rw [hf, Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have hs := Finset.sum_erase_add Finset.univ
    (fun j => if A < b j then (1 : ℕ) else 0) (Finset.mem_univ i)
  have hi : (if A < max (b i) v then (1 : ℕ) else 0) ≤
      (if A < b i then 1 else 0) + (if A < v then 1 else 0) := by
    by_cases hx : A < b i <;> by_cases hv : A < v <;> simp [lt_max_iff, hx, hv]
  omega

lemma evolve_exceedCount_le {K : ℕ} (select : (Fin K → ℝ) → Fin K)
    (v : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A) (N : ℕ) :
    exceedCount (evolve select v N) A ≤
      ∑ n ∈ Finset.range N, if A < v n then 1 else 0 := by
  induction N with
  | zero => simp [exceedCount, evolve, not_lt.mpr hA]
  | succ n ih =>
    rw [evolve, Finset.sum_range_succ]
    exact (exceedCount_insert_le _ _ _ _).trans (Nat.add_le_add_right ih _)

lemma exceedCount_eq_of_lt_min {K : ℕ} (b : Fin K → ℝ) (i : Fin K)
    (hi : ∀ j, b i ≤ b j) {A : ℝ} (hA : A < b i) : exceedCount b A = K := by
  have h : ∀ j, A < b j := fun j => hA.trans_le (hi j)
  simp [exceedCount, h]

lemma weighted_excess {t Q : ℝ} (ht : 0 < t) (hQ : 0 ≤ Q) (z r : ℝ) :
    t * max 0 (z - (r + Q / t)) = max 0 (t * max 0 (z - r) - Q) := by
  rw [mul_max_of_nonneg _ _ ht.le, mul_zero]
  have he : t * (z - (r + Q / t)) = t * (z - r) - Q := by
    field_simp
    ring
  rw [he]
  by_cases hz : z - r ≤ 0
  · have hn : t * (z - r) - Q ≤ 0 := by
      have h := mul_nonpos_of_nonneg_of_nonpos ht.le hz
      linarith
    simp [max_eq_left hz, max_eq_left hn, max_eq_left (neg_nonpos.mpr hQ)]
  · rw [max_eq_right (le_of_not_ge hz)]

lemma excess_split (v Q A : ℝ) :
    max 0 (v - Q) ≤ max 0 (min v A - min Q A) + max 0 (v - A) := by
  rcases le_total v A with hv | hv
  · rcases le_total Q A with hQ | hQ
    · simp [min_eq_left hv, min_eq_left hQ, max_eq_left (sub_nonpos.mpr hv)]
    · have h : v - Q ≤ 0 := by linarith
      simp [min_eq_left hv, min_eq_right hQ, max_eq_left (sub_nonpos.mpr hv), max_eq_left h]
  · rcases le_total Q A with hQ | hQ
    · have h : 0 ≤ v - Q := by linarith
      rw [min_eq_right hv, min_eq_left hQ, max_eq_right h,
        max_eq_right (sub_nonneg.mpr hQ), max_eq_right (sub_nonneg.mpr hv)]
      linarith
    · rw [min_eq_right hv, min_eq_right hQ, sub_self, max_self, zero_add,
        max_eq_right (sub_nonneg.mpr hv)]
      exact max_le (sub_nonneg.mpr hv) (by linarith)

end OracleTemplate.QuantileClipping
