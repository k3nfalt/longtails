import outputs.Algorithms.RennalaSgd
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

open scoped BigOperators

namespace OracleTemplate.Rennala

noncomputable def prefixRate {n : ℕ} (tau : Fin n → ℝ) (m : Fin n) : ℝ :=
  ∑ i : Fin n, if i ≤ m then 1 / tau i else 0

noncomputable def allocationTime {n : ℕ} (tau : Fin n → ℝ) (S : ℕ) (m : Fin n) : ℝ :=
  ((S : ℝ) + (m.val + 1 : ℕ)) / prefixRate tau m

noncomputable def deadline (p : Params) : ℝ :=
  if hn : 0 < p.n then
    96 * Finset.univ.inf' (show (Finset.univ : Finset (Fin p.n)).Nonempty from
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
      (fun m : Fin p.n => (prefixRate p.tau m / (m.val + 1 : ℕ))⁻¹ *
        (p.L * p.Delta / p.eps + p.v * p.L * p.Delta / ((m.val + 1 : ℕ) * p.eps ^ 2)))
  else 0

lemma horizon_bounds (a : ℝ) (ha : 0 ≤ a) :
    (⌊24 * a⌋₊ : ℝ) ≤ 24 * a ∧
    24 * a < (⌊24 * a⌋₊ + 1 : ℕ) ∧
    0 < ⌊24 * a⌋₊ + 1 := by
  refine ⟨Nat.floor_le (by positivity : (0 : ℝ) ≤ 24 * a), ?_, Nat.succ_pos _⟩
  simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (24 * a)


lemma optimal_allocation {n : ℕ} (hn : 0 < n) (tau : Fin n → ℝ)
    (htau : ∀ i, 0 < tau i) (horder : Monotone tau) (S : ℕ) (hS : 0 < S) :
    ∃ j : Fin n,
      (∀ k, allocationTime tau S j ≤ allocationTime tau S k) ∧
      (∀ k, allocationTime tau S k = allocationTime tau S j → j ≤ k) ∧
      tau j < allocationTime tau S j ∧
      let B := fun i : Fin n => if i ≤ j then allocationTime tau S j / tau i - 1 else 0
      (∀ i, 0 ≤ B i) ∧
      (∀ i, i ≤ j → 0 < B i) ∧
      (∑ i, B i) = (S : ℝ) ∧
      (∀ i, 0 < B i → tau i * (1 + B i) ≤ allocationTime tau S j) := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨j0, _, hj0⟩ := Finset.exists_min_image Finset.univ (allocationTime tau S) hne
  let mins := Finset.univ.filter (fun i : Fin n => allocationTime tau S i = allocationTime tau S j0)
  have hmins : mins.Nonempty := ⟨j0, by simp [mins]⟩
  let j := mins.min' hmins
  have hjmem : j ∈ mins := Finset.min'_mem mins hmins
  have hjeq : allocationTime tau S j = allocationTime tau S j0 :=
    (Finset.mem_filter.mp hjmem).2
  have hmin : ∀ k, allocationTime tau S j ≤ allocationTime tau S k := by
    intro k
    rw [hjeq]
    exact hj0 k (Finset.mem_univ _)
  have hsmall : ∀ k, allocationTime tau S k = allocationTime tau S j → j ≤ k := by
    intro k hk
    exact Finset.min'_le mins k (by simp [mins, hk, hjeq])
  have hrate (m : Fin n) : prefixRate tau m = ∑ i ∈ Finset.Iic m, 1 / tau i := by
    unfold prefixRate
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp
  have hratepos (m : Fin n) : 0 < prefixRate tau m := by
    rw [hrate]
    exact Finset.sum_pos' (fun i _ => le_of_lt (one_div_pos.mpr (htau i)))
      ⟨m, Finset.mem_Iic.mpr le_rfl, one_div_pos.mpr (htau m)⟩
  have hprod (m : Fin n) : allocationTime tau S m * prefixRate tau m =
      (S : ℝ) + ((m.val + 1 : ℕ) : ℝ) := by
    exact div_mul_cancel₀ _ (ne_of_gt (hratepos m))
  have hpos : tau j < allocationTime tau S j := by
    by_cases hz : j.val = 0
    · have hset : Finset.Iic j = {j} := by
        ext i
        simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_iff_val_le_val, Fin.ext_iff]
        omega
      have hjrate : prefixRate tau j = 1 / tau j := by rw [hrate, hset]; simp
      have hh : allocationTime tau S j / tau j = (S : ℝ) + 1 := by
        simpa [hjrate, hz, div_eq_mul_inv] using hprod j
      have hsreal : (0 : ℝ) < S := by exact_mod_cast hS
      have hdiv : 1 < allocationTime tau S j / tau j := by linarith
      simpa using (lt_div_iff₀ (htau j)).mp hdiv
    · let k : Fin n := ⟨j.val - 1, by omega⟩
      have hkj : k < j := by change k.val < j.val; dsimp [k]; omega
      have hcard : ((j.val + 1 : ℕ) : ℝ) = ((k.val + 1 : ℕ) : ℝ) + 1 := by
        have hh : j.val + 1 = (k.val + 1) + 1 := by dsimp [k]; omega
        exact_mod_cast hh
      have hstrict : allocationTime tau S j < allocationTime tau S k := by
        rcases lt_or_eq_of_le (hmin k) with hh | hh
        · exact hh
        · exact False.elim ((not_le_of_gt hkj) (hsmall k hh.symm))
      have hset : Finset.Iic j = insert j (Finset.Iic k) := by
        ext i
        simp only [Finset.mem_Iic, Finset.mem_insert, Fin.le_iff_val_le_val, Fin.ext_iff]
        dsimp [k]
        omega
      have hjnot : j ∉ Finset.Iic k := by
        simpa only [Finset.mem_Iic] using not_le_of_gt hkj
      have hsplit : prefixRate tau j = prefixRate tau k + 1 / tau j := by
        rw [hrate j, hset, Finset.sum_insert hjnot, ← hrate k]
        ring
      by_contra hh
      have hle : allocationTime tau S j ≤ tau j := le_of_not_gt hh
      have hpart : allocationTime tau S j * (1 / tau j) ≤ 1 := by
        rw [mul_one_div]
        exact (div_le_iff₀ (htau j)).mpr (by simpa using hle)
      have hm := mul_lt_mul_of_pos_right hstrict (hratepos k)
      have hjprod := hprod j
      have hkprod := hprod k
      rw [hsplit, mul_add, hcard] at hjprod
      linarith
  refine ⟨j, hmin, hsmall, hpos, ?_⟩
  let B := fun i : Fin n => if i ≤ j then allocationTime tau S j / tau i - 1 else 0
  change (∀ i, 0 ≤ B i) ∧ (∀ i, i ≤ j → 0 < B i) ∧
    (∑ i, B i) = (S : ℝ) ∧
    (∀ i, 0 < B i → tau i * (1 + B i) ≤ allocationTime tau S j)
  have hbpos : ∀ i, i ≤ j → 0 < B i := by
    intro i hi
    dsimp [B]
    rw [ite_eq_left hi]
    apply sub_pos.mpr
    apply (lt_div_iff₀ (htau i)).mpr
    simpa using lt_of_le_of_lt (horder hi) hpos
  have hbnonneg : ∀ i, 0 ≤ B i := by
    intro i
    by_cases hi : i ≤ j
    · exact le_of_lt (hbpos i hi)
    · simp [B, hi]
  refine ⟨hbnonneg, hbpos, ?_, ?_⟩
  · calc
      (∑ i, B i) = ∑ i ∈ Finset.Iic j, (allocationTime tau S j / tau i - 1) := by
        dsimp [B]
        rw [← Finset.sum_filter]
        congr 1
        ext i
        simp
      _ = allocationTime tau S j * prefixRate tau j - ((j.val + 1 : ℕ) : ℝ) := by
        rw [Finset.sum_sub_distrib, hrate]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Fin.card_Iic]
        congr 1
        simp_rw [div_eq_mul_inv]
        simp only [one_mul]
        rw [Finset.mul_sum]
      _ = (S : ℝ) := by rw [hprod]; ring
  · intro i hi
    have hij : i ≤ j := by
      by_contra hh
      simp [B, hh] at hi
    have hτ : tau i ≠ 0 := ne_of_gt (htau i)
    apply le_of_eq
    dsimp [B]
    rw [ite_eq_left hij]
    field_simp [hτ]
    <;> ring


lemma rounded_allocation {n : ℕ} (tau : Fin n → ℝ) (htau : ∀ i, 0 < tau i)
    (S : ℕ) (B : Fin n → ℝ) (t : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hsum : (S : ℝ) ≤ ∑ i, B i)
    (htime : ∀ i, 0 < B i → tau i * (1 + B i) ≤ t) :
    S ≤ ∑ i, ⌈B i⌉₊ ∧
    ∀ i, 0 < ⌈B i⌉₊ → tau i * (1 + (⌈B i⌉₊ : ℝ)) ≤ 2 * t := by
  constructor
  · have hsum' : (S : ℝ) ≤ ∑ i, (⌈B i⌉₊ : ℝ) :=
      hsum.trans (Finset.sum_le_sum fun i _ => Nat.le_ceil (B i))
    exact_mod_cast hsum'
  · intro i hi
    have hbi : 0 < B i := Nat.ceil_pos.mp hi
    have hceil := Nat.ceil_lt_add_one (hB i)
    have hround : 1 + (⌈B i⌉₊ : ℝ) ≤ 2 * (1 + B i) := by linarith
    calc
      tau i * (1 + (⌈B i⌉₊ : ℝ)) ≤ tau i * (2 * (1 + B i)) :=
        mul_le_mul_of_nonneg_left hround (le_of_lt (htau i))
      _ = 2 * (tau i * (1 + B i)) := by ring
      _ ≤ 2 * t := mul_le_mul_of_nonneg_left (htime i hbi) (by norm_num)


end OracleTemplate.Rennala
