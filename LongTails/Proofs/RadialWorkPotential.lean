import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace LongTails.Proofs.RadialWorkPotential

noncomputable def occupied (l h r : ℝ) : ℝ := max (r-l) 0 - max (r-h) 0

lemma occupied_mono {l h x y : ℝ} (hlh : l ≤ h) (hxy : x ≤ y) :
    occupied l h x ≤ occupied l h y := by
  simp only [occupied, max_def]
  split_ifs <;> linarith

lemma occupied_bounds {l h r : ℝ} (hlh : l ≤ h) :
    0 ≤ occupied l h r ∧ occupied l h r ≤ h-l := by
  simp only [occupied, max_def]
  split_ifs <;> constructor <;> linarith

lemma occupied_equal {l h x y : ℝ} (hlh : l ≤ h) (hxy : x ≤ y)
    (hne : y ≤ l ∨ h ≤ x) : occupied l h x = occupied l h y := by
  rcases hne with h | h <;> simp only [occupied, max_def] <;> split_ifs <;> linarith

lemma occupied_sum (edge : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    ∑ j ∈ Finset.range n, occupied (edge j) (edge (j+1)) r =
      max (r-edge 0) 0 - max (r-edge n) 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; unfold occupied; ring

noncomputable def clock (edge speed : ℕ → ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, occupied (edge j) (edge (j+1)) r / speed j

lemma clock_mono (edge speed : ℕ → ℝ) (n : ℕ)
    (he : Monotone edge) (hv : ∀ j < n, 0 < speed j) : Monotone (clock edge speed n) := by
  intro x y hxy
  exact Finset.sum_le_sum fun j hj => div_le_div_of_nonneg_right
    (occupied_mono (he (Nat.le_succ j)) hxy) (hv j (Finset.mem_range.mp hj)).le

lemma clock_step (edge speed : ℕ → ℝ) (n : ℕ) {r u : ℝ}
    (he : Monotone edge) (hv : ∀ j < n, 0 < speed j)
    (hlo : edge 0 ≤ r) (hhi : r+u ≤ edge n) (hu : 0 < u)
    (hc : ∀ j < n, edge j < r+u → r < edge (j+1) → speed j ≤ u) :
    clock edge speed n r + 1 ≤ clock edge speed n (r+u) := by
  have hsum : (∑ j ∈ Finset.range n, (occupied (edge j) (edge (j+1)) (r+u) -
      occupied (edge j) (edge (j+1)) r) / u) = 1 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, occupied_sum, occupied_sum]
    rw [max_eq_left (by linarith : 0 ≤ r+u-edge 0), max_eq_right (by linarith : r+u-edge n ≤ 0),
      max_eq_left (by linarith : 0 ≤ r-edge 0), max_eq_right (by linarith : r-edge n ≤ 0)]
    field_simp
    ring
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      (occupied (edge j) (edge (j+1)) (r+u)-occupied (edge j) (edge (j+1)) r)/u ≤
      occupied (edge j) (edge (j+1)) (r+u)/speed j - occupied (edge j) (edge (j+1)) r/speed j := by
    rw [← sub_div]
    by_cases hl : edge j < r+u
    · by_cases hh : r < edge (j+1)
      · exact div_le_div_of_nonneg_left
          (sub_nonneg.mpr (occupied_mono (he (Nat.le_succ j)) (by linarith)))
          (hv j (Finset.mem_range.mp hj)) (hc j (Finset.mem_range.mp hj) hl hh)
      · rw [← occupied_equal (he (Nat.le_succ j)) (by linarith : r ≤ r+u)
          (Or.inr (le_of_not_gt hh))]
        simp
    · rw [← occupied_equal (he (Nat.le_succ j)) (by linarith : r ≤ r+u)
        (Or.inl (le_of_not_gt hl))]
      simp
  have h := Finset.sum_le_sum hterm
  rw [hsum, Finset.sum_sub_distrib] at h
  dsimp only [clock]
  linarith

lemma clock_strict {edge speed : ℕ → ℝ} {n : ℕ} (he : Monotone edge)
    (hv : ∀ j < n, 0 < speed j) {r : ℝ} (hlo : edge 0 ≤ r) (hhi : r < edge n) :
    clock edge speed n r < ∑ j ∈ Finset.range n, (edge (j+1) - edge j) / speed j := by
  have h (j : ℕ) : occupied (edge j) (edge (j+1)) r ≤ edge (j+1)-edge j :=
    (occupied_bounds (he (Nat.le_succ j))).2
  have hex : ∃ j ∈ Finset.range n, occupied (edge j) (edge (j+1)) r < edge (j+1)-edge j := by
    by_contra! hn
    have hsum := Finset.sum_congr rfl fun j hj => le_antisymm (h j) (hn j hj)
    rw [occupied_sum, max_eq_left (by linarith : 0 ≤ r-edge 0),
      max_eq_right (by linarith : r-edge n ≤ 0)] at hsum
    have htele (k : ℕ) : ∑ j ∈ Finset.range k, (edge (j+1)-edge j) = edge k-edge 0 := by
      induction k with
      | zero => simp
      | succ k ih => rw [Finset.sum_range_succ, ih]; ring
    rw [htele] at hsum
    linarith
  obtain ⟨j,hj,hj'⟩ := hex
  exact Finset.sum_lt_sum (fun i hi => div_le_div_of_nonneg_right (h i) (hv i (Finset.mem_range.mp hi)).le)
    ⟨j,hj,div_lt_div_of_pos_right hj' (hv j (Finset.mem_range.mp hj))⟩

lemma first_fit (R : ℕ → ℝ) (fit : ℕ → Prop) (edge speed : ℕ → ℝ) (n : ℕ)
    (he : Monotone edge) (hv : ∀ j < n, 0 < speed j) (hlo : edge 0 ≤ R 0) :
    let K := ⌈∑ j ∈ Finset.range n, (edge (j+1)-edge j)/speed j⌉₊
    (∀ t ≤ K, edge n ≤ R t → fit t) →
    (∀ t < K, ¬fit t → ∃ u > 0, R t+u ≤ R (t+1) ∧
      ∀ j < n, edge j < R t+u → R t < edge (j+1) → speed j ≤ u) →
    ∃ t ≤ K, fit t := by
  intro K hgate hstep
  by_contra! hn
  have hr (t : ℕ) (ht : t ≤ K) : R t < edge n := lt_of_not_ge (fun h => hn t ht (hgate t ht h))
  have hp (t : ℕ) (ht : t ≤ K) : edge 0 ≤ R t ∧ (t : ℝ) ≤ clock edge speed n (R t) := by
    induction t with
    | zero =>
      refine ⟨hlo, ?_⟩
      simp only [Nat.cast_zero]
      exact Finset.sum_nonneg fun j hj => div_nonneg
        (occupied_bounds (he (Nat.le_succ j))).1 (hv j (Finset.mem_range.mp hj)).le
    | succ t ih =>
      obtain ⟨u,hu,hreach,h⟩ := hstep t (by omega) (hn t (by omega))
      obtain ⟨hl,hi⟩ := ih (by omega)
      have hg := clock_step edge speed n he hv hl (hreach.trans (hr (t+1) ht).le) hu h
      have hm := clock_mono edge speed n he hv hreach
      exact ⟨by linarith, by rw [Nat.cast_succ]; linarith⟩
  obtain ⟨hl,hi⟩ := hp K le_rfl
  have hs := clock_strict he hv hl (hr K le_rfl)
  have hceil : (∑ j ∈ Finset.range n, (edge (j+1)-edge j)/speed j) ≤ (K : ℝ) := Nat.le_ceil _
  linarith

end LongTails.Proofs.RadialWorkPotential
