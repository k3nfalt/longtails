import LongTails.Proofs.SpikedSoftCutSelection

open scoped BigOperators

noncomputable section

namespace LongTails.Proofs.EuclideanGridNet

abbrev Point (k : ℕ) := EuclideanSpace ℝ (Fin k)

def gridPoint (k : ℕ) (a : Fin k → Fin (16 * k + 1)) : Point k :=
  WithLp.toLp 2 (fun i => 2 * LongTails.Algorithms.SpikedSoftCut.gridCoefficients a i - 1)

def grid (k : ℕ) : Finset (Point k) :=
  ((Finset.univ : Finset (Fin k → Fin (16 * k + 1))).image (gridPoint k)).filter (fun x => ‖x‖ ≤ 2)

lemma grid_card (k : ℕ) : (grid k).card ≤ (16 * k + 1) ^ k := by
  classical
  apply (Finset.card_filter_le _ _).trans
  exact (Finset.card_image_le).trans_eq (by simp)

lemma grid_norm (k : ℕ) (u : Point k) (hu : u ∈ grid k) : ‖u‖ ≤ 2 :=
  (Finset.mem_filter.mp hu).2

lemma grid_covers_unit (k : ℕ) (x : Point k) (hx : ‖x‖ = 1) :
    ∃ u ∈ grid k, ‖x - u‖ ≤ 1 / 8 := by
  classical
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst k
    have hzero : x = 0 := Subsingleton.elim _ _
    simp [hzero] at hx
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn : 0 < 16 * k := by omega
  let θ : Fin k → ℝ := fun i => (x i + 1) / 2
  have hθ (i : Fin k) : 0 ≤ θ i ∧ θ i ≤ 1 := by
    have h := PiLp.norm_apply_le x i
    rw [hx, Real.norm_eq_abs] at h
    have hh := abs_le.mp h
    dsimp [θ]
    constructor <;> linarith
  obtain ⟨a, ha⟩ := SpikedSoftCutSelection.exists_grid_approximation hn θ hθ
  let u := gridPoint k a
  have hcoord (i : Fin k) : |(x - u) i| ≤ 1 / (8 * (k : ℝ)) := by
    have h := ha i
    have heq : (x - u) i = -2 *
        (LongTails.Algorithms.SpikedSoftCut.gridCoefficients a i - θ i) := by
      change x i - (2 * LongTails.Algorithms.SpikedSoftCut.gridCoefficients a i - 1) = _
      dsimp [θ]
      ring
    rw [heq, abs_mul]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hb := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
    push_cast at hb
    have hc : (2 : ℝ) * (1 / (16 * (k : ℝ))) = 1 / (8 * (k : ℝ)) := by ring
    exact hb.trans_eq hc
  have hsq : ‖x - u‖ ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i, ((x - u) i) ^ 2 ≤ ∑ _i : Fin k, (1 / (8 * (k : ℝ))) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := hcoord i
        have hnonneg : 0 ≤ 1 / (8 * (k : ℝ)) := by positivity
        nlinarith [sq_abs ((x - u) i), abs_nonneg ((x - u) i)]
      _ = (k : ℝ) * (1 / (8 * (k : ℝ))) ^ 2 := by simp
      _ ≤ (1 / 8 : ℝ) ^ 2 := by
        have hk0 : (k : ℝ) ≠ 0 := by positivity
        field_simp
        nlinarith
  have hclose : ‖x - u‖ ≤ 1 / 8 := by nlinarith [norm_nonneg (x - u)]
  have hunorm : ‖u‖ ≤ 2 := by
    have h := norm_add_le (u - x) x
    rw [sub_add_cancel, norm_sub_rev, hx] at h
    linarith
  refine ⟨u, Finset.mem_filter.mpr ⟨?_, hunorm⟩, hclose⟩
  exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩

end LongTails.Proofs.EuclideanGridNet
