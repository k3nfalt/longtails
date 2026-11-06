import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

namespace LongTails.Proofs.FiniteRiskMesh

open scoped BigOperators

lemma same_floor_coordinate_close (x y c a : ℝ) (ha : 0 < a)
    (h : Int.floor ((x - c) / a) = Int.floor ((y - c) / a)) :
    |x - y| ≤ a := by
  have hh := Int.abs_sub_lt_one_of_floor_eq_floor h
  have he : (x - c) / a - (y - c) / a = (x - y) / a := by ring
  rw [he, abs_div, abs_of_pos ha] at hh
  exact ((div_lt_one ha).mp hh).le

lemma same_floor_euclidean_close {d : ℕ} (x y c : EuclideanSpace ℝ (Fin d))
    (a : ℝ) (ha : 0 < a)
    (h : ∀ i, Int.floor ((x i - c i) / a) = Int.floor ((y i - c i) / a)) :
    ‖x - y‖ ≤ (d + 1 : ℝ) * a := by
  have hc (i : Fin d) : (x i - y i) ^ 2 ≤ a ^ 2 := by
    have hi := same_floor_coordinate_close (x i) (y i) (c i) a ha (h i)
    have hh := mul_self_le_mul_self (abs_nonneg (x i - y i)) hi
    simpa only [← pow_two, sq_abs] using hh
  have hs : ‖x - y‖ ^ 2 ≤ (d : ℝ) * a ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hc i)
    simpa using hh
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hda : 0 ≤ (d : ℝ) * a ^ 2 := mul_nonneg hd (sq_nonneg a)
  have hmul : (d : ℝ) * a ^ 2 ≤ ((d + 1 : ℝ) * a) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (d : ℝ)) (sq_nonneg a)]
  nlinarith [norm_nonneg (x - y), mul_pos (show (0 : ℝ) < d + 1 by positivity) ha]

lemma finite_cover_of_cells {E C : Type*} [PseudoMetricSpace E] [Fintype C]
    (Q : Set E) (hne : Q.Nonempty) (tag : Q → C) (r : ℝ)
    (hclose : ∀ x y : Q, tag x = tag y → dist x.val y.val ≤ r) :
    ∃ H : Finset E, H.Nonempty ∧ H.card ≤ Fintype.card C ∧
      (∀ x ∈ H, x ∈ Q) ∧ ∀ x ∈ Q, ∃ y ∈ H, dist x y ≤ r := by
  classical
  let C0 := Set.range tag
  let _ : Fintype C0 := Fintype.ofFinite C0
  let p : C0 → Q := fun c => c.property.choose
  have hp (c : C0) : tag (p c) = c.val := c.property.choose_spec
  let H : Finset E := Finset.univ.image (fun c : C0 => (p c).val)
  have hsubset : ∀ x ∈ H, x ∈ Q := by
    intro x hx
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
    exact (p c).property
  have hcover : ∀ x ∈ Q, ∃ y ∈ H, dist x y ≤ r := by
    intro x hx
    let c : C0 := ⟨tag ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    refine ⟨(p c).val, Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩, ?_⟩
    exact hclose ⟨x, hx⟩ (p c) (hp c).symm
  refine ⟨H, ?_, ?_, hsubset, hcover⟩
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hy, _⟩ := hcover x hx
    exact ⟨y, hy⟩
  · exact (Finset.card_image_le).trans (by simpa using Fintype.card_le_of_injective (fun c : C0 => c.val) Subtype.val_injective)

lemma floor_cell_mem (z R a : ℝ) (ha : 0 < a) (hz : |z| ≤ R) :
    Int.floor (z / a) ∈ Finset.Icc (-((Nat.ceil (R / a) + 1 : ℕ) : ℤ))
      ((Nat.ceil (R / a) + 1 : ℕ) : ℤ) := by
  have hlo := Int.floor_le (z / a)
  have hhi := Int.lt_floor_add_one (z / a)
  have hceil := Nat.le_ceil (R / a)
  have hupper : z / a ≤ R / a := div_le_div_of_nonneg_right (le_abs_self z |>.trans hz) ha.le
  have hlower : -(R / a) ≤ z / a := by
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (neg_le_of_abs_le hz) ha.le
  rw [Finset.mem_Icc]
  constructor
  · have hreal : -(Nat.ceil (R / a) + 1 : ℝ) ≤ (Int.floor (z / a) : ℝ) := by
      linarith
    exact_mod_cast hreal
  · have hreal : (Int.floor (z / a) : ℝ) ≤ (Nat.ceil (R / a) + 1 : ℝ) := by
      linarith
    exact_mod_cast hreal

lemma exists_euclidean_mesh {d : ℕ} (Q : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) (R a : ℝ) (ha : 0 < a) (hne : Q.Nonempty)
    (hbound : ∀ x ∈ Q, ‖x - c‖ ≤ R) :
    ∃ H : Finset (EuclideanSpace ℝ (Fin d)), H.Nonempty ∧
      H.card ≤ (2 * (Nat.ceil (R / a) + 1) + 1) ^ d ∧
      (∀ x ∈ H, x ∈ Q) ∧ ∀ x ∈ Q, ∃ y ∈ H, dist x y ≤ (d + 1 : ℝ) * a := by
  classical
  let B : ℕ := Nat.ceil (R / a) + 1
  let I : Finset ℤ := Finset.Icc (-(B : ℤ)) B
  let Cells := Fin d → I
  let tag : Q → Cells := fun x i => ⟨Int.floor ((x.val i - c i) / a), by
    have hcoord := (PiLp.norm_apply_le (x.val - c) i).trans (hbound x.val x.property)
    have habs : |x.val i - c i| ≤ R := by simpa using hcoord
    exact floor_cell_mem _ R a ha habs⟩
  have hclose : ∀ x y : Q, tag x = tag y → dist x.val y.val ≤ (d + 1 : ℝ) * a := by
    intro x y h
    rw [dist_eq_norm]
    apply same_floor_euclidean_close x.val y.val c a ha
    intro i
    exact congrArg Subtype.val (congrFun h i)
  obtain ⟨H, hH, hcard, hsubset, hcover⟩ := finite_cover_of_cells Q hne tag _ hclose
  have hI : Fintype.card I = 2 * B + 1 := by
    simp only [Fintype.card_coe, I, Int.card_Icc]
    omega
  have hCells : Fintype.card Cells = (2 * B + 1) ^ d := by
    simp [Cells, hI]
  refine ⟨H, hH, ?_, hsubset, hcover⟩
  simpa only [hCells, B] using hcard

end LongTails.Proofs.FiniteRiskMesh
