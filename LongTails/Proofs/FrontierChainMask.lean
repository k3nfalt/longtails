import LongTails.Proofs.FrontierChainGeometry
import Mathlib.Topology.MetricSpace.Lipschitz

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.FrontierChainMask

open FrontierChain FrontierChainProfiles

noncomputable def cutoff (t : ℝ) : ℝ := min 1 (max 0 (2 - 4 * |t|))

lemma cutoff_bounds (t : ℝ) : 0 ≤ cutoff t ∧ cutoff t ≤ 1 := by
  exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

lemma cutoff_zero {t : ℝ} (h : 1 / 2 ≤ |t|) : cutoff t = 0 := by
  simp [cutoff, max_eq_left (by linarith : 2 - 4 * |t| ≤ 0)]

lemma cutoff_one {t : ℝ} (h : |t| ≤ 1 / 4) : cutoff t = 1 := by
  apply min_eq_left
  exact (show 1 ≤ 2 - 4 * |t| by linarith).trans (le_max_right _ _)

lemma cutoff_lipschitz (x y : ℝ) : |cutoff x - cutoff y| ≤ 4 * |x - y| := by
  have h1 := abs_max_sub_max_le_max (0 : ℝ) (2 - 4 * |x|) 0 (2 - 4 * |y|)
  have h2 := abs_min_sub_min_le_max (1 : ℝ) (max 0 (2 - 4 * |x|)) 1 (max 0 (2 - 4 * |y|))
  simp only [sub_self, abs_zero] at h1 h2
  rw [max_eq_right (abs_nonneg ((2 - 4 * |x|) - (2 - 4 * |y|)))] at h1
  rw [max_eq_right (abs_nonneg (max 0 (2 - 4 * |x|) - max 0 (2 - 4 * |y|)))] at h2
  have h3 : |(2 - 4 * |x|) - (2 - 4 * |y|)| = 4 * |(|x| - |y|)| := by
    rw [show (2 - 4 * |x|) - (2 - 4 * |y|) = -4 * (|x| - |y|) by ring, abs_mul]
    norm_num
  have h4 := abs_abs_sub_abs_le_abs_sub x y
  dsimp [cutoff]
  rw [h3] at h1
  linarith

variable {d k : ℕ}

noncomputable def mask (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) (i : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j : Fin (k + 1) => if i ≤ j.val then cutoff (x (π j)) else 1)

lemma mask_bounds (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) (i : ℕ) :
    0 ≤ mask π x i ∧ mask π x i ≤ 1 := by
  classical
  constructor
  · apply Finset.le_inf'
    intro j _
    split_ifs
    · exact (cutoff_bounds _).1
    · norm_num
  · have h := Finset.inf'_le (fun j : Fin (k + 1) => if i ≤ j.val then cutoff (x (π j)) else 1)
      (Finset.mem_univ (0 : Fin (k + 1)))
    apply h.trans
    split_ifs
    · exact (cutoff_bounds _).2
    · exact le_rfl

lemma mask_zero (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (i : ℕ) (j : Fin (k + 1)) (hij : i ≤ j.val) (hj : 1 / 2 ≤ |x (π j)|) : mask π x i = 0 := by
  apply le_antisymm _ (mask_bounds π x i).1
  have h := Finset.inf'_le (fun j : Fin (k + 1) => if i ≤ j.val then cutoff (x (π j)) else 1)
    (Finset.mem_univ j)
  simpa only [mask, ite_eq_left hij, cutoff_zero hj] using h

lemma mask_one (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (i : ℕ) (h : ∀ j : Fin (k + 1), i ≤ j.val → |x (π j)| ≤ 1 / 4) : mask π x i = 1 := by
  apply le_antisymm (mask_bounds π x i).2
  apply Finset.le_inf'
  intro j _
  split_ifs with hj
  · rw [cutoff_one (h j hj)]
  · exact le_rfl

lemma mask_lipschitz (π : Fin (k + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d))
    (i : ℕ) : |mask π x i - mask π y i| ≤ 4 * ‖x - y‖ := by
  classical
  have hdir (x y : EuclideanSpace ℝ (Fin d)) : mask π x i ≤ mask π y i + 4 * ‖x - y‖ := by
    obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun j : Fin (k + 1) => if i ≤ j.val then cutoff (y (π j)) else 1)
    have hx := Finset.inf'_le
      (fun j : Fin (k + 1) => if i ≤ j.val then cutoff (x (π j)) else 1) hj
    change mask π y i = _ at he
    rw [he]
    apply hx.trans
    split_ifs
    · have hc := cutoff_lipschitz (x (π j)) (y (π j))
      have hn : |x (π j) - y (π j)| ≤ ‖x - y‖ := by
        simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x - y) (π j)
      have hs := le_abs_self (cutoff (x (π j)) - cutoff (y (π j)))
      linarith
    · have hn := norm_nonneg (x - y)
      linarith
  have hxy := hdir x y
  have hyx := hdir y x
  rw [norm_sub_rev y x] at hyx
  rw [abs_le]
  constructor <;> linarith

lemma mask_prefix (π π' : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (i r : ℕ) (hπ : ∀ j : Fin (k + 1), j.val < r → π j = π' j)
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4)
    (hx' : ∀ j : Fin (k + 1), r ≤ j.val → |x (π' j)| ≤ 1 / 4) :
    mask π x i = mask π' x i := by
  unfold mask
  congr 1
  funext j
  split_ifs
  · by_cases hj : j.val < r
    · rw [hπ j hj]
    · rw [cutoff_one (hx j (by omega)), cutoff_one (hx' j (by omega))]
  · rfl

end LongTails.Proofs.FrontierChainMask
