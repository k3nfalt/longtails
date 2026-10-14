import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.BallProximal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def polyObjective (v : ℕ → E) : ℕ → E → ℝ
  | 0 => fun _ => 0
  | N + 1 => fun x => max (polyObjective v N x) ⟪v N, x⟫

lemma polyObjective_nonneg (v : ℕ → E) (N : ℕ) (x : E) : 0 ≤ polyObjective v N x := by
  induction N with
  | zero => rfl
  | succ N ih => exact le_trans ih (le_max_left _ _)

lemma polyObjective_plane (v : ℕ → E) {N i : ℕ} (hi : i < N) (x : E) :
    ⟪v i, x⟫ ≤ polyObjective v N x := by
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact le_trans (ih hi) (le_max_left _ _)
      · exact le_max_right _ _

lemma polyObjective_upper (v : ℕ → E) {N : ℕ} {x : E} {b : ℝ} (hb : 0 ≤ b)
    (hv : ∀ i < N, ⟪v i, x⟫ ≤ b) : polyObjective v N x ≤ b := by
  induction N with
  | zero => exact hb
  | succ N ih => exact max_le (ih (fun i hi => hv i (by omega))) (hv N (by omega))

lemma polyObjective_zero (v : ℕ → E) (N : ℕ) : polyObjective v N 0 = 0 := by
  apply le_antisymm (polyObjective_upper v le_rfl (by simp)) (polyObjective_nonneg v N 0)

lemma polyObjective_convex (v : ℕ → E) (N : ℕ) :
    ConvexOn ℝ Set.univ (polyObjective v N) := by
  induction N with
  | zero => exact convexOn_const _ convex_univ
  | succ N ih =>
      exact ih.sup ((innerSL ℝ (v N)).toLinearMap.convexOn convex_univ)

lemma polyObjective_continuous (v : ℕ → E) (N : ℕ) : Continuous (polyObjective v N) := by
  induction N with
  | zero => exact continuous_const
  | succ N ih => exact ih.max (continuous_const.inner continuous_id)

lemma polyObjective_support (v : ℕ → E) {N i : ℕ} (hi : i < N) {x : E}
    (he : polyObjective v N x = ⟪v i, x⟫) (z : E) :
    polyObjective v N x + ⟪v i, z - x⟫ ≤ polyObjective v N z := by
  rw [he, inner_sub_right]
  linarith [polyObjective_plane v hi z]

lemma radial_ball_minimum {f : E → ℝ} {x u : E} {a : ℝ}
    (ha : 0 < a) (hu : ‖u‖ = 1)
    (hs : ∀ z, f x + ⟪a • u, z - x⟫ ≤ f z) :
    ∀ z, ‖z - (x + u)‖ ≤ 1 → f x ≤ f z := by
  intro z hz
  have hnorm := real_inner_le_norm u ((x + u) - z)
  rw [hu, norm_sub_rev, one_mul] at hnorm
  have hs' := hs z
  have he : ⟪u, z - x⟫ = 1 - ⟪u, (x + u) - z⟫ := by
    rw [show z - x = u - ((x + u) - z) by module, inner_sub_right,
      real_inner_self_eq_norm_sq, hu]
    norm_num
  rw [real_inner_smul_left, he] at hs'
  have hp := mul_nonneg ha.le (show 0 ≤ 1 - ⟪u, (x + u) - z⟫ by linarith)
  linarith

lemma radial_ball_unique {f : E → ℝ} {x u z : E} {a : ℝ}
    (ha : 0 < a) (hu : ‖u‖ = 1)
    (hs : f x + ⟪a • u, z - x⟫ ≤ f z)
    (hz : ‖z - (x + u)‖ ≤ 1) (hf : f z ≤ f x) : z = x := by
  have he : ⟪u, z - x⟫ = ⟪u, z - (x + u)⟫ + 1 := by
    rw [show z - x = (z - (x + u)) + u by module, inner_add_right,
      real_inner_self_eq_norm_sq, hu]
    norm_num
  rw [real_inner_smul_left, he] at hs
  have hi : ⟪u, z - (x + u)⟫ ≤ -1 := by nlinarith
  have hn : ‖z - (x + u)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (z - (x + u))]
  have hn' : ‖z - x‖ ^ 2 = ‖z - (x + u)‖ ^ 2 + 2 * ⟪u, z - (x + u)⟫ + 1 := by
    rw [show z - x = u + (z - (x + u)) by module, norm_add_sq_real, hu]
    ring
  have hz' : ‖z - x‖ = 0 := by nlinarith [sq_nonneg ‖z - x‖, norm_nonneg (z - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz')

end

end OracleTemplate.BallProximal
