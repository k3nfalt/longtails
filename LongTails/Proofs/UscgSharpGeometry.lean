import LongTails.Proofs.MinimaxLmoDescent
import LongTails.Proofs.LaggedAlignment

namespace LongTails.Proofs.UscgSharpGeometry

open LongTails.Setups.UscgConstant
open OracleTemplate.NormBallLMO
open scoped RealInnerProductSpace

variable {d : ℕ} {N : Seminorm ℝ (Space d)} {R : ℝ}

lemma direction_dual {m v : Space d}
    (hmin : ∀ w, N w ≤ 1 → ⟪m, v⟫ ≤ ⟪m, w⟫) :
    ⟪m, v⟫ ≤ -dualNorm N m := by
  have h : dualNorm N m ≤ -⟪m, v⟫ := by
    apply dualNorm_le_of
    intro w hw
    have hh := hmin (-w) (by simpa using hw)
    rw [inner_neg_right] at hh
    linarith
  linarith

lemma alignment_bounds (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) {g m v : Space d}
    (hv : N v ≤ 1) (hmin : ∀ w, N w ≤ 1 → ⟪m, v⟫ ≤ ⟪m, w⟫) :
    0 ≤ dualNorm N g + ⟪g, v⟫ ∧
    dualNorm N g + ⟪g, v⟫ ≤ 2 * dualNorm N g ∧
    dualNorm N g + ⟪g, v⟫ ≤ 2 * dualNorm N (g - m) := by
  have hneg := inner_le_dualNorm hR g (v := -v) (by simpa using hv)
  rw [inner_neg_right] at hneg
  have hpos := inner_le_dualNorm hR g hv
  have he := inner_le_dualNorm hR (g - m) hv
  rw [inner_sub_left] at he
  have hd := direction_dual hmin
  have ht := dualNorm_sub_le hR g m
  constructor
  · linarith
  constructor <;> linarith

lemma scaled_direction {m v : Space d} {c : ℝ} (hc : 0 ≤ c)
    (hmin : ∀ w, N w ≤ 1 → ⟪m, v⟫ ≤ ⟪m, w⟫) :
    ∀ w, N w ≤ 1 → ⟪c • m, v⟫ ≤ ⟪c • m, w⟫ := by
  intro w hw
  simpa only [inner_smul_left, RCLike.conj_to_real] using
    mul_le_mul_of_nonneg_left (hmin w hw) hc

lemma gradient_self_bound (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R)
    (hdef : ∀ x, N x = 0 → x = 0) {f : Space d → ℝ} {L fmin : ℝ}
    (hL : 0 < L) (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, dualNorm N (gradient f x - gradient f y) ≤ L * N (x - y))
    (hlower : ∀ x, fmin ≤ f x) {lmo : Space d → Space d}
    (hlmo : IsBallLMO N 1 lmo) (x : Space d) :
    dualNorm N (gradient f x) ^ 2 ≤ 2 * L * (f x - fmin) := by
  apply LaggedAlignment.self_bound hL
  · intro t ht
    have hd := descent hR hdef hgrad hlip x (x + t • lmo (gradient f x))
    have hv := hlmo.feasible (gradient f x)
    have hn : N (t • lmo (gradient f x)) ≤ t := by
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg ht]
      nlinarith
    have hsq := pow_le_pow_left₀ (apply_nonneg N _) hn 2
    have hm := lmo_dualNorm_eq hR (by norm_num : (0 : ℝ) < 1) hlmo (gradient f x)
    simp only [add_sub_cancel_left, inner_smul_right] at hd
    simp only [one_mul] at hm
    rw [hm] at hd
    have hlo := hlower (x + t • lmo (gradient f x))
    have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ L / 2 by positivity)
    nlinarith
  · exact dualNorm_nonneg hR _

lemma alignment_capped (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R)
    {g m v z b : Space d} {ζ C : ℝ}
    (hnoise : dualNorm N z ≤ ζ * ‖z‖) (hg : dualNorm N g ≤ ζ * C)
    (hv : N v ≤ 1) (hmin : ∀ w, N w ≤ 1 → ⟪m, v⟫ ≤ ⟪m, w⟫)
    (he : m - g = z + b) :
    dualNorm N g + ⟪g, v⟫ ≤ 2 * ζ * min C ‖z‖ + 2 * dualNorm N b := by
  obtain ⟨-, ha, hb⟩ := alignment_bounds (g := g) hR hv hmin
  rw [OracleTemplate.MinimaxLmo.dualNorm_sub_comm hR g m, he] at hb
  have hadd := dualNorm_add_le hR z b
  have hbn := dualNorm_nonneg hR b
  by_cases hc : C ≤ ‖z‖
  · rw [min_eq_left hc]
    nlinarith
  · rw [min_eq_right (le_of_lt (lt_of_not_ge hc))]
    nlinarith

end LongTails.Proofs.UscgSharpGeometry
