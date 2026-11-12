import LongTails.Proofs.GeneralizedMirrorGeometry
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.NNNorm

namespace LongTails.Proofs.GeneralizedMirrorSmoothness

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V]

lemma local_bound {F : E → V} {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hc : Continuous F)
    (hgl : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (L0 + L1 * M) * ‖x - y‖)
    (x y : E) (hd : L1 * ‖x - y‖ ≤ 1) :
    ‖F x - F y‖ * (1 - L1 * ‖x - y‖) ≤ (L0 + L1 * ‖F x‖) * ‖x - y‖ := by
  have hcont : ContinuousOn (fun θ : ℝ => ‖F (x + θ • (y - x))‖) (Set.Icc 0 1) :=
    (hc.comp (by fun_prop)).norm.continuousOn
  obtain ⟨θs, hθs, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one) hcont
  have hle : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖F (x + θ • (y - x))‖ ≤ ‖F (x + θs • (y - x))‖ := fun θ hθ => hmax hθ
  have h1 := hgl x (x + θs • (y - x)) ‖F (x + θs • (y - x))‖ (by
    intro θ hθ
    have he : x + θ • (x + θs • (y - x) - x) = x + (θ * θs) • (y - x) := by
      rw [add_sub_cancel_left, smul_smul]
    rw [he]
    exact hle _ ⟨mul_nonneg hθ.1 hθs.1, by nlinarith [hθ.1, hθ.2, hθs.1, hθs.2]⟩)
  have h2 := hgl x y ‖F (x + θs • (y - x))‖ hle
  have hxz : ‖x - (x + θs • (y - x))‖ ≤ ‖x - y‖ := by
    rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθs.1,
      norm_sub_rev y x]
    exact mul_le_of_le_one_left (norm_nonneg _) hθs.2
  have hins := norm_le_insert (F x) (F (x + θs • (y - x)))
  have hM : 0 ≤ ‖F (x + θs • (y - x))‖ := norm_nonneg _
  generalize ‖F (x + θs • (y - x))‖ = M at h1 h2 hins hM
  have hd0 : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hc0 : 0 ≤ L0 + L1 * M := by positivity
  have h3 : M ≤ ‖F x‖ + (L0 + L1 * M) * ‖x - y‖ := by
    have := h1.trans (mul_le_mul_of_nonneg_left hxz hc0)
    linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hL1
  have h5 : (L0 + L1 * M) * (1 - L1 * ‖x - y‖) ≤ L0 + L1 * ‖F x‖ := by nlinarith
  have h6 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr hd)
  have h7 := mul_le_mul_of_nonneg_right h5 hd0
  nlinarith

lemma local_difference {F : E → V} {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hc : Continuous F)
    (hgl : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (L0 + L1 * M) * ‖x - y‖)
    (x y : E) (hd : L1 * ‖x - y‖ ≤ 1 / 2) :
    ‖F x - F y‖ ≤ 2 * (L0 + L1 * ‖F x‖) * ‖x - y‖ := by
  have h := local_bound hL0 hL1 hc hgl x y (by linarith)
  have hn := norm_nonneg (F x - F y)
  have hm := mul_le_mul_of_nonneg_left hd hn
  nlinarith

lemma derivative_model {f : E → ℝ} {df : E → E →L[ℝ] ℝ} {x y : E} {B : ℝ}
    (hf : ∀ w, HasFDerivAt f (df w) w)
    (hb : ∀ w ∈ segment ℝ x y, ‖df w - df x‖ ≤ B) :
    f y ≤ f x + df x (y - x) + B * ‖y - x‖ := by
  let H : E → ℝ := fun w => f w - df x w
  have hd : ∀ w, HasFDerivAt H (df w - df x) w :=
    fun w => (hf w).sub (df x).hasFDerivAt
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w _ => (hd w).hasFDerivWithinAt) hb (left_mem_segment ℝ x y)
      (right_mem_segment ℝ x y)
  have hh := (le_abs_self (H y - H x)).trans h
  dsimp [H] at hh
  rw [map_sub]
  linarith

lemma local_descent {f : E → ℝ} {df : E → E →L[ℝ] ℝ} {L0 L1 : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hc : Continuous df)
    (hf : ∀ w, HasFDerivAt f (df w) w)
    (hgl : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖df (x + θ • (y - x))‖ ≤ M) →
      ‖df x - df y‖ ≤ (L0 + L1 * M) * ‖x - y‖)
    (x y : E) (hd : L1 * ‖x - y‖ ≤ 1 / 2) :
    f y ≤ f x + df x (y - x) + 2 * (L0 + L1 * ‖df x‖) * ‖y - x‖ ^ 2 := by
  have hmodel := derivative_model hf (x := x) (y := y)
    (B := 2 * (L0 + L1 * ‖df x‖) * ‖y - x‖) (by
      intro w hw
      rw [segment_eq_image' ℝ x y] at hw
      obtain ⟨t, ht, rfl⟩ := hw
      have hn : ‖x - (x + t • (y - x))‖ ≤ ‖x - y‖ := by
        rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg ht.1, norm_sub_rev y x]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2
      have hcap : L1 * ‖x - (x + t • (y - x))‖ ≤ 1 / 2 :=
        (mul_le_mul_of_nonneg_left hn hL1).trans hd
      have h := local_difference hL0 hL1 hc hgl x (x + t • (y - x)) hcap
      rw [norm_sub_rev (df x)] at h
      have hC : 0 ≤ 2 * (L0 + L1 * ‖df x‖) := by positivity
      have hb := h.trans (mul_le_mul_of_nonneg_left hn hC)
      simpa only [norm_sub_rev x y] using hb)
  nlinarith

lemma positive_direction (g : E →L[ℝ] ℝ) (hg : g ≠ 0) :
    ∃ v : E, ‖v‖ = 1 ∧ ‖g‖ / 2 < g v := by
  have hp : 0 < ‖g‖₊ := nnnorm_pos.mpr hg
  obtain ⟨v, hv, hgv⟩ := g.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm
    (show ‖g‖₊ / 2 < ‖g‖₊ from by exact div_lt_self hp (by norm_num))
  have hv' : ‖v‖ = 1 := by simpa using congrArg NNReal.toReal hv
  have hgv' : ‖g‖ / 2 < |g v| := by exact_mod_cast hgv
  by_cases hs : 0 ≤ g v
  · exact ⟨v, hv', by simpa only [abs_of_nonneg hs] using hgv'⟩
  · refine ⟨-v, by simpa using hv', ?_⟩
    simpa only [map_neg, abs_of_neg (lt_of_not_ge hs)] using hgv'

lemma self_bound {f : E → ℝ} {df : E → E →L[ℝ] ℝ} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hc : Continuous df)
    (hf : ∀ w, HasFDerivAt f (df w) w)
    (hgl : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖df (x + θ • (y - x))‖ ≤ M) →
      ‖df x - df y‖ ≤ (L0 + L1 * M) * ‖x - y‖)
    (x u : E) (hmin : ∀ w, f u ≤ f w) :
    ‖df x‖ ^ 2 ≤ 32 * (L0 + L1 * ‖df x‖) * (f x - f u) := by
  have hgap : 0 ≤ f x - f u := sub_nonneg.mpr (hmin x)
  by_cases hg : df x = 0
  · simp only [hg, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    positivity
  obtain ⟨v, hv, hgv⟩ := positive_direction (df x) hg
  let C := L0 + L1 * ‖df x‖
  have hC : 0 < C := by dsimp [C]; positivity
  let η := ‖df x‖ / (8 * C)
  have hη : 0 < η := by dsimp [η]; exact div_pos (norm_pos_iff.mpr hg) (by positivity)
  have hn : ‖x - (x - η • v)‖ = η := by
    rw [sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos hη, hv, mul_one]
  have hcap : L1 * ‖x - (x - η • v)‖ ≤ 1 / 2 := by
    rw [hn]
    dsimp [η]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have he : L1 * (‖df x‖ / (8 * C)) * 2 = L1 * ‖df x‖ / (4 * C) := by ring
    rw [he]
    apply (div_le_one (by positivity : 0 < 4 * C)).mpr
    dsimp [C]
    nlinarith [mul_nonneg hL1 (norm_nonneg (df x))]
  have hd := local_descent hL0.le hL1 hc hf hgl x (x - η • v) hcap
  have he : x - η • v - x = -(η • v) := by abel
  rw [he, map_neg, map_smul, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos hη, hv, mul_one] at hd
  have hlow := hmin (x - η • v)
  have hg' := mul_lt_mul_of_pos_left hgv hη
  change f (x - η • v) ≤ f x + -(η * df x v) + 2 * C * η ^ 2 at hd
  have hid : η * (‖df x‖ / 2) - 2 * C * η ^ 2 = ‖df x‖ ^ 2 / (32 * C) := by
    dsimp [η]
    field_simp
    ring
  have hbound : ‖df x‖ ^ 2 / (32 * C) ≤ f x - f u := by nlinarith
  have hh := (div_le_iff₀ (by positivity : 0 < 32 * C)).mp hbound
  dsimp [C] at hh
  nlinarith

end LongTails.Proofs.GeneralizedMirrorSmoothness
