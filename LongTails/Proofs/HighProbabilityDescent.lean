import LongTails.Algorithms.HighProbabilityStationarity
import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HighProbabilityDescent

open LongTails.Algorithms.HighProbabilityStationarity OracleTemplate

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma direction_inner (gr g : E) (hg : g ≠ 0) :
    ‖gr‖ - 2 * min ‖g - gr‖ ‖gr‖ ≤ ⟪gr, g⟫ / ‖g‖ := by
  have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
  rcases min_cases ‖g - gr‖ ‖gr‖ with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm]
    have h1 : ⟪gr, g⟫ = ‖g‖ ^ 2 - ⟪g - gr, g⟫ := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm]
      ring
    have h2 : ⟪g - gr, g⟫ ≤ ‖g - gr‖ * ‖g‖ := real_inner_le_norm _ _
    have h3 : ‖gr‖ ≤ ‖g‖ + ‖g - gr‖ := by
      have := norm_sub_le g (g - gr)
      simp only [sub_sub_cancel] at this
      linarith
    rw [le_div_iff₀ hgpos]
    nlinarith
  · rw [hm]
    have h2 : -(‖gr‖ * ‖g‖) ≤ ⟪gr, g⟫ := by
      have := abs_real_inner_le_norm gr g
      linarith [neg_abs_le ⟪gr, g⟫]
    rw [le_div_iff₀ hgpos]
    nlinarith

lemma normalized_descent {f : E → ℝ} {L η : ℝ} (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (x g : E) :
    f (normalizedStep η x g) ≤
      f x - η * (‖gradient f x‖ - 2 * min ‖g - gradient f x‖ ‖gradient f x‖) + L / 2 * η ^ 2 := by
  classical
  by_cases h0 : g = 0
  · have hs : normalizedStep η x g = x := by simp [normalizedStep, h0]
    rw [hs, h0, zero_sub, norm_neg, min_self]
    have : 0 ≤ L / 2 * η ^ 2 := by positivity
    nlinarith [norm_nonneg (gradient f x)]
  · have hs : normalizedStep η x g = x - (η / ‖g‖) • g := by simp [normalizedStep, h0]
    rw [hs]
    have hgpos : 0 < ‖g‖ := norm_pos_iff.mpr h0
    have hu := Gradient.smooth_upper_bound hg hlip x (x - (η / ‖g‖) • g)
    have hd : x - (η / ‖g‖) • g - x = -((η / ‖g‖) • g) := by abel
    rw [hd, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity), div_mul_cancel₀ η hgpos.ne'] at hu
    have hdir := direction_inner (gradient f x) g h0
    have hk : η / ‖g‖ * ⟪gradient f x, g⟫ = η * (⟪gradient f x, g⟫ / ‖g‖) := by ring
    rw [hk] at hu
    nlinarith [mul_le_mul_of_nonneg_left hdir hη]

lemma grad_sq_le_inf {f : E → ℝ} {L fstar : ℝ} (hL : 0 < L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hlow : ∀ y, fstar ≤ f y)
    (x : E) : ‖gradient f x‖ ^ 2 ≤ 2 * L * (f x - fstar) := by
  have hd := Gradient.descent hL hg hlip x
  have hl := hlow (x - (1 / L) • gradient f x)
  have h2 : ‖gradient f x‖ ^ 2 / (2 * L) ≤ f x - fstar := by linarith
  rw [div_le_iff₀ (by positivity)] at h2
  linarith

lemma trajectory_bound {f : E → ℝ} {L η fstar Δ W Gcap : ℝ} (hL : 0 < L) (hη : 0 ≤ η)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (hlow : ∀ y, fstar ≤ f y)
    (x : ℕ → E) (ghat : ℕ → E) (hx : ∀ t, x (t + 1) = normalizedStep η (x t) (ghat t))
    (Dbar : ℕ → ℝ) (hDbar0 : ∀ t, 0 ≤ Dbar t)
    (hcap : ∀ t, ‖gradient f (x t)‖ ≤ Gcap →
      2 * min ‖ghat t - gradient f (x t)‖ ‖gradient f (x t)‖ ≤ Dbar t)
    (T : ℕ) (hW : (∑ t ∈ Finset.range T, Dbar t) ≤ W) (hgap : f (x 0) - fstar ≤ Δ)
    (hG : 0 ≤ Gcap) (hroom : 2 * L * (Δ + η * W + T * (L / 2 * η ^ 2)) ≤ Gcap ^ 2) :
    η * (∑ t ∈ Finset.range T, ‖gradient f (x t)‖) ≤ Δ + η * W + T * (L / 2 * η ^ 2) := by
  let D : ℕ → ℝ := fun t => 2 * min ‖ghat t - gradient f (x t)‖ ‖gradient f (x t)‖
  have hstep (t : ℕ) : f (x (t + 1)) ≤
      f (x t) - η * (‖gradient f (x t)‖ - D t) + L / 2 * η ^ 2 := by
    rw [hx t]
    exact normalized_descent hg hlip hη hL.le (x t) (ghat t)
  have hpartial (t : ℕ) (ht : t ≤ T) : (∑ s ∈ Finset.range t, Dbar s) ≤ W :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr ht)
      (fun s _ _ => hDbar0 s)).trans hW
  have hmain : ∀ t ≤ T,
      f (x t) - fstar + η * (∑ s ∈ Finset.range t, ‖gradient f (x s)‖) ≤
        Δ + η * (∑ s ∈ Finset.range t, D s) + t * (L / 2 * η ^ 2) ∧
      (∑ s ∈ Finset.range t, D s) ≤ ∑ s ∈ Finset.range t, Dbar s := by
    intro t
    induction t with
    | zero => intro _; simp [hgap]
    | succ t ih =>
      intro ht
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hsumD := hpartial t (by omega)
      have hD0 : 0 ≤ ∑ s ∈ Finset.range t, ‖gradient f (x s)‖ :=
        Finset.sum_nonneg fun s _ => norm_nonneg _
      have hval : f (x t) - fstar ≤ Δ + η * W + T * (L / 2 * η ^ 2) := by
        have hT : (t : ℝ) * (L / 2 * η ^ 2) ≤ T * (L / 2 * η ^ 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : t ≤ T)) (by positivity)
        have hηD : η * (∑ s ∈ Finset.range t, D s) ≤ η * W :=
          mul_le_mul_of_nonneg_left (h2.trans hsumD) hη
        nlinarith [mul_nonneg hη hD0]
      have hgrad : ‖gradient f (x t)‖ ≤ Gcap := by
        have hsq := grad_sq_le_inf hL hg hlip hlow (x t)
        have : ‖gradient f (x t)‖ ^ 2 ≤ Gcap ^ 2 := by nlinarith
        exact (sq_le_sq₀ (norm_nonneg _) hG).mp this
      have hDt : D t ≤ Dbar t := hcap t hgrad
      refine ⟨?_, ?_⟩
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hs := hstep t
        push_cast
        nlinarith
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        linarith
  obtain ⟨h1, h2⟩ := hmain T le_rfl
  have hfT : 0 ≤ f (x T) - fstar := by linarith [hlow (x T)]
  have hηD : η * (∑ s ∈ Finset.range T, D s) ≤ η * W :=
    mul_le_mul_of_nonneg_left (h2.trans hW) hη
  linarith

lemma count_large (a : ℕ → ℝ) (ha : ∀ t, 0 ≤ a t) (τ : ℝ) (T : ℕ) :
    τ * ((Finset.range T).filter (fun t => τ < a t)).card ≤ ∑ t ∈ Finset.range T, a t := by
  classical
  calc τ * ((Finset.range T).filter (fun t => τ < a t)).card =
        ∑ t ∈ (Finset.range T).filter (fun t => τ < a t), τ := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ t ∈ (Finset.range T).filter (fun t => τ < a t), a t :=
          Finset.sum_le_sum fun t ht => (Finset.mem_filter.mp ht).2.le
    _ ≤ ∑ t ∈ Finset.range T, a t :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun t _ _ => ha t)

end LongTails.Proofs.HighProbabilityDescent
