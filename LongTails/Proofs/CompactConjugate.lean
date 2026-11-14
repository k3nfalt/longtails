import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open Set Filter
open scoped RealInnerProductSpace Topology

namespace LongTails.Proofs.CompactConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def maximizer (K : Set E) (H : E → ℝ) (x : E) : E :=
  Classical.epsilon fun z => z ∈ K ∧ IsMaxOn (fun v => ⟪x, v⟫ - H v) K z

lemma maximizer_spec {K : Set E} {H : E → ℝ} (hK : IsCompact K)
    (hne : K.Nonempty) (hH : ContinuousOn H K) (x : E) :
    maximizer K H x ∈ K ∧ IsMaxOn (fun v => ⟪x, v⟫ - H v) K (maximizer K H x) := by
  unfold maximizer
  exact Classical.epsilon_spec (hK.exists_isMaxOn hne
    ((continuous_const.inner continuous_id).continuousOn.sub hH))

lemma maximizer_distance_bound (H : E → ℝ) (x y u v : E) (M : ℝ) (hM : 0 < M)
    (hu : ⟪x, v⟫ - H v + ‖u - v‖ ^ 2 / (2 * M) ≤ ⟪x, u⟫ - H u)
    (hv : ⟪y, u⟫ - H u + ‖u - v‖ ^ 2 / (2 * M) ≤ ⟪y, v⟫ - H v) :
    ‖u - v‖ ≤ M * ‖x - y‖ := by
  have he : ⟪x, u⟫ - ⟪x, v⟫ + (⟪y, v⟫ - ⟪y, u⟫) = ⟪x - y, u - v⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hs : ‖u - v‖ ^ 2 / M ≤ ⟪x - y, u - v⟫ := by
    rw [← he]
    have hhalf : ‖u - v‖ ^ 2 / M = 2 * (‖u - v‖ ^ 2 / (2 * M)) := by ring
    rw [hhalf]
    linarith
  have hb := hs.trans (real_inner_le_norm (x - y) (u - v))
  have hm := (div_le_iff₀ hM).mp hb
  by_cases hz : ‖u - v‖ = 0
  · rw [hz]
    positivity
  · have hp : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_of_pos_right hp).mp
    nlinarith only [hm]

lemma value_remainder_bound (H : E → ℝ) (x y u v : E) (M : ℝ)
    (hu : ⟪x, v⟫ - H v ≤ ⟪x, u⟫ - H u)
    (hv : ⟪y, u⟫ - H u ≤ ⟪y, v⟫ - H v)
    (hd : ‖v - u‖ ≤ M * ‖y - x‖) :
    0 ≤ (⟪y, v⟫ - H v) - (⟪x, u⟫ - H u) - ⟪u, y - x⟫ ∧
    (⟪y, v⟫ - H v) - (⟪x, u⟫ - H u) - ⟪u, y - x⟫ ≤ M * ‖y - x‖ ^ 2 := by
  have hb := real_inner_le_norm (y - x) (v - u)
  have hm := mul_le_mul_of_nonneg_left hd (norm_nonneg (y - x))
  simp only [inner_sub_left, inner_sub_right, real_inner_comm u] at hb hu hv ⊢
  constructor <;> nlinarith

lemma hasGradientAt_of_quadratic_remainder [CompleteSpace E] (f : E → ℝ) (x g : E) (M : ℝ)
    (h : ∀ y, 0 ≤ f y - f x - ⟪g, y - x⟫ ∧
      f y - f x - ⟪g, y - x⟫ ≤ M * ‖y - x‖ ^ 2) :
    HasGradientAt f g x := by
  rw [hasGradientAt_iff_tendsto]
  apply squeeze_zero (fun y => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (g := fun y => M * ‖y - x‖)
  · intro y
    rw [Real.norm_of_nonneg (h y).1]
    have hh := mul_le_mul_of_nonneg_left (h y).2 (inv_nonneg.mpr (norm_nonneg (y - x)))
    by_cases he : ‖y - x‖ = 0
    · simp [he]
    · convert hh using 1
      field_simp
  · have hc : Continuous (fun y : E => M * ‖y - x‖) := by fun_prop
    simpa using hc.tendsto x

noncomputable def value (K : Set E) (H : E → ℝ) (x : E) : ℝ :=
  ⟪x, maximizer K H x⟫ - H (maximizer K H x)

lemma value_hasGradientAt [CompleteSpace E] {K : Set E} {H : E → ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hH : ContinuousOn H K)
    (M : ℝ) (hM : 0 < M)
    (hgrowth : ∀ x v, v ∈ K →
      ⟪x, v⟫ - H v + ‖maximizer K H x - v‖ ^ 2 / (2 * M) ≤ value K H x)
    (x : E) : HasGradientAt (value K H) (maximizer K H x) x := by
  apply hasGradientAt_of_quadratic_remainder _ _ _ M
  intro y
  have hx := maximizer_spec hK hne hH x
  have hy := maximizer_spec hK hne hH y
  have hu := hgrowth x (maximizer K H y) hy.1
  have hv := hgrowth y (maximizer K H x) hx.1
  rw [norm_sub_rev (maximizer K H y)] at hv
  have hd := maximizer_distance_bound H x y (maximizer K H x) (maximizer K H y) M hM hu hv
  rw [norm_sub_rev (maximizer K H x), norm_sub_rev x] at hd
  exact value_remainder_bound H x y (maximizer K H x) (maximizer K H y) M
    (hx.2 hy.1) (hy.2 hx.1) hd

lemma strong_segment_of_second_derivative (f f' f'' : ℝ → ℝ) (K : ℝ)
    (hc : ContinuousOn f (Icc 0 1))
    (h1 : ∀ t ∈ Ioo 0 1, HasDerivAt f (f' t) t)
    (h2 : ∀ t ∈ Ioo 0 1, HasDerivAt f' (f'' t) t)
    (hK : ∀ t ∈ Ioo 0 1, K ≤ f'' t)
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    f t ≤ (1 - t) * f 0 + t * f 1 - K / 2 * t * (1 - t) := by
  let F := fun s => f s - K / 2 * s ^ 2
  let F' := fun s => f' s - K * s
  let F'' := fun s => f'' s - K
  have hd1 (s : ℝ) (hs : s ∈ Ioo 0 1) : HasDerivAt F (F' s) s := by
    convert (h1 s hs).sub (((hasDerivAt_id s).pow 2).const_mul (K / 2)) using 1
    · ext y
      rfl
    · dsimp [F']
      ring
  have hd2 (s : ℝ) (hs : s ∈ Ioo 0 1) : HasDerivAt F' (F'' s) s := by
    convert (h2 s hs).sub ((hasDerivAt_id s).const_mul K) using 1
    · ext y
      rfl
    · simp [F'']
  have hcv : ConvexOn ℝ (Icc 0 1) F := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := F') (f'' := F'') (convex_Icc 0 1)
    · exact hc.sub ((continuous_const.mul (continuous_id.pow 2)).continuousOn)
    · intro s hs
      exact (hd1 s (by simpa only [interior_Icc] using hs)).hasDerivWithinAt
    · intro s hs
      exact (hd2 s (by simpa only [interior_Icc] using hs)).hasDerivWithinAt
    · intro s hs
      exact sub_nonneg.mpr (hK s (by simpa only [interior_Icc] using hs))
  have hh := hcv.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, F, zero_pow (by decide : 2 ≠ 0),
    one_pow, sub_zero] at hh
  nlinarith only [hh]

lemma le_of_unit_limits (A B : ℝ)
    (h : ∀ t : ℝ, 0 < t → t < 1 → (1 - t) * A ≤ B) : A ≤ B := by
  have hc : Continuous (fun t : ℝ => (1 - t) * A) := by fun_prop
  have hl : Tendsto (fun t : ℝ => (1 - t) * A) (𝓝[>] (0 : ℝ)) (𝓝 A) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin,
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with t ht ht'
  exact h t ht ht'

lemma maximizer_growth_of_segment (H : E → ℝ) (a u v : E) (γ : ℝ)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1,
      H ((1 - t) • u + t • v) ≤ (1 - t) * H u + t * H v - γ * t * (1 - t))
    (hopt : ∀ t ∈ Icc (0 : ℝ) 1,
      ⟪a, (1 - t) • u + t • v⟫ - H ((1 - t) • u + t • v) ≤ ⟪a, u⟫ - H u) :
    ⟪a, v⟫ - H v + γ ≤ ⟪a, u⟫ - H u := by
  have hh : γ ≤ (⟪a, u⟫ - H u) - (⟪a, v⟫ - H v) := by
    apply le_of_unit_limits
    intro t ht ht'
    have hs := hsegment t ⟨ht.le, ht'.le⟩
    have ho := hopt t ⟨ht.le, ht'.le⟩
    simp only [inner_add_right, real_inner_smul_right] at ho
    apply (mul_le_mul_iff_of_pos_left ht).mp
    nlinarith only [hs, ho]
  linarith

lemma value_convex {K : Set E} {H : E → ℝ} (hK : IsCompact K)
    (hne : K.Nonempty) (hH : ContinuousOn H K) : ConvexOn ℝ univ (value K H) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hv := maximizer_spec hK hne hH (a • x + b • y)
  have hx := (maximizer_spec hK hne hH x).2 hv.1
  have hy := (maximizer_spec hK hne hH y).2 hv.1
  have h1 := mul_le_mul_of_nonneg_left hx ha
  have h2 := mul_le_mul_of_nonneg_left hy hb
  simp only [value, inner_add_left, real_inner_smul_left, smul_eq_mul]
  dsimp at h1 h2
  have he : a * H (maximizer K H (a • x + b • y)) +
      b * H (maximizer K H (a • x + b • y)) = H (maximizer K H (a • x + b • y)) := by
    rw [← add_mul, hab, one_mul]
  nlinarith only [h1, h2, he]

end LongTails.Proofs.CompactConjugate
