import LongTails.Proofs.ThirdOrderObjectiveGeometry
import LongTails.Algorithms.GradientOnlyGuarded

namespace LongTails.Proofs.GradientQuadrature

open scoped RealInnerProductSpace
open Set
open LongTails.Algorithms.GradientOnlyGuarded

lemma quadratic_taylor_bound {k k₁ k₂ : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (h₀ : ∀ t, HasDerivAt k (k₁ t) t)
    (h₁ : ∀ t, HasDerivAt k₁ (k₂ t) t)
    (h₂ : ∀ t, |k₂ t - k₂ 0| ≤ M * |t|) (t : ℝ) :
    |k t - k 0 - k₁ 0 * t - k₂ 0 * t ^ 2 / 2| ≤ M * |t| ^ 3 := by
  let r₁ := fun s : ℝ => k₁ s - k₁ 0 - s * k₂ 0
  have hd₁ : ∀ s, HasDerivAt r₁ (k₂ s - k₂ 0) s := by
    intro s
    convert ((h₁ s).sub_const (k₁ 0)).sub ((hasDerivAt_id s).mul_const (k₂ 0)) using 1 <;>
      (try funext u) <;> simp [r₁]
  have hb₁ : ∀ s, |r₁ s| ≤ M * |s| ^ 2 := by
    intro s
    have hm := ThirdOrderTaylorBounds.power_derivative_bound hM 1 hd₁
      (by simpa only [Real.norm_eq_abs, pow_one] using h₂) s
    simpa [r₁, Real.norm_eq_abs] using hm
  let r₀ := fun s : ℝ => k s - k 0 - s * k₁ 0 - s ^ 2 / 2 * k₂ 0
  have hd₀ : ∀ s, HasDerivAt r₀ (r₁ s) s := by
    intro s
    convert (((h₀ s).sub_const (k 0)).sub ((hasDerivAt_id s).mul_const (k₁ 0))).sub
      ((((hasDerivAt_id s).pow 2).div_const 2).mul_const (k₂ 0)) using 1
    all_goals
      try funext u
      dsimp [r₀, r₁]
    all_goals ring
  have hm := ThirdOrderTaylorBounds.power_derivative_bound hM 2 hd₀
    (by simpa only [Real.norm_eq_abs] using hb₁) t
  have he : r₀ t - r₀ 0 = k t - k 0 - k₁ 0 * t - k₂ 0 * t ^ 2 / 2 := by
    dsimp [r₀]
    ring
  simpa only [he, Real.norm_eq_abs] using hm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma gradient_quadratic_remainder {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (c w v : E) (s : ℝ) :
    |⟪gradient f (c + s • w), v⟫ - ⟪gradient f c, v⟫ -
      ⟪fderiv ℝ (gradient f) c w, v⟫ * s -
      ⟪fderiv ℝ (fderiv ℝ (gradient f)) c w w, v⟫ * s ^ 2 / 2| ≤
      (L * ‖w‖ ^ 3 * ‖v‖) * |s| ^ 3 := by
  let H := fderiv ℝ (gradient f)
  let T := fderiv ℝ H
  let path := fun r : ℝ => c + r • w
  have hp (r : ℝ) : HasDerivAt path w r := by
    convert (hasDerivAt_const r c).add ((hasDerivAt_id r).smul_const w) using 1
    · funext u
      rfl
    · simp
  obtain ⟨_, hf₁, hf₂⟩ := GradientDependentLocal.derivative_chain hf
  have h₀ (r : ℝ) : HasDerivAt (fun u => ⟪gradient f (path u), v⟫) ⟪H (path r) w, v⟫ r := by
    simpa [H] using HasDerivAt.inner ℝ ((hf₁ (path r)).comp_hasDerivAt r (hp r)) (hasDerivAt_const r v)
  have h₁ (r : ℝ) : HasDerivAt (fun u => ⟪H (path u) w, v⟫) ⟪T (path r) w w, v⟫ r := by
    simpa [H, T] using HasDerivAt.inner ℝ (((hf₂ (path r)).comp_hasDerivAt r (hp r)).clm_apply
      (hasDerivAt_const r w)) (hasDerivAt_const r v)
  have h₂ (r : ℝ) : |⟪T (path r) w w, v⟫ - ⟪T (path 0) w w, v⟫| ≤
      (L * ‖w‖ ^ 3 * ‖v‖) * |r| := by
    have hi : ⟪T (path r) w w, v⟫ - ⟪T (path 0) w w, v⟫ =
        ⟪(T (path r) - T (path 0)) w w, v⟫ := by
      simp only [sub_apply, inner_sub_left]
    rw [hi]
    calc
      _ ≤ ‖(T (path r) - T (path 0)) w w‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖T (path r) - T (path 0)‖ * ‖w‖ * ‖w‖) * ‖v‖ := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ (L * ‖path r - path 0‖ * ‖w‖ * ‖w‖) * ‖v‖ := by
        gcongr
        exact hT _ _
      _ = (L * ‖w‖ ^ 3 * ‖v‖) * |r| := by
        simp only [path, zero_smul, add_zero, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        ring
  have hm := quadratic_taylor_bound (by positivity : 0 ≤ L * ‖w‖ ^ 3 * ‖v‖) h₀ h₁ h₂ s
  simpa [path, H, T] using hm

lemma piece_estimate {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (c v : E) :
    |(⟪gradient f (c + (1 / Real.sqrt 3) • v), v⟫ + ⟪gradient f (c + (-1 / Real.sqrt 3) • v), v⟫) -
      (f (c + (1 : ℝ) • v) - f (c + (-1 : ℝ) • v))| ≤ 3 * L * ‖v‖ ^ 4 := by
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3p : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  let w := (1 / Real.sqrt 3) • v
  have hw₁ : c + (1 / Real.sqrt 3) • v = c + (1 : ℝ) • w := by simp [w]
  have hw₂ : c + (-1 / Real.sqrt 3) • v = c + (-1 : ℝ) • w := by
    simp only [w, smul_smul]
    congr 2
    ring
  have hp := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT c v 1
  have hm := ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT c v (-1)
  have gp := gradient_quadratic_remainder hf hL hT c w v 1
  have gm := gradient_quadratic_remainder hf hL hT c w v (-1)
  have hT3 : ⟪fderiv ℝ (fderiv ℝ (gradient f)) c w w, v⟫ =
      ⟪fderiv ℝ (fderiv ℝ (gradient f)) c v v, v⟫ / 3 := by
    simp only [w, map_smul, smul_apply, real_inner_smul_left]
    field_simp
    rw [hs3]
    ring
  have hnw : ‖w‖ = ‖v‖ / Real.sqrt 3 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_div, abs_one, abs_of_pos hs3p]
    ring
  have hbound : L * ‖w‖ ^ 3 * ‖v‖ ≤ L * ‖v‖ ^ 4 / 5 := by
    rw [hnw]
    have hs : 5 ≤ Real.sqrt 3 ^ 3 := by nlinarith [hs3, hs3p]
    have hv : 0 ≤ ‖v‖ ^ 4 := by positivity
    rw [div_pow]
    have : L * (‖v‖ ^ 3 / Real.sqrt 3 ^ 3) * ‖v‖ = L * ‖v‖ ^ 4 / Real.sqrt 3 ^ 3 := by ring
    rw [this]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hs
  simp only [abs_one, one_pow, mul_one, show |(-1 : ℝ)| = 1 by norm_num] at hp hm gp gm
  rw [hw₁, hw₂]
  have e1 := abs_le.mp hp
  have e2 := abs_le.mp hm
  have e3 := abs_le.mp gp
  have e4 := abs_le.mp gm
  rw [abs_le]
  constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, hT3, hbound]

omit [FiniteDimensional ℝ E] in
lemma piece_endpoints (a b : E) {m : ℕ} (hm : 0 < m) (i : ℕ) :
    (a + ((2 * (i : ℝ) + 1) / (2 * m)) • (b - a)) + (1 : ℝ) • ((1 / (2 * (m : ℝ))) • (b - a)) =
      a + (((i + 1 : ℕ) : ℝ) / m) • (b - a) ∧
    (a + ((2 * (i : ℝ) + 1) / (2 * m)) • (b - a)) + (-1 : ℝ) • ((1 / (2 * (m : ℝ))) • (b - a)) =
      a + ((i : ℝ) / m) • (b - a) := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have key : ∀ s : ℝ, (a + ((2 * (i : ℝ) + 1) / (2 * m)) • (b - a)) +
      s • ((1 / (2 * (m : ℝ))) • (b - a)) = a + (((2 * (i : ℝ) + 1) + s) / (2 * m)) • (b - a) := by
    intro s
    rw [smul_smul, add_assoc, ← add_smul]
    congr 2
    field_simp
  constructor
  · rw [key]
    congr 2
    push_cast
    field_simp
    ring
  · rw [key]
    congr 2
    field_simp
    ring

lemma surrogate_error {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (a b : E) {m : ℕ} (hm : 0 < m) :
    |surrogate (gradient f) a b m - (f b - f a)| ≤ L * ‖b - a‖ ^ 4 / m ^ 3 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  let v : E := (1 / (2 * (m : ℝ))) • (b - a)
  let pt : ℕ → E := fun i => a + ((i : ℝ) / m) • (b - a)
  have hv : ‖v‖ = ‖b - a‖ / (2 * m) := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_div, abs_one]
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * m)]
    ring
  have hpiece : ∀ i ∈ Finset.range m,
      |pieceValue (gradient f) a b m i - (f (pt (i + 1)) - f (pt i))| ≤
        3 * L * (‖b - a‖ / (2 * m)) ^ 4 := by
    intro i _
    obtain ⟨he₁, he₂⟩ := piece_endpoints a b hm i
    have hh := piece_estimate hf hL hT (a + ((2 * (i : ℝ) + 1) / (2 * m)) • (b - a)) v
    rw [he₁, he₂, hv] at hh
    have hpv : pieceValue (gradient f) a b m i =
        ⟪gradient f ((a + ((2 * (i : ℝ) + 1) / (2 * m)) • (b - a)) + (1 / Real.sqrt 3) • v), v⟫ +
          ⟪gradient f ((a + ((2 * (i : ℝ) + 1) / (2 * m)) • (b - a)) + (-1 / Real.sqrt 3) • v), v⟫ := by
      simp only [pieceValue, node, inner_add_left, v]
    rw [hpv]
    simpa only [pt] using hh
  have htel : ∑ i ∈ Finset.range m, (f (pt (i + 1)) - f (pt i)) = f b - f a := by
    rw [Finset.sum_range_sub (fun i => f (pt i))]
    simp only [pt, Nat.cast_zero, zero_div, zero_smul, add_zero]
    rw [div_self (ne_of_gt hm'), one_smul, add_sub_cancel]
  have hsum : |surrogate (gradient f) a b m - (f b - f a)| ≤
      ∑ i ∈ Finset.range m, 3 * L * (‖b - a‖ / (2 * m)) ^ 4 := by
    rw [← htel, surrogate, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hpiece)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  refine hsum.trans ?_
  rw [div_pow]
  have hcalc : (m : ℝ) * (3 * L * (‖b - a‖ ^ 4 / (2 * (m : ℝ)) ^ 4)) =
      (3 / 16) * (L * ‖b - a‖ ^ 4 / m ^ 3) := by
    field_simp
    ring
  rw [hcalc]
  have : 0 ≤ L * ‖b - a‖ ^ 4 / m ^ 3 := by positivity
  linarith

end LongTails.Proofs.GradientQuadrature
