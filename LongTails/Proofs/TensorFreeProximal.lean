import LongTails.Proofs.TensorFreeModelTermination

namespace LongTails.Proofs.TensorFreeProximal

open LongTails.Algorithms.TensorFreeModel LongTails.Proofs.TensorFreeModel
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma residual_alignment {g s : E} {L : ℝ} (hL : 0 ≤ L)
    (hres : ‖g + (L * ‖s‖ ^ 2) • s‖ ≤ (‖g‖ + L * ‖s‖ ^ 3) / 6) :
    4 * (‖g‖ ^ 2 + (L * ‖s‖ ^ 3) ^ 2) ≤ 9 * (L * ‖s‖ ^ 2) * ⟪g, -s⟫ := by
  have hs := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hres
  have he : ‖g + (L * ‖s‖ ^ 2) • s‖ ^ 2 =
      ‖g‖ ^ 2 - 2 * (L * ‖s‖ ^ 2) * ⟪g, -s⟫ + (L * ‖s‖ ^ 3) ^ 2 := by
    rw [norm_add_sq_real]
    simp only [inner_smul_right, inner_neg_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ L * ‖s‖ ^ 2)]
    ring
  rw [he] at hs
  nlinarith [sq_nonneg (‖g‖ - L * ‖s‖ ^ 3)]

lemma model_residual_vector {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ}
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (z s : E)
    (hm : ‖exactGradient (gradient f z) (fderiv ℝ (gradient f) z)
      (fderiv ℝ (fderiv ℝ (gradient f)) z) L s‖ ≤ ‖gradient f (z + s)‖ / 6) :
    ‖gradient f (z + s) + (L * ‖s‖ ^ 2) • s‖ ≤
      (‖gradient f (z + s)‖ + L * ‖s‖ ^ 3) / 6 := by
  have ht := gradient_remainder hf hT z s
  let m := exactGradient (gradient f z) (fderiv ℝ (gradient f) z)
    (fderiv ℝ (fderiv ℝ (gradient f)) z) L s
  have he : gradient f (z + s) + (L * ‖s‖ ^ 2) • s = m +
      (gradient f (z + s) - gradient f z - fderiv ℝ (gradient f) z s -
        (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (gradient f)) z s s) := by
    dsimp [m, exactGradient]
    module
  rw [he]
  have hh := norm_add_le m (gradient f (z + s) - gradient f z - fderiv ℝ (gradient f) z s -
    (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ (gradient f)) z s s)
  change ‖m‖ ≤ ‖gradient f (z + s)‖ / 6 at hm
  linarith

lemma cubic_alignment {a b d L p : ℝ} (hb : 0 < b)
    (hL : 0 < L) (hp : 0 ≤ p)
    (hid : d ^ 3 = L * b ^ 2) (h : 4 * (a ^ 2 + b ^ 2) ≤ 9 * d * p) :
    a ^ 4 ≤ 2 * L * p ^ 3 := by
  have hc := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * (a ^ 2 + b ^ 2)) h 3
  have hy : 27 * a ^ 4 * b ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (a ^ 2 - 2 * b ^ 2))
      (show 0 ≤ 4 * a ^ 2 + b ^ 2 by positivity)]
  have hc' : 64 * (a ^ 2 + b ^ 2) ^ 3 ≤ 729 * L * b ^ 2 * p ^ 3 := by
    calc
      _ = (4 * (a ^ 2 + b ^ 2)) ^ 3 := by ring
      _ ≤ (9 * d * p) ^ 3 := hc
      _ = 729 * (d ^ 3) * p ^ 3 := by ring
      _ = _ := by rw [hid]; ring
  have hz : a ^ 4 * b ^ 2 ≤ (2 * L * p ^ 3) * b ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ L * p ^ 3 by positivity) (sq_nonneg b)]
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hb)).mp hz


omit [FiniteDimensional ℝ E] in
lemma residual_descent {g s : E} {L : ℝ} (hL : 0 < L)
    (hres : ‖g + (L * ‖s‖ ^ 2) • s‖ ≤ (‖g‖ + L * ‖s‖ ^ 3) / 6) :
    0 ≤ ⟪g, -s⟫ ∧ ‖g‖ ^ 4 ≤ 2 * L * ⟪g, -s⟫ ^ 3 := by
  by_cases hs : s = 0
  · subst s
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0), mul_zero, smul_zero, add_zero] at hres
    have hg : g = 0 := norm_eq_zero.mp (by linarith [norm_nonneg g])
    simp [hg]
  · have hr : 0 < ‖s‖ := norm_pos_iff.mpr hs
    have hh := residual_alignment hL.le hres
    have hp : 0 ≤ ⟪g, -s⟫ := by
      have hprod : 0 ≤ 9 * (L * ‖s‖ ^ 2) * ⟪g, -s⟫ := (by positivity :
        0 ≤ 4 * (‖g‖ ^ 2 + (L * ‖s‖ ^ 3) ^ 2)).trans hh
      exact nonneg_of_mul_nonneg_right hprod (by positivity)
    refine ⟨hp, cubic_alignment (a := ‖g‖) (b := L * ‖s‖ ^ 3)
      (d := L * ‖s‖ ^ 2) (by positivity) hL hp (by ring) hh⟩

lemma model_descent {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L : ℝ} (hL : 0 < L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (z s : E)
    (hm : ‖exactGradient (gradient f z) (fderiv ℝ (gradient f) z)
      (fderiv ℝ (fderiv ℝ (gradient f)) z) L s‖ ≤ ‖gradient f (z + s)‖ / 6) :
    0 ≤ ⟪gradient f (z + s), -s⟫ ∧
      ‖gradient f (z + s)‖ ^ 4 ≤ 2 * L * ⟪gradient f (z + s), -s⟫ ^ 3 :=
  residual_descent hL (model_residual_vector hf hT z s hm)


lemma model_distance_bounds {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L : ℝ} (hL : 0 < L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (z s u : E)
    (hmin : ∀ x, f u ≤ f x)
    (hm : ‖exactGradient (gradient f z) (fderiv ℝ (gradient f) z)
      (fderiv ℝ (fderiv ℝ (gradient f)) z) L s‖ ≤ ‖gradient f (z + s)‖ / 6) :
    ‖gradient f (z + s)‖ ≤ 2 * L * ‖z - u‖ ^ 3 ∧
      f (z + s) - f u ≤ 2 * L * ‖z - u‖ ^ 4 := by
  let g := gradient f (z + s)
  have hsupp := OracleTemplate.Gradient.convex_support hc
    (fun x => (hf.differentiable (by norm_num) x).hasGradientAt) (z + s) u
  have he : ⟪g, u - (z + s)⟫ = ⟪g, -s⟫ - ⟪g, z - u⟫ := by
    rw [← inner_sub_right]
    congr 1
    module
  change ⟪g, u - (z + s)⟫ ≤ f u - f (z + s) at hsupp
  rw [he] at hsupp
  obtain ⟨hp, hpow⟩ := model_descent hf hL hT z s hm
  have hinner := real_inner_le_norm g (z - u)
  have hupper : ⟪g, -s⟫ ≤ ‖g‖ * ‖z - u‖ := by linarith [hmin (z + s)]
  have hgrad : ‖g‖ ≤ 2 * L * ‖z - u‖ ^ 3 := by
    by_cases hg : ‖g‖ = 0
    · rw [hg]
      positivity
    · have hgpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hg)
      have hh := pow_le_pow_left₀ hp hupper 3
      have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * L by positivity)
      have hmul : ‖g‖ * ‖g‖ ^ 3 ≤ (2 * L * ‖z - u‖ ^ 3) * ‖g‖ ^ 3 := by
        calc
          _ = ‖g‖ ^ 4 := by ring
          _ ≤ 2 * L * ⟪g, -s⟫ ^ 3 := hpow
          _ ≤ 2 * L * (‖g‖ * ‖z - u‖) ^ 3 := hm
          _ = _ := by ring
      exact (mul_le_mul_iff_left₀ (pow_pos hgpos 3)).mp hmul
  refine ⟨hgrad, ?_⟩
  have hh := mul_le_mul_of_nonneg_right hgrad (norm_nonneg (z - u))
  change 0 ≤ ⟪g, -s⟫ at hp
  nlinarith

lemma model_gap_descent {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L : ℝ} (hL : 0 < L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (z s u : E)
    (hmin : ∀ x, f u ≤ f x)
    (hm : ‖exactGradient (gradient f z) (fderiv ℝ (gradient f) z)
      (fderiv ℝ (fderiv ℝ (gradient f)) z) L s‖ ≤ ‖gradient f (z + s)‖ / 6) :
    ‖gradient f (z + s)‖ ^ 4 ≤ 2 * L * (f z - f u) ^ 3 := by
  obtain ⟨hp, hpow⟩ := model_descent hf hL hT z s hm
  have hsupp := OracleTemplate.Gradient.convex_support hc
    (fun x => (hf.differentiable (by norm_num) x).hasGradientAt) (z + s) z
  have he : z - (z + s) = -s := by module
  rw [he] at hsupp
  have hh : ⟪gradient f (z + s), -s⟫ ≤ f z - f u := by linarith [hmin (z + s)]
  exact hpow.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp hh 3) (by positivity))

end LongTails.Proofs.TensorFreeProximal
