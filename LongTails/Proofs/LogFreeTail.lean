import LongTails.Proofs.LogFreeSteps

namespace LongTails.Proofs.LogFreeTail

open scoped RealInnerProductSpace
open LongTails.Proofs.LogFreeGeometry LongTails.Proofs.LogFreeLinearAlgebra
  LongTails.Proofs.LogFreeSteps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def sys (f : E → ℝ) (γ : ℝ) (y : E) : E →L[ℝ] E :=
  fderiv ℝ (gradient f) y + γ • ContinuousLinearMap.id ℝ E

lemma sys_inner (f : E → ℝ) (γ : ℝ) (y v : E) :
    ⟪sys f γ y v, v⟫ = ⟪fderiv ℝ (gradient f) y v, v⟫ + γ * ‖v‖ ^ 2 := by
  simp [sys, inner_add_left, real_inner_smul_left]

lemma sys_apply_inner (f : E → ℝ) (γ : ℝ) (y a b : E) :
    ⟪sys f γ y a, b⟫ = ⟪fderiv ℝ (gradient f) y a, b⟫ + γ * ⟪a, b⟫ := by
  simp [sys, inner_add_left, real_inner_smul_left]

lemma contraction_scalar {Λ Λ' P' ζ ζ' Y : ℝ} (hΛ : 0 ≤ Λ) (hP : 0 ≤ P')
    (hζ : ζ ≤ 1 / 16) (hζ'0 : 0 ≤ ζ') (hζ' : ζ' ≤ 1 / 8)
    (hY : Y ^ 2 ≤ Λ / 2 ^ 40 * P') (hPΛ : (1 - ζ) * P' ≤ Λ')
    (hb : Λ' ≤ ζ' * Real.sqrt (Λ * P') + Y) : Λ' ≤ Λ / 16 := by
  by_cases hpos : Λ' ≤ 0
  · exact hpos.trans (by positivity)
  have hpos' : 0 < Λ' := lt_of_not_ge hpos
  set X := ζ' * Real.sqrt (Λ * P') with hX
  have hX0 : 0 ≤ X := by positivity
  have hX2 : X ^ 2 = ζ' ^ 2 * (Λ * P') := by
    rw [hX, mul_pow, Real.sq_sqrt (mul_nonneg hΛ hP)]
  have hsq : Λ' ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by nlinarith [sq_nonneg (X - Y)]
  have hP'b : P' ≤ 16 / 15 * Λ' := by nlinarith
  have hz2 : ζ' ^ 2 ≤ 1 / 64 := by nlinarith
  have hcomb : Λ' ^ 2 ≤ (2 * (1 / 64) * Λ + 2 * (Λ / 2 ^ 40)) * P' := by
    have : ζ' ^ 2 * (Λ * P') ≤ 1 / 64 * (Λ * P') :=
      mul_le_mul_of_nonneg_right hz2 (mul_nonneg hΛ hP)
    nlinarith
  have hfac : 0 ≤ 2 * (1 / 64) * Λ + 2 * (Λ / 2 ^ 40) := by positivity
  have hfin : Λ' * Λ' ≤ Λ' * (16 / 15 * (2 * (1 / 64) * Λ + 2 * (Λ / 2 ^ 40))) := by
    have := mul_le_mul_of_nonneg_left hP'b hfac
    nlinarith
  have hdiv := le_of_mul_le_mul_left hfin hpos'
  nlinarith

lemma cube_small {L a μ Λ : ℝ} (hL : 0 ≤ L) (hμ : 0 < μ) (ha2 : a ^ 2 ≤ Λ / μ)
    (hLa : L * a ^ 2 ≤ μ / 2 ^ 20) : (L * a ^ 3 / 6) ^ 2 / μ ≤ Λ / 2 ^ 40 := by
  have hΛ : 0 ≤ Λ := by
    have : 0 ≤ Λ / μ := le_trans (sq_nonneg a) ha2
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hμ))
  have e1 : (L * a ^ 3 / 6) ^ 2 / μ = (L * a ^ 2) ^ 2 * a ^ 2 / (36 * μ) := by
    field_simp
    ring
  rw [e1, div_le_iff₀ (by positivity)]
  have hLa0 : 0 ≤ L * a ^ 2 := by positivity
  have hsq1 : (L * a ^ 2) ^ 2 ≤ (μ / 2 ^ 20) ^ 2 := pow_le_pow_left₀ hLa0 hLa 2
  have hsq2 : (L * a ^ 2) ^ 2 * a ^ 2 ≤ (μ / 2 ^ 20) ^ 2 * (Λ / μ) :=
    mul_le_mul hsq1 ha2 (sq_nonneg _) (by positivity)
  have e2 : (μ / 2 ^ 20) ^ 2 * (Λ / μ) = Λ / 2 ^ 40 * μ := by field_simp
  nlinarith

lemma small_step {L μ Λ a : ℝ} (hL : 0 ≤ L) (hμ : 0 < μ) (ha2 : a ^ 2 ≤ Λ / μ)
    (hs : L * Λ ≤ μ ^ 2 / 2 ^ 20) : L * a ^ 2 ≤ μ / 2 ^ 20 := by
  have h1 : L * a ^ 2 ≤ L * (Λ / μ) := mul_le_mul_of_nonneg_left ha2 hL
  have h3 : L * (Λ / μ) = (L * Λ) / μ := by ring
  have h4 : (L * Λ) / μ ≤ (μ ^ 2 / 2 ^ 20) / μ := div_le_div_of_nonneg_right hs hμ.le
  have h5 : (μ ^ 2 / 2 ^ 20) / μ = μ / 2 ^ 20 := by field_simp
  linarith

section Tail

variable {f : E → ℝ} (hf : ContDiff ℝ 3 f) {L : ℝ} (hL : 0 ≤ L)
  (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
    fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
include hf hL hT

omit hL hT in
lemma sys_symm (γ : ℝ) (y : E) : Symm (sys f γ y) := by
  intro a b
  have hs := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
    (hf.of_le (by norm_num)) y a b
  have hs' : ⟪fderiv ℝ (gradient f) y a, b⟫ = ⟪fderiv ℝ (gradient f) y b, a⟫ := by
    rw [real_inner_comm a (fderiv ℝ (gradient f) y b)]; exact hs
  rw [sys_apply_inner, sys_apply_inner, hs', real_inner_comm a b]

omit hL hT in
lemma third_symm (y d : E) : Symm (fderiv ℝ (fderiv ℝ (gradient f)) y d) := by
  intro a b
  exact ThirdOrderObjectiveGeometry.third_swap_last hf y d a b

lemma third_relative {γ μ ζ : ℝ} (hμ : 0 < μ) (y d : E)
    (hcoer : ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪sys f γ y v, v⟫)
    (hstab : ∀ v, |⟪(fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y) v, v⟫| ≤
      ζ * ⟪sys f γ y v, v⟫) (v : E) :
    |⟪fderiv ℝ (fderiv ℝ (gradient f)) y d v, v⟫| ≤
      (ζ + L * ‖d‖ ^ 2 / (2 * μ)) * ⟪sys f γ y v, v⟫ := by
  set M := fderiv ℝ (fderiv ℝ (gradient f)) y d
  set Er := fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y - M
  have hr : ‖Er‖ ≤ L * ‖d‖ ^ 2 / 2 := TensorFreeModel.hessian_remainder hf hT y d
  have hsplit : ⟪M v, v⟫ = ⟪(fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y) v, v⟫ -
      ⟪Er v, v⟫ := by
    simp [Er, inner_sub_left]
  have hEr : |⟪Er v, v⟫| ≤ L * ‖d‖ ^ 2 / 2 * ‖v‖ ^ 2 := by
    calc |⟪Er v, v⟫| ≤ ‖Er v‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖Er‖ * ‖v‖) * ‖v‖ := by gcongr; exact Er.le_opNorm v
      _ ≤ (L * ‖d‖ ^ 2 / 2 * ‖v‖) * ‖v‖ := by gcongr
      _ = _ := by ring
  have hv2 : ‖v‖ ^ 2 ≤ ⟪sys f γ y v, v⟫ / μ := by
    rw [le_div_iff₀ hμ]; linarith [hcoer v]
  have hc : L * ‖d‖ ^ 2 / 2 * ‖v‖ ^ 2 ≤ L * ‖d‖ ^ 2 / (2 * μ) * ⟪sys f γ y v, v⟫ := by
    have h0 : 0 ≤ L * ‖d‖ ^ 2 / 2 := by positivity
    calc L * ‖d‖ ^ 2 / 2 * ‖v‖ ^ 2 ≤ L * ‖d‖ ^ 2 / 2 * (⟪sys f γ y v, v⟫ / μ) :=
          mul_le_mul_of_nonneg_left hv2 h0
      _ = _ := by field_simp
  rw [hsplit]
  have := abs_sub (⟪(fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y) v, v⟫)
    (⟪Er v, v⟫)
  have := hstab v
  linarith

lemma tail_decrease {γ μ ζ : ℝ} (hμ : 0 < μ) (hζ : ζ ≤ 1 / 16)
    (c y d : E)
    (hcoer : ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪sys f γ y v, v⟫)
    (hd : fderiv ℝ (gradient f) y d + γ • d = -(gradient f y + γ • (y - c)))
    (hsmall : L * ⟪sys f γ y d, d⟫ ≤ μ ^ 2 / 2 ^ 20)
    (hstab : ∀ v, |⟪(fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y) v, v⟫| ≤
      ζ * ⟪sys f γ y v, v⟫) :
    regF f γ c (y + d) ≤ regF f γ c y - ⟪sys f γ y d, d⟫ / 3 := by
  set Λ := ⟪sys f γ y d, d⟫ with hΛ
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) (hcoer d)
  have hd2 : ‖d‖ ^ 2 ≤ Λ / μ := by rw [le_div_iff₀ hμ]; linarith [hcoer d]
  have hLd : L * ‖d‖ ^ 2 ≤ μ / 2 ^ 20 := small_step hL hμ hd2 hsmall
  have hrel := third_relative hf hL hT hμ y d hcoer hstab d
  have hz : ζ + L * ‖d‖ ^ 2 / (2 * μ) ≤ 1 / 8 := by
    have : L * ‖d‖ ^ 2 / (2 * μ) ≤ 1 / 2 ^ 21 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hle := (abs_le.mp (line_expansion hf hL hT γ c y d 1)).2
  simp only [one_smul, one_pow, abs_one, mul_one, one_mul] at hle
  have hgd := residual_inner hd
  have hsy := sys_inner f γ y d
  rw [hgd, ← hsy] at hle
  have hT3' := (abs_le.mp hrel).2
  have hL4 : L * ‖d‖ ^ 4 ≤ Λ / 2 ^ 20 := by
    have h1 : L * ‖d‖ ^ 4 = (L * ‖d‖ ^ 2) * ‖d‖ ^ 2 := by ring
    rw [h1]
    have h2 : (L * ‖d‖ ^ 2) * ‖d‖ ^ 2 ≤ (μ / 2 ^ 20) * (Λ / μ) :=
      mul_le_mul hLd hd2 (sq_nonneg _) (by positivity)
    have h3 : (μ / 2 ^ 20) * (Λ / μ) = Λ / 2 ^ 20 := by field_simp
    linarith
  have hprod : (ζ + L * ‖d‖ ^ 2 / (2 * μ)) * Λ ≤ 1 / 8 * Λ := mul_le_mul_of_nonneg_right hz hΛ0
  nlinarith

lemma tail_contraction {γ μ ζ : ℝ} (hμ : 0 < μ) (hζ0 : 0 ≤ ζ) (hζ : ζ ≤ 1 / 16)
    (c y d d' : E)
    (hcoer : ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪sys f γ y v, v⟫)
    (hd : fderiv ℝ (gradient f) y d + γ • d = -(gradient f y + γ • (y - c)))
    (hsmall : L * ⟪sys f γ y d, d⟫ ≤ μ ^ 2 / 2 ^ 20)
    (hstab : ∀ v, |⟪(fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y) v, v⟫| ≤
      ζ * ⟪sys f γ y v, v⟫)
    (hd' : fderiv ℝ (gradient f) (y + d) d' + γ • d' =
      -(gradient f (y + d) + γ • (y + d - c))) :
    ⟪sys f γ (y + d) d', d'⟫ ≤ ⟪sys f γ y d, d⟫ / 16 ∧
      regF f γ c (y + d) ≤ regF f γ c y - ⟪sys f γ y d, d⟫ / 3 := by
  refine ⟨?_, tail_decrease hf hL hT hμ hζ c y d hcoer hd hsmall hstab⟩
  set Λ := ⟪sys f γ y d, d⟫ with hΛ
  set Λ' := ⟪sys f γ (y + d) d', d'⟫ with hΛ'
  set P' := ⟪sys f γ y d', d'⟫ with hP'
  set M := fderiv ℝ (fderiv ℝ (gradient f)) y d with hM
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) (hcoer d)
  have hd2 : ‖d‖ ^ 2 ≤ Λ / μ := by rw [le_div_iff₀ hμ]; linarith [hcoer d]
  have hd'2 : ‖d'‖ ^ 2 ≤ P' / μ := by rw [le_div_iff₀ hμ]; linarith [hcoer d']
  have hP'0 : 0 ≤ P' := le_trans (by positivity) (hcoer d')
  have hLd : L * ‖d‖ ^ 2 ≤ μ / 2 ^ 20 := small_step hL hμ hd2 hsmall
  have hζ'b : ζ + L * ‖d‖ ^ 2 / (2 * μ) ≤ 1 / 8 := by
    have : L * ‖d‖ ^ 2 / (2 * μ) ≤ 1 / 2 ^ 21 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hζ'0 : 0 ≤ ζ + L * ‖d‖ ^ 2 / (2 * μ) := add_nonneg hζ0 (by positivity)
  have hrel := third_relative hf hL hT hμ y d hcoer hstab
  have hcross := relative_bilinear (sys_symm hf γ y) (third_symm hf y d) hζ'0 hrel d d'
  have hsys' : Λ' = P' + ⟪(fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y) d', d'⟫ := by
    rw [hΛ', hP', sys_inner, sys_inner]
    simp [inner_sub_left]
    ring
  have hPΛ : (1 - ζ) * P' ≤ Λ' := by
    have h1 := hstab d'
    have h2 := neg_abs_le (⟪(fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y) d', d'⟫)
    rw [hsys']; nlinarith
  set e₁ := gradient f (y + d) - gradient f y - fderiv ℝ (gradient f) y d - (1 / 2 : ℝ) • M d
    with he₁
  have he₁b : ‖e₁‖ ≤ L * ‖d‖ ^ 3 / 6 := TensorFreeModel.gradient_remainder hf hT y d
  have hg' : gradient f (y + d) + γ • (y + d - c) = (1 / 2 : ℝ) • M d + e₁ := by
    have : gradient f (y + d) + γ • (y + d - c) =
        (gradient f y + γ • (y - c)) + (fderiv ℝ (gradient f) y d + γ • d) +
          ((1 / 2 : ℝ) • M d + e₁) := by
      rw [he₁]; simp only [smul_sub, smul_add]; abel
    rw [this, hd]; abel
  have hΛ'eq : Λ' = -((1 / 2) * ⟪M d, d'⟫ + ⟪e₁, d'⟫) := by
    have h := residual_inner hd'
    rw [hg', inner_add_left, real_inner_smul_left] at h
    rw [hΛ', sys_inner]; linarith
  have hY : |⟪e₁, d'⟫| ≤ L * ‖d‖ ^ 3 / 6 * ‖d'‖ := by
    calc |⟪e₁, d'⟫| ≤ ‖e₁‖ * ‖d'‖ := abs_real_inner_le_norm _ _
      _ ≤ _ := by gcongr
  have hc : |⟪M d, d'⟫| ≤ 2 * (ζ + L * ‖d‖ ^ 2 / (2 * μ)) * Real.sqrt (Λ * P') := hcross
  have hbound : Λ' ≤ (ζ + L * ‖d‖ ^ 2 / (2 * μ)) * Real.sqrt (Λ * P') +
      L * ‖d‖ ^ 3 / 6 * ‖d'‖ := by
    have h1 := neg_abs_le (⟪M d, d'⟫)
    have h2 := neg_abs_le (⟪e₁, d'⟫)
    rw [hΛ'eq]; nlinarith
  have hK := cube_small hL hμ hd2 hLd
  have hY2 : (L * ‖d‖ ^ 3 / 6 * ‖d'‖) ^ 2 ≤ Λ / 2 ^ 40 * P' := by
    have e1 : (L * ‖d‖ ^ 3 / 6 * ‖d'‖) ^ 2 = (L * ‖d‖ ^ 3 / 6) ^ 2 * ‖d'‖ ^ 2 := by ring
    have h1 : (L * ‖d‖ ^ 3 / 6) ^ 2 * ‖d'‖ ^ 2 ≤ (L * ‖d‖ ^ 3 / 6) ^ 2 * (P' / μ) :=
      mul_le_mul_of_nonneg_left hd'2 (sq_nonneg _)
    have e2 : (L * ‖d‖ ^ 3 / 6) ^ 2 * (P' / μ) = ((L * ‖d‖ ^ 3 / 6) ^ 2 / μ) * P' := by ring
    rw [e1]
    exact h1.trans (e2 ▸ mul_le_mul_of_nonneg_right hK hP'0)
  exact contraction_scalar hΛ0 hP'0 hζ hζ'0 hζ'b hY2 hPΛ hbound

end Tail

end LongTails.Proofs.LogFreeTail
