import LongTails.Proofs.LogFreeTail

namespace LongTails.Proofs.LogFreeEscape

open scoped RealInnerProductSpace
open LongTails.Proofs.LogFreeGeometry LongTails.Proofs.LogFreeLinearAlgebra
  LongTails.Proofs.LogFreeSteps LongTails.Proofs.LogFreeTail

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma cube_sign {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (s : ℝ) : (-(σ * s)) ^ 3 = -(σ * s ^ 3) := by
  rcases hσ with h | h <;> subst h <;> ring

lemma sign_sq {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) : σ ^ 2 = 1 := by
  rcases hσ with h | h <;> subst h <;> norm_num

section Escape

variable {f : E → ℝ} (hf : ContDiff ℝ 3 f) {L : ℝ} (hL : 0 ≤ L)
  (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
    fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
include hf hL hT

set_option maxHeartbeats 1000000 in
lemma magnified_escape {γ μ ζ r u s σ : ℝ} (hr : 0 < r) (hu : u = L * r ^ 4)
    (hμ : μ = 128 * L * r ^ 2) (hγ : γ = 256 * L * r ^ 2) (hLpos : 0 < L)
    (c y d v : E)
    (hcoer : ∀ w, μ * ‖w‖ ^ 2 ≤ ⟪sys f γ y w, w⟫)
    (hd : fderiv ℝ (gradient f) y d + γ • d = -(gradient f y + γ • (y - c)))
    (hΛpos : 0 < ⟪sys f γ y d, d⟫) (hΛu : ⟪sys f γ y d, d⟫ ≤ u / 2 ^ 20)
    (hs : s = 8 * Real.sqrt (u / ⟪sys f γ y d, d⟫))
    (hv : ⟪sys f γ y v, v⟫ = 1)
    (hσ : σ = 1 ∨ σ = -1)
    (hgap : ζ < σ * ⟪(fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y) v, v⟫)
    (hsmall : L * ⟪sys f γ y d, d⟫ ≤ ζ * μ ^ 2)
    (hdist : γ * ‖y - c‖ * r ≤ u / 2)
    (hbig : 18 ≤ s * ζ) :
    min (min (f (y - (σ * s) • d + r • (‖v‖⁻¹ • v)))
      (f (y - (σ * s) • d - r • (‖v‖⁻¹ • v)))) (f (y + (σ * s) • d)) ≤ f y - s * ζ * u := by
  set Λ := ⟪sys f γ y d, d⟫ with hΛ
  set M := fderiv ℝ (fderiv ℝ (gradient f)) y d with hM
  have hμpos : 0 < μ := by rw [hμ]; positivity
  have hu0 : 0 < u := by rw [hu]; positivity
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> subst h <;> norm_num
  have hσ2 := sign_sq hσ
  have hd2 : ‖d‖ ^ 2 ≤ Λ / μ := by rw [le_div_iff₀ hμpos]; linarith [hcoer d]
  have hv2 : ‖v‖ ^ 2 ≤ 1 / μ := by rw [le_div_iff₀ hμpos]; linarith [hcoer v]
  have hvne : v ≠ 0 := by
    intro h; rw [h] at hv; simp at hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hs2Λ : s ^ 2 * Λ = 64 * u := by
    rw [hs, mul_pow, Real.sq_sqrt (div_nonneg hu0.le hΛpos.le)]; field_simp; ring
  have hsd2 : (s * ‖d‖) ^ 2 ≤ r ^ 2 / 2 := by
    have h1 : (s * ‖d‖) ^ 2 = s ^ 2 * ‖d‖ ^ 2 := by ring
    have h2 : s ^ 2 * ‖d‖ ^ 2 ≤ s ^ 2 * (Λ / μ) := mul_le_mul_of_nonneg_left hd2 (sq_nonneg _)
    have h3 : s ^ 2 * (Λ / μ) = 64 * u / μ := by rw [← hs2Λ]; ring
    have h4 : 64 * u / μ = r ^ 2 / 2 := by rw [hu, hμ]; field_simp; ring
    linarith
  have hsd : s * ‖d‖ ≤ r := by
    have : (s * ‖d‖) ^ 2 ≤ r ^ 2 := by linarith [sq_nonneg r]
    exact (pow_le_pow_iff_left₀ (by positivity) hr.le (by norm_num)).mp this
  set Er := fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y - M with hEr
  have hrem : ‖Er‖ ≤ L * ‖d‖ ^ 2 / 2 := TensorFreeModel.hessian_remainder hf hT y d
  have hEv : |⟪Er v, v⟫| ≤ ζ / 2 := by
    calc |⟪Er v, v⟫| ≤ ‖Er v‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖Er‖ * ‖v‖) * ‖v‖ := by gcongr; exact Er.le_opNorm v
      _ = ‖Er‖ * ‖v‖ ^ 2 := by ring
      _ ≤ (L * ‖d‖ ^ 2 / 2) * (1 / μ) := mul_le_mul hrem hv2 (sq_nonneg _) (by positivity)
      _ ≤ (L * (Λ / μ) / 2) * (1 / μ) := by gcongr
      _ = L * Λ / (2 * μ ^ 2) := by field_simp
      _ ≤ ζ / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hθ : ζ / 2 ≤ σ * ⟪M v, v⟫ := by
    have hsplit : ⟪M v, v⟫ = ⟪(fderiv ℝ (gradient f) (y + d) - fderiv ℝ (gradient f) y) v, v⟫ -
        ⟪Er v, v⟫ := by
      simp [hEr, inner_sub_left]
    rw [hsplit, mul_sub]
    have : |σ * ⟪Er v, v⟫| ≤ ζ / 2 := by rw [abs_mul, hσabs, one_mul]; exact hEv
    have := le_abs_self (σ * ⟪Er v, v⟫)
    linarith
  set z := y - (σ * s) • d with hz
  have hzr : z = y + (-(σ * s)) • d := by rw [hz, neg_smul, ← sub_eq_add_neg]
  have hHz := TensorFreeModel.hessian_remainder hf hT y ((-(σ * s)) • d)
  rw [← hzr] at hHz
  have hzd : ‖(-(σ * s)) • d‖ = s * ‖d‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_mul, hσabs, one_mul, abs_of_nonneg hs0]
  have hHzv : ⟪fderiv ℝ (gradient f) z v, v⟫ ≤ -(s * ζ / 4) := by
    set Ez := fderiv ℝ (gradient f) z - fderiv ℝ (gradient f) y -
      fderiv ℝ (fderiv ℝ (gradient f)) y ((-(σ * s)) • d)
    have hsp : ⟪fderiv ℝ (gradient f) z v, v⟫ = ⟪fderiv ℝ (gradient f) y v, v⟫ +
        (-(σ * s)) * ⟪M v, v⟫ + ⟪Ez v, v⟫ := by
      have : fderiv ℝ (gradient f) z = fderiv ℝ (gradient f) y +
          (-(σ * s)) • M + Ez := by
        simp only [Ez, map_smul, hM]; abel
      rw [this]
      simp [inner_add_left, real_inner_smul_left]
    have hEz : |⟪Ez v, v⟫| ≤ L * r ^ 2 / 4 * ‖v‖ ^ 2 := by
      calc |⟪Ez v, v⟫| ≤ ‖Ez v‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖Ez‖ * ‖v‖) * ‖v‖ := by gcongr; exact Ez.le_opNorm v
        _ = ‖Ez‖ * ‖v‖ ^ 2 := by ring
        _ ≤ (L * (s * ‖d‖) ^ 2 / 2) * ‖v‖ ^ 2 := by
            gcongr; rw [← hzd]; exact hHz
        _ ≤ (L * (r ^ 2 / 2) / 2) * ‖v‖ ^ 2 := by gcongr
        _ = _ := by ring
    have hHy : ⟪fderiv ℝ (gradient f) y v, v⟫ = 1 - γ * ‖v‖ ^ 2 := by
      have := sys_inner f γ y v; rw [hv] at this; linarith
    have hprod : s * (ζ / 2) ≤ s * (σ * ⟪M v, v⟫) := mul_le_mul_of_nonneg_left hθ hs0
    have hγv : L * r ^ 2 / 4 * ‖v‖ ^ 2 ≤ γ * ‖v‖ ^ 2 := by
      rw [hγ]; nlinarith [sq_nonneg ‖v‖]
    have hEz' := (abs_le.mp hEz).2
    rw [hsp, hHy]
    linarith
  set e := ‖v‖⁻¹ • v with he
  have hen : ‖e‖ = 1 := by rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']
  have hHe : ⟪fderiv ℝ (gradient f) z e, e⟫ ≤ -((s * ζ * μ) / 4) := by
    have : ⟪fderiv ℝ (gradient f) z e, e⟫ = ⟪fderiv ℝ (gradient f) z v, v⟫ / ‖v‖ ^ 2 := by
      have hvne' : ‖v‖ ≠ 0 := hvpos.ne'
      rw [he, map_smul, real_inner_smul_left, real_inner_smul_right]
      field_simp
    rw [this, div_le_iff₀ (by positivity)]
    have hv2' : μ * ‖v‖ ^ 2 ≤ 1 := by
      have := hcoer v; rw [hv] at this; exact this
    have hsz : 0 ≤ s * ζ := by linarith
    nlinarith [mul_nonneg hsz (by linarith : (0 : ℝ) ≤ 1 - μ * ‖v‖ ^ 2)]
  have hesc := plain_escape hf hL hT (s * ζ * μ) r z e hen hHe
  have hlin : |s * ⟪gradient f y, d⟫| ≤ s * Λ + u / 2 := by
    have hgd := residual_inner hd
    have hsy := sys_inner f γ y d
    have hsplit : ⟪gradient f y, d⟫ = -Λ - γ * ⟪y - c, d⟫ := by
      have : ⟪gradient f y + γ • (y - c), d⟫ = ⟪gradient f y, d⟫ + γ * ⟪y - c, d⟫ := by
        rw [inner_add_left, real_inner_smul_left]
      rw [← hsy, ← hΛ] at hgd; linarith
    rw [hsplit]
    have hcs : |⟪y - c, d⟫| ≤ ‖y - c‖ * ‖d‖ := abs_real_inner_le_norm _ _
    have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
    have h2 : s * (γ * |⟪y - c, d⟫|) ≤ u / 2 := by
      calc s * (γ * |⟪y - c, d⟫|) ≤ s * (γ * (‖y - c‖ * ‖d‖)) := by gcongr
        _ = γ * ‖y - c‖ * (s * ‖d‖) := by ring
        _ ≤ γ * ‖y - c‖ * r := by gcongr
        _ ≤ u / 2 := hdist
    have hsγ : 0 ≤ s * γ := mul_nonneg hs0 hγ0
    have h3 : s * γ * (-|⟪y - c, d⟫|) ≤ s * γ * ⟪y - c, d⟫ :=
      mul_le_mul_of_nonneg_left (neg_abs_le _) hsγ
    have h4 : s * γ * ⟪y - c, d⟫ ≤ s * γ * |⟪y - c, d⟫| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hsγ
    have hsΛ0 : 0 ≤ s * Λ := mul_nonneg hs0 hΛpos.le
    rw [abs_le]; constructor <;> linarith
  have hsΛ : s * Λ ≤ u / 128 := by
    have h1 : (s * Λ) ^ 2 = 64 * u * Λ := by rw [← hs2Λ]; ring
    have h2 : 64 * u * Λ ≤ (u / 128) ^ 2 := by
      have : 64 * u * Λ ≤ 64 * u * (u / 2 ^ 20) := mul_le_mul_of_nonneg_left hΛu (by positivity)
      nlinarith
    nlinarith [sq_nonneg (s * Λ - u / 128), mul_nonneg hs0 hΛpos.le]
  have hquad : s ^ 2 / 2 * ⟪fderiv ℝ (gradient f) y d, d⟫ ≤ 32 * u := by
    have hsy := sys_inner f γ y d
    have hγ0 : 0 ≤ γ := by rw [hγ]; positivity
    have : ⟪fderiv ℝ (gradient f) y d, d⟫ ≤ Λ := by
      rw [hΛ, hsy]; nlinarith [sq_nonneg ‖d‖]
    nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr this), hs2Λ]
  have hquart : L * ‖d‖ ^ 4 * |σ * s| ^ 4 ≤ u / 4 := by
    have : L * ‖d‖ ^ 4 * |σ * s| ^ 4 = L * ((s * ‖d‖) ^ 2) ^ 2 := by
      rw [abs_mul, hσabs, one_mul, abs_of_nonneg hs0]; ring
    rw [this]
    have h0 : 0 ≤ (s * ‖d‖) ^ 2 := sq_nonneg _
    have : ((s * ‖d‖) ^ 2) ^ 2 ≤ (r ^ 2 / 2) ^ 2 := pow_le_pow_left₀ h0 hsd2 2
    rw [hu]; nlinarith
  have hquart' : L * ‖d‖ ^ 4 * |-(σ * s)| ^ 4 ≤ u / 4 := by rwa [abs_neg]
  have hzv := (abs_le.mp (ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT y d
    (-(σ * s)))).2
  rw [← hzr] at hzv
  have hwv := (abs_le.mp (ThirdOrderObjectiveGeometry.directional_cubic_remainder hf hL hT y d
    (σ * s))).2
  have hc3 := cube_sign hσ s
  have hτ : ⟪fderiv ℝ (fderiv ℝ (gradient f)) y d d, d⟫ = ⟪M d, d⟫ := rfl
  rw [hτ, hc3] at hzv
  rw [hτ] at hwv
  have hs3 : (σ * s) ^ 3 = σ * s ^ 3 := by
    rcases hσ with h | h <;> subst h <;> ring
  have hs2 : (σ * s) ^ 2 = s ^ 2 := by rw [mul_pow, hσ2, one_mul]
  have hs2' : (-(σ * s)) ^ 2 = s ^ 2 := by rw [neg_sq, hs2]
  rw [hs3, hs2] at hwv
  rw [hs2'] at hzv
  have hlin' := abs_le.mp hlin
  have hσlin : |σ| * |s * ⟪gradient f y, d⟫| ≤ s * Λ + u / 2 := by rw [hσabs, one_mul]; exact hlin
  have hlinσ : |⟪gradient f y, d⟫ * (σ * s)| ≤ s * Λ + u / 2 := by
    rw [show ⟪gradient f y, d⟫ * (σ * s) = σ * (s * ⟪gradient f y, d⟫) by ring, abs_mul]
    exact hσlin
  have hlinσ' := abs_le.mp hlinσ
  have hmu : s * ζ * μ * r ^ 2 / 8 = 16 * (s * ζ) * u := by rw [hμ, hu]; ring
  have hLr : L * r ^ 4 = u := hu.symm
  rw [hmu, hLr] at hesc
  have hsu : 18 * u ≤ s * ζ * u := mul_le_mul_of_nonneg_right hbig hu0.le
  by_cases hcase : -(σ * s ^ 3 * ⟪M d, d⟫) / 6 ≤ 8 * (s * ζ) * u
  · have hz' : f z ≤ f y + (s * Λ + u / 2) + 32 * u + 8 * (s * ζ) * u + u / 4 := by
      linarith
    have h1 := min_le_left (min (f (z + r • e)) (f (z - r • e))) (f (y + (σ * s) • d))
    linarith
  · have hcase' : σ * s ^ 3 * ⟪M d, d⟫ / 6 < -(8 * (s * ζ) * u) := by
      have := lt_of_not_ge hcase; linarith
    have hw' : f (y + (σ * s) • d) ≤ f y + (s * Λ + u / 2) + 32 * u - 8 * (s * ζ) * u + u / 4 := by
      linarith
    have h1 := min_le_right (min (f (z + r • e)) (f (z - r • e))) (f (y + (σ * s) • d))
    linarith

end Escape

end LongTails.Proofs.LogFreeEscape
