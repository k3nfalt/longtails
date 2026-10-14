import LongTails.Proofs.BacktrackingCompositePotential
import Mathlib.Analysis.Complex.ExponentialBounds

open Set

namespace OracleTemplate.CompositeParameterFree

open LongTails.Setups.CompositeGeneralizedParameterFree

lemma logb_two_le_two_log {x : ℝ} (hx : 1 ≤ x) : Real.logb 2 x ≤ 2 * Real.log x := by
  have hl2 := Real.log_two_gt_d9
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

lemma max_logb_le {x : ℝ} (hx : 0 < x) : max 0 (Real.logb 2 x) ≤ 2 * Real.log (1 + x) := by
  have h1 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  rcases le_or_gt 1 x with h | h
  · rw [max_eq_right (Real.logb_nonneg (by norm_num) h)]
    calc Real.logb 2 x ≤ 2 * Real.log x := logb_two_le_two_log h
      _ ≤ 2 * Real.log (1 + x) := by
        have := Real.log_le_log hx (by linarith : x ≤ 1 + x)
        linarith
  · rw [max_eq_left (Real.logb_neg (by norm_num) hx h).le]
    linarith

lemma sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

variable {Ls L1 R Δ h0 : ℝ}

lemma Amin_pos (hLs : 0 < Ls) (hΔ : 0 < Δ) (hh0 : 0 < h0) :
    0 < Amin Ls L1 Δ h0 := by
  unfold Amin hbar; exact lt_min hh0 (by positivity)

lemma inv_Amin_le (hLs : 0 < Ls) (hΔ : 0 < Δ) (hh0 : 0 < h0) :
    1 / Amin Ls L1 Δ h0 ≤ 1 / h0 + 24 * Ls + 352 * L1 ^ 2 * Δ := by
  unfold Amin hbar
  have hd : 0 < 12 * Ls + 176 * L1 ^ 2 * Δ := by positivity
  rcases le_total h0 (1 / (12 * Ls + 176 * L1 ^ 2 * Δ) / 2) with h | h
  · rw [min_eq_left h]
    have : 0 ≤ 24 * Ls + 352 * L1 ^ 2 * Δ := by positivity
    linarith
  · rw [min_eq_right h]
    have e : 1 / (1 / (12 * Ls + 176 * L1 ^ 2 * Δ) / 2) = 24 * Ls + 352 * L1 ^ 2 * Δ := by
      field_simp; ring
    rw [e]
    have : 0 ≤ 1 / h0 := by positivity
    linarith

lemma Amin_ge (hLs : 0 < Ls) (hΔ : 0 < Δ) (hh0 : 0 < h0) :
    h0 / (1 + h0 * (24 * Ls + 352 * L1 ^ 2 * Δ)) ≤ Amin Ls L1 Δ h0 := by
  have hA := Amin_pos (L1 := L1) hLs hΔ hh0
  have h1 := inv_Amin_le (L1 := L1) hLs hΔ hh0
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hA] at h1
  have e : (1 / h0 + 24 * Ls + 352 * L1 ^ 2 * Δ) * Amin Ls L1 Δ h0 * h0 =
      (1 + h0 * (24 * Ls + 352 * L1 ^ 2 * Δ)) * Amin Ls L1 Δ h0 := by
    field_simp; ring
  have h2 := mul_le_mul_of_nonneg_right h1 hh0.le
  rw [one_mul, e] at h2
  linarith

lemma inv_sqrt_Amin_le (hLs : 0 < Ls) (hL1 : 0 ≤ L1) (hΔ : 0 < Δ) (hh0 : 0 < h0) :
    1 / Real.sqrt (Amin Ls L1 Δ h0) ≤
      1 / Real.sqrt h0 + 5 * Real.sqrt Ls + 19 * L1 * Real.sqrt Δ := by
  have hA := Amin_pos (L1 := L1) hLs hΔ hh0
  have h1 := inv_Amin_le (L1 := L1) hLs hΔ hh0
  have e1 : 1 / Real.sqrt (Amin Ls L1 Δ h0) = Real.sqrt (1 / Amin Ls L1 Δ h0) := by
    rw [one_div, one_div, Real.sqrt_inv]
  have e2 : 1 / Real.sqrt h0 = Real.sqrt (1 / h0) := by
    rw [one_div, one_div, Real.sqrt_inv]
  rw [e1, e2]
  have h2 : Real.sqrt (24 * Ls) ≤ 5 * Real.sqrt Ls := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hLs.le]; nlinarith
  have h3 : Real.sqrt (352 * L1 ^ 2 * Δ) ≤ 19 * L1 * Real.sqrt Δ := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, mul_pow, Real.sq_sqrt hΔ.le]
    nlinarith [mul_nonneg (sq_nonneg L1) hΔ.le]
  calc Real.sqrt (1 / Amin Ls L1 Δ h0)
      ≤ Real.sqrt (1 / h0 + 24 * Ls + 352 * L1 ^ 2 * Δ) := Real.sqrt_le_sqrt h1
    _ ≤ Real.sqrt (1 / h0 + 24 * Ls) + Real.sqrt (352 * L1 ^ 2 * Δ) :=
        sqrt_add_le (by positivity) (by positivity)
    _ ≤ Real.sqrt (1 / h0) + Real.sqrt (24 * Ls) + Real.sqrt (352 * L1 ^ 2 * Δ) := by
        have := sqrt_add_le (a := 1 / h0) (b := 24 * Ls) (by positivity) (by positivity)
        linarith
    _ ≤ Real.sqrt (1 / h0) + 5 * Real.sqrt Ls + 19 * L1 * Real.sqrt Δ := by linarith

lemma hlow_ge (hLs : 0 < Ls) (hL1 : 0 ≤ L1) (hR : 0 < R) (hΔ : 0 < Δ) (hh0 : 0 < h0) :
    h0 / (2 * ((1 + h0 * (40 * Ls + 400 * L1 ^ 2 * Δ)) *
      (8 * (1 + 32 * L1 * R) ^ 2 + 200 * L1 ^ 2 * R ^ 2))) ≤ hlow Ls L1 R Δ h0 := by
  set U := 1 + h0 * (40 * Ls + 400 * L1 ^ 2 * Δ) with hU
  set V := 8 * (1 + 32 * L1 * R) ^ 2 + 200 * L1 ^ 2 * R ^ 2 with hV
  have hU1 : 1 ≤ U := by
    simp only [U]; nlinarith [mul_nonneg hh0.le (by positivity : (0:ℝ) ≤ 40 * Ls + 400 * L1 ^ 2 * Δ)]
  have hV8 : 8 ≤ V := by simp only [V]; nlinarith [mul_nonneg hL1 hR.le, sq_nonneg (L1 * R)]
  have hUV : 0 < U * V := by positivity
  have hA := Amin_pos (L1 := L1) hLs hΔ hh0
  have hAge := Amin_ge (L1 := L1) hLs hΔ hh0
  set Am := Amin Ls L1 Δ h0 with hAm
  have hD : 0 < 1 + h0 * (24 * Ls + 352 * L1 ^ 2 * Δ) := by positivity
  have hAmU : h0 ≤ Am * U := by
    rw [div_le_iff₀ hD] at hAge
    have : 1 + h0 * (24 * Ls + 352 * L1 ^ 2 * Δ) ≤ U := by
      simp only [U]; nlinarith [mul_nonneg hh0.le (by positivity : (0:ℝ) ≤ 16 * Ls + 48 * L1 ^ 2 * Δ)]
    nlinarith
  have hAmh : 8 * Ls * Am ≤ 1 / 3 := by
    have hle : Am ≤ hbar Ls L1 Δ / 2 := min_le_right _ _
    unfold hbar at hle
    have hd : 0 < 12 * Ls + 176 * L1 ^ 2 * Δ := by positivity
    rw [le_div_iff₀ (by norm_num), le_div_iff₀ hd] at hle
    nlinarith [mul_nonneg hA.le (by positivity : (0:ℝ) ≤ 176 * L1 ^ 2 * Δ), mul_nonneg hA.le hLs.le]
  have h1 : h0 / (U * V) ≤ hbar Ls L1 Δ := by
    unfold hbar
    rw [div_le_div_iff₀ hUV (by positivity)]
    have hU8 : U * 8 ≤ U * V := mul_le_mul_of_nonneg_left hV8 (by linarith)
    have : h0 * (12 * Ls + 176 * L1 ^ 2 * Δ) ≤ U := by
      simp only [U]; nlinarith [mul_nonneg hh0.le (by positivity : (0:ℝ) ≤ 28 * Ls + 224 * L1 ^ 2 * Δ)]
    nlinarith
  have h2 : h0 / (U * V) ≤ gfun Ls L1 R Am := by
    unfold gfun
    apply le_min
    · rw [div_le_div_iff₀ hUV (by positivity)]
      have hV' : 8 * Ls * Am + 96 * L1 ^ 2 * R ^ 2 ≤ V := by
        simp only [V]; nlinarith [mul_nonneg hL1 hR.le, sq_nonneg (L1 * R)]
      have p1 := mul_le_mul_of_nonneg_left hV' hh0.le
      have p2 := mul_le_mul_of_nonneg_right hAmU (by linarith : (0:ℝ) ≤ V)
      nlinarith
    · rw [div_le_div_iff₀ hUV (by positivity)]
      have hV' : 4 * (1 + 32 * L1 * R) ^ 2 ≤ V := by
        simp only [V]; nlinarith [sq_nonneg (1 + 32 * L1 * R), sq_nonneg (L1 * R)]
      have p1 := mul_le_mul_of_nonneg_left hV' hh0.le
      have p2 := mul_le_mul_of_nonneg_right hAmU (by linarith : (0:ℝ) ≤ V)
      nlinarith
  calc h0 / (2 * (U * V)) = h0 / (U * V) / 2 := by field_simp
    _ ≤ min (hbar Ls L1 Δ) (gfun Ls L1 R Am) / 2 :=
        div_le_div_of_nonneg_right (le_min h1 h2) (by norm_num)
    _ = hlow Ls L1 R Δ h0 := rfl

lemma L0c_le (hLs : 0 < Ls) (hΔ : 0 < Δ) (hh0 : 0 < h0) :
    L0c Ls (Amin Ls L1 Δ h0) ≤
      1 + 2 * Real.log (5 / 2 + 1 / (16 * Ls * h0) + 22 * L1 ^ 2 * Δ / Ls) := by
  have hA := Amin_pos (L1 := L1) hLs hΔ hh0
  have h1 := inv_Amin_le (L1 := L1) hLs hΔ hh0
  unfold L0c
  have hx : 0 < 1 / (16 * Ls * Amin Ls L1 Δ h0) := by positivity
  have h2 := max_logb_le hx
  have h3 : 1 + 1 / (16 * Ls * Amin Ls L1 Δ h0) ≤
      5 / 2 + 1 / (16 * Ls * h0) + 22 * L1 ^ 2 * Δ / Ls := by
    have e : 1 / (16 * Ls * Amin Ls L1 Δ h0) = (1 / Amin Ls L1 Δ h0) / (16 * Ls) := by
      field_simp
    rw [e]
    have := div_le_div_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ 16 * Ls)
    have e2 : (1 / h0 + 24 * Ls + 352 * L1 ^ 2 * Δ) / (16 * Ls) =
        1 / (16 * Ls * h0) + 3 / 2 + 22 * L1 ^ 2 * Δ / Ls := by
      field_simp; ring
    linarith
  have := Real.log_le_log (by positivity) h3
  linarith

lemma cap_ratio_le (hLs : 0 < Ls) (hL1 : 0 ≤ L1) (hR : 0 < R) (hΔ : 0 < Δ) (hh0 : 0 < h0) :
    δc Ls / ρc L1 R / Real.sqrt (Amin Ls L1 Δ h0) ≤
      (12 + 400 * L1 * R) * (1 + 1 / Real.sqrt (Ls * h0) + L1 * Real.sqrt (Δ / Ls)) := by
  have hA := Amin_pos (L1 := L1) hLs hΔ hh0
  have h1 := inv_sqrt_Amin_le hLs hL1 hΔ hh0
  have hs32 : 5 ≤ Real.sqrt 32 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hsLs : 0 < Real.sqrt Ls := Real.sqrt_pos.mpr hLs
  have hsh0 : 0 < Real.sqrt h0 := Real.sqrt_pos.mpr hh0
  have hsA : 0 < Real.sqrt (Amin Ls L1 Δ h0) := Real.sqrt_pos.mpr hA
  have e : δc Ls / ρc L1 R / Real.sqrt (Amin Ls L1 Δ h0) =
      (12 + 400 * L1 * R) / (4 * Real.sqrt 32 * Real.sqrt Ls) * (1 / Real.sqrt (Amin Ls L1 Δ h0)) := by
    unfold δc ρc
    rw [Real.sqrt_mul (by norm_num)]
    field_simp
  rw [e]
  have hcoef : 0 ≤ (12 + 400 * L1 * R) := by positivity
  have h2 : (12 + 400 * L1 * R) / (4 * Real.sqrt 32 * Real.sqrt Ls) * (1 / Real.sqrt (Amin Ls L1 Δ h0)) ≤
      (12 + 400 * L1 * R) / (4 * Real.sqrt 32 * Real.sqrt Ls) *
        (1 / Real.sqrt h0 + 5 * Real.sqrt Ls + 19 * L1 * Real.sqrt Δ) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  refine h2.trans ?_
  rw [Real.sqrt_mul hLs.le, Real.sqrt_div hΔ.le]
  have hden : 20 * Real.sqrt Ls ≤ 4 * Real.sqrt 32 * Real.sqrt Ls := by nlinarith
  have hpos : 0 < 20 * Real.sqrt Ls := by positivity
  have h3 : (12 + 400 * L1 * R) / (4 * Real.sqrt 32 * Real.sqrt Ls) ≤ (12 + 400 * L1 * R) / (20 * Real.sqrt Ls) :=
    div_le_div_of_nonneg_left hcoef hpos hden
  have hsum : 0 ≤ 1 / Real.sqrt h0 + 5 * Real.sqrt Ls + 19 * L1 * Real.sqrt Δ := by positivity
  calc (12 + 400 * L1 * R) / (4 * Real.sqrt 32 * Real.sqrt Ls) *
        (1 / Real.sqrt h0 + 5 * Real.sqrt Ls + 19 * L1 * Real.sqrt Δ)
      ≤ (12 + 400 * L1 * R) / (20 * Real.sqrt Ls) *
        (1 / Real.sqrt h0 + 5 * Real.sqrt Ls + 19 * L1 * Real.sqrt Δ) :=
        mul_le_mul_of_nonneg_right h3 hsum
    _ = (12 + 400 * L1 * R) * ((1 / (Real.sqrt Ls * Real.sqrt h0)) / 20 + 1 / 4 +
        (19 / 20) * (L1 * (Real.sqrt Δ / Real.sqrt Ls))) := by
        field_simp; ring
    _ ≤ (12 + 400 * L1 * R) * (1 + 1 / (Real.sqrt Ls * Real.sqrt h0) + L1 * (Real.sqrt Δ / Real.sqrt Ls)) := by
        apply mul_le_mul_of_nonneg_left _ hcoef
        have : 0 ≤ 1 / (Real.sqrt Ls * Real.sqrt h0) := by positivity
        have : 0 ≤ L1 * (Real.sqrt Δ / Real.sqrt Ls) := by positivity
        linarith

lemma trials_sufficient (hLs : 0 < Ls) (hL1 : 0 ≤ L1) (hR : 0 < R) (hΔ : 0 < Δ) (hh0 : 0 < h0)
    {ε : ℝ} :
    2 * (1 + L0c Ls (Amin Ls L1 Δ h0) +
        4 / 3 * (4 * Real.sqrt 32 * Real.sqrt (Ls * R ^ 2 / ε) + (1 + ρc L1 R) / ρc L1 R *
          Real.log (1 + δc Ls / ρc L1 R / Real.sqrt (Amin Ls L1 Δ h0)))) +
      Real.logb 2 (h0 / hlow Ls L1 R Δ h0) ≤
    4 + 61 * Real.sqrt (Ls * R ^ 2 / ε) +
      (35 + 1067 * L1 * R) *
        Real.log (1 + (12 + 400 * L1 * R) * (1 + 1 / Real.sqrt (Ls * h0) + L1 * Real.sqrt (Δ / Ls))) +
      4 * Real.log (5 / 2 + 1 / (16 * Ls * h0) + 22 * L1 ^ 2 * Δ / Ls) +
      2 * Real.log (2 * ((1 + h0 * (40 * Ls + 400 * L1 ^ 2 * Δ)) *
        (8 * (1 + 32 * L1 * R) ^ 2 + 200 * L1 ^ 2 * R ^ 2))) := by
  have hA := Amin_pos (L1 := L1) hLs hΔ hh0
  have hρ := ρc_pos hL1 hR
  have hδ := δc_pos hLs
  have hL := L0c_le (L1 := L1) hLs hΔ hh0
  have hcap := cap_ratio_le hLs hL1 hR hΔ hh0
  have hlowpos : 0 < hlow Ls L1 R Δ h0 := by
    have := hlow_ge hLs hL1 hR hΔ hh0
    have : 0 < h0 / (2 * ((1 + h0 * (40 * Ls + 400 * L1 ^ 2 * Δ)) *
      (8 * (1 + 32 * L1 * R) ^ 2 + 200 * L1 ^ 2 * R ^ 2))) := by positivity
    linarith
  set U := 1 + h0 * (40 * Ls + 400 * L1 ^ 2 * Δ) with hU
  set V := 8 * (1 + 32 * L1 * R) ^ 2 + 200 * L1 ^ 2 * R ^ 2 with hV
  have hU1 : 1 ≤ U := by simp only [U]; nlinarith [mul_nonneg hh0.le (by positivity : (0:ℝ) ≤ 40 * Ls + 400 * L1 ^ 2 * Δ)]
  have hV8 : 8 ≤ V := by simp only [V]; nlinarith [mul_nonneg hL1 hR.le, sq_nonneg (L1 * R)]
  have hrej : Real.logb 2 (h0 / hlow Ls L1 R Δ h0) ≤ 2 * Real.log (2 * (U * V)) := by
    have h1 : h0 / hlow Ls L1 R Δ h0 ≤ 2 * (U * V) := by
      have := hlow_ge hLs hL1 hR hΔ hh0
      rw [div_le_iff₀ hlowpos]
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have h2 : (1 : ℝ) ≤ h0 / hlow Ls L1 R Δ h0 := by
      rw [le_div_iff₀ hlowpos, one_mul]
      have e1 := gfun_le_quarter (Ls := Ls) hL1 hR hA.le
      have e2 := min_le_right (hbar Ls L1 Δ) (gfun Ls L1 R (Amin Ls L1 Δ h0))
      have e3 : Amin Ls L1 Δ h0 ≤ h0 := min_le_left _ _
      unfold hlow
      linarith
    calc Real.logb 2 (h0 / hlow Ls L1 R Δ h0) ≤ 2 * Real.log (h0 / hlow Ls L1 R Δ h0) :=
          logb_two_le_two_log h2
      _ ≤ 2 * Real.log (2 * (U * V)) := by
          have := Real.log_le_log (by positivity) h1
          linarith
  have hρe : (1 + ρc L1 R) / ρc L1 R = 13 + 400 * L1 * R := by
    unfold ρc; field_simp; ring
  rw [hρe]
  have hlog : Real.log (1 + δc Ls / ρc L1 R / Real.sqrt (Amin Ls L1 Δ h0)) ≤
      Real.log (1 + (12 + 400 * L1 * R) * (1 + 1 / Real.sqrt (Ls * h0) + L1 * Real.sqrt (Δ / Ls))) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlog0 : 0 ≤ Real.log (1 + (12 + 400 * L1 * R) * (1 + 1 / Real.sqrt (Ls * h0) + L1 * Real.sqrt (Δ / Ls))) :=
    Real.log_nonneg (by
      have : 0 ≤ (12 + 400 * L1 * R) * (1 + 1 / Real.sqrt (Ls * h0) + L1 * Real.sqrt (Δ / Ls)) := by positivity
      linarith)
  have hs32 : Real.sqrt 32 ≤ 57 / 10 := by
    rw [Real.sqrt_le_iff]; norm_num
  have hsq : 0 ≤ Real.sqrt (Ls * R ^ 2 / ε) := Real.sqrt_nonneg _
  have hLR : 0 ≤ L1 * R := by positivity
  have hterm : 4 / 3 * (4 * Real.sqrt 32 * Real.sqrt (Ls * R ^ 2 / ε)) ≤ 61 / 2 * Real.sqrt (Ls * R ^ 2 / ε) := by
    nlinarith
  have hterm2 : 4 / 3 * ((13 + 400 * L1 * R) * Real.log (1 + δc Ls / ρc L1 R / Real.sqrt (Amin Ls L1 Δ h0))) ≤
      (35 / 2 + 1067 / 2 * L1 * R) *
        Real.log (1 + (12 + 400 * L1 * R) * (1 + 1 / Real.sqrt (Ls * h0) + L1 * Real.sqrt (Δ / Ls))) := by
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ) ≤ 13 + 400 * L1 * R)
    nlinarith [mul_nonneg hLR hlog0]
  linarith

end OracleTemplate.CompositeParameterFree
