import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.MeanInequalitiesPow

namespace LongTails.Proofs.TailObliviousGeometry

open scoped RealInnerProductSpace

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma concave_power_tangent {r s t : ℝ} (hr1 : 0 ≤ r) (hr2 : r ≤ 2) (hs : 0 < s)
    (ht : 0 ≤ t) :
    t ^ (r / 2) ≤ s ^ (r / 2) + r / 2 * s ^ (r / 2 - 1) * (t - s) := by
  have hp0 : 0 ≤ r / 2 := by positivity
  have hp1 : r / 2 ≤ 1 := by linarith
  have hb := rpow_one_add_le_one_add_mul_self (s := t / s - 1)
    (by have : 0 ≤ t / s := div_nonneg ht hs.le; linarith) hp0 hp1
  have hts : 1 + (t / s - 1) = t / s := by ring
  rw [hts, Real.div_rpow ht hs.le] at hb
  have hsp : 0 < s ^ (r / 2) := Real.rpow_pos_of_pos hs _
  have hpow : s ^ (r / 2 - 1) = s ^ (r / 2) / s := by
    rw [Real.rpow_sub hs, Real.rpow_one]
  rw [div_le_iff₀ hsp] at hb
  rw [hpow]
  have : s ^ (r / 2) / s * (t - s) = s ^ (r / 2) * (t / s - 1) := by
    field_simp
  rw [mul_assoc, this]
  nlinarith

omit [NormedSpace ℝ E] in
lemma norm_rpow_eq_sq_rpow (x : E) (r : ℝ) : ‖x‖ ^ r = (‖x‖ ^ 2) ^ (r / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x)]
  congr 1
  push_cast
  ring

noncomputable def powerDual (J : E → E →L[ℝ] ℝ) (r : ℝ) (x : E) : E →L[ℝ] ℝ :=
  (‖x‖ ^ (r - 2)) • J x

lemma powerDual_norm (J : E → E →L[ℝ] ℝ) (hJ : ∀ x, ‖J x‖ ≤ ‖x‖) (r : ℝ)
    (x : E) : ‖powerDual J r x‖ ≤ ‖x‖ ^ (r - 1) := by
  unfold powerDual
  rcases (norm_nonneg x).eq_or_lt with h0 | hpos
  · have hx : x = 0 := norm_eq_zero.mp h0.symm
    have hJ0 : J x = 0 := by
      have h := hJ x
      rw [← h0] at h
      exact norm_le_zero_iff.mp h
    simp [hJ0, Real.rpow_nonneg (norm_nonneg x)]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc
      ‖x‖ ^ (r - 2) * ‖J x‖ ≤ ‖x‖ ^ (r - 2) * ‖x‖ :=
        mul_le_mul_of_nonneg_left (hJ x) (Real.rpow_nonneg (norm_nonneg _) _)
      _ = ‖x‖ ^ (r - 1) := by
        rw [show r - 1 = (r - 2) + 1 by ring, Real.rpow_add hpos, Real.rpow_one]

lemma power_smooth_of_square_smooth (C : ℝ) (hC : 0 ≤ C) (J : E → E →L[ℝ] ℝ)
    (hJ : ∀ x, ‖J x‖ ≤ ‖x‖)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + C * ‖y‖ ^ 2)
    {r : ℝ} (hr1 : 1 < r) (hr2 : r ≤ 2) (x y : E) :
    ‖x + y‖ ^ r ≤ ‖x‖ ^ r + r * powerDual J r x y + (C + 6) * ‖y‖ ^ r := by
  set a := ‖x‖ with ha
  set b := ‖y‖ with hb
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hr0 : 0 ≤ r := by linarith
  have hdual : |powerDual J r x y| ≤ a ^ (r - 1) * b := by
    have h3 : |powerDual J r x y| ≤ ‖powerDual J r x‖ * ‖y‖ := by
      simpa [Real.norm_eq_abs] using (powerDual J r x).le_opNorm y
    exact h3.trans (mul_le_mul_of_nonneg_right (powerDual_norm J hJ r x) hb0)
  rcases le_or_gt b a with hba | hab
  · rcases ha0.eq_or_lt with ha00 | hapos
    · have hb00 : b = 0 := le_antisymm (ha00 ▸ hba) hb0
      have hx : x = 0 := norm_eq_zero.mp ha00.symm
      have hy : y = 0 := norm_eq_zero.mp hb00
      subst hx hy
      have h1 := Real.rpow_nonneg ha0 r
      have h2 := Real.rpow_nonneg hb0 r
      simp only [add_zero, map_zero, mul_zero, norm_zero, Real.zero_rpow (by linarith : r ≠ 0)]
      nlinarith
    · have hs : 0 < a ^ 2 := by positivity
      have ht : 0 ≤ ‖x + y‖ ^ 2 := by positivity
      have htan := concave_power_tangent hr0 hr2 hs ht
      have hmono : ‖x + y‖ ^ 2 ≤ a ^ 2 + 2 * J x y + C * b ^ 2 := hsmooth x y
      have hpow2 : (a ^ 2) ^ (r / 2) = a ^ r := (norm_rpow_eq_sq_rpow x r).symm
      have hpow1 : (a ^ 2) ^ (r / 2 - 1) = a ^ (r - 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha0]
        congr 1
        push_cast
        ring
      rw [hpow2, hpow1] at htan
      have hcoef : 0 ≤ r / 2 * a ^ (r - 2) := by positivity
      have hlin : r / 2 * a ^ (r - 2) * (‖x + y‖ ^ 2 - a ^ 2) ≤
          r / 2 * a ^ (r - 2) * (2 * J x y + C * b ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hcoef
      have hdualeq : powerDual J r x y = a ^ (r - 2) * J x y := by
        simp [powerDual, ha]
      have hbsq : a ^ (r - 2) * b ^ 2 ≤ b ^ r := by
        rcases hb0.eq_or_lt with hb00 | hbpos
        · rw [← hb00]; simp [Real.zero_rpow (by linarith : r ≠ 0)]
        · have hq : a ^ (r - 2) ≤ b ^ (r - 2) :=
            Real.rpow_le_rpow_of_nonpos hbpos hba (by linarith)
          calc
            a ^ (r - 2) * b ^ 2 ≤ b ^ (r - 2) * b ^ 2 :=
              mul_le_mul_of_nonneg_right hq (by positivity)
            _ = b ^ r := by
              rw [← Real.rpow_natCast, ← Real.rpow_add hbpos]
              norm_num
      have hlhs : ‖x + y‖ ^ r = (‖x + y‖ ^ 2) ^ (r / 2) := norm_rpow_eq_sq_rpow (x + y) r
      have hbr : 0 ≤ b ^ r := Real.rpow_nonneg hb0 _
      rw [hlhs, hdualeq]
      have : r / 2 * a ^ (r - 2) * (2 * J x y + C * b ^ 2) =
          r * (a ^ (r - 2) * J x y) + r / 2 * C * (a ^ (r - 2) * b ^ 2) := by ring
      have hCb : r / 2 * C * (a ^ (r - 2) * b ^ 2) ≤ (C + 6) * b ^ r := by
        have h1 : r / 2 * C ≤ C := by nlinarith
        have h2 : 0 ≤ a ^ (r - 2) * b ^ 2 := by positivity
        nlinarith
      linarith
  · have hbpos : 0 < b := lt_of_le_of_lt ha0 hab
    have htri : ‖x + y‖ ≤ 2 * b := by
      have := norm_add_le x y
      linarith
    have hl : ‖x + y‖ ^ r ≤ 4 * b ^ r := by
      calc
        ‖x + y‖ ^ r ≤ (2 * b) ^ r := Real.rpow_le_rpow (norm_nonneg _) htri hr0
        _ = 2 ^ r * b ^ r := Real.mul_rpow (by norm_num) hb0
        _ ≤ 4 * b ^ r := by
          have : (2 : ℝ) ^ r ≤ 2 ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hr2
          have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
          nlinarith [Real.rpow_nonneg hb0 r]
    have hd : a ^ (r - 1) * b ≤ b ^ r := by
      calc
        a ^ (r - 1) * b ≤ b ^ (r - 1) * b :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ha0 hab.le (by linarith)) hb0
        _ = b ^ r := by
          rw [← Real.rpow_add_one hbpos.ne']
          ring_nf
    have har : 0 ≤ a ^ r := Real.rpow_nonneg ha0 _
    have hbr : 0 ≤ b ^ r := Real.rpow_nonneg hb0 _
    have hlow : -(r * (a ^ (r - 1) * b)) ≤ r * powerDual J r x y := by
      have := neg_abs_le (powerDual J r x y)
      nlinarith
    have : r * (a ^ (r - 1) * b) ≤ 2 * b ^ r := by nlinarith
    nlinarith

end Normed

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma inner_square_smooth (x y : E) :
    ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * (innerSL ℝ x) y + 1 * ‖y‖ ^ 2 := by
  rw [innerSL_apply_apply, norm_add_sq_real]
  linarith

lemma inner_power_smooth {r : ℝ} (hr1 : 1 < r) (hr2 : r ≤ 2) (x y : E) :
    ‖x + y‖ ^ r ≤ ‖x‖ ^ r + r * powerDual (innerSL ℝ) r x y + 7 * ‖y‖ ^ r := by
  have h := power_smooth_of_square_smooth 1 zero_le_one (innerSL ℝ)
    (fun x => (innerSL_apply_norm ℝ x).le) inner_square_smooth hr1 hr2 x y
  norm_num at h ⊢
  linarith


lemma real_rpow_add_le {p a b : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ p ≤ a ^ p + b ^ p := by
  have h := NNReal.rpow_add_le_add_rpow ⟨a, ha⟩ ⟨b, hb⟩ hp hp1
  exact_mod_cast h

lemma extragradient_pathwise (H : E → E) (a L η : ℝ) (u x ζ : E)
    (hmono : ∀ y z, a * ‖y - z‖ ^ 2 ≤ ⟪H y - H z, y - z⟫)
    (hlip : ∀ y z, ‖H y - H z‖ ≤ L * ‖y - z‖) (hu : H u = 0)
    (ha : 0 ≤ a) (hL : 0 ≤ L) (hη : 0 ≤ η) (hηa : η * a ≤ 1 / 4) (hηL : η * L ≤ 1 / 4) :
    ‖x - η • H (x - η • (H x + ζ)) - u‖ ^ 2 ≤
      (1 - η * a) * ‖x - u‖ ^ 2 + 2 * η ^ 2 * ‖ζ‖ ^ 2 := by
  set h1 := H x + ζ with hh1
  set xt := x - η • h1 with hxt
  set q := H xt with hq
  set e := x - u with he
  have hA : x - η • q - u = e - η • q := by rw [he]; abel
  have hxte : xt - u = e - η • h1 := by rw [hxt, he]; abel
  have hmon := hmono xt u
  rw [hu, sub_zero, ← hq, hxte] at hmon
  have hnA : ‖e - η • q‖ ^ 2 = ‖e‖ ^ 2 - 2 * η * ⟪q, e⟫ + η ^ 2 * ‖q‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη,
      real_inner_comm]
    ring
  have hneh : ‖e - η • h1‖ ^ 2 = ‖e‖ ^ 2 - 2 * η * ⟪e, h1⟫ + η ^ 2 * ‖h1‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    ring
  have hinner : ⟪q, e - η • h1⟫ = ⟪q, e⟫ - η * ⟪q, h1⟫ := by
    rw [inner_sub_right, inner_smul_right]
  have hqh : ‖q - h1‖ ^ 2 = ‖q‖ ^ 2 - 2 * ⟪q, h1⟫ + ‖h1‖ ^ 2 := norm_sub_sq_real q h1
  have hdiff : q - h1 = (H xt - H x) - ζ := by rw [hq, hh1]; abel
  have hlipx : ‖H xt - H x‖ ≤ L * (η * ‖h1‖) := by
    have := hlip xt x
    rwa [hxt, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
      at this
  have hqn : ‖q - h1‖ ≤ L * (η * ‖h1‖) + ‖ζ‖ := by
    rw [hdiff]
    exact (norm_sub_le _ _).trans (by linarith)
  have hL0 : 0 ≤ L * (η * ‖h1‖) := le_trans (norm_nonneg _) hlipx
  have hqn2 : ‖q - h1‖ ^ 2 ≤ 2 * (L * η) ^ 2 * ‖h1‖ ^ 2 + 2 * ‖ζ‖ ^ 2 := by
    have h0 : 0 ≤ ‖q - h1‖ := norm_nonneg _
    have hsq : ‖q - h1‖ ^ 2 ≤ (L * (η * ‖h1‖) + ‖ζ‖) ^ 2 := pow_le_pow_left₀ h0 hqn 2
    nlinarith [sq_nonneg (L * (η * ‖h1‖) - ‖ζ‖)]
  have hpar : ‖e‖ ^ 2 ≤ 2 * ‖e - η • h1‖ ^ 2 + 2 * η ^ 2 * ‖h1‖ ^ 2 := by
    have htri : ‖e‖ ≤ ‖e - η • h1‖ + η * ‖h1‖ := by
      calc ‖e‖ = ‖(e - η • h1) + η • h1‖ := by rw [sub_add_cancel]
        _ ≤ ‖e - η • h1‖ + ‖η • h1‖ := norm_add_le _ _
        _ = ‖e - η • h1‖ + η * ‖h1‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    have h0 : 0 ≤ ‖e‖ := norm_nonneg _
    have hsq := pow_le_pow_left₀ h0 htri 2
    nlinarith [sq_nonneg (‖e - η • h1‖ - η * ‖h1‖)]
  rw [hA, hnA]
  have hLη : (L * η) ^ 2 ≤ 1 / 16 := by
    have : 0 ≤ L * η := mul_nonneg hL hη
    nlinarith
  have hh1n : 0 ≤ ‖h1‖ ^ 2 := sq_nonneg _
  have hηa0 : 0 ≤ η * a := mul_nonneg hη ha
  nlinarith [hmon, hinner, hqh, hqn2, hpar, mul_nonneg hηa0 hh1n, sq_nonneg η,
    mul_nonneg (sq_nonneg η) hh1n]


lemma sq_rpow_half (t r : ℝ) (ht : 0 ≤ t) : (t ^ 2) ^ (r / 2) = t ^ r := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  congr 1
  push_cast
  ring

lemma extragradient_power (H : E → E) (a L η α : ℝ) (u x ζ : E)
    (hmono : ∀ y z, a * ‖y - z‖ ^ 2 ≤ ⟪H y - H z, y - z⟫)
    (hlip : ∀ y z, ‖H y - H z‖ ≤ L * ‖y - z‖) (hu : H u = 0)
    (ha : 0 ≤ a) (hL : 0 ≤ L) (hη : 0 ≤ η) (hηa : η * a ≤ 1 / 4) (hηL : η * L ≤ 1 / 4)
    (hα1 : 1 < α) (hα2 : α ≤ 2) :
    ‖x - η • H (x - η • (H x + ζ)) - u‖ ^ α ≤
      (1 - η * a) ^ (α / 2) * ‖x - u‖ ^ α + 2 ^ (α / 2) * η ^ α * ‖ζ‖ ^ α := by
  have hp := extragradient_pathwise H a L η u x ζ hmono hlip hu ha hL hη hηa hηL
  have hc : 0 ≤ 1 - η * a := by linarith
  have h0 : 0 ≤ α / 2 := by linarith
  have h1 : α / 2 ≤ 1 := by linarith
  calc ‖x - η • H (x - η • (H x + ζ)) - u‖ ^ α
      = (‖x - η • H (x - η • (H x + ζ)) - u‖ ^ 2) ^ (α / 2) :=
        (sq_rpow_half _ α (norm_nonneg _)).symm
    _ ≤ ((1 - η * a) * ‖x - u‖ ^ 2 + 2 * η ^ 2 * ‖ζ‖ ^ 2) ^ (α / 2) :=
        Real.rpow_le_rpow (sq_nonneg _) hp h0
    _ ≤ ((1 - η * a) * ‖x - u‖ ^ 2) ^ (α / 2) + (2 * η ^ 2 * ‖ζ‖ ^ 2) ^ (α / 2) :=
        real_rpow_add_le h0 h1 (by positivity) (by positivity)
    _ = (1 - η * a) ^ (α / 2) * ‖x - u‖ ^ α + 2 ^ (α / 2) * η ^ α * ‖ζ‖ ^ α := by
        rw [Real.mul_rpow hc (sq_nonneg _), sq_rpow_half _ α (norm_nonneg _),
          Real.mul_rpow (by positivity) (sq_nonneg _), Real.mul_rpow (by norm_num) (sq_nonneg _),
          sq_rpow_half _ α hη, sq_rpow_half _ α (norm_nonneg _)]

end Inner

end LongTails.Proofs.TailObliviousGeometry
