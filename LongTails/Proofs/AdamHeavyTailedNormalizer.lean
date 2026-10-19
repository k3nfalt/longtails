import LongTails.Proofs.AdamHeavyTailedAlgebra
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdamHeavyTailedNormalizer

lemma norm_linear_remainder {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (hx : 0 < ‖x‖) :
    0 ≤ ‖x + y‖ - ‖x‖ - ⟪x, y⟫ / ‖x‖ ∧
      ‖x + y‖ - ‖x‖ - ⟪x, y⟫ / ‖x‖ ≤ ‖y‖ ^ 2 / (2 * ‖x‖) := by
  have hc := real_inner_le_norm x (x + y)
  rw [inner_add_right, real_inner_self_eq_norm_sq] at hc
  have hsq := norm_add_sq_real x y
  have hcancel : (⟪x, y⟫ / ‖x‖) * ‖x‖ = ⟪x, y⟫ := div_mul_cancel₀ _ hx.ne'
  constructor
  · apply (mul_nonneg_iff_of_pos_right hx).mp
    nlinarith
  · apply (le_div_iff₀ (by positivity : 0 < 2 * ‖x‖)).2
    nlinarith [sq_nonneg (‖x + y‖ - ‖x‖)]

lemma norm_linear_remainder_abs {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) (hx : 0 < ‖x‖) :
    |‖x + y‖ - ‖x‖ - ⟪x, y⟫ / ‖x‖| ≤ ‖y‖ ^ 2 / (2 * ‖x‖) := by
  rw [abs_of_nonneg (norm_linear_remainder x y hx).1]
  exact (norm_linear_remainder x y hx).2

lemma reciprocal_remainder_identity {r r' τ n dn k : ℝ}
    (hr : r ≠ 0) (hd : r + τ ≠ 0) (hd' : r' + τ ≠ 0) :
    (n + dn) / (r' + τ) - n / (r + τ) -
        (dn / (r + τ) - n * k / (r * (r + τ) ^ 2)) =
      dn * (1 / (r' + τ) - 1 / (r + τ)) -
        n * (r' - r - k / r) / (r + τ) ^ 2 +
        n * (r' - r) ^ 2 / ((r' + τ) * (r + τ) ^ 2) := by
  field_simp
  ring

lemma reciprocal_difference_le {d d' A D : ℝ} (hA : 0 < A)
    (hd : A ≤ d) (hd' : A ≤ d') (hD : |d' - d| ≤ D) :
    |1 / d' - 1 / d| ≤ D / A ^ 2 := by
  have hd0 : 0 < d := hA.trans_le hd
  have hd0' : 0 < d' := hA.trans_le hd'
  have hid : 1 / d' - 1 / d = (d - d') / (d' * d) := by field_simp
  rw [hid, abs_div, abs_of_pos (mul_pos hd0' hd0), abs_sub_comm]
  have hAA : A ^ 2 ≤ d' * d := by nlinarith [mul_le_mul hd' hd hA.le hd0'.le]
  exact div_le_div₀ ((abs_nonneg _).trans hD) hD (sq_pos_of_pos hA) hAA

lemma reciprocal_quadratic_remainder {r r' τ A D n dn k : ℝ}
    (hr : 0 < r) (hτ : 0 ≤ τ) (hA : 0 < A) (hD : 0 ≤ D)
    (hAr : A ≤ r + τ) (hAr' : A ≤ r' + τ)
    (hn : |n| ≤ r) (hdn : |dn| ≤ D) (hdiff : |r' - r| ≤ D)
    (hrem : |r' - r - k / r| ≤ D ^ 2 / (2 * r)) :
    |(n + dn) / (r' + τ) - n / (r + τ) -
      (dn / (r + τ) - n * k / (r * (r + τ) ^ 2))| ≤ 3 * D ^ 2 / A ^ 2 := by
  have hd : 0 < r + τ := hA.trans_le hAr
  have hd' : 0 < r' + τ := hA.trans_le hAr'
  have hdiff' : |(r' + τ) - (r + τ)| ≤ D := by simpa using hdiff
  have h₁ : |dn * (1 / (r' + τ) - 1 / (r + τ))| ≤ D ^ 2 / A ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ D * (D / A ^ 2) := mul_le_mul hdn
        (reciprocal_difference_le hA hAr hAr' hdiff') (abs_nonneg _) hD
      _ = _ := by ring
  have h₂ : |n * (r' - r - k / r) / (r + τ) ^ 2| ≤ D ^ 2 / (2 * A ^ 2) := by
    rw [abs_div, abs_mul, abs_of_pos (sq_pos_of_pos hd)]
    calc
      _ ≤ r * (D ^ 2 / (2 * r)) / (r + τ) ^ 2 := by gcongr
      _ = D ^ 2 / (2 * (r + τ) ^ 2) := by field_simp
      _ ≤ D ^ 2 / (2 * A ^ 2) := by gcongr
  have hsq : (r' - r) ^ 2 ≤ D ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdiff 2
  have hprod : A ^ 2 ≤ (r' + τ) * (r + τ) := by
    nlinarith [mul_le_mul hAr' hAr hA.le hd'.le]
  have h₃ : |n * (r' - r) ^ 2 / ((r' + τ) * (r + τ) ^ 2)| ≤ D ^ 2 / A ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (r' - r)),
      abs_of_pos (mul_pos hd' (sq_pos_of_pos hd))]
    calc
      _ ≤ (r + τ) * D ^ 2 / ((r' + τ) * (r + τ) ^ 2) := by gcongr; linarith
      _ = D ^ 2 / ((r' + τ) * (r + τ)) := by field_simp
      _ ≤ D ^ 2 / A ^ 2 := div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hA) hprod
  rw [reciprocal_remainder_identity hr.ne' hd.ne' hd'.ne']
  have hsub (a b : ℝ) : |a - b| ≤ |a| + |b| := by
    simpa using abs_sub_le a 0 b
  have htriangle := (abs_add_le
    (dn * (1 / (r' + τ) - 1 / (r + τ)) - n * (r' - r - k / r) / (r + τ) ^ 2)
    (n * (r' - r) ^ 2 / ((r' + τ) * (r + τ) ^ 2))).trans
      (add_le_add (hsub _ _) le_rfl)
  have hhalf : D ^ 2 / (2 * A ^ 2) = (D ^ 2 / A ^ 2) / 2 := by ring
  have hnonneg : 0 ≤ D ^ 2 / A ^ 2 := by positivity
  rw [hhalf] at h₂
  have hthree : 3 * D ^ 2 / A ^ 2 = 3 * (D ^ 2 / A ^ 2) := by ring
  rw [hthree]
  linarith

lemma quadratic_linear_interpolation {u p : ℝ} (hu : 0 ≤ u) (hp : 1 ≤ p)
    (hp2 : p ≤ 2) : min (3 * u ^ 2) (4 * u) ≤ 4 * u ^ p := by
  by_cases hu1 : u ≤ 1
  · have hpow : u ^ 2 ≤ u ^ p := by
      simpa only [Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_ge' hu hu1 (by linarith : 0 ≤ p) hp2
    exact (min_le_left _ _).trans (by nlinarith [Real.rpow_nonneg hu p])
  · have hpow : u ≤ u ^ p := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hu1) hp
    exact (min_le_right _ _).trans (by linarith)

lemma normalized_difference_le {n n' d d' A D : ℝ} (hA : 0 < A) (hD : 0 ≤ D)
    (hd : A ≤ d) (hd' : A ≤ d') (hn : |n| ≤ d)
    (hn' : |n' - n| ≤ D) (hdd : |d' - d| ≤ D) :
    |n' / d' - n / d| ≤ 2 * D / A := by
  have hd0 := hA.trans_le hd
  have hd0' := hA.trans_le hd'
  have hid : n' / d' - n / d = (n' - n) / d' + n * (d - d') / (d' * d) := by
    field_simp
    ring
  have h₁ : |(n' - n) / d'| ≤ D / A := by
    rw [abs_div, abs_of_pos hd0']
    exact div_le_div₀ hD hn' hA hd'
  have h₂ : |n * (d - d') / (d' * d)| ≤ D / A := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hd0' hd0), abs_sub_comm d d']
    calc
      _ ≤ d * D / (d' * d) := by gcongr
      _ = D / d' := by field_simp
      _ ≤ D / A := div_le_div_of_nonneg_left hD hA hd'
  rw [hid]
  have ht := abs_add_le ((n' - n) / d') (n * (d - d') / (d' * d))
  have htwo : 2 * D / A = 2 * (D / A) := by ring
  rw [htwo]
  linarith

lemma normalized_linear_form_le {n dn r d A D k : ℝ}
    (hr : 0 < r) (hA : 0 < A) (hD : 0 ≤ D) (hd : A ≤ d) (hrd : r ≤ d)
    (hn : |n| ≤ r) (hdn : |dn| ≤ D) (hk : |k| ≤ r * D) :
    |dn / d - n * k / (r * d ^ 2)| ≤ 2 * D / A := by
  have hd0 := hA.trans_le hd
  have h₁ : |dn / d| ≤ D / A := by
    rw [abs_div, abs_of_pos hd0]
    exact div_le_div₀ hD hdn hA hd
  have h₂ : |n * k / (r * d ^ 2)| ≤ D / A := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hr (sq_pos_of_pos hd0))]
    calc
      _ ≤ d * (r * D) / (r * d ^ 2) := by gcongr; exact hn.trans hrd
      _ = D / d := by field_simp
      _ ≤ D / A := div_le_div_of_nonneg_left hD hA hd
  have ht : |dn / d - n * k / (r * d ^ 2)| ≤ |dn / d| + |n * k / (r * d ^ 2)| := by
    simpa using abs_sub_le (dn / d) 0 (n * k / (r * d ^ 2))
  have htwo : 2 * D / A = 2 * (D / A) := by ring
  rw [htwo]
  linarith

lemma regularized_taylor_remainder {r r' τ A D n dn k p : ℝ}
    (hr : 0 < r) (hτ : 0 ≤ τ) (hA : 0 < A) (hD : 0 ≤ D)
    (hAr : A ≤ r + τ) (hAr' : A ≤ r' + τ)
    (hn : |n| ≤ r) (hdn : |dn| ≤ D) (hdiff : |r' - r| ≤ D)
    (hk : |k| ≤ r * D) (hrem : |r' - r - k / r| ≤ D ^ 2 / (2 * r))
    (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    |(n + dn) / (r' + τ) - n / (r + τ) -
      (dn / (r + τ) - n * k / (r * (r + τ) ^ 2))| ≤ 4 * (D / A) ^ p := by
  have hquad := reciprocal_quadratic_remainder hr hτ hA hD hAr hAr' hn hdn hdiff hrem
  have hdiff' : |(r' + τ) - (r + τ)| ≤ D := by simpa using hdiff
  have hdn' : |(n + dn) - n| ≤ D := by simpa using hdn
  have hnorm := normalized_difference_le hA hD hAr hAr' (hn.trans (by linarith)) hdn' hdiff'
  have hlin := normalized_linear_form_le hr hA hD hAr (by linarith) hn hdn hk
  have ht : |(n + dn) / (r' + τ) - n / (r + τ) -
      (dn / (r + τ) - n * k / (r * (r + τ) ^ 2))| ≤
      |(n + dn) / (r' + τ) - n / (r + τ)| +
      |dn / (r + τ) - n * k / (r * (r + τ) ^ 2)| := by
    simpa using abs_sub_le ((n + dn) / (r' + τ) - n / (r + τ)) 0
      (dn / (r + τ) - n * k / (r * (r + τ) ^ 2))
  apply le_trans (le_min (a := 3 * (D / A) ^ 2) (b := 4 * (D / A)) ?_ ?_)
    (quadratic_linear_interpolation (div_nonneg hD hA.le) hp hp2)
  · convert hquad using 1; ring
  · have he : 2 * D / A = 2 * (D / A) := by ring
    rw [he] at hnorm hlin
    linarith

lemma zero_regularized_taylor_remainder {τ D dn p : ℝ} (hτ : 0 < τ)
    (hD : 0 ≤ D) (hdn : |dn| ≤ D) (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    |dn / (D + τ) - dn / τ| ≤ 4 * (D / τ) ^ p := by
  have hdt : 0 < D + τ := by positivity
  have hid : dn / (D + τ) - dn / τ = dn * (1 / (D + τ) - 1 / τ) := by ring
  have hquad : |dn / (D + τ) - dn / τ| ≤ D ^ 2 / τ ^ 2 := by
    rw [hid, abs_mul]
    calc
      _ ≤ D * (D / τ ^ 2) := mul_le_mul hdn
        (reciprocal_difference_le hτ le_rfl (by linarith)
          (by simp [abs_of_nonneg hD] : |D + τ - τ| ≤ D)) (abs_nonneg _) hD
      _ = _ := by ring
  have h₁ : |dn / (D + τ)| ≤ D / τ := by
    rw [abs_div, abs_of_pos hdt]
    exact div_le_div₀ hD hdn hτ (by linarith)
  have h₂ : |dn / τ| ≤ D / τ := by
    rw [abs_div, abs_of_pos hτ]
    exact div_le_div_of_nonneg_right hdn hτ.le
  have ht : |dn / (D + τ) - dn / τ| ≤ |dn / (D + τ)| + |dn / τ| := by
    simpa using abs_sub_le (dn / (D + τ)) 0 (dn / τ)
  apply le_trans (le_min (a := 3 * (D / τ) ^ 2) (b := 4 * (D / τ)) ?_ ?_)
    (quadratic_linear_interpolation (div_nonneg hD hτ.le) hp hp2)
  · have he : D ^ 2 / τ ^ 2 = (D / τ) ^ 2 := by ring
    rw [he] at hquad
    nlinarith [sq_nonneg (D / τ)]
  · have hn : 0 ≤ D / τ := by positivity
    linarith

lemma normalized_functional_taylor {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) (x y : E)
    {τ A p : ℝ} (hτ : 0 < τ) (hA : 0 < A)
    (hAx : A ≤ ‖x‖ + τ) (hAy : A ≤ ‖x + y‖ + τ) (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    |ℓ (x + y) / (‖x + y‖ + τ) - ℓ x / (‖x‖ + τ) -
      (ℓ y / (‖x‖ + τ) - ℓ x * ⟪x, y⟫ / (‖x‖ * (‖x‖ + τ) ^ 2))| ≤
        4 * (‖y‖ / A) ^ p := by
  have hbound (z : E) : |ℓ z| ≤ ‖z‖ := by
    calc
      |ℓ z| = ‖ℓ z‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖ℓ‖ * ‖z‖ := ℓ.le_opNorm z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hℓ (norm_nonneg _)
      _ = ‖z‖ := one_mul _
  by_cases hx : x = 0
  · subst x
    simp only [zero_add, map_zero, norm_zero, zero_mul, zero_div, sub_zero] at hAx ⊢
    apply (zero_regularized_taylor_remainder hτ (norm_nonneg _) (hbound y) hp hp2).trans
    gcongr
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hdiff : |‖x + y‖ - ‖x‖| ≤ ‖y‖ := by
      simpa using abs_norm_sub_norm_le (x + y) x
    have hk : |⟪x, y⟫| ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm x y
    simpa only [map_add] using regularized_taylor_remainder hx0 hτ.le hA (norm_nonneg y)
      hAx hAy (hbound x) (hbound y) hdiff hk (norm_linear_remainder_abs x y hx0) hp hp2

lemma normalized_linear_coefficient_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) (x v : E)
    {τ : ℝ} (hτ : 0 < τ) :
    |ℓ v / (‖x‖ + τ) - ℓ x * ⟪x, v⟫ / (‖x‖ * (‖x‖ + τ) ^ 2)| ≤
      2 * ‖v‖ / τ := by
  have hbound (z : E) : |ℓ z| ≤ ‖z‖ := by
    calc
      |ℓ z| = ‖ℓ z‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖ℓ‖ * ‖z‖ := ℓ.le_opNorm z
      _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hℓ (norm_nonneg _)
      _ = ‖z‖ := one_mul _
  have hd : 0 < ‖x‖ + τ := by positivity
  have hfirst : |ℓ v / (‖x‖ + τ)| ≤ ‖v‖ / τ := by
    rw [abs_div, abs_of_pos hd]
    exact div_le_div₀ (norm_nonneg _) (hbound _) hτ (by linarith [norm_nonneg x])
  have hsecond : |ℓ x * ⟪x, v⟫ / (‖x‖ * (‖x‖ + τ) ^ 2)| ≤ ‖v‖ / τ := by
    by_cases hx : x = 0
    · subst x
      simp only [map_zero, zero_mul, zero_div, abs_zero]
      positivity
    · have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
      rw [abs_div, abs_mul, abs_of_pos (mul_pos hx0 (sq_pos_of_pos hd))]
      calc
        _ ≤ (‖x‖ * (‖x‖ * ‖v‖)) / (‖x‖ * (‖x‖ + τ) ^ 2) := by
          gcongr
          · exact hbound x
          · exact abs_real_inner_le_norm x v
        _ = ‖x‖ * ‖v‖ / (‖x‖ + τ) ^ 2 := by field_simp
        _ ≤ ‖v‖ / τ := by
          apply (div_le_div_iff₀ (sq_pos_of_pos hd) hτ).2
          nlinarith [mul_nonneg (norm_nonneg v) (sq_nonneg ‖x‖),
            mul_nonneg (norm_nonneg v) (sq_nonneg τ),
            mul_nonneg (norm_nonneg v) (mul_nonneg hx0.le hτ.le)]
  have ht : |ℓ v / (‖x‖ + τ) - ℓ x * ⟪x, v⟫ / (‖x‖ * (‖x‖ + τ) ^ 2)| ≤
      |ℓ v / (‖x‖ + τ)| + |ℓ x * ⟪x, v⟫ / (‖x‖ * (‖x‖ + τ) ^ 2)| := by
    simpa using abs_sub_le (ℓ v / (‖x‖ + τ)) 0
      (ℓ x * ⟪x, v⟫ / (‖x‖ * (‖x‖ + τ) ^ 2))
  calc
    _ ≤ ‖v‖ / τ + ‖v‖ / τ := ht.trans (add_le_add hfirst hsecond)
    _ = _ := by ring

lemma normalized_line_taylor {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) (x v : E)
    {τ A p : ℝ} (hτ : 0 < τ) (hA : 0 < A)
    (hAx : A ≤ ‖x‖ + τ) (hAv : ∀ z : ℝ, A ≤ ‖x + z • v‖ + τ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (z : ℝ) :
    |ℓ (x + z • v) / (‖x + z • v‖ + τ) - ℓ x / (‖x‖ + τ) -
      (ℓ v / (‖x‖ + τ) - ℓ x * ⟪x, v⟫ / (‖x‖ * (‖x‖ + τ) ^ 2)) * z| ≤
        (4 * (‖v‖ / A) ^ p) * |z| ^ p := by
  have hb := normalized_functional_taylor ℓ hℓ x (z • v) hτ hA hAx (hAv z) hp hp2
  have hlin : ℓ (z • v) / (‖x‖ + τ) -
      ℓ x * ⟪x, z • v⟫ / (‖x‖ * (‖x‖ + τ) ^ 2) =
      (ℓ v / (‖x‖ + τ) - ℓ x * ⟪x, v⟫ / (‖x‖ * (‖x‖ + τ) ^ 2)) * z := by
    simp only [map_smul, real_inner_smul_right, smul_eq_mul]
    ring
  rw [hlin] at hb
  have he : (‖z • v‖ / A) ^ p = (‖v‖ / A) ^ p * |z| ^ p := by
    rw [norm_smul, Real.norm_eq_abs]
    rw [show |z| * ‖v‖ / A = (‖v‖ / A) * |z| by ring]
    exact Real.mul_rpow (by positivity) (abs_nonneg _)
  rw [he] at hb
  simpa only [mul_assoc] using hb

lemma coordinate_normalizer_taylor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace ℝ ι) (i j : ι) {c τ A p : ℝ}
    (hτ : 0 < τ) (hA : 0 < A) (hAx : A ≤ ‖x‖ + τ)
    (hAv : ∀ z : ℝ, A ≤ ‖x + z • PiLp.single 2 j c‖ + τ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ∃ a : ℝ, |a| ≤ 2 * |c| / τ ∧ ∀ z : ℝ,
      |((x + z • PiLp.single 2 j c) : EuclideanSpace ℝ ι) i / (‖x + z • PiLp.single 2 j c‖ + τ) -
        x i / (‖x‖ + τ) - a * z| ≤ (4 * (|c| / A) ^ p) * |z| ^ p := by
  let ℓ : EuclideanSpace ℝ ι →L[ℝ] ℝ := PiLp.proj 2 (fun _ : ι => ℝ) i
  have hℓ : ‖ℓ‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro y
    change ‖y i‖ ≤ 1 * ‖y‖
    simpa only [one_mul] using PiLp.norm_apply_le y i
  let v : EuclideanSpace ℝ ι := PiLp.single 2 j c
  have hv : ‖v‖ = |c| := by simp [v, PiLp.norm_single, Real.norm_eq_abs]
  refine ⟨ℓ v / (‖x‖ + τ) - ℓ x * ⟪x, v⟫ / (‖x‖ * (‖x‖ + τ) ^ 2), ?_, ?_⟩
  · simpa only [hv] using normalized_linear_coefficient_bound ℓ hℓ x v hτ
  · intro z
    simpa [ℓ, v, PiLp.norm_single, Real.norm_eq_abs] using
      normalized_line_taylor ℓ hℓ x v hτ hA hAx hAv hp hp2 z

lemma fixed_coordinate_denominator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace ℝ ι) (i j : ι) (hij : i ≠ j) (c τ z : ℝ) :
    |x i| + τ ≤ ‖x + z • PiLp.single 2 j c‖ + τ := by
  apply add_le_add _ le_rfl
  have hb := PiLp.norm_apply_le ((x + z • PiLp.single 2 j c) : EuclideanSpace ℝ ι) i
  simpa [PiLp.single_apply, hij, Ne.symm hij, Real.norm_eq_abs] using hb

lemma denominator_decay {v ρ τ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hτ : 0 ≤ τ) (g : ℝ) :
    Real.sqrt (1 - ρ) * (Real.sqrt v + τ) ≤
      Real.sqrt ((1 - ρ) * v + ρ * g ^ 2) + τ := by
  have hb : 0 ≤ 1 - ρ := sub_nonneg.mpr hρ1
  have hs : Real.sqrt (1 - ρ) ≤ 1 := by
    have hsq := Real.sq_sqrt hb
    have hn := Real.sqrt_nonneg (1 - ρ)
    nlinarith
  have hmono : Real.sqrt ((1 - ρ) * v) ≤ Real.sqrt ((1 - ρ) * v + ρ * g ^ 2) :=
    Real.sqrt_le_sqrt (le_add_of_nonneg_right (mul_nonneg hρ (sq_nonneg g)))
  rw [Real.sqrt_mul hb] at hmono
  nlinarith [mul_le_mul_of_nonneg_right hs hτ]

lemma denominator_current {v ρ : ℝ} (hv : 0 ≤ v) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (g : ℝ) :
    Real.sqrt ρ * |g| ≤ Real.sqrt ((1 - ρ) * v + ρ * g ^ 2) := by
  have hmono : Real.sqrt (ρ * g ^ 2) ≤ Real.sqrt ((1 - ρ) * v + ρ * g ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  simpa only [Real.sqrt_mul hρ, Real.sqrt_sq_eq_abs] using hmono

lemma normalized_current_bound {v ρ τ : ℝ} (hv : 0 ≤ v) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hτ : 0 < τ) (g : ℝ) :
    |g / (Real.sqrt ((1 - ρ) * v + ρ * g ^ 2) + τ)| ≤ 1 / Real.sqrt ρ := by
  have hd : 0 < Real.sqrt ((1 - ρ) * v + ρ * g ^ 2) + τ := by positivity
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  rw [abs_div, abs_of_pos hd]
  apply (div_le_div_iff₀ hd hs).2
  have hc := denominator_current hv hρ.le hρ1 g
  nlinarith

lemma normalized_momentum_step {v ρ τ q : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hτ : 0 < τ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (m g : ℝ) :
    |(q * m + (1 - q) * g) / (Real.sqrt ((1 - ρ) * v + ρ * g ^ 2) + τ)| ≤
      (q / Real.sqrt (1 - ρ)) * |m / (Real.sqrt v + τ)| +
        (1 - q) * |g / (Real.sqrt ((1 - ρ) * v + ρ * g ^ 2) + τ)| := by
  let d := Real.sqrt v + τ
  let d' := Real.sqrt ((1 - ρ) * v + ρ * g ^ 2) + τ
  have hd : 0 < d := by dsimp [d]; positivity
  have hd' : 0 < d' := by dsimp [d']; positivity
  have hb : 0 < Real.sqrt (1 - ρ) := Real.sqrt_pos.mpr (by linarith)
  have hdecay : Real.sqrt (1 - ρ) * d ≤ d' := denominator_decay hρ hρ1.le hτ.le g
  have hm : |m / d'| ≤ (1 / Real.sqrt (1 - ρ)) * |m / d| := by
    rw [abs_div, abs_div, abs_of_pos hd', abs_of_pos hd]
    calc
      |m| / d' ≤ |m| / (Real.sqrt (1 - ρ) * d) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hb hd) hdecay
      _ = _ := by ring
  change |(q * m + (1 - q) * g) / d'| ≤
    (q / Real.sqrt (1 - ρ)) * |m / d| + (1 - q) * |g / d'|
  have hid : (q * m + (1 - q) * g) / d' = q * (m / d') + (1 - q) * (g / d') := by ring
  rw [hid]
  calc
    _ ≤ |q * (m / d')| + |(1 - q) * (g / d')| := abs_add_le _ _
    _ = q * |m / d'| + (1 - q) * |g / d'| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hq, abs_of_nonneg (sub_nonneg.mpr hq1)]
    _ ≤ q * ((1 / Real.sqrt (1 - ρ)) * |m / d|) + (1 - q) * |g / d'| := by
      gcongr
    _ = _ := by ring

lemma signal_denominator_upper {w ρ τ μ : ℝ} (hw : 0 ≤ w) (hρ : 0 ≤ ρ) :
    Real.sqrt (w + ρ * μ ^ 2) + τ ≤ Real.sqrt w + τ + Real.sqrt ρ * |μ| := by
  have hs : (Real.sqrt ρ * |μ|) ^ 2 = ρ * μ ^ 2 := by rw [mul_pow, Real.sq_sqrt hρ, sq_abs]
  have hh : Real.sqrt (w + ρ * μ ^ 2) ≤ Real.sqrt w + Real.sqrt ρ * |μ| := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hw, mul_nonneg (Real.sqrt_nonneg w) (mul_nonneg (Real.sqrt_nonneg ρ) (abs_nonneg μ))]
  linarith

end LongTails.Proofs.AdamHeavyTailedNormalizer
