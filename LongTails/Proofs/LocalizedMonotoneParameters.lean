import LongTails.Proofs.LocalizedMonotoneCoercivity

namespace LongTails.Proofs.LocalizedMonotoneParameters

open LocalizedMonotoneConstruction LocalizedMonotoneCoercivity

noncomputable def width (R : ℝ) (n : ℕ) : ℝ :=
  R / (4 * ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))

noncomputable def height (R : ℝ) (n : ℕ) : ℝ := 2 * width R n * ((n : ℝ) + 1)

noncomputable def offset (R : ℝ) (n : ℕ) : ℝ :=
  2 * height R n + (n - 1 : ℕ) * (3 * width R n / 2)

lemma width_pos (R : ℝ) (hR : 0 < R) (n : ℕ) : 0 < width R n := by
  dsimp [width]
  positivity

lemma width_identity (R : ℝ) (n : ℕ) :
    width R n * ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = R / 4 := by
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have hs := Real.sqrt_pos.mpr hm
  dsimp [width]
  field_simp

lemma width_le_quarter (R : ℝ) (hR : 0 ≤ R) (n : ℕ) : width R n ≤ R / 4 := by
  have hm : 1 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hs : 1 ≤ Real.sqrt ((n : ℝ) + 1) := Real.one_le_sqrt.mpr hm
  have hd : 4 ≤ 4 * ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) := by nlinarith
  exact div_le_div_of_nonneg_left hR (by norm_num) hd

lemma height_ge (R : ℝ) (hR : 0 < R) (n : ℕ) : 2 * width R n ≤ height R n := by
  dsimp [height]
  nlinarith [width_pos R hR n, Nat.cast_nonneg (α := ℝ) n]

lemma offset_nonneg (R : ℝ) (hR : 0 < R) (n : ℕ) : 0 ≤ offset R n := by
  have ha := width_pos R hR n
  dsimp [offset, height]
  positivity

lemma offset_upper (R : ℝ) (hR : 0 < R) (n : ℕ) :
    offset R n ≤ 6 * width R n * ((n : ℝ) + 1) := by
  have hn : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
    have h : ((n - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 1
    linarith
  have ha := width_pos R hR n
  dsimp [offset, height]
  nlinarith

lemma offset_sqrt_upper (R : ℝ) (hR : 0 < R) (n : ℕ) :
    Real.sqrt ((n : ℝ) + 1) * offset R n ≤ 3 * R / 2 := by
  have h := mul_le_mul_of_nonneg_left (offset_upper R hR n) (Real.sqrt_nonneg ((n : ℝ) + 1))
  have he := width_identity R n
  nlinarith

lemma root_norm {d n : ℕ} (R : ℝ) (hR : 0 < R) (π : Fin (n + 1) ↪ Fin d) :
    ‖rootPoint (height R n) (3 * width R n / 2) π‖ ≤ R := by
  have ha := width_pos R hR n
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have hheight : 0 ≤ height R n := by dsimp [height]; positivity
  have h := rootPoint_norm_sq (height R n) (3 * width R n / 2) hheight (by positivity) π
  have hB : height R n + n * (3 * width R n / 2) ≤ 4 * width R n * ((n : ℝ) + 1) := by
    dsimp [height]
    nlinarith [mul_nonneg ha.le (Nat.cast_nonneg (α := ℝ) n)]
  have hB0 : 0 ≤ height R n + n * (3 * width R n / 2) := by positivity
  have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0 hB 2) hm.le
  have hscale : 4 * width R n * ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = R := by
    nlinarith [width_identity R n]
  have he := congrArg (fun z : ℝ => z ^ 2) hscale
  simp only [mul_pow, Real.sq_sqrt hm.le] at he
  nlinarith [norm_nonneg (rootPoint (height R n) (3 * width R n / 2) π)]

lemma coercivity_budget (R : ℝ) (hR : 0 < R) (n : ℕ) :
    Real.sqrt ((n : ℝ) + 1) * offset R n +
      (2 * ((n : ℝ) + 1) + 1) * (R / (2 * ((n : ℝ) + 1))) ≤ 4 * R := by
  have hm : 1 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hterm : (2 * ((n : ℝ) + 1) + 1) * (R / (2 * ((n : ℝ) + 1))) ≤ 3 * R / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    field_simp
    nlinarith
  nlinarith [offset_sqrt_upper R hR n]

lemma terminal_budget (R : ℝ) (hR : 0 < R) (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt ((n : ℝ) + 1) * (R / (2 * ((n : ℝ) + 1))) ≤
      offset R n - width R n - n * (3 * width R n / 2) := by
  have ha := width_pos R hR n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsub : ((n - 1 : ℕ) : ℝ) = n - 1 := by rw [Nat.cast_sub hn]; norm_num
  have he : Real.sqrt ((n : ℝ) + 1) * (R / (2 * ((n : ℝ) + 1))) =
      2 * width R n * ((n : ℝ) + 1) := by
    have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)
    dsimp [width]
    have hm : 0 < (n : ℝ) + 1 := by positivity
    have hp := Real.sqrt_pos.mpr hm
    field_simp
    nlinarith
  rw [he]
  dsimp [offset, height]
  rw [hsub]
  nlinarith [mul_le_mul_of_nonneg_right hn' ha.le]

lemma smoothness_scale (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (n : ℕ) :
    (L * width R n / 4) * (2 / width R n + 32 / (4 * R)) ≤ L := by
  have ha := width_pos R hR n
  have hbound := width_le_quarter R hR.le n
  have he : (L * width R n / 4) * (2 / width R n + 32 / (4 * R)) =
      L / 2 + 2 * L * width R n / R := by field_simp; ring
  rw [he]
  have hh : 2 * L * width R n / R ≤ L / 2 := by
    apply (div_le_iff₀ hR).mpr
    nlinarith [mul_le_mul_of_nonneg_left hbound hL]
  linarith

lemma observation_ratio (R : ℝ) (hR : 0 < R) (n : ℕ) :
    (6 * R) ^ 2 / (width R n) ^ 2 = 576 * ((n : ℝ) + 1) ^ 3 := by
  have hm : 0 < (n : ℝ) + 1 := by positivity
  have hs := Real.sq_sqrt hm.le
  dsimp [width]
  rw [div_pow, mul_pow, mul_pow, hs]
  field_simp
  ring

lemma residual_scale (L R : ℝ) (n : ℕ) :
    (L * width R n / 4) * (R / (2 * ((n : ℝ) + 1))) =
      L * R ^ 2 / (32 * ((n : ℝ) + 1) ^ 2 * Real.sqrt ((n : ℝ) + 1)) := by
  dsimp [width]
  field_simp
  ring

end LongTails.Proofs.LocalizedMonotoneParameters
