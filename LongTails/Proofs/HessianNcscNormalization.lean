import LongTails.Algorithms.HessianNcscIgt
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

namespace OracleTemplate.HessianNcsc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def dphi (η lam : ℝ) (m h : E) : E :=
  -(η / nscale lam m) • h + (η * ⟪m, h⟫ / nscale lam m ^ 3) • m

variable {lam η : ℝ}

omit [InnerProductSpace ℝ E] in
lemma nscale_sq (lam : ℝ) (m : E) : nscale lam m ^ 2 = ‖m‖ ^ 2 + lam ^ 2 :=
  Real.sq_sqrt (by positivity)

omit [InnerProductSpace ℝ E] in
lemma nscale_ge (m : E) : lam ≤ nscale lam m := by
  apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg ‖m‖]

omit [InnerProductSpace ℝ E] in
lemma nscale_pos (hl : 0 < lam) (m : E) : 0 < nscale lam m := lt_of_lt_of_le hl (nscale_ge m)

omit [InnerProductSpace ℝ E] in
lemma norm_le_nscale (m : E) : ‖m‖ ≤ nscale lam m := by
  apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg lam]

omit [InnerProductSpace ℝ E] in
lemma nscale_le (hl : 0 < lam) (m : E) : nscale lam m ≤ ‖m‖ + lam := by
  rw [nscale, Real.sqrt_le_left]
  · nlinarith [norm_nonneg m]
  · positivity

omit [InnerProductSpace ℝ E] in
lemma nscale_diff (hl : 0 < lam) (m m' : E) : |nscale lam m' - nscale lam m| ≤ ‖m' - m‖ := by
  have ha := nscale_pos hl m
  have hb := nscale_pos hl m'
  have hsq : nscale lam m' ^ 2 - nscale lam m ^ 2 = ‖m'‖ ^ 2 - ‖m‖ ^ 2 := by
    rw [nscale_sq, nscale_sq]; ring
  have hab : nscale lam m' - nscale lam m = (‖m'‖ - ‖m‖) * (‖m'‖ + ‖m‖) / (nscale lam m' + nscale lam m) := by
    field_simp
    nlinarith [hsq]
  rw [hab, abs_div, abs_mul, abs_of_pos (by linarith : 0 < nscale lam m' + nscale lam m)]
  have h1 : |‖m'‖ - ‖m‖| ≤ ‖m' - m‖ := abs_norm_sub_norm_le m' m
  have h2 : |‖m'‖ + ‖m‖| ≤ nscale lam m' + nscale lam m := by
    rw [abs_of_nonneg (by positivity)]
    exact add_le_add (norm_le_nscale m') (norm_le_nscale m)
  rw [div_le_iff₀ (by linarith)]
  calc |‖m'‖ - ‖m‖| * |‖m'‖ + ‖m‖| ≤ ‖m' - m‖ * (nscale lam m' + nscale lam m) :=
        mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = ‖m' - m‖ * (nscale lam m' + nscale lam m) := rfl

lemma nphi_norm (hl : 0 < lam) (hη : 0 ≤ η) (m : E) : ‖nphi η lam m‖ ≤ η := by
  have hs := nscale_pos hl m
  rw [nphi, norm_smul, norm_neg, Real.norm_of_nonneg (div_nonneg hη hs.le)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hs]
  exact mul_le_mul_of_nonneg_left (norm_le_nscale m) hη

lemma nphi_lip (hl : 0 < lam) (hη : 0 ≤ η) (m m' : E) :
    ‖nphi η lam m' - nphi η lam m‖ ≤ (2 * η / lam) * ‖m' - m‖ := by
  set a := nscale lam m
  set b := nscale lam m'
  have ha := nscale_pos hl m
  have hb := nscale_pos hl m'
  have hal : lam ≤ a := nscale_ge m
  have ha' : a ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  have e : nphi η lam m' - nphi η lam m = -(η / a) • (m' - m) - (η * (a - b) / (a * b)) • m' := by
    have hbx : (η / b) = η / a + η * (a - b) / (a * b) := by field_simp; ring
    rw [show nphi η lam m' = -(η / b) • m' from rfl, show nphi η lam m = -(η / a) • m from rfl, hbx]
    simp only [neg_add, add_smul, smul_sub, neg_smul]; abel
  rw [e]
  have hd := nscale_diff hl m m'
  have h1 : ‖(η / a) • (m' - m)‖ ≤ (η / lam) * ‖m' - m‖ := by
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hη ha.le)]
    gcongr
  have h2 : ‖(η * (a - b) / (a * b)) • m'‖ ≤ (η / lam) * ‖m' - m‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hη,
      abs_of_pos (mul_pos ha hb)]
    have hm' : ‖m'‖ ≤ b := norm_le_nscale m'
    have hab : |a - b| ≤ ‖m' - m‖ := by rw [abs_sub_comm]; exact hd
    calc η * |a - b| / (a * b) * ‖m'‖ ≤ η * ‖m' - m‖ / (a * b) * b := by
          gcongr
      _ = (η / a) * ‖m' - m‖ := by field_simp
      _ ≤ (η / lam) * ‖m' - m‖ := by gcongr
  calc ‖-(η / a) • (m' - m) - (η * (a - b) / (a * b)) • m'‖
      ≤ ‖(η / a) • (m' - m)‖ + ‖(η * (a - b) / (a * b)) • m'‖ := by
        rw [neg_smul]; refine (norm_sub_le _ _).trans ?_; rw [norm_neg]
    _ ≤ (η / lam) * ‖m' - m‖ + (η / lam) * ‖m' - m‖ := add_le_add h1 h2
    _ = (2 * η / lam) * ‖m' - m‖ := by ring

lemma dphi_add (m h k : E) : dphi η lam m (h + k) = dphi η lam m h + dphi η lam m k := by
  simp only [dphi, smul_add, inner_add_right, mul_add, add_div, add_smul]; abel

lemma dphi_smul (m h : E) (c : ℝ) : dphi η lam m (c • h) = c • dphi η lam m h := by
  simp only [dphi, smul_add, inner_smul_right, smul_smul]
  congr 1
  · ring_nf
  · congr 1; ring

lemma nphi_taylor (hl : 0 < lam) (hη : 0 ≤ η) (m h : E) :
    ‖nphi η lam (m + h) - nphi η lam m - dphi η lam m h‖ ≤ (6 * η / lam ^ 2) * ‖h‖ ^ 2 := by
  set a := nscale lam m
  set b := nscale lam (m + h)
  set i := ⟪m, h⟫
  set k := ‖h‖
  set n := ‖m‖
  have ha := nscale_pos hl m
  have hb := nscale_pos hl (m + h)
  have hal : lam ≤ a := nscale_ge m
  have hbl : lam ≤ b := nscale_ge (m + h)
  have ha' : a ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  have hab' : a + b ≠ 0 := by positivity
  have hna : n ≤ a := norm_le_nscale m
  have hi : |i| ≤ n * k := abs_real_inner_le_norm m h
  have hba : |b - a| ≤ k := by
    have := nscale_diff hl m (m + h); simpa using this
  have hb2 : b ^ 2 = a ^ 2 + 2 * i + k ^ 2 := by
    rw [nscale_sq, nscale_sq, norm_add_sq_real]; ring
  set c1 : ℝ := η * (1 / a - 1 / b - i / a ^ 3)
  set c2 : ℝ := η * (1 / a - 1 / b)
  have e : nphi η lam (m + h) - nphi η lam m - dphi η lam m h = c1 • m + c2 • h := by
    simp only [nphi, dphi, c1, c2]
    rw [smul_add]
    have h3 : η * i / a ^ 3 = η * (i / a ^ 3) := by ring
    rw [h3]
    simp only [neg_smul, mul_sub, sub_smul]
    rw [div_eq_mul_one_div η a, div_eq_mul_one_div η b]
    abel
  rw [e]
  have hnum : |(1 / a - 1 / b - i / a ^ 3)| * n ≤ 5 * k ^ 2 / (a * b) := by
    have key : 1 / a - 1 / b - i / a ^ 3 =
        -(i * a * (b - a) - k ^ 2 * a ^ 2 + 2 * i ^ 2 + i * k ^ 2) / (a ^ 3 * b * (a + b)) := by
      have hP : a ^ 2 * b * (a + b) - a ^ 3 * (a + b) - i * b * (a + b) =
          -(i * a * (b - a) - k ^ 2 * a ^ 2 + 2 * i ^ 2 + i * k ^ 2) := by
        linear_combination (a ^ 2 - i) * hb2
      rw [← hP]
      field_simp
    rw [key, abs_div, abs_neg, abs_of_pos (by positivity : 0 < a ^ 3 * b * (a + b))]
    have hnum2 : |i * a * (b - a) - k ^ 2 * a ^ 2 + 2 * i ^ 2 + i * k ^ 2| ≤ k ^ 2 * (5 * a ^ 2 + a * b) := by
      have hk : k ≤ a + b := by
        have := norm_le_nscale (lam := lam) (m + h)
        have h1 : ‖h‖ ≤ ‖m + h‖ + ‖m‖ := by
          have := norm_sub_le (m + h) m; simpa using this
        linarith
      have hiak : |i| ≤ a * k := hi.trans (mul_le_mul_of_nonneg_right hna (norm_nonneg h))
      have t1 : |i * a * (b - a)| ≤ a * k * a * k := by
        rw [abs_mul, abs_mul, abs_of_pos ha]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hiak ha.le) hba (abs_nonneg _) (by positivity)
      have t3 : |2 * i ^ 2| ≤ 2 * (a * k) ^ 2 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_pow]
        have := pow_le_pow_left₀ (abs_nonneg i) hiak 2
        linarith
      have t4 : |i * k ^ 2| ≤ a * k * k ^ 2 := by
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ k ^ 2)]
        exact mul_le_mul_of_nonneg_right hiak (by positivity)
      have t2 : |k ^ 2 * a ^ 2| = k ^ 2 * a ^ 2 := abs_of_nonneg (by positivity)
      calc |i * a * (b - a) - k ^ 2 * a ^ 2 + 2 * i ^ 2 + i * k ^ 2|
          ≤ |i * a * (b - a)| + |k ^ 2 * a ^ 2| + |2 * i ^ 2| + |i * k ^ 2| := by
            have := abs_add_le (i * a * (b - a) - k ^ 2 * a ^ 2 + 2 * i ^ 2) (i * k ^ 2)
            have := abs_add_le (i * a * (b - a) - k ^ 2 * a ^ 2) (2 * i ^ 2)
            have := abs_sub (i * a * (b - a)) (k ^ 2 * a ^ 2)
            linarith
        _ ≤ a * k * a * k + k ^ 2 * a ^ 2 + 2 * (a * k) ^ 2 + a * k * k ^ 2 := by
            rw [t2]; linarith
        _ ≤ k ^ 2 * (5 * a ^ 2 + a * b) := by
            have : a * k * k ^ 2 ≤ a * (a + b) * k ^ 2 := by
              have := mul_le_mul_of_nonneg_left hk ha.le
              nlinarith [sq_nonneg k]
            nlinarith
    calc |i * a * (b - a) - k ^ 2 * a ^ 2 + 2 * i ^ 2 + i * k ^ 2| / (a ^ 3 * b * (a + b)) * n
        ≤ k ^ 2 * (5 * a ^ 2 + a * b) / (a ^ 3 * b * (a + b)) * a := by
          gcongr
      _ = k ^ 2 * (5 * a + b) / (a * b * (a + b)) := by field_simp
      _ ≤ 5 * k ^ 2 / (a * b) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : k ^ 2 * (5 * a + b) * (a * b) ≤ 5 * k ^ 2 * (a * b * (a + b)) := by
            have h5 : 5 * a + b ≤ 5 * (a + b) := by linarith
            have := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ k ^ 2 * (a * b))
            nlinarith
          linarith
  have hc2 : |1 / a - 1 / b| * k ≤ k ^ 2 / (a * b) := by
    have : 1 / a - 1 / b = (b - a) / (a * b) := by
      rw [div_sub_div _ _ ha.ne' hb.ne']; ring
    rw [this, abs_div, abs_of_pos (mul_pos ha hb)]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (mul_pos ha hb)]
    nlinarith [abs_nonneg (b - a)]
  have hab : 1 / (a * b) ≤ 1 / lam ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos ha hb) (by positivity)]
    nlinarith
  calc ‖c1 • m + c2 • h‖ ≤ |c1| * n + |c2| * k := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ = η * (|1 / a - 1 / b - i / a ^ 3| * n) + η * (|1 / a - 1 / b| * k) := by
        simp only [c1, c2, abs_mul, abs_of_nonneg hη]; ring
    _ ≤ η * (5 * k ^ 2 / (a * b)) + η * (k ^ 2 / (a * b)) := by gcongr
    _ = 6 * η * k ^ 2 * (1 / (a * b)) := by ring
    _ ≤ 6 * η * k ^ 2 * (1 / lam ^ 2) := by gcongr
    _ = (6 * η / lam ^ 2) * ‖h‖ ^ 2 := by ring

lemma nphi_descent (hl : 0 < lam) (hη : 0 ≤ η) (G e : E) :
    ⟪G, nphi η lam (G + e)⟫ ≤ -(η * (‖G‖ - lam - 2 * ‖e‖)) := by
  set m := G + e
  set s := nscale lam m
  have hs := nscale_pos hl m
  have hms : ‖m‖ ≤ s := norm_le_nscale m
  have hsl : s ≤ ‖m‖ + lam := nscale_le hl m
  have e1 : ⟪G, nphi η lam m⟫ = -(η / s) * ⟪G, m⟫ := by
    rw [nphi, inner_smul_right]
  have hG : G = m - e := by simp [m]
  have e2 : ⟪G, m⟫ = ‖m‖ ^ 2 - ⟪e, m⟫ := by
    rw [hG, inner_sub_left, real_inner_self_eq_norm_sq]
  have hem : ⟪e, m⟫ ≤ ‖e‖ * ‖m‖ := real_inner_le_norm e m
  have hmG : ‖G‖ - ‖e‖ ≤ ‖m‖ := by
    have := norm_sub_le m e; rw [← hG] at this; linarith
  rw [e1, e2]
  have h1 : ‖m‖ ^ 2 / s ≥ ‖m‖ - lam := by
    rw [ge_iff_le, le_div_iff₀ hs]
    nlinarith [norm_nonneg m]
  have h2 : ‖e‖ * ‖m‖ / s ≤ ‖e‖ := by
    rw [div_le_iff₀ hs]; exact mul_le_mul_of_nonneg_left hms (norm_nonneg e)
  have key : -(η / s) * (‖m‖ ^ 2 - ⟪e, m⟫) ≤ -(η * (‖m‖ ^ 2 / s)) + η * (‖e‖ * ‖m‖ / s) := by
    have : -(η / s) * (‖m‖ ^ 2 - ⟪e, m⟫) = -(η * (‖m‖ ^ 2 / s)) + η * (⟪e, m⟫ / s) := by ring
    rw [this]
    gcongr
  nlinarith [mul_le_mul_of_nonneg_left h1 hη, mul_le_mul_of_nonneg_left h2 hη]

end OracleTemplate.HessianNcsc
