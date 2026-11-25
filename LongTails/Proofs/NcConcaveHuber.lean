import LongTails.Proofs.NcConcaveScalars

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveHuber

open LongTails.Proofs.SmoothConvexFiniteGeometry LongTails.Proofs.NcConcaveScalars

noncomputable def huber (c t : ℝ) : ℝ := c ^ 2 * (ramp (t / c) + ramp (-t / c))

noncomputable def dhuber (c t : ℝ) : ℝ := c * (rampSlope (t / c) - rampSlope (-t / c))

lemma huber_model {c : ℝ} (hc : 0 < c) (x y : ℝ) :
    0 ≤ huber c y - huber c x - dhuber c x * (y - x) ∧
      huber c y - huber c x - dhuber c x * (y - x) ≤ (y - x) ^ 2 := by
  have h1 := ramp_model (x / c) (y / c)
  have h2 := ramp_model (-x / c) (-y / c)
  have hc2 : 0 < c ^ 2 := by positivity
  have e : huber c y - huber c x - dhuber c x * (y - x) =
      c ^ 2 * ((ramp (y / c) - ramp (x / c) - rampSlope (x / c) * (y / c - x / c)) +
        (ramp (-y / c) - ramp (-x / c) - rampSlope (-x / c) * (-y / c - -x / c))) := by
    have hc' : c ≠ 0 := hc.ne'
    simp only [huber, dhuber]
    generalize ramp (y / c) = R1
    generalize ramp (x / c) = R2
    generalize ramp (-y / c) = R3
    generalize ramp (-x / c) = R4
    generalize rampSlope (x / c) = S1
    generalize rampSlope (-x / c) = S2
    field_simp
    ring
  rw [e]
  have e2 : (y / c - x / c) ^ 2 = (y - x) ^ 2 / c ^ 2 := by field_simp
  have e3 : (-y / c - -x / c) ^ 2 = (y - x) ^ 2 / c ^ 2 := by field_simp; ring
  rw [e2] at h1; rw [e3] at h2
  constructor
  · exact mul_nonneg hc2.le (by linarith)
  · have : c ^ 2 * ((y - x) ^ 2 / c ^ 2 / 2 + (y - x) ^ 2 / c ^ 2 / 2) = (y - x) ^ 2 := by
      have hc0 : c ^ 2 ≠ 0 := hc2.ne'
      rw [show (y - x) ^ 2 / c ^ 2 / 2 + (y - x) ^ 2 / c ^ 2 / 2 = (y - x) ^ 2 / c ^ 2 by ring,
        mul_div_cancel₀ _ hc0]
    calc _ ≤ c ^ 2 * ((y - x) ^ 2 / c ^ 2 / 2 + (y - x) ^ 2 / c ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (add_le_add h1.2 h2.2) hc2.le
      _ = (y - x) ^ 2 := this

lemma huber_hasDerivAt {c : ℝ} (hc : 0 < c) (x : ℝ) : HasDerivAt (huber c) (dhuber c x) x :=
  hasDerivAt_of_model (C := 1) (fun x y => by
    have h := huber_model hc x y
    rw [abs_of_nonneg h.1]; linarith [h.2]) x

lemma huber_of_abs_le {c t : ℝ} (hc : 0 < c) (ht : |t| ≤ c) : huber c t = t ^ 2 / 2 := by
  have h := abs_le.mp ht
  simp only [huber, ramp]
  rcases le_or_gt t 0 with h0 | h0
  · have a1 : t / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg h0 hc.le
    have a2 : ¬ (-t / c ≤ 0) ∨ -t / c = 0 := by
      by_cases hz : t = 0
      · right; simp [hz]
      · left; push Not; exact div_pos (by
          rcases lt_or_eq_of_le h0 with h | h
          · linarith
          · exact absurd h hz) hc
    have a3 : -t / c ≤ 1 := by rw [div_le_one hc]; linarith
    rcases a2 with a2 | a2
    · rw [ite_eq_left a1, ite_eq_right a2, ite_eq_left a3]; field_simp; ring
    · rw [ite_eq_left a1, a2]; simp; have : t = 0 := by
        have := a2; field_simp at this; linarith
      subst this; ring
  · have a1 : ¬ (t / c ≤ 0) := by push Not; exact div_pos h0 hc
    have a2 : -t / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le
    have a3 : t / c ≤ 1 := by rw [div_le_one hc]; linarith
    rw [ite_eq_right a1, ite_eq_left a3, ite_eq_left a2]; field_simp; ring

lemma dhuber_of_abs_le {c t : ℝ} (hc : 0 < c) (ht : |t| ≤ c) : dhuber c t = t := by
  have h := abs_le.mp ht
  simp only [dhuber, rampSlope]
  rcases le_or_gt t 0 with h0 | h0
  · have a1 : t / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg h0 hc.le
    have a3 : -t / c ≤ 1 := by rw [div_le_one hc]; linarith
    have a4 : 0 ≤ -t / c := div_nonneg (by linarith) hc.le
    rw [max_eq_left a1, min_eq_right (by norm_num : (0 : ℝ) ≤ 1), max_eq_right a4,
      min_eq_right a3]
    field_simp; ring
  · have a1 : 0 ≤ t / c := (div_pos h0 hc).le
    have a3 : t / c ≤ 1 := by rw [div_le_one hc]; linarith
    have a4 : -t / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le
    rw [max_eq_right a1, min_eq_right a3, max_eq_left a4, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    field_simp
    ring

lemma dhuber_abs {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : |dhuber c t| ≤ c := by
  simp only [dhuber]
  have h1 := rampSlope_nonneg (t / c); have h2 := rampSlope_le_one (t / c)
  have h3 := rampSlope_nonneg (-t / c); have h4 := rampSlope_le_one (-t / c)
  rw [abs_mul, abs_of_nonneg hc]
  have : |rampSlope (t / c) - rampSlope (-t / c)| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  nlinarith

end LongTails.Proofs.NcConcaveHuber
