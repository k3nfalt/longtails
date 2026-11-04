import Mathlib

namespace LongTails.Proofs.UscgSharpRamp

noncomputable def objective (L g x : ℝ) : ℝ := g * x + L / 2 * (min x 0) ^ 2

def slope (L g x : ℝ) : ℝ := g + L * min x 0

lemma derivative (L g x : ℝ) : HasDerivAt (objective L g) (slope L g x) x := by
  have hl (x : ℝ) : HasDerivAt (fun y : ℝ => g * y + L / 2 * y ^ 2) (g + L * x) x := by
    convert ((hasDerivAt_id x).const_mul g).add (((hasDerivAt_id x).pow 2).const_mul (L / 2)) using 1
    · funext y
      simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]
      ring
  have hr (x : ℝ) : HasDerivAt (fun y : ℝ => g * y) g x := by
    simpa using (hasDerivAt_id x).const_mul g
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hh := (hl x).congr_of_eventuallyEq (show objective L g =ᶠ[nhds x] (fun y => g * y + L / 2 * y ^ 2) from by
      filter_upwards [gt_mem_nhds hx] with y hy
      simp [objective, min_eq_left hy.le])
    simpa [slope, min_eq_left hx.le] using hh
  · have hleft : HasDerivWithinAt (objective L g) g (Set.Iic 0) 0 := by
      have hh : HasDerivAt (fun y : ℝ => g * y + L / 2 * y ^ 2) g 0 := by simpa using hl 0
      apply hh.hasDerivWithinAt.congr
      · intro y hy
        simp [objective, min_eq_left (Set.mem_Iic.mp hy)]
      · simp [objective]
    have hright : HasDerivWithinAt (objective L g) g (Set.Ici 0) 0 := by
      apply (hr 0).hasDerivWithinAt.congr
      · intro y hy
        simp [objective, min_eq_right (Set.mem_Ici.mp hy)]
      · simp [objective]
    have hh := hleft.hasFDerivWithinAt.union hright.hasFDerivWithinAt
    rw [show slope L g 0 = g by simp [slope]]
    change HasFDerivAt (objective L g) (ContinuousLinearMap.toSpanSingleton ℝ g) 0
    simpa [Set.Iic_union_Ici] using hh
  · have hh := (hr x).congr_of_eventuallyEq (show objective L g =ᶠ[nhds x] (fun y => g * y) from by
      filter_upwards [lt_mem_nhds hx] with y hy
      simp [objective, min_eq_right hy.le])
    simpa [slope, min_eq_right hx.le] using hh

lemma slope_lipschitz {L : ℝ} (hL : 0 ≤ L) (g x y : ℝ) :
    |slope L g x - slope L g y| ≤ L * |x - y| := by
  have hmin : |min x 0 - min y 0| ≤ |x - y| := by
    rcases le_total x 0 with hx | hx <;> rcases le_total y 0 with hy | hy
    · simp [min_eq_left hx, min_eq_left hy]
    · simp only [min_eq_left hx, min_eq_right hy, sub_zero, abs_of_nonpos hx]
      rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
      linarith
    · simp only [min_eq_right hx, min_eq_left hy, zero_sub, abs_neg, abs_of_nonpos hy]
      rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
      linarith
    · simp [min_eq_right hx, min_eq_right hy]
  calc
    _ = L * |min x 0 - min y 0| := by rw [slope, slope]; rw [show g + L * min x 0 - (g + L * min y 0) = L * (min x 0 - min y 0) by ring, abs_mul, abs_of_nonneg hL]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmin hL

lemma lower_bound {L g : ℝ} (hL : 0 < L) (hg : 0 ≤ g) (x : ℝ) :
    -(g ^ 2 / (2 * L)) ≤ objective L g x := by
  rcases le_total x 0 with hx | hx
  · unfold objective
    rw [min_eq_left hx]
    apply (neg_le_iff_add_nonneg).mpr
    have heq : g * x + L / 2 * x ^ 2 + g ^ 2 / (2 * L) = (L * x + g) ^ 2 / (2 * L) := by field_simp; ring
    rw [heq]
    positivity
  · have : 0 ≤ objective L g x := by simp only [objective, min_eq_right hx, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]; positivity
    have : 0 ≤ g ^ 2 / (2 * L) := by positivity
    linarith

lemma plateau {L g x : ℝ} (hx : 0 ≤ x) : slope L g x = g := by
  simp [slope, min_eq_right hx]

end LongTails.Proofs.UscgSharpRamp
