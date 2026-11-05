import LongTails.Setups.StochasticPowerSmoothFixedPoint
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Tactic

namespace LongTails.Proofs.PowerSmoothLpGeometry

noncomputable def slope (s x : ℝ) : ℝ := if 0 ≤ x then x ^ (s - 1) else -(-x) ^ (s - 1)

lemma power_difference {r x y : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) : |x ^ r - y ^ r| ≤ |x - y| ^ r := by
  rcases le_total y x with h | h
  · have hm := Real.rpow_le_rpow hy h hr0
    rw [abs_of_nonneg (sub_nonneg.mpr hm), abs_of_nonneg (sub_nonneg.mpr h)]
    have ha := Real.rpow_add_le_add_rpow hy (sub_nonneg.mpr h) hr0 hr1
    rw [show y + (x - y) = x by ring] at ha
    linarith
  · have hm := Real.rpow_le_rpow hx h hr0
    rw [abs_of_nonpos (sub_nonpos.mpr hm), abs_of_nonpos (sub_nonpos.mpr h)]
    have ha := Real.rpow_add_le_add_rpow hx (sub_nonneg.mpr h) hr0 hr1
    rw [show x + (y - x) = y by ring] at ha
    simpa only [neg_sub] using (by linarith : -(x ^ r - y ^ r) ≤ (y - x) ^ r)

lemma slope_holder {s : ℝ} (hs : 1 < s) (hs2 : s ≤ 2) (x y : ℝ) :
    |slope s x - slope s y| ≤ 2 * |x - y| ^ (s - 1) := by
  have hr0 : 0 ≤ s - 1 := by linarith
  have hr1 : s - 1 ≤ 1 := by linarith
  have hp : 0 ≤ |x - y| ^ (s - 1) := Real.rpow_nonneg (abs_nonneg _) _
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · simp only [slope, ite_eq_left hx, ite_eq_left hy]
    have := power_difference hr0 hr1 hx hy
    linarith
  · have hy' : y < 0 := lt_of_not_ge hy
    simp only [slope, ite_eq_left hx, ite_eq_right hy, sub_neg_eq_add]
    rw [abs_of_nonneg (add_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg (by linarith) _))]
    have hb : |x - y| = x - y := abs_of_nonneg (by linarith)
    have h1 := Real.rpow_le_rpow hx (show x ≤ |x - y| by rw [hb]; linarith) hr0
    have h2 := Real.rpow_le_rpow (show 0 ≤ -y by linarith)
      (show -y ≤ |x - y| by rw [hb]; linarith) hr0
    linarith
  · have hx' : x < 0 := lt_of_not_ge hx
    simp only [slope, ite_eq_right hx, ite_eq_left hy]
    have hneg : -(-x) ^ (s - 1) - y ^ (s - 1) ≤ 0 := by
      have := Real.rpow_nonneg (show 0 ≤ -x by linarith) (s - 1)
      have := Real.rpow_nonneg hy (s - 1)
      linarith
    rw [abs_of_nonpos hneg]
    have hb : |x - y| = y - x := by rw [abs_of_nonpos (by linarith)]; ring
    have h1 := Real.rpow_le_rpow hy (show y ≤ |x - y| by rw [hb]; linarith) hr0
    have h2 := Real.rpow_le_rpow (show 0 ≤ -x by linarith)
      (show -x ≤ |x - y| by rw [hb]; linarith) hr0
    linarith
  · simp only [slope, ite_eq_right hx, ite_eq_right hy]
    have ha := power_difference hr0 hr1 (show 0 ≤ -x by linarith) (show 0 ≤ -y by linarith)
    have he : |-x - -y| = |x - y| := by rw [← abs_neg (x - y)]; congr 1; ring
    rw [he] at ha
    have he' : |-(-x) ^ (s - 1) - -(-y) ^ (s - 1)| =
        |(-x) ^ (s - 1) - (-y) ^ (s - 1)| := by
      rw [← abs_neg ((-x) ^ (s - 1) - (-y) ^ (s - 1))]
      congr 1
      ring
    rw [he']
    linarith

lemma slope_eq {s : ℝ} (hs : 1 < s) (x : ℝ) : slope s x = |x| ^ (s - 2) * x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp only [slope, ite_eq_right (not_le.mpr hx), abs_of_neg hx]
    have he := Real.rpow_add_one (show -x ≠ 0 by linarith) (s - 2)
    rw [show s - 2 + 1 = s - 1 by ring] at he
    rw [he]
    ring
  · subst x
    simp [slope, Real.zero_rpow (show s - 1 ≠ 0 by linarith)]
  · simp only [slope, ite_eq_left hx.le, abs_of_pos hx]
    have he := Real.rpow_add_one hx.ne' (s - 2)
    rw [show s - 2 + 1 = s - 1 by ring] at he
    exact he

lemma scalar_power_smooth {s : ℝ} (hs : 1 < s) (hs2 : s ≤ 2) (a b : ℝ) :
    |a + b| ^ s ≤ |a| ^ s + s * slope s a * b + 4 * |b| ^ s := by
  let f : ℝ → ℝ := fun t => |a + t * b| ^ s - s * slope s a * (t * b)
  let f' : ℝ → ℝ := fun t => s * (slope s (a + t * b) - slope s a) * b
  have hd : ∀ t, HasDerivAt f (f' t) t := by
    intro t
    have hinner : HasDerivAt (fun t : ℝ => a + t * b) b t := by
      simpa using ((hasDerivAt_id t).mul_const b).const_add a
    have h1 := (hasDerivAt_abs_rpow (a + t * b) hs).comp t hinner
    have h2 := (((hasDerivAt_id t).mul_const b).const_mul (s * slope s a))
    convert h1.sub h2 using 1
    · rfl
    · dsimp [f']
      rw [slope_eq hs (a + t * b)]
      ring
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f' t‖ ≤ 4 * |b| ^ s := by
    intro t ht
    have hb : |a + t * b - a| ≤ |b| := by
      rw [show a + t * b - a = t * b by ring, abs_mul, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (abs_nonneg _) ht.2
    have hh := slope_holder hs hs2 (a + t * b) a
    have hp := Real.rpow_le_rpow (abs_nonneg _) hb (by linarith : 0 ≤ s - 1)
    have he : |b| ^ (s - 1) * |b| = |b| ^ s := by
      have := Real.rpow_add_one' (abs_nonneg b) (show s - 1 + 1 ≠ 0 by linarith)
      simpa only [sub_add_cancel] using this.symm
    dsimp [f']
    rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < s)]
    have hm := mul_le_mul_of_nonneg_left (hh.trans (mul_le_mul_of_nonneg_left hp (by norm_num)))
      (show 0 ≤ s by linarith)
    have hm' := mul_le_mul_of_nonneg_right hm (abs_nonneg b)
    have hp0 : 0 ≤ |b| ^ s := Real.rpow_nonneg (abs_nonneg _) _
    nlinarith [he, mul_le_mul_of_nonneg_right hs2 hp0]
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Set.Icc (0 : ℝ) 1) => (hd t).hasDerivWithinAt) hbound
    (convex_Icc (0 : ℝ) 1) (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  simp only [f, zero_mul, add_zero, mul_zero, sub_zero, one_mul,
    Real.norm_eq_abs, abs_one, mul_one] at hm
  have hh := (le_abs_self (|a + b| ^ s - s * slope s a * b - |a| ^ s)).trans hm
  linarith

lemma lp_norm_power {ι : Type*} [Fintype ι] (p : ENNReal)
    (hp : 0 < p.toReal) (x : PiLp p (fun _ : ι => ℝ)) :
    ‖x‖ ^ p.toReal = ∑ i, |x i| ^ p.toReal := by
  rw [PiLp.norm_eq_sum hp, ← Real.rpow_mul (Finset.sum_nonneg fun _ _ =>
    Real.rpow_nonneg (norm_nonneg _) _), one_div_mul_cancel hp.ne', Real.rpow_one]
  simp only [Real.norm_eq_abs]

lemma lp_power_smooth {ι : Type*} [Fintype ι] (p : ENNReal) [Fact (1 ≤ p)]
    (hp : 1 < p.toReal) (hp2 : p.toReal ≤ 2) :
    ∃ j : PiLp p (fun _ : ι => ℝ) → PiLp p (fun _ : ι => ℝ) →L[ℝ] ℝ,
      LongTails.Setups.StochasticPowerSmoothFixedPoint.PowerSmooth
        (PiLp p (fun _ : ι => ℝ)) p.toReal 4 j := by
  classical
  let j : PiLp p (fun _ : ι => ℝ) → PiLp p (fun _ : ι => ℝ) →L[ℝ] ℝ :=
    fun x => ∑ i, slope p.toReal (x i) • PiLp.proj p (fun _ : ι => ℝ) i
  refine ⟨j, ?_⟩
  intro x y
  rw [lp_norm_power p (by linarith), lp_norm_power p (by linarith),
    lp_norm_power p (by linarith)]
  have hj : j x y = ∑ i, slope p.toReal (x i) * y i := by
    simp [j]
  rw [hj, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [PiLp.add_apply, mul_assoc] using scalar_power_smooth hp hp2 (x i) (y i)

end LongTails.Proofs.PowerSmoothLpGeometry
