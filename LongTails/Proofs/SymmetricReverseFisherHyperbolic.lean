import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace LongTails.Proofs.SymmetricReverseFisherHyperbolic

noncomputable def sech (x : ℝ) : ℝ := (Real.cosh x)⁻¹

noncomputable def kernelU (x : ℝ) : ℝ := Real.tanh x + x * sech x ^ 2

noncomputable def kernelV (x : ℝ) : ℝ :=
  Real.tanh x + 3 * x * sech x ^ 2 - 2 * x ^ 2 * Real.tanh x * sech x ^ 2

noncomputable def kernelW (x : ℝ) : ℝ :=
  2 * sech x ^ 2 * (3 * Real.tanh x - 2 * x + 3 * x * sech x ^ 2)

lemma sech_pos (x : ℝ) : 0 < sech x := inv_pos.mpr (Real.cosh_pos x)

lemma sech_le_one (x : ℝ) : sech x ≤ 1 := by
  exact inv_le_one_of_one_le₀ (Real.one_le_cosh x)

lemma tanh_sq_add_sech_sq (x : ℝ) : Real.tanh x ^ 2 + sech x ^ 2 = 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  dsimp [sech]
  field_simp
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (sech x ^ 2) x := by
  convert (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x)
    (ne_of_gt (Real.cosh_pos x)) using 1
  · exact funext (fun y => Real.tanh_eq_sinh_div_cosh y)
  · dsimp [sech]
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq x]

lemma hasDerivAt_sech (x : ℝ) :
    HasDerivAt sech (-Real.tanh x * sech x) x := by
  convert (Real.hasDerivAt_cosh x).inv (ne_of_gt (Real.cosh_pos x)) using 1
  · rfl
  · rw [Real.tanh_eq_sinh_div_cosh]
    dsimp [sech]
    ring

lemma hasDerivAt_sech_sq (x : ℝ) :
    HasDerivAt (fun y => sech y ^ 2) (-2 * Real.tanh x * sech x ^ 2) x := by
  convert (hasDerivAt_sech x).pow 2 using 1
  ring

lemma hasDerivAt_kernelU (x : ℝ) :
    HasDerivAt kernelU (2 * sech x ^ 2 * (1 - x * Real.tanh x)) x := by
  convert (hasDerivAt_tanh x).add ((hasDerivAt_id x).mul (hasDerivAt_sech_sq x))
    using 1
  · rfl
  · simp only [id_eq]
    ring

lemma hasDerivAt_kernelU_prime (x : ℝ) :
    HasDerivAt (fun y => 2 * sech y ^ 2 * (1 - y * Real.tanh y)) (-kernelW x) x := by
  convert ((hasDerivAt_sech_sq x).const_mul 2).mul
    ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).mul (hasDerivAt_tanh x))) using 1
  · rfl
  · simp only [kernelW, id_eq, Pi.sub_apply, Pi.mul_apply]
    linear_combination -4 * x * sech x ^ 2 * tanh_sq_add_sech_sq x

lemma kernelV_eq (x : ℝ) :
    kernelV x = kernelU x + x * (2 * sech x ^ 2 * (1 - x * Real.tanh x)) := by
  dsimp [kernelV, kernelU]
  ring

lemma cosh_gt_quadratic {x : ℝ} (hx : 0 < x) :
    1 + x ^ 2 / 2 < Real.cosh x := by
  have hh : 0 < x / 2 := by positivity
  have hs := Real.self_lt_sinh_iff.mpr hh
  have hc := Real.cosh_two_mul (x := x / 2)
  have hsq := Real.cosh_sq_sub_sinh_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hc
  have hs' : (x / 2) ^ 2 < Real.sinh (x / 2) ^ 2 := by nlinarith
  nlinarith

lemma cosh_sq_gt_twice_sq {x : ℝ} (hx : 0 < x) :
    2 * x ^ 2 < Real.cosh x ^ 2 := by
  have hc := cosh_gt_quadratic hx
  have hc' : (1 + x ^ 2 / 2) ^ 2 < Real.cosh x ^ 2 := by
    nlinarith [Real.cosh_pos x, sq_nonneg x]
  nlinarith [sq_nonneg (x ^ 2 - 2)]

lemma kernelV_pos {x : ℝ} (hx : 0 < x) : 0 < kernelV x := by
  have hcosh := cosh_sq_gt_twice_sq hx
  have hs : 0 < sech x ^ 2 := sq_pos_of_pos (sech_pos x)
  have hid : sech x ^ 2 * Real.cosh x ^ 2 = 1 := by
    dsimp [sech]
    field_simp
  have hmul := mul_lt_mul_of_pos_left hcosh hs
  have ht : 0 < Real.tanh x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hx) (Real.cosh_pos x)
  have hp : 0 < Real.tanh x * (1 - 2 * x ^ 2 * sech x ^ 2) := by
    apply mul_pos ht
    nlinarith
  dsimp [kernelV]
  nlinarith [mul_pos hx hs]

lemma mul_sech_sq_lt_tanh {x : ℝ} (hx : 0 < x) :
    x * sech x ^ 2 < Real.tanh x := by
  have h := Real.self_lt_sinh_iff.mpr (show 0 < 2 * x by positivity)
  rw [Real.sinh_two_mul] at h
  have hsc : x < Real.sinh x * Real.cosh x := by linarith
  have hmul := mul_lt_mul_of_pos_right hsc (sq_pos_of_pos (sech_pos x))
  have he : Real.sinh x * Real.cosh x * sech x ^ 2 = Real.tanh x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    dsimp [sech]
    field_simp
  rwa [he] at hmul

noncomputable def kernelSign (x : ℝ) : ℝ :=
  3 * (Real.tanh x / x) + 1 - 3 * Real.tanh x ^ 2

lemma kernelW_eq_sign {x : ℝ} (hx : x ≠ 0) :
    kernelW x = 2 * x * sech x ^ 2 * kernelSign x := by
  dsimp [kernelW, kernelSign]
  field_simp
  linear_combination 3 * x * sech x ^ 2 * tanh_sq_add_sech_sq x

lemma hasDerivAt_kernelSign {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt kernelSign
      (3 * (sech x ^ 2 * x - Real.tanh x) / x ^ 2 -
        6 * Real.tanh x * sech x ^ 2) x := by
  convert (((hasDerivAt_tanh x).div (hasDerivAt_id x) hx).const_mul 3).add_const 1 |>.sub
    (((hasDerivAt_tanh x).pow 2).const_mul 3) using 1
  · rfl
  · simp only [id_eq]
    ring

lemma kernelSign_strictAntiOn : StrictAntiOn kernelSign (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_kernelSign (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
    rw [(hasDerivAt_kernelSign (ne_of_gt hx')).deriv]
    have hn : sech x ^ 2 * x - Real.tanh x < 0 := by
      nlinarith [mul_sech_sq_lt_tanh hx']
    have hfirst : 3 * (sech x ^ 2 * x - Real.tanh x) / x ^ 2 < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hn) (sq_pos_of_pos hx')
    have ht : 0 < Real.tanh x := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos (Real.sinh_pos_iff.mpr hx') (Real.cosh_pos x)
    have hs := sq_pos_of_pos (sech_pos x)
    have hp : 0 < 6 * Real.tanh x * sech x ^ 2 := by positivity
    linarith

lemma tanh_eq_exp_two (x : ℝ) :
    Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
  rw [Real.tanh_eq, Real.exp_neg, show Real.exp (2 * x) = Real.exp x ^ 2 by
    rw [two_mul, Real.exp_add, pow_two]]
  field_simp

lemma tanh_two_gt : (19 : ℝ) / 20 < Real.tanh 2 := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4) 6
  norm_num [Finset.sum_range_succ] at he
  have he' : 39 < Real.exp 4 := by linarith
  rw [tanh_eq_exp_two]
  norm_num only
  apply (lt_div_iff₀ (show 0 < Real.exp 4 + 1 by positivity)).mpr
  linarith

lemma kernelSign_three_halves_pos : 0 < kernelSign (3 / 2) := by
  have ht : 0 < Real.tanh (3 / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (Real.cosh_pos _)
  have hp := mul_pos (sub_pos.mpr (Real.tanh_lt_one (3 / 2)))
    (show 0 < 3 * Real.tanh (3 / 2) + 1 by positivity)
  dsimp [kernelSign]
  nlinarith

lemma kernelSign_two_neg : kernelSign 2 < 0 := by
  have ht := tanh_two_gt
  have ht' := Real.tanh_lt_one 2
  dsimp [kernelSign]
  nlinarith

lemma exists_kernel_crossing : ∃ b ∈ Set.Icc (3 / 2 : ℝ) 2,
    kernelSign b = 0 ∧
    (∀ x, 0 < x → x ≤ b → 0 ≤ kernelW x) ∧
    (∀ x, b ≤ x → kernelW x ≤ 0) := by
  have hc : ContinuousOn kernelSign (Set.Icc (3 / 2 : ℝ) 2) := by
    intro x hx
    exact (hasDerivAt_kernelSign (by linarith [hx.1])).continuousAt.continuousWithinAt
  obtain ⟨b, hb, hzero⟩ := intermediate_value_Icc' (by norm_num : (3 / 2 : ℝ) ≤ 2) hc
    ⟨kernelSign_two_neg.le, kernelSign_three_halves_pos.le⟩
  have hb' : 0 < b := by linarith [hb.1]
  refine ⟨b, hb, hzero, ?_, ?_⟩
  · intro x hx hxb
    rw [kernelW_eq_sign (ne_of_gt hx)]
    have hs := kernelSign_strictAntiOn.antitoneOn hx hb' hxb
    rw [hzero] at hs
    positivity
  · intro x hbx
    have hx : 0 < x := hb'.trans_le hbx
    rw [kernelW_eq_sign (ne_of_gt hx)]
    have hs := kernelSign_strictAntiOn.antitoneOn hb' hx hbx
    rw [hzero] at hs
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hs

lemma tanh_div_strictAntiOn : StrictAntiOn (fun x : ℝ => Real.tanh x / x) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact ((hasDerivAt_tanh x).div (hasDerivAt_id x)
      (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
    erw [((hasDerivAt_tanh x).div (hasDerivAt_id x) (ne_of_gt hx')).deriv]
    apply div_neg_of_neg_of_pos
    · simp only [id_eq, mul_one]
      nlinarith [mul_sech_sq_lt_tanh hx']
    · exact sq_pos_of_pos hx'

lemma tanh_scale_le {x t : ℝ} (hx : 0 < x) (ht : 0 < t) (ht1 : t ≤ 1) :
    t * Real.tanh x ≤ Real.tanh (t * x) := by
  have htx : 0 < t * x := mul_pos ht hx
  have hle : t * x ≤ x := mul_le_of_le_one_left hx.le ht1
  have h := tanh_div_strictAntiOn.antitoneOn htx hx hle
  have hh := (div_le_div_iff₀ hx htx).mp h
  nlinarith

lemma sinh_ratio_antitoneOn {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    AntitoneOn (fun x : ℝ => Real.sinh (t * x) / Real.sinh x) (Set.Ioi 0) := by
  have hd (x : ℝ) (hx : 0 < x) :=
    (((hasDerivAt_id x).const_mul t).sinh).div (Real.hasDerivAt_sinh x)
      (ne_of_gt (Real.sinh_pos_iff.mpr hx))
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (by simpa only [interior_Ioi, Set.mem_Ioi] using hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, Set.mem_Ioi] using hx
    erw [(hd x hx').deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    have hh := tanh_scale_le hx' ht ht1
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh] at hh
    have hc : 0 < Real.cosh x * Real.cosh (t * x) :=
      mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
    have hh' := mul_le_mul_of_nonneg_right hh hc.le
    field_simp at hh'
    simp only [id_eq, mul_one]
    nlinarith

lemma sech_mul_cosh (x : ℝ) : sech x * Real.cosh x = 1 :=
  inv_mul_cancel₀ (ne_of_gt (Real.cosh_pos x))

lemma sech_sq_mul_cosh (x : ℝ) : sech x ^ 2 * Real.cosh x = sech x := by
  calc
    _ = sech x * (sech x * Real.cosh x) := by ring
    _ = sech x := by rw [sech_mul_cosh, mul_one]

lemma sech_mul_sinh (x : ℝ) : sech x * Real.sinh x = Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  dsimp [sech]
  ring

lemma sech_le_exp (x : ℝ) : sech x ≤ 2 * Real.exp (-x) := by
  have hc := Real.cosh_eq x
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hc' := congrArg (fun y : ℝ => y * Real.exp (-x)) hc
  have hh : 1 ≤ Real.cosh x * (2 * Real.exp (-x)) := by
    nlinarith [sq_nonneg (Real.exp (-x))]
  exact (inv_le_iff_one_le_mul₀' (Real.cosh_pos x)).mpr hh

noncomputable def kernelPrimitive (x : ℝ) : ℝ :=
  2 * x * sech x - (2 * sech x ^ 2 * (1 - x * Real.tanh x)) * Real.sinh x

lemma kernelPrimitive_zero : kernelPrimitive 0 = 0 := by simp [kernelPrimitive]

lemma hasDerivAt_kernelPrimitive (x : ℝ) :
    HasDerivAt kernelPrimitive (kernelW x * Real.sinh x) x := by
  convert (((hasDerivAt_id x).const_mul 2).mul (hasDerivAt_sech x)).sub
    ((hasDerivAt_kernelU_prime x).mul (Real.hasDerivAt_sinh x)) using 1
  · rfl
  · simp only [id_eq]
    linear_combination 2 * (1 - x * Real.tanh x) * sech_sq_mul_cosh x

lemma kernelPrimitive_eq (x : ℝ) : kernelPrimitive x =
    2 * sech x * (x - Real.tanh x + x * Real.tanh x ^ 2) := by
  dsimp [kernelPrimitive]
  linear_combination -2 * sech x * (1 - x * Real.tanh x) * sech_mul_sinh x

lemma kernelW_mul_sinh (x : ℝ) : kernelW x * Real.sinh x =
    2 * sech x * Real.tanh x * (3 * Real.tanh x - 2 * x + 3 * x * sech x ^ 2) := by
  dsimp [kernelW]
  linear_combination 2 * sech x *
    (3 * Real.tanh x - 2 * x + 3 * x * sech x ^ 2) * sech_mul_sinh x

lemma kernelPrimitive_bound {x : ℝ} (hx : 0 ≤ x) :
    |kernelPrimitive x| ≤ 4 * (2 * x + 1) * Real.exp (-x) := by
  have hs : 0 ≤ sech x := (sech_pos x).le
  have ht := (Real.abs_tanh_lt_one x).le
  have ht2 := (Real.tanh_sq_lt_one x).le
  have hinner : |x - Real.tanh x + x * Real.tanh x ^ 2| ≤ 2 * x + 1 := by
    calc
      _ ≤ |x - Real.tanh x| + |x * Real.tanh x ^ 2| := abs_add_le _ _
      _ ≤ (x + 1) + x := by
        apply add_le_add
        · exact (abs_sub x (Real.tanh x)).trans (by simpa [abs_of_nonneg hx] using add_le_add_left ht x)
        · rw [abs_mul, abs_of_nonneg hx, abs_of_nonneg (sq_nonneg _)]
          exact mul_le_of_le_one_right hx ht2
      _ = _ := by ring
  rw [kernelPrimitive_eq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * sech x)]
  calc
    _ ≤ 2 * sech x * (2 * x + 1) := mul_le_mul_of_nonneg_left hinner (by positivity)
    _ ≤ 4 * (2 * x + 1) * Real.exp (-x) := by
      have h := mul_le_mul_of_nonneg_right (sech_le_exp x) (show 0 ≤ 2 * (2 * x + 1) by positivity)
      nlinarith

lemma kernelW_sinh_bound {x : ℝ} (hx : 0 ≤ x) :
    |kernelW x * Real.sinh x| ≤ 4 * (3 + 5 * x) * Real.exp (-x) := by
  have ht := (Real.abs_tanh_lt_one x).le
  have hs : 0 ≤ sech x := (sech_pos x).le
  have hs2 : sech x ^ 2 ≤ 1 := by nlinarith [sech_le_one x]
  have hb : |3 * Real.tanh x - 2 * x + 3 * x * sech x ^ 2| ≤ 3 + 5 * x := by
    calc
      _ ≤ |3 * Real.tanh x - 2 * x| + |3 * x * sech x ^ 2| := abs_add_le _ _
      _ ≤ (3 + 2 * x) + 3 * x := by
        apply add_le_add
        · calc
            _ ≤ |3 * Real.tanh x| + |2 * x| := abs_sub _ _
            _ ≤ 3 + 2 * x := by
              rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3),
                abs_of_nonneg (by positivity : 0 ≤ 2 * x)]
              linarith
        · rw [abs_of_nonneg (by positivity)]
          exact mul_le_of_le_one_right (by positivity) hs2
      _ = _ := by ring
  rw [kernelW_mul_sinh, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 2 * sech x)]
  calc
    _ ≤ 2 * sech x * 1 * (3 + 5 * x) := by gcongr
    _ ≤ 4 * (3 + 5 * x) * Real.exp (-x) := by
      have h := mul_le_mul_of_nonneg_right (sech_le_exp x) (show 0 ≤ 2 * (3 + 5 * x) by positivity)
      nlinarith

@[fun_prop]
lemma continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tanh x).continuousAt)

@[fun_prop]
lemma continuous_sech : Continuous sech :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_sech x).continuousAt)

@[fun_prop]
lemma continuous_kernelW : Continuous kernelW := by unfold kernelW; fun_prop

lemma sech_neg (x : ℝ) : sech (-x) = sech x := by simp [sech]

lemma kernelW_neg (x : ℝ) : kernelW (-x) = -kernelW x := by
  simp only [kernelW, sech_neg, Real.tanh_neg]
  ring

lemma kernelW_linear_bound (x : ℝ) : |kernelW x| ≤ 6 + 10 * |x| := by
  have ht := (Real.abs_tanh_lt_one x).le
  have hs : 0 ≤ sech x := (sech_pos x).le
  have hs2 : sech x ^ 2 ≤ 1 := by nlinarith [sech_le_one x]
  have hb : |3 * Real.tanh x - 2 * x + 3 * x * sech x ^ 2| ≤ 3 + 5 * |x| := by
    calc
      _ ≤ |3 * Real.tanh x - 2 * x| + |3 * x * sech x ^ 2| := abs_add_le _ _
      _ ≤ (3 + 2 * |x|) + 3 * |x| := by
        apply add_le_add
        · calc
            _ ≤ |3 * Real.tanh x| + |2 * x| := abs_sub _ _
            _ ≤ 3 + 2 * |x| := by
              simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
                abs_of_pos (by norm_num : (0 : ℝ) < 2)]
              linarith
        · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3),
            abs_of_nonneg (sq_nonneg (sech x))]
          exact mul_le_of_le_one_right (by positivity) hs2
      _ = _ := by ring
  rw [kernelW, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * sech x ^ 2)]
  calc
    _ ≤ 2 * 1 * (3 + 5 * |x|) := by gcongr
    _ = _ := by ring

lemma sech_sq_lower_small {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 3 / 2) :
    (1 : ℝ) / 6 ≤ sech x ^ 2 := by
  have he1 : Real.exp 1 ≤ 11 / 4 := le_trans Real.exp_one_lt_d9.le (by norm_num)
  have he3 : Real.exp 3 ≤ 21 := by
    have h := pow_le_pow_left₀ (Real.exp_pos 1).le he1 3
    have he := Real.exp_nat_mul (1 : ℝ) 3
    norm_num only [Nat.cast_ofNat, mul_one] at he
    rw [← he] at h
    norm_num at h
    linarith
  have hen : Real.exp (-3) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hc3 : Real.cosh 3 ≤ 11 := by rw [Real.cosh_eq]; linarith
  have hc := Real.cosh_two_mul (x := (3 : ℝ) / 2)
  rw [show 2 * ((3 : ℝ) / 2) = 3 by ring] at hc
  have hs : Real.cosh (3 / 2) ^ 2 ≤ 6 := by
    linarith [Real.cosh_sq_sub_sinh_sq ((3 : ℝ) / 2)]
  have hm : Real.cosh x ≤ Real.cosh (3 / 2) := by
    apply Real.cosh_le_cosh.mpr
    simpa only [abs_of_nonneg hx, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)] using hx1
  have hsq : Real.cosh x ^ 2 ≤ 6 := (pow_le_pow_left₀ (Real.cosh_pos x).le hm 2).trans hs
  have hid : sech x ^ 2 * Real.cosh x ^ 2 = 1 := by unfold sech; field_simp
  nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (sech x))]

lemma kernelV_lower_small {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 3 / 2) :
    x ≤ 2 * kernelV x := by
  rcases hx.eq_or_lt with hx | hx
  · subst x
    simp [kernelV]
  have hc := cosh_sq_gt_twice_sq hx
  have hid : sech x ^ 2 * Real.cosh x ^ 2 = 1 := by unfold sech; field_simp
  have hh := mul_lt_mul_of_pos_left hc (sq_pos_of_pos (sech_pos x))
  have ht : 0 < Real.tanh x := by rw [Real.tanh_eq_sinh_div_cosh]; positivity
  have hp : 0 ≤ Real.tanh x * (1 - 2 * x ^ 2 * sech x ^ 2) := by
    apply mul_nonneg ht.le
    nlinarith
  have hs := sech_sq_lower_small hx.le hx1
  have hm := mul_le_mul_of_nonneg_left hs hx.le
  unfold kernelV
  nlinarith

lemma exp_three_lower : (20 : ℝ) ≤ Real.exp 3 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3) 9
  norm_num [Finset.sum_range_succ] at h
  linarith

lemma exp_two_lower {y : ℝ} (hy : 3 / 2 ≤ y) :
    20 * (1 + 2 * (y - 3 / 2) + 2 * (y - 3 / 2) ^ 2) ≤ Real.exp (2 * y) := by
  have h := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ 2 * (y - 3 / 2)) 3
  norm_num [Finset.sum_range_succ] at h
  have he : 2 * y = 3 + 2 * (y - 3 / 2) := by ring
  rw [he, Real.exp_add]
  have hn : 0 ≤ 1 + 2 * (y - 3 / 2) + 2 * (y - 3 / 2) ^ 2 := by positivity
  apply mul_le_mul exp_three_lower _ hn (Real.exp_pos _).le
  nlinarith

lemma kernel_polynomial_pos {y Q : ℝ} (hy : 3 / 2 ≤ y)
    (hQ : 20 * (1 + 2 * (y - 3 / 2) + 2 * (y - 3 / 2) ^ 2) ≤ Q) :
    0 < 29 * Q ^ 4 + (-240 * y ^ 2 - 1800 * y + 3296) * Q ^ 3 +
      (9360 * y - 6) * Q ^ 2 + (240 * y ^ 2 - 1800 * y - 3304) * Q - 31 := by
  have h20 : 20 ≤ Q := by nlinarith [sq_nonneg (y - 3 / 2)]
  have hfirst : 130 ≤ 29 * Q - 240 * y ^ 2 - 1800 * y + 3296 := by
    nlinarith [sq_nonneg (y - 3 / 2 - 17 / 23)]
  have hsecond : 0 ≤ Q * (9360 * y - 6) + 240 * y ^ 2 - 1800 * y - 3304 := by
    have h := mul_le_mul_of_nonneg_right h20 (show 0 ≤ 9360 * y - 6 by linarith)
    nlinarith [sq_nonneg y]
  have h1 := mul_le_mul_of_nonneg_right hfirst (show 0 ≤ Q ^ 3 by positivity)
  have h2 := mul_nonneg (show 0 ≤ Q by linarith) hsecond
  have h3 : 1 ≤ Q ^ 3 := by nlinarith [sq_nonneg (Q - 1), mul_nonneg (show 0 ≤ Q - 1 by linarith) (sq_nonneg Q)]
  nlinarith

lemma sech_sq_exp_two (x : ℝ) :
    sech x ^ 2 = 4 * Real.exp (2 * x) / (Real.exp (2 * x) + 1) ^ 2 := by
  have h : sech x ^ 2 = 1 - Real.tanh x ^ 2 := by linarith [tanh_sq_add_sech_sq x]
  rw [h, tanh_eq_exp_two]
  field_simp
  ring

lemma kernel_nine_certificate (y : ℝ) :
    15 * (Real.exp (2 * y) + 1) ^ 4 * (2 * kernelV y + 9 * kernelW y - 1 / 15) =
      29 * Real.exp (2 * y) ^ 4 + (-240 * y ^ 2 - 1800 * y + 3296) * Real.exp (2 * y) ^ 3 +
      (9360 * y - 6) * Real.exp (2 * y) ^ 2 +
      (240 * y ^ 2 - 1800 * y - 3304) * Real.exp (2 * y) - 31 := by
  unfold kernelV kernelW
  rw [tanh_eq_exp_two, sech_sq_exp_two]
  field_simp
  ring

lemma kernel_nine_lower {y : ℝ} (hy : 3 / 2 ≤ y) :
    (1 : ℝ) / 15 ≤ 2 * kernelV y + 9 * kernelW y := by
  have h := kernel_polynomial_pos hy (exp_two_lower hy)
  rw [← kernel_nine_certificate] at h
  have hm : 0 < 15 * (Real.exp (2 * y) + 1) ^ 4 := by positivity
  exact (sub_pos.mp ((mul_pos_iff_of_pos_left hm).mp h)).le

lemma tanh_lower_large {y : ℝ} (hy : 3 / 2 ≤ y) : (9 : ℝ) / 10 ≤ Real.tanh y := by
  have he : 20 ≤ Real.exp (2 * y) := exp_three_lower.trans (Real.exp_le_exp.mpr (by linarith))
  rw [tanh_eq_exp_two]
  apply (le_div_iff₀ (show 0 < Real.exp (2 * y) + 1 by positivity)).mpr
  linarith

lemma kernelV_lower_middle {y : ℝ} (hy : 3 / 2 ≤ y) (hy2 : y ≤ 2) :
    (13 : ℝ) / 25 ≤ kernelV y := by
  have ht := tanh_lower_large hy
  have ht1 := Real.tanh_lt_one y
  have hs : sech y ^ 2 ≤ 19 / 100 := by nlinarith [tanh_sq_add_sech_sq y]
  have hyt : y * Real.tanh y ≤ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ 1 - Real.tanh y by linarith)]
  have hys : y * sech y ^ 2 ≤ 38 / 100 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 - y by linarith) (sq_nonneg (sech y))]
  have hp := mul_nonneg (mul_nonneg (show 0 ≤ y by linarith) (sq_nonneg (sech y)))
    (show 0 ≤ 2 - y * Real.tanh y by linarith)
  unfold kernelV
  nlinarith

lemma kernel_combination_lower {a y : ℝ} (ha : 0 ≤ a) (ha3 : a ≤ 3) (hy : 0 ≤ y) :
    min y 1 / 15 ≤ 2 * kernelV y + a ^ 2 * kernelW y := by
  obtain ⟨b, hb, _, hpos, hneg⟩ := exists_kernel_crossing
  rcases le_total y (3 / 2) with hsmall | hlarge
  · have hw : 0 ≤ kernelW y := by
      rcases hy.eq_or_lt with hy | hy
      · subst y
        simp [kernelW]
      · exact hpos y hy (hsmall.trans hb.1)
    have hv := kernelV_lower_small hy hsmall
    have hp := mul_nonneg (sq_nonneg a) hw
    have hm := min_le_left y (1 : ℝ)
    have hn : 0 ≤ min y 1 := le_min hy zero_le_one
    linarith
  · rw [min_eq_right (show 1 ≤ y by linarith)]
    by_cases hw : kernelW y ≤ 0
    · have hsq : a ^ 2 ≤ 9 := by nlinarith
      have hm := mul_le_mul_of_nonpos_right hsq hw
      linarith [kernel_nine_lower hlarge]
    · have hy2 : y ≤ 2 := by
        by_contra h
        have hn := hneg y (hb.2.trans (le_of_not_ge h))
        exact hw hn
      have hp := mul_nonneg (sq_nonneg a) (le_of_not_ge hw)
      linarith [kernelV_lower_middle hlarge hy2]

lemma kernelV_neg (x : ℝ) : kernelV (-x) = -kernelV x := by
  simp [kernelV, sech, Real.tanh_neg]
  ring

lemma kernelV_quadratic_bound (x : ℝ) : |kernelV x| ≤ 1 + 3 * |x| + 2 * x ^ 2 := by
  have hs : sech x ^ 2 ≤ 1 := by nlinarith [sech_pos x, sech_le_one x]
  have ht : |Real.tanh x| ≤ 1 := (Real.abs_tanh_lt_one x).le
  have h1 : |3 * x * sech x ^ 2| ≤ 3 * |x| := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_pow, abs_of_pos (sech_pos x)]
    exact mul_le_of_le_one_right (by positivity) hs
  have h2 : |2 * x ^ 2 * Real.tanh x * sech x ^ 2| ≤ 2 * x ^ 2 := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow, sq_abs, abs_of_pos (sech_pos x)]
    calc
      _ ≤ 2 * x ^ 2 * |Real.tanh x| := mul_le_of_le_one_right (by positivity) hs
      _ ≤ 2 * x ^ 2 := mul_le_of_le_one_right (by positivity) ht
  calc
    |kernelV x| ≤ |Real.tanh x| + |3 * x * sech x ^ 2| +
        |2 * x ^ 2 * Real.tanh x * sech x ^ 2| := by
      unfold kernelV
      have h := abs_add_le (Real.tanh x + 3 * x * sech x ^ 2)
        (-(2 * x ^ 2 * Real.tanh x * sech x ^ 2))
      rw [abs_neg, ← sub_eq_add_neg] at h
      linarith [abs_add_le (Real.tanh x) (3 * x * sech x ^ 2)]
    _ ≤ 1 + 3 * |x| + 2 * x ^ 2 := by linarith

lemma sech_sq_le_exp (x : ℝ) : sech x ^ 2 ≤ 4 * Real.exp (-2 * x) := by
  have h := pow_le_pow_left₀ (sech_pos x).le (sech_le_exp x) 2
  have he : Real.exp (-2 * x) = Real.exp (-x) ^ 2 := by
    rw [show -2 * x = -x + -x by ring, Real.exp_add, pow_two]
  rw [he]
  nlinarith

lemma kernelW_lower_exp {y : ℝ} (hy : 0 ≤ y) :
    -16 * y * Real.exp (-2 * y) ≤ kernelW y := by
  have ht : 0 ≤ Real.tanh y := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hy) (Real.cosh_pos y).le
  have hs := sech_sq_le_exp y
  have hm := mul_le_mul_of_nonneg_left hs hy
  have hp := mul_nonneg (sq_nonneg (sech y))
    (show 0 ≤ 3 * Real.tanh y + 3 * y * sech y ^ 2 by positivity)
  unfold kernelW
  nlinarith

lemma square_exp_bound_large {y : ℝ} (hy : 3 ≤ y) :
    y ^ 2 * Real.exp (-2 * y) ≤ 9 / 400 := by
  have he6 : 400 ≤ Real.exp 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) exp_three_lower 2
    rw [show Real.exp 3 ^ 2 = Real.exp 6 by rw [pow_two, ← Real.exp_add]; norm_num] at h
    norm_num at h
    exact h
  have heh := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ 2 * (y - 3)) 3
  norm_num [Finset.sum_range_succ] at heh
  have hpoly : 0 ≤ 1 + 2 * (y - 3) + 2 * (y - 3) ^ 2 := by positivity
  have he : 400 * (1 + 2 * (y - 3) + 2 * (y - 3) ^ 2) ≤ Real.exp (2 * y) := by
    rw [show 2 * y = 6 + 2 * (y - 3) by ring, Real.exp_add]
    apply mul_le_mul he6 _ hpoly (Real.exp_pos _).le
    nlinarith
  have hm : 400 * y ^ 2 ≤ 9 * Real.exp (2 * y) := by nlinarith [sq_nonneg (y - 3)]
  rw [show -2 * y = -(2 * y) by ring, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  linarith

lemma kernelV_lower_large {y : ℝ} (hy : 3 ≤ y) : (18 : ℝ) / 25 ≤ kernelV y := by
  have ht := tanh_lower_large (show 3 / 2 ≤ y by linarith)
  have ht1 := (Real.tanh_lt_one y).le
  have hs := sech_sq_le_exp y
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg y)
  have hb := square_exp_bound_large hy
  have htprod := mul_le_mul_of_nonneg_left ht1
    (mul_nonneg (sq_nonneg y) (sq_nonneg (sech y)))
  have hp : 0 ≤ y * sech y ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  unfold kernelV
  nlinarith

end LongTails.Proofs.SymmetricReverseFisherHyperbolic
