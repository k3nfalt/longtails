import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Real.Pi.Bounds

open Real

namespace OracleTemplate.ArrowHurwicz

noncomputable def bandEdge : ℝ := sin (π / 12)

noncomputable def bandWeight (ω : ℝ) : ℝ := (sin (ω / 2) - bandEdge) ^ 2

noncomputable def bandCoef (j : ℕ) : ℝ :=
  2 / π * ∫ ω in (π / 6)..π, bandWeight ω * sin (((j : ℝ) + 1 / 2) * ω)

lemma band_integrand_identity (a p ω : ℝ) :
    (sin (ω / 2) - a) ^ 2 * sin (p * ω) =
      (1 / 2 + a ^ 2) * sin (p * ω) - (sin ((p + 1) * ω) + sin ((p - 1) * ω)) / 4 -
        a * (cos ((p - 1 / 2) * ω) - cos ((p + 1 / 2) * ω)) := by
  set u := ω / 2 with hu
  have hω : ω = 2 * u := by rw [hu]; ring
  have e1 : (p + 1) * ω = p * ω + 2 * u := by rw [hω]; ring
  have e2 : (p - 1) * ω = p * ω - 2 * u := by rw [hω]; ring
  have e3 : (p - 1 / 2) * ω = p * ω - u := by rw [hω]; ring
  have e4 : (p + 1 / 2) * ω = p * ω + u := by rw [hω]; ring
  rw [e1, e2, e3, e4, sin_add, sin_sub, cos_sub, cos_add, sin_two_mul, cos_two_mul]
  have hs := sin_sq_add_cos_sq u
  linear_combination (sin (p * ω)) * hs

noncomputable def bandAnti (a p ω : ℝ) : ℝ :=
  -(1 / 2 + a ^ 2) * cos (p * ω) / p + (cos ((p + 1) * ω) / (p + 1) + cos ((p - 1) * ω) / (p - 1)) / 4 -
    a * (sin ((p - 1 / 2) * ω) / (p - 1 / 2) - sin ((p + 1 / 2) * ω) / (p + 1 / 2))

lemma band_hasDerivAt_cos_div (c ω : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun ω => cos (c * ω) / c) (-sin (c * ω)) ω := by
  have h := ((hasDerivAt_id ω).const_mul c).cos
  have h2 := h.div_const c
  simp only [id] at h2
  convert h2 using 1
  field_simp

lemma band_hasDerivAt_sin_div (c ω : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun ω => sin (c * ω) / c) (cos (c * ω)) ω := by
  have h := ((hasDerivAt_id ω).const_mul c).sin
  have h2 := h.div_const c
  simp only [id] at h2
  convert h2 using 1
  field_simp

lemma band_hasDerivAt_anti (a p ω : ℝ) (h0 : p ≠ 0) (h1 : p + 1 ≠ 0) (h2 : p - 1 ≠ 0)
    (h3 : p - 1 / 2 ≠ 0) (h4 : p + 1 / 2 ≠ 0) :
    HasDerivAt (bandAnti a p) ((sin (ω / 2) - a) ^ 2 * sin (p * ω)) ω := by
  rw [band_integrand_identity]
  have d0 := (band_hasDerivAt_cos_div p ω h0).const_mul (-(1 / 2 + a ^ 2))
  have d1 := band_hasDerivAt_cos_div (p + 1) ω h1
  have d2 := band_hasDerivAt_cos_div (p - 1) ω h2
  have d3 := band_hasDerivAt_sin_div (p - 1 / 2) ω h3
  have d4 := band_hasDerivAt_sin_div (p + 1 / 2) ω h4
  have := ((d0.add ((d1.add d2).div_const 4)).sub ((d3.sub d4).const_mul a))
  unfold bandAnti
  convert this using 1
  · funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  · ring

noncomputable def bandAnti0 (a ω : ℝ) : ℝ :=
  -(3 / 2 + 2 * a ^ 2) * cos (ω / 2) + cos (3 / 2 * ω) / 6 - a * (ω - sin ω)

lemma band_hasDerivAt_anti0 (a ω : ℝ) :
    HasDerivAt (bandAnti0 a) ((sin (ω / 2) - a) ^ 2 * sin ((1 / 2 : ℝ) * ω)) ω := by
  have d1 := ((hasDerivAt_id ω).div_const 2).cos.const_mul (-(3 / 2 + 2 * a ^ 2))
  have d2 := (((hasDerivAt_id ω).const_mul (3 / 2 : ℝ)).cos).div_const 6
  have d3 := ((hasDerivAt_id ω).sub (hasDerivAt_sin ω)).const_mul a
  have := (d1.add d2).sub d3
  simp only [id] at this
  unfold bandAnti0
  convert this using 1
  · funext x; simp only [Pi.add_apply, Pi.sub_apply, id]
  · have e : (3 / 2 : ℝ) * ω = ω / 2 + ω := by ring
    have e2 : ω = 2 * (ω / 2) := by ring
    have e3 : (1 / 2 : ℝ) * ω = ω / 2 := by ring
    rw [e, e3, sin_add]
    conv_rhs => rw [show sin ω = sin (2 * (ω / 2)) by rw [← e2], show cos ω = cos (2 * (ω / 2)) by rw [← e2]]
    rw [sin_two_mul, cos_two_mul]
    have hs := sin_sq_add_cos_sq (ω / 2)
    linear_combination (sin (ω / 2) - 2 * a) * hs


lemma band_cos_half_odd (k : ℤ) : cos (((k : ℝ) + 1 / 2) * π) = 0 := by
  rw [cos_eq_zero_iff]
  exact ⟨k, by ring⟩

lemma band_anti_pi (a : ℝ) (j : ℕ) :
    bandAnti a ((j : ℝ) + 1 / 2) π = 0 := by
  unfold bandAnti
  have c0 : cos (((j : ℝ) + 1 / 2) * π) = 0 := by
    have := band_cos_half_odd (j : ℤ); push_cast at this; exact this
  have c1 : cos (((j : ℝ) + 1 / 2 + 1) * π) = 0 := by
    have := band_cos_half_odd ((j : ℤ) + 1); push_cast at this
    rw [show ((j : ℝ) + 1 / 2 + 1) = (j : ℝ) + 1 + 1 / 2 by ring]; exact this
  have c2 : cos (((j : ℝ) + 1 / 2 - 1) * π) = 0 := by
    have := band_cos_half_odd ((j : ℤ) - 1); push_cast at this
    rw [show ((j : ℝ) + 1 / 2 - 1) = (j : ℝ) - 1 + 1 / 2 by ring]; exact this
  have s1 : sin (((j : ℝ) + 1 / 2 - 1 / 2) * π) = 0 := by
    rw [show ((j : ℝ) + 1 / 2 - 1 / 2) * π = (j : ℝ) * π by ring]; exact sin_nat_mul_pi j
  have s2 : sin (((j : ℝ) + 1 / 2 + 1 / 2) * π) = 0 := by
    rw [show ((j : ℝ) + 1 / 2 + 1 / 2) * π = ((j + 1 : ℕ) : ℝ) * π by push_cast; ring]
    exact sin_nat_mul_pi (j + 1)
  rw [c0, c1, c2, s1, s2]
  ring

lemma bandCoef_eq (j : ℕ) (hj : 1 ≤ j) :
    bandCoef j = -(2 / π) * bandAnti bandEdge ((j : ℝ) + 1 / 2) (π / 6) := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  set p : ℝ := (j : ℝ) + 1 / 2 with hp
  have h0 : p ≠ 0 := by rw [hp]; linarith
  have h1 : p + 1 ≠ 0 := by rw [hp]; linarith
  have h2 : p - 1 ≠ 0 := by rw [hp]; linarith
  have h3 : p - 1 / 2 ≠ 0 := by rw [hp]; linarith
  have h4 : p + 1 / 2 ≠ 0 := by rw [hp]; linarith
  have hint : ∫ ω in (π / 6)..π, bandWeight ω * sin (p * ω) =
      bandAnti bandEdge p π - bandAnti bandEdge p (π / 6) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x _
      exact band_hasDerivAt_anti bandEdge p x h0 h1 h2 h3 h4
    · apply Continuous.intervalIntegrable
      unfold bandWeight
      fun_prop
  unfold bandCoef
  rw [hint, hp, band_anti_pi]
  ring

lemma bandCoef_zero :
    bandCoef 0 = 2 / π * (bandAnti0 bandEdge π - bandAnti0 bandEdge (π / 6)) := by
  have hint : ∫ ω in (π / 6)..π, bandWeight ω * sin ((((0 : ℕ) : ℝ) + 1 / 2) * ω) =
      bandAnti0 bandEdge π - bandAnti0 bandEdge (π / 6) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x _
      have := band_hasDerivAt_anti0 bandEdge x
      simpa [bandWeight] using this
    · apply Continuous.intervalIntegrable
      unfold bandWeight
      fun_prop
  unfold bandCoef
  rw [hint]


lemma band_anti_edge (u p : ℝ) (_h1 : p ^ 2 - 1 ≠ 0) (h2 : p ^ 2 - 1 / 4 ≠ 0) (h0 : p ≠ 0)
    (h3 : p + 1 ≠ 0) (h4 : p - 1 ≠ 0) (h5 : p - 1 / 2 ≠ 0) (h6 : p + 1 / 2 ≠ 0) :
    bandAnti (sin u) p (2 * u) =
      cos (p * (2 * u)) * ((1 - 2 * sin u ^ 2) / (2 * p * (p ^ 2 - 1)) +
          sin u ^ 2 / (2 * p * (p ^ 2 - 1 / 4))) +
        sin (p * (2 * u)) * (sin u * cos u * (3 / 4) / ((p ^ 2 - 1) * (p ^ 2 - 1 / 4))) := by
  unfold bandAnti
  have e1 : (p + 1) * (2 * u) = p * (2 * u) + 2 * u := by ring
  have e2 : (p - 1) * (2 * u) = p * (2 * u) - 2 * u := by ring
  have e3 : (p - 1 / 2) * (2 * u) = p * (2 * u) - u := by ring
  have e4 : (p + 1 / 2) * (2 * u) = p * (2 * u) + u := by ring
  have hc2 : cos (2 * u) = 1 - 2 * sin u ^ 2 := by rw [cos_two_mul, cos_sq']; ring
  rw [e1, e2, e3, e4, cos_add, cos_sub, sin_sub, sin_add, sin_two_mul, hc2]
  have k1 : 2 * p - 1 ≠ 0 := by intro h; apply h5; linarith
  have k2 : 2 * p + 1 ≠ 0 := by intro h; apply h6; linarith
  have k3 : 4 * p ^ 2 - 1 ≠ 0 := by intro h; apply h2; linarith
  have k4 : p ^ 2 - 1 = (p - 1) * (p + 1) := by ring
  rw [show p - 1 / 2 = (2 * p - 1) / 2 by ring, show p + 1 / 2 = (2 * p + 1) / 2 by ring,
    show p ^ 2 - 1 / 4 = (4 * p ^ 2 - 1) / 4 by ring, k4]
  have k5 : -1 + p ^ 2 * 4 ≠ 0 := by intro h; apply k3; linarith
  field_simp
  ring_nf
  field_simp
  ring

lemma band_edge_facts : sin (π / 12) * cos (π / 12) = 1 / 4 ∧ 1 - 2 * sin (π / 12) ^ 2 = √3 / 2 := by
  have h2 : (2 : ℝ) * (π / 12) = π / 6 := by ring
  constructor
  · have := sin_two_mul (π / 12)
    rw [h2, sin_pi_div_six] at this
    linarith
  · have := cos_two_mul (π / 12)
    rw [h2, cos_pi_div_six, cos_sq'] at this
    linarith

lemma bandCoef_abs_le (j : ℕ) (hj : 1 ≤ j) :
    |bandCoef j| ≤ 2 / π * ((√3 / 2) / (2 * ((j : ℝ) + 1 / 2) * (((j : ℝ) + 1 / 2) ^ 2 - 1)) +
      ((2 - √3) / 4) / (2 * ((j : ℝ) + 1 / 2) * (((j : ℝ) + 1 / 2) ^ 2 - 1 / 4)) +
      (3 / 16) / ((((j : ℝ) + 1 / 2) ^ 2 - 1) * (((j : ℝ) + 1 / 2) ^ 2 - 1 / 4))) := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  set p : ℝ := (j : ℝ) + 1 / 2 with hp
  have hp1 : 0 < p ^ 2 - 1 := by nlinarith
  have hp2 : 0 < p ^ 2 - 1 / 4 := by nlinarith
  have hp0 : 0 < p := by linarith
  obtain ⟨f1, f2⟩ := band_edge_facts
  have hsq : sin (π / 12) ^ 2 = (2 - √3) / 4 := by linarith
  have hedge := band_anti_edge (π / 12) p hp1.ne' hp2.ne' hp0.ne' (by linarith) (by linarith)
    (by linarith) (by linarith)
  rw [show 2 * (π / 12) = π / 6 by ring] at hedge
  rw [bandCoef_eq j hj, ← hp]
  unfold bandEdge
  rw [hedge, f2, hsq, f1]
  have hA : 0 ≤ (√3 / 2) / (2 * p * (p ^ 2 - 1)) + ((2 - √3) / 4) / (2 * p * (p ^ 2 - 1 / 4)) := by
    have : √3 ≤ 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h3 : 0 ≤ √3 := Real.sqrt_nonneg 3
    positivity
  have hB : 0 ≤ 1 / 4 * (3 / 4) / ((p ^ 2 - 1) * (p ^ 2 - 1 / 4)) := by positivity
  have hpi : 0 < π := pi_pos
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 / π)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc |cos (p * (π / 6)) * ((√3 / 2) / (2 * p * (p ^ 2 - 1)) + (2 - √3) / 4 / (2 * p * (p ^ 2 - 1 / 4))) +
        sin (p * (π / 6)) * (1 / 4 * (3 / 4) / ((p ^ 2 - 1) * (p ^ 2 - 1 / 4)))|
      ≤ |cos (p * (π / 6))| * ((√3 / 2) / (2 * p * (p ^ 2 - 1)) + (2 - √3) / 4 / (2 * p * (p ^ 2 - 1 / 4))) +
        |sin (p * (π / 6))| * (1 / 4 * (3 / 4) / ((p ^ 2 - 1) * (p ^ 2 - 1 / 4))) := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hA, abs_of_nonneg hB]
    _ ≤ 1 * ((√3 / 2) / (2 * p * (p ^ 2 - 1)) + (2 - √3) / 4 / (2 * p * (p ^ 2 - 1 / 4))) +
        1 * (1 / 4 * (3 / 4) / ((p ^ 2 - 1) * (p ^ 2 - 1 / 4))) := by
        gcongr
        · exact abs_cos_le_one _
        · exact abs_sin_le_one _
    _ = _ := by ring


lemma band_sqrt3_bounds : 1.7320508 < √3 ∧ √3 < 1.7320509 := by
  constructor
  · rw [show (1.7320508 : ℝ) = √(1.7320508 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [show (1.7320509 : ℝ) = √(1.7320509 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma band_sqrt2_bounds : 1.4142135 < √2 ∧ √2 < 1.4142136 := by
  constructor
  · rw [show (1.4142135 : ℝ) = √(1.4142135 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  · rw [show (1.4142136 : ℝ) = √(1.4142136 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma bandEdge_pos : 0 < bandEdge := by
  unfold bandEdge
  apply sin_pos_of_pos_of_lt_pi
  · positivity
  · linarith [pi_pos]

lemma bandEdge_bounds : 0.2588190 < bandEdge ∧ bandEdge < 0.2588191 := by
  obtain ⟨_, f2⟩ := band_edge_facts
  obtain ⟨s1, s2⟩ := band_sqrt3_bounds
  have hpos := bandEdge_pos
  have hsq : bandEdge ^ 2 = (2 - √3) / 4 := by unfold bandEdge; linarith
  constructor <;> nlinarith

lemma bandEdge_gt_quarter : 1 / 4 < bandEdge := by
  have := bandEdge_bounds.1; linarith

lemma bandCos_bounds : 0.965925 < cos (π / 12) ∧ cos (π / 12) < 0.965927 := by
  obtain ⟨f1, _⟩ := band_edge_facts
  obtain ⟨b1, b2⟩ := bandEdge_bounds
  have hc : cos (π / 12) = 1 / (4 * bandEdge) := by
    unfold bandEdge at *
    field_simp
    linarith
  rw [hc]
  constructor
  · rw [lt_div_iff₀ (by linarith)]; nlinarith
  · rw [div_lt_iff₀ (by linarith)]; nlinarith

lemma bandCoef_zero_ge : 0.415 ≤ bandCoef 0 := by
  rw [bandCoef_zero]
  unfold bandAnti0
  have e1 : cos (π / 2) = 0 := cos_pi_div_two
  have e2 : cos (3 / 2 * π) = 0 := by
    have := band_cos_half_odd 1; push_cast at this
    rw [show (3 / 2 : ℝ) * π = (1 + 1 / 2) * π by ring]; exact this
  have e3 : cos (π / 6 / 2) = cos (π / 12) := by ring_nf
  have e4 : cos (3 / 2 * (π / 6)) = √2 / 2 := by
    rw [show (3 / 2 : ℝ) * (π / 6) = π / 4 by ring]; exact cos_pi_div_four
  rw [e1, e2, e3, e4, sin_pi, sin_pi_div_six]
  obtain ⟨_, f2⟩ := band_edge_facts
  have hsq : bandEdge ^ 2 = (2 - √3) / 4 := by unfold bandEdge; linarith
  obtain ⟨a1, a2⟩ := bandEdge_bounds
  obtain ⟨c1, c2⟩ := bandCos_bounds
  obtain ⟨s1, s2⟩ := band_sqrt3_bounds
  obtain ⟨r1, r2⟩ := band_sqrt2_bounds
  have p1 := pi_gt_d6
  have p2 := pi_lt_d6
  have hpi : 0 < π := pi_pos
  rw [hsq]
  rw [show 2 / π * (-(3 / 2 + 2 * ((2 - √3) / 4)) * 0 + 0 / 6 - bandEdge * (π - 0) -
      (-(3 / 2 + 2 * ((2 - √3) / 4)) * cos (π / 12) + √2 / 2 / 6 - bandEdge * (π / 6 - 1 / 2))) =
      2 / π * ((5 / 2 - √3 / 2) * cos (π / 12) - √2 / 12 - bandEdge / 2) - 5 / 3 * bandEdge by
    field_simp; ring_nf]
  have hX : 1.3310 ≤ (5 / 2 - √3 / 2) * cos (π / 12) - √2 / 12 - bandEdge / 2 := by nlinarith
  have h1 : 2 * 1.3310 / 3.141593 ≤ 2 * 1.3310 / π :=
    div_le_div_of_nonneg_left (by norm_num) hpi p2.le
  have h2 : 2 * 1.3310 / π ≤ 2 / π * ((5 / 2 - √3 / 2) * cos (π / 12) - √2 / 12 - bandEdge / 2) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith) hpi.le
  have hq := h1.trans h2
  norm_num at hq ⊢
  linarith


lemma band_term_bounds (x : ℝ) (hx : 1 ≤ x) :
    (√3 / 2) / (2 * (x + 1 / 2) * ((x + 1 / 2) ^ 2 - 1)) +
        ((2 - √3) / 4) / (2 * (x + 1 / 2) * ((x + 1 / 2) ^ 2 - 1 / 4)) +
        (3 / 16) / (((x + 1 / 2) ^ 2 - 1) * ((x + 1 / 2) ^ 2 - 1 / 4)) ≤
      (√3 / 8 / ((x - 1 / 2) * (x + 1 / 2)) + ((2 - √3) / 12 + 3 / 20) / x) -
        (√3 / 8 / ((x + 1 / 2) * (x + 3 / 2)) + ((2 - √3) / 12 + 3 / 20) / (x + 1)) ∧
    (x + 1) * ((√3 / 2) / (2 * (x + 1 / 2) * ((x + 1 / 2) ^ 2 - 1)) +
        ((2 - √3) / 4) / (2 * (x + 1 / 2) * ((x + 1 / 2) ^ 2 - 1 / 4)) +
        (3 / 16) / (((x + 1 / 2) ^ 2 - 1) * ((x + 1 / 2) ^ 2 - 1 / 4))) ≤
      (√3 / 4 + (2 - √3) / 8 + 3 / 16) / (x - 1 / 2) -
        (√3 / 4 + (2 - √3) / 8 + 3 / 16) / (x + 1 / 2) := by
  obtain ⟨s1, s2⟩ := band_sqrt3_bounds
  have c2 : 0 ≤ 2 - √3 := by linarith
  have c3 : 0 ≤ √3 := by linarith
  have e1 : (x + 1 / 2) ^ 2 - 1 = (x - 1 / 2) * (x + 3 / 2) := by ring
  have e2 : (x + 1 / 2) ^ 2 - 1 / 4 = x * (x + 1) := by ring
  have hx0 : 0 < x := by linarith
  have ha : 0 < x - 1 / 2 := by linarith
  have n1 : -1 + x * 2 ≠ 0 := by intro h; linarith
  have n2 : 1 + x * 2 ≠ 0 := by intro h; linarith
  have n3 : 3 + x * 2 ≠ 0 := by intro h; linarith
  have n4 : x - 1 / 2 ≠ 0 := by intro h; linarith
  have n5 : x + 1 / 2 ≠ 0 := by intro h; linarith
  have n6 : x + 3 / 2 ≠ 0 := by intro h; linarith
  have n7 : x + 1 ≠ 0 := by intro h; linarith
  have n8 : x ≠ 0 := by intro h; linarith
  rw [e1, e2]
  have t1 : (√3 / 2) / (2 * (x + 1 / 2) * ((x - 1 / 2) * (x + 3 / 2))) =
      √3 / 8 / ((x - 1 / 2) * (x + 1 / 2)) - √3 / 8 / ((x + 1 / 2) * (x + 3 / 2)) := by
    field_simp; ring_nf; field_simp; ring_nf
  have t2 : ((2 - √3) / 4) / (2 * (x + 1 / 2) * (x * (x + 1))) ≤
      (2 - √3) / 12 / x - (2 - √3) / 12 / (x + 1) := by
    rw [show (2 - √3) / 12 / x - (2 - √3) / 12 / (x + 1) = (2 - √3) / (12 * (x * (x + 1))) by
      field_simp; ring_nf]
    rw [show ((2 - √3) / 4) / (2 * (x + 1 / 2) * (x * (x + 1))) = (2 - √3) / (8 * (x + 1 / 2) * (x * (x + 1))) by
      field_simp; ring_nf]
    apply div_le_div_of_nonneg_left c2 (by positivity)
    nlinarith [mul_pos hx0 (by linarith : (0:ℝ) < x + 1)]
  have t3 : (3 / 16) / (((x - 1 / 2) * (x + 3 / 2)) * (x * (x + 1))) ≤ 3 / 20 / x - 3 / 20 / (x + 1) := by
    rw [show 3 / 20 / x - 3 / 20 / (x + 1) = 3 / (20 * (x * (x + 1))) by field_simp; ring_nf]
    rw [show (3 / 16) / (((x - 1 / 2) * (x + 3 / 2)) * (x * (x + 1))) =
      3 / (16 * ((x - 1 / 2) * (x + 3 / 2)) * (x * (x + 1))) by field_simp]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have : (5 : ℝ) / 4 ≤ (x - 1 / 2) * (x + 3 / 2) := by nlinarith
    have hp : 0 < x * (x + 1) := by positivity
    nlinarith
  constructor
  · rw [t1]
    have : ((2 - √3) / 12 + 3 / 20) / x - ((2 - √3) / 12 + 3 / 20) / (x + 1) =
        ((2 - √3) / 12 / x - (2 - √3) / 12 / (x + 1)) + (3 / 20 / x - 3 / 20 / (x + 1)) := by ring
    linarith
  · set W := √3 / 4 + (2 - √3) / 8 + 3 / 16
    have hW : W / (x - 1 / 2) - W / (x + 1 / 2) =
        √3 / 4 / ((x - 1 / 2) * (x + 1 / 2)) + (2 - √3) / 8 / ((x - 1 / 2) * (x + 1 / 2)) +
          3 / 16 / ((x - 1 / 2) * (x + 1 / 2)) := by
      simp only [W]; field_simp; ring_nf; field_simp; ring_nf
    rw [hW, mul_add, mul_add]
    have hd : 0 < (x - 1 / 2) * (x + 1 / 2) := by positivity
    have u1 : (x + 1) * ((√3 / 2) / (2 * (x + 1 / 2) * ((x - 1 / 2) * (x + 3 / 2)))) ≤
        √3 / 4 / ((x - 1 / 2) * (x + 1 / 2)) := by
      rw [show (x + 1) * ((√3 / 2) / (2 * (x + 1 / 2) * ((x - 1 / 2) * (x + 3 / 2)))) =
        √3 / 4 * ((x + 1) / ((x + 3 / 2) * ((x - 1 / 2) * (x + 1 / 2)))) by field_simp; ring_nf]
      rw [div_eq_mul_one_div (√3 / 4)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_div_iff₀ (by positivity) hd]
      nlinarith
    have u2 : (x + 1) * (((2 - √3) / 4) / (2 * (x + 1 / 2) * (x * (x + 1)))) ≤
        (2 - √3) / 8 / ((x - 1 / 2) * (x + 1 / 2)) := by
      rw [show (x + 1) * (((2 - √3) / 4) / (2 * (x + 1 / 2) * (x * (x + 1)))) =
        (2 - √3) / 8 / (x * (x + 1 / 2)) by field_simp; ring_nf]
      apply div_le_div_of_nonneg_left (by linarith) hd
      nlinarith
    have u3 : (x + 1) * ((3 / 16) / (((x - 1 / 2) * (x + 3 / 2)) * (x * (x + 1)))) ≤
        3 / 16 / ((x - 1 / 2) * (x + 1 / 2)) := by
      rw [show (x + 1) * ((3 / 16) / (((x - 1 / 2) * (x + 3 / 2)) * (x * (x + 1)))) =
        3 / 16 / ((x - 1 / 2) * ((x + 3 / 2) * x)) by field_simp]
      apply div_le_div_of_nonneg_left (by norm_num) hd
      apply mul_le_mul_of_nonneg_left _ ha.le
      nlinarith
    linarith

lemma bandCoef_sum_le (J : ℕ) :
    ∑ i ∈ Finset.range J, |bandCoef (i + 1)| ≤ 0.294 ∧
      ∑ i ∈ Finset.range J, ((i : ℝ) + 2) * |bandCoef (i + 1)| ≤ 0.834 := by
  set P : ℕ → ℝ := fun i => √3 / 8 / (((i : ℝ) + 1 - 1 / 2) * ((i : ℝ) + 1 + 1 / 2)) +
    ((2 - √3) / 12 + 3 / 20) / ((i : ℝ) + 1) with hP
  set Q : ℕ → ℝ := fun i => (√3 / 4 + (2 - √3) / 8 + 3 / 16) / ((i : ℝ) + 1 - 1 / 2) with hQ
  have hpi : 0 < π := pi_pos
  have key : ∀ i : ℕ, |bandCoef (i + 1)| ≤ 2 / π * (P i - P (i + 1)) ∧
      ((i : ℝ) + 2) * |bandCoef (i + 1)| ≤ 2 / π * (Q i - Q (i + 1)) := by
    intro i
    have hx : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i)
    have hb := bandCoef_abs_le (i + 1) (Nat.succ_le_succ (Nat.zero_le i))
    obtain ⟨k1, k2⟩ := band_term_bounds ((i + 1 : ℕ) : ℝ) hx
    have h2pi : 0 ≤ 2 / π := by positivity
    push_cast at hb k1 k2 hx
    constructor
    · refine hb.trans (mul_le_mul_of_nonneg_left ?_ h2pi)
      have eqP : P i - P (i + 1) = √3 / 8 / (((i : ℝ) + 1 - 1 / 2) * ((i : ℝ) + 1 + 1 / 2)) +
          ((2 - √3) / 12 + 3 / 20) / ((i : ℝ) + 1) -
          (√3 / 8 / (((i : ℝ) + 1 + 1 / 2) * ((i : ℝ) + 1 + 3 / 2)) +
            ((2 - √3) / 12 + 3 / 20) / ((i : ℝ) + 1 + 1)) := by
        simp only [hP]; push_cast
        rw [show (i : ℝ) + 1 + 1 - 1 / 2 = (i : ℝ) + 1 + 1 / 2 by ring,
          show (i : ℝ) + 1 + 1 + 1 / 2 = (i : ℝ) + 1 + 3 / 2 by ring]
      rw [eqP]; exact k1
    · have h0 : (0 : ℝ) ≤ (i : ℝ) + 2 := by positivity
      have eqQ : Q i - Q (i + 1) = (√3 / 4 + (2 - √3) / 8 + 3 / 16) / ((i : ℝ) + 1 - 1 / 2) -
          (√3 / 4 + (2 - √3) / 8 + 3 / 16) / ((i : ℝ) + 1 + 1 / 2) := by
        simp only [hQ]; push_cast
        rw [show (i : ℝ) + 1 + 1 - 1 / 2 = (i : ℝ) + 1 + 1 / 2 by ring]
      calc ((i : ℝ) + 2) * |bandCoef (i + 1)| ≤ ((i : ℝ) + 2) * (2 / π * (√3 / 2 / (2 * ((i:ℝ) + 1 + 1 / 2) * (((i:ℝ) + 1 + 1 / 2) ^ 2 - 1)) + (2 - √3) / 4 / (2 * ((i:ℝ) + 1 + 1 / 2) * (((i:ℝ) + 1 + 1 / 2) ^ 2 - 1 / 4)) + 3 / 16 / ((((i:ℝ) + 1 + 1 / 2) ^ 2 - 1) * (((i:ℝ) + 1 + 1 / 2) ^ 2 - 1 / 4)))) :=
            mul_le_mul_of_nonneg_left hb h0
        _ = 2 / π * (((i : ℝ) + 1 + 1) * (√3 / 2 / (2 * ((i:ℝ) + 1 + 1 / 2) * (((i:ℝ) + 1 + 1 / 2) ^ 2 - 1)) + (2 - √3) / 4 / (2 * ((i:ℝ) + 1 + 1 / 2) * (((i:ℝ) + 1 + 1 / 2) ^ 2 - 1 / 4)) + 3 / 16 / ((((i:ℝ) + 1 + 1 / 2) ^ 2 - 1) * (((i:ℝ) + 1 + 1 / 2) ^ 2 - 1 / 4)))) := by ring
        _ ≤ 2 / π * (Q i - Q (i + 1)) := by
            apply mul_le_mul_of_nonneg_left _ h2pi
            rw [eqQ]; exact k2
  obtain ⟨s1, s2⟩ := band_sqrt3_bounds
  have p1 := pi_gt_d6
  constructor
  · calc ∑ i ∈ Finset.range J, |bandCoef (i + 1)| ≤ ∑ i ∈ Finset.range J, 2 / π * (P i - P (i + 1)) :=
          Finset.sum_le_sum fun i _ => (key i).1
      _ = 2 / π * (P 0 - P J) := by rw [← Finset.mul_sum, Finset.sum_range_sub']
      _ ≤ 2 / π * P 0 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : 0 ≤ P J := by
            simp only [hP]
            have : 0 < ((J : ℝ) + 1 - 1 / 2) := by have := (Nat.cast_nonneg J : (0:ℝ) ≤ J); linarith
            have : (0 : ℝ) ≤ (2 - √3) / 12 + 3 / 20 := by linarith
            positivity
          linarith
      _ ≤ 0.294 := by
          simp only [hP]; norm_num
          rw [div_mul_eq_mul_div, div_le_iff₀ hpi]
          nlinarith
  · calc ∑ i ∈ Finset.range J, ((i : ℝ) + 2) * |bandCoef (i + 1)| ≤
          ∑ i ∈ Finset.range J, 2 / π * (Q i - Q (i + 1)) := Finset.sum_le_sum fun i _ => (key i).2
      _ = 2 / π * (Q 0 - Q J) := by rw [← Finset.mul_sum, Finset.sum_range_sub']
      _ ≤ 2 / π * Q 0 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : 0 ≤ Q J := by
            simp only [hQ]
            have : 0 < ((J : ℝ) + 1 - 1 / 2) := by have := (Nat.cast_nonneg J : (0:ℝ) ≤ J); linarith
            have : (0 : ℝ) ≤ √3 / 4 + (2 - √3) / 8 + 3 / 16 := by linarith
            positivity
          linarith
      _ ≤ 0.834 := by
          simp only [hQ]; norm_num
          rw [div_mul_eq_mul_div, div_le_iff₀ hpi]
          nlinarith

end OracleTemplate.ArrowHurwicz
