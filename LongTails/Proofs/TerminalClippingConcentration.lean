import LongTails.Proofs.TerminalClippingEnergy
import LongTails.Proofs.RobustEnergyConcentration

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.TerminalClipping

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]
  {P : Measure Ω} [IsProbabilityMeasure P]

omit [SecondCountableTopology E] in
lemma centered_inner_mgf {X : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    {C v τ : ℝ} (hτ : 0 ≤ τ) (z : E)
    (hbound : ∀ ω, ‖X ω‖ ≤ C) (hmoment : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ v)
    (hsmall : 2 * τ * C * ‖z‖ ≤ 1) :
    Integrable (fun ω => Real.exp (-τ * ⟪X ω - ∫ u, X u ∂P, z⟫)) P ∧
    (∫ ω, Real.exp (-τ * ⟪X ω - ∫ u, X u ∂P, z⟫) ∂P) ≤
      Real.exp (τ ^ 2 * ‖z‖ ^ 2 * v) := by
  let m := ∫ u, X u ∂P
  let Y := fun ω => X ω - m
  have hm : ‖m‖ ≤ C := by
    have hh := norm_integral_le_of_norm_le (integrable_const C : Integrable (fun _ : Ω => C) P)
      (Filter.Eventually.of_forall hbound)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, m] using hh
  have hY : Measurable Y := hX.sub_const m
  have hYi : Integrable Y P := hXi.sub (integrable_const m)
  have hY2 := centered_second_moment hXi hX2
  have hYbound (ω : Ω) : ‖Y ω‖ ≤ 2 * C :=
    (norm_sub_le _ _).trans (by linarith [hbound ω])
  have hzero : (∫ ω, Y ω ∂P) = 0 := by
    dsimp [Y]
    rw [integral_sub hXi (integrable_const m)]
    simp [m]
  let Z := fun ω => -τ * ⟪Y ω, z⟫
  have hZ : Measurable Z := by dsimp [Z]; fun_prop
  have hZi : Integrable Z P := (hYi.inner_const z).const_mul (-τ)
  have hZbound (ω : Ω) : |Z ω| ≤ 1 := by
    dsimp [Z]
    rw [abs_mul, abs_neg, abs_of_nonneg hτ]
    have hi := (abs_real_inner_le_norm (Y ω) z).trans
      (mul_le_mul_of_nonneg_right (hYbound ω) (norm_nonneg z))
    have hh := mul_le_mul_of_nonneg_left hi hτ
    nlinarith
  have hmean : (∫ ω, Z ω ∂P) ≤ 0 := by
    dsimp [Z]
    rw [integral_const_mul]
    simp_rw [real_inner_comm z]
    rw [integral_inner hYi z, hzero]
    simp
  have hp (ω : Ω) : (Z ω) ^ 2 ≤ (τ ^ 2 * ‖z‖ ^ 2) * ‖Y ω‖ ^ 2 := by
    have hi := sq_le_sq₀ (abs_nonneg ⟪Y ω, z⟫) (by positivity : 0 ≤ ‖Y ω‖ * ‖z‖)
    have hh := hi.mpr (abs_real_inner_le_norm (Y ω) z)
    rw [sq_abs, mul_pow] at hh
    have ht := mul_le_mul_of_nonneg_left hh (sq_nonneg τ)
    dsimp [Z]
    nlinarith
  have hZ2 : Integrable (fun ω => (Z ω) ^ 2) P := by
    apply (hY2.1.const_mul (τ ^ 2 * ‖z‖ ^ 2)).mono' (hZ.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hp ω)
  have hsecond : (∫ ω, (Z ω) ^ 2 ∂P) ≤ τ ^ 2 * ‖z‖ ^ 2 * v := by
    have hh := integral_mono hZ2 (hY2.1.const_mul (τ ^ 2 * ‖z‖ ^ 2)) hp
    rw [integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hY2.2.trans hmoment) (by positivity))
  simpa only [zero_add, Z, Y, m] using
    RobustGradient.bounded_increment_mgf hZ hZbound hmean hsecond

omit [SecondCountableTopology E] [IsProbabilityMeasure P] in
lemma raw_energy_moments {X : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    {η C b v : ℝ} (hη : 0 ≤ η) (z : E)
    (hbound : ∀ ω, ‖X ω‖ ≤ C)
    (hmean : -⟪z, ∫ ω, X ω ∂P⟫ ≤ b)
    (hmoment : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ v) :
    let W := fun ω => -2 * η * ⟪z, X ω⟫ + η ^ 2 * ‖X ω‖ ^ 2
    Integrable W P ∧ Integrable (fun ω => (W ω) ^ 2) P ∧
      (∀ ω, |W ω| ≤ 2 * η * C * ‖z‖ + η ^ 2 * C ^ 2) ∧
      (∫ ω, W ω ∂P) ≤ 2 * η * b + η ^ 2 * v ∧
      (∫ ω, (W ω) ^ 2 ∂P) ≤
        (8 * η ^ 2 * ‖z‖ ^ 2 + 2 * η ^ 4 * C ^ 2) * v := by
  dsimp only
  let W := fun ω => -2 * η * ⟪z, X ω⟫ + η ^ 2 * ‖X ω‖ ^ 2
  let K := 8 * η ^ 2 * ‖z‖ ^ 2 + 2 * η ^ 4 * C ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hW : Measurable W := by dsimp [W]; fun_prop
  have hWi : Integrable W P := ((hXi.const_inner z).const_mul (-2 * η)).add
    (hX2.const_mul (η ^ 2))
  have hp (ω : Ω) : (W ω) ^ 2 ≤ K * ‖X ω‖ ^ 2 := by
    have hh := RobustGradient.energy_increment_sq (a := 2 * η) (b := 2 * η)
      (c := 1 / 4) (by positivity) le_rfl
      (X ω) z (hbound ω)
    convert hh using 1 <;> dsimp [W, K] <;> ring
  have hW2 : Integrable (fun ω => (W ω) ^ 2) P := by
    apply (hX2.const_mul K).mono' (hW.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hp ω)
  refine ⟨hWi, hW2, ?_, ?_, ?_⟩
  · intro ω
    have hh := RobustGradient.energy_increment_abs (a := 2 * η) (b := 2 * η)
      (c := 1 / 4) (by positivity) (by positivity) le_rfl (by norm_num)
      (X ω) z (hbound ω)
    convert hh using 1 <;> ring
  · rw [integral_add ((hXi.const_inner z).const_mul (-2 * η)) (hX2.const_mul (η ^ 2)),
      integral_const_mul, integral_const_mul, integral_inner hXi z]
    have hm := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 2 * η by positivity)
    have hv := mul_le_mul_of_nonneg_left hmoment (sq_nonneg η)
    nlinarith
  · have hh := integral_mono hW2 (hX2.const_mul K) hp
    rw [integral_const_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hmoment hK)

omit [SecondCountableTopology E] in
lemma projected_energy_mgf {X : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    {projection : E → E} (hp : Measurable projection) (x u : E)
    (hproj : ∀ y, ‖projection y - u‖ ^ 2 ≤ ‖y - u‖ ^ 2)
    {η C b v τ : ℝ} (hη : 0 ≤ η) (hτ : 0 ≤ τ)
    (hbound : ∀ ω, ‖X ω‖ ≤ C)
    (hmean : -⟪x - u, ∫ ω, X ω ∂P⟫ ≤ b)
    (hmoment : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ v)
    (hsmall : τ * (2 * η * C * ‖x - u‖ + η ^ 2 * C ^ 2) ≤ 1) :
    Integrable (fun ω => Real.exp (τ * ‖projection (x - η • X ω) - u‖ ^ 2)) P ∧
    (∫ ω, Real.exp (τ * ‖projection (x - η • X ω) - u‖ ^ 2) ∂P) ≤
      Real.exp (τ * ‖x - u‖ ^ 2 + τ * (2 * η * b + η ^ 2 * v) +
        τ ^ 2 * (8 * η ^ 2 * ‖x - u‖ ^ 2 + 2 * η ^ 4 * C ^ 2) * v) := by
  let W := fun ω => -2 * η * ⟪x - u, X ω⟫ + η ^ 2 * ‖X ω‖ ^ 2
  have hw := raw_energy_moments hX hXi hX2 hη (x - u) hbound hmean hmoment
  have hW : Measurable W := by dsimp [W]; fun_prop
  have hscaled (ω : Ω) : |τ * W ω| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hτ]
    exact (mul_le_mul_of_nonneg_left (hw.2.2.1 ω) hτ).trans hsmall
  have hm : (∫ ω, τ * W ω ∂P) ≤ τ * (2 * η * b + η ^ 2 * v) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hw.2.2.2.1 hτ
  have hs : (∫ ω, (τ * W ω) ^ 2 ∂P) ≤
      τ ^ 2 * ((8 * η ^ 2 * ‖x - u‖ ^ 2 + 2 * η ^ 4 * C ^ 2) * v) := by
    simp_rw [mul_pow]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hw.2.2.2.2 (sq_nonneg τ)
  have he := RobustGradient.bounded_increment_mgf (hW.const_mul τ) hscaled hm hs
  have hpoint (ω : Ω) : Real.exp (τ * ‖projection (x - η • X ω) - u‖ ^ 2) ≤
      Real.exp (τ * ‖x - u‖ ^ 2) * Real.exp (τ * W ω) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hd := hproj (x - η • X ω)
    have hv : x - η • X ω - u = (x - u) - η • X ω := by module
    rw [hv, norm_sub_sq_real (x - u) (η • X ω), real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hη, mul_pow] at hd
    have hh := mul_le_mul_of_nonneg_left hd hτ
    dsimp [W]
    nlinarith
  have hi : Integrable (fun ω => Real.exp (τ * ‖projection (x - η • X ω) - u‖ ^ 2)) P := by
    apply (he.1.const_mul (Real.exp (τ * ‖x - u‖ ^ 2))).mono'
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · exact Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, Real.abs_exp]
        exact hpoint ω)
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi (he.1.const_mul (Real.exp (τ * ‖x - u‖ ^ 2))) hpoint
  rw [integral_const_mul] at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left he.2 (Real.exp_nonneg _))
  rw [← Real.exp_add] at hh'
  convert hh' using 1; congr 1; ring

lemma nonnegative_bounded_mgf {Z : Ω → ℝ} (hZ : Measurable Z)
    (hi : Integrable Z P) {H v : ℝ} (hH : 0 < H)
    (hzero : ∀ ω, 0 ≤ Z ω) (hbound : ∀ ω, Z ω ≤ H)
    (hmean : (∫ ω, Z ω ∂P) ≤ v) :
    Integrable (fun ω => Real.exp (Z ω / H)) P ∧
    (∫ ω, Real.exp (Z ω / H) ∂P) ≤ Real.exp (2 * v / H) := by
  have hb (ω : Ω) : |Z ω / H| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (hzero ω) hH.le)]
    exact (div_le_one hH).mpr (hbound ω)
  have hp (ω : Ω) : (Z ω / H) ^ 2 ≤ Z ω / H := by
    have hl : 0 ≤ Z ω / H := div_nonneg (hzero ω) hH.le
    have hu : Z ω / H ≤ 1 := (div_le_one hH).mpr (hbound ω)
    nlinarith
  have hi2 : Integrable (fun ω => (Z ω / H) ^ 2) P := by
    apply (hi.div_const H).mono' ((hZ.div_const H).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hp ω)
  have hm : (∫ ω, Z ω / H ∂P) ≤ v / H := by
    rw [integral_div]
    exact div_le_div_of_nonneg_right hmean hH.le
  have hs : (∫ ω, (Z ω / H) ^ 2 ∂P) ≤ v / H :=
    (integral_mono hi2 (hi.div_const H) hp).trans hm
  have hh := RobustGradient.bounded_increment_mgf (hZ.div_const H) hb hm hs
  convert hh using 1; ring

omit [IsProbabilityMeasure P] in
lemma compensated_mgf {Z : Ω → ℝ} {C : ℝ}
    (hi : Integrable (fun ω => Real.exp (Z ω)) P)
    (hb : (∫ ω, Real.exp (Z ω) ∂P) ≤ Real.exp C) :
    Integrable (fun ω => Real.exp (Z ω - C)) P ∧
    (∫ ω, Real.exp (Z ω - C) ∂P) ≤ 1 := by
  simp_rw [Real.exp_sub]
  refine ⟨hi.div_const _, ?_⟩
  rw [integral_div]
  exact (div_le_one (Real.exp_pos C)).mpr hb

end OracleTemplate.TerminalClipping
