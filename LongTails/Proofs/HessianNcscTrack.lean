import LongTails.Proofs.HessianNcscPhi
import LongTails.Proofs.HessianNcscProcess

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.HessianNcsc

variable {E F Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]

structure OracleHyp (gx : E × F → E) (gy : E × F → F) (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (p : Measure Ω) (σ : ℝ) : Prop where
  mx : Measurable (Function.uncurry ox)
  my : Measurable (Function.uncurry oy)
  ix : ∀ z, Integrable (ox z) p
  iy : ∀ z, Integrable (oy z) p
  ex : ∀ z, ∫ ω, ox z ω ∂p = gx z
  ey : ∀ z, ∫ ω, oy z ω ∂p = gy z
  iv : ∀ z, Integrable (fun ω => ‖ox z ω - gx z‖ ^ 2 + ‖oy z ω - gy z‖ ^ 2) p
  v : ∀ z, ∫ ω, ‖ox z ω - gx z‖ ^ 2 + ‖oy z ω - gy z‖ ^ 2 ∂p ≤ σ ^ 2

namespace OracleHyp

variable {gx : E × F → E} {gy : E × F → F} {ox : E × F → Ω → E} {oy : E × F → Ω → F}
  {p : Measure Ω} [IsProbabilityMeasure p] {σ : ℝ} (O : OracleHyp gx gy ox oy p σ)
include O

omit [CompleteSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace F] [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] [IsProbabilityMeasure p] in
lemma meas_x (z : E × F) : Measurable (ox z) := O.mx.comp (measurable_const.prodMk measurable_id)

omit [CompleteSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace F] [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] [IsProbabilityMeasure p] in
lemma meas_y (z : E × F) : Measurable (oy z) := O.my.comp (measurable_const.prodMk measurable_id)

omit [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] [IsProbabilityMeasure p] in
lemma ivx (z : E × F) : Integrable (fun ω => ‖ox z ω - gx z‖ ^ 2) p := by
  refine (O.iv z).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (((O.meas_x z).sub measurable_const).norm.pow_const 2).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    have := sq_nonneg ‖oy z ω - gy z‖; linarith

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace F] [FiniteDimensional ℝ F] [IsProbabilityMeasure p] in
lemma ivy (z : E × F) : Integrable (fun ω => ‖oy z ω - gy z‖ ^ 2) p := by
  refine (O.iv z).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (((O.meas_y z).sub measurable_const).norm.pow_const 2).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    have := sq_nonneg ‖ox z ω - gx z‖; linarith

omit [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ F] [IsProbabilityMeasure p] in
lemma vx (z : E × F) : ∫ ω, ‖ox z ω - gx z‖ ^ 2 ∂p ≤ σ ^ 2 := by
  have h := O.v z
  rw [integral_add (O.ivx z) (O.ivy z)] at h
  have : 0 ≤ ∫ ω, ‖oy z ω - gy z‖ ^ 2 ∂p := integral_nonneg (fun ω => sq_nonneg _)
  linarith

omit [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ F] [IsProbabilityMeasure p] in
lemma vy (z : E × F) : ∫ ω, ‖oy z ω - gy z‖ ^ 2 ∂p ≤ σ ^ 2 := by
  have h := O.v z
  rw [integral_add (O.ivx z) (O.ivy z)] at h
  have : 0 ≤ ∫ ω, ‖ox z ω - gx z‖ ^ 2 ∂p := integral_nonneg (fun ω => sq_nonneg _)
  linarith

omit [CompleteSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace F] [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] in
lemma nx_int (z : E × F) : Integrable (fun ω => ox z ω - gx z) p := (O.ix z).sub (integrable_const _)

omit [CompleteSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace F] [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] in
lemma ny_int (z : E × F) : Integrable (fun ω => oy z ω - gy z) p := (O.iy z).sub (integrable_const _)

omit [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace F] [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] in
lemma nx_mean (z : E × F) : ∫ ω, (ox z ω - gx z) ∂p = 0 := by
  rw [integral_sub (O.ix z) (integrable_const _), O.ex z, integral_const]; simp

omit [CompleteSpace E] [BorelSpace E]
    [SecondCountableTopology E] [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] in
lemma ny_mean (z : E × F) : ∫ ω, (oy z ω - gy z) ∂p = 0 := by
  rw [integral_sub (O.iy z) (integrable_const _), O.ey z, integral_const]; simp

end OracleHyp

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω' : Type*} [MeasurableSpace Ω']

lemma mean_minimizes (q : Measure Ω') [IsProbabilityMeasure q] (X : Ω' → V) (hX : Integrable X q)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) q) (c : V) :
    ∫ ω, ‖X ω - ∫ ω', X ω' ∂q‖ ^ 2 ∂q ≤ ∫ ω, ‖X ω - c‖ ^ 2 ∂q := by
  set m := ∫ ω', X ω' ∂q
  have hN : Integrable (fun ω => X ω - m) q := hX.sub (integrable_const _)
  have hN0 : ∫ ω, (X ω - m) ∂q = 0 := by rw [integral_sub hX (integrable_const _)]; simp [m]
  have hN2 : Integrable (fun ω => ‖X ω - m‖ ^ 2) q := by
    refine (((hX2.const_mul 2).add (integrable_const (2 * ‖m‖ ^ 2)))).mono' ?_ ?_
    · exact (hN.aestronglyMeasurable.norm.pow 2)
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      have := norm_sub_le (X ω) m
      have h2 : ‖X ω - m‖ ^ 2 ≤ (‖X ω‖ + ‖m‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      show ‖X ω - m‖ ^ 2 ≤ 2 * ‖X ω‖ ^ 2 + 2 * ‖m‖ ^ 2
      nlinarith [sq_nonneg (‖X ω‖ - ‖m‖)]
  have h := sq_add_mean_zero q (m - c) (fun ω => X ω - m) hN hN0 hN2
  have e : ∀ ω, m - c + (X ω - m) = X ω - c := fun ω => by abel
  simp_rw [e] at h
  rw [h]
  have := sq_nonneg ‖m - c‖
  linarith

omit [InnerProductSpace ℝ V] [CompleteSpace V] in
lemma young_sq (a b : V) {δ : ℝ} (hδ : 0 < δ) : ‖a + b‖ ^ 2 ≤ (1 + δ) * ‖a‖ ^ 2 + (1 + 1 / δ) * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have h3 : 2 * ‖a‖ * ‖b‖ ≤ δ * ‖a‖ ^ 2 + (1 / δ) * ‖b‖ ^ 2 := by
    have : 0 ≤ (δ * ‖a‖ - ‖b‖) ^ 2 := sq_nonneg _
    have e : δ * ‖a‖ ^ 2 + (1 / δ) * ‖b‖ ^ 2 - 2 * ‖a‖ * ‖b‖ = (δ * ‖a‖ - ‖b‖) ^ 2 / δ := by
      field_simp; ring
    have : 0 ≤ (δ * ‖a‖ - ‖b‖) ^ 2 / δ := by positivity
    linarith
  nlinarith

end General

section NoiseX

variable {Ω' : Type*} [MeasurableSpace Ω'] (q : Measure Ω') [IsProbabilityMeasure q]

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure q] in
omit [MeasurableSpace E] in
lemma dphi_integral_zero {η lam : ℝ} (u0 : E) (c : ℝ) (n : Ω' → E) (hn : Integrable n q)
    (hn0 : ∫ ω, n ω ∂q = 0) : ∫ ω, dphi η lam u0 (c • n ω) ∂q = 0 := by
  have h1 : Integrable (fun ω => -(η / nscale lam u0) • (c • n ω)) q := (hn.smul c).smul _
  have h2 : Integrable (fun ω => (η * ⟪u0, c • n ω⟫ / nscale lam u0 ^ 3) • u0) q := by
    have : Integrable (fun ω => η * ⟪u0, c • n ω⟫ / nscale lam u0 ^ 3) q :=
      (((hn.smul c).const_inner u0).const_mul η).div_const _
    exact this.smul_const u0
  simp only [dphi]
  rw [integral_add h1 h2, integral_smul, integral_smul, hn0, smul_zero, smul_zero, zero_add]
  rw [integral_smul_const]
  have : ∫ ω, η * ⟪u0, c • n ω⟫ / nscale lam u0 ^ 3 ∂q = 0 := by
    rw [integral_div, integral_const_mul, integral_inner (f := fun a => c • n a) (hn.smul c) u0,
      integral_smul, hn0]
    simp
  rw [this, zero_smul]

lemma noise_x {η lam α s2 : ℝ} (hl : 0 < lam) (hη : 0 ≤ η) (hα0 : 0 < α)
    (w' u0 : E) (n : Ω' → E) (hnm : Measurable n) (hn : Integrable n q) (hn0 : ∫ ω, n ω ∂q = 0)
    (hn2 : Integrable (fun ω => ‖n ω‖ ^ 2) q) (hs2 : ∫ ω, ‖n ω‖ ^ 2 ∂q ≤ s2) :
    (∀ ω, ‖(w' + (1 / α) • nphi η lam (u0 + α • n ω)) - (w' + (1 / α) • nphi η lam u0)‖ ≤
        (2 * η / lam) * ‖n ω‖) ∧
    (∀ ω, ‖(w' + (1 / α) • nphi η lam (u0 + α • n ω)) - (w' + (1 / α) • nphi η lam u0)‖ ≤
        2 * η / α) ∧
    Integrable (fun ω => w' + (1 / α) • nphi η lam (u0 + α • n ω)) q ∧
    ‖∫ ω, ((w' + (1 / α) • nphi η lam (u0 + α • n ω)) - (w' + (1 / α) • nphi η lam u0)) ∂q‖ ≤
        6 * η * α * s2 / lam ^ 2 ∧
    ∫ ω, ‖(w' + (1 / α) • nphi η lam (u0 + α • n ω)) - (w' + (1 / α) • nphi η lam u0)‖ ^ 2 ∂q ≤
        (2 * η / lam) ^ 2 * s2 := by
  set X := fun ω => w' + (1 / α) • nphi η lam (u0 + α • n ω)
  set xh := w' + (1 / α) • nphi η lam u0
  have hdiff : ∀ ω, X ω - xh = (1 / α) • (nphi η lam (u0 + α • n ω) - nphi η lam u0) := by
    intro ω; simp only [X, xh, smul_sub]; abel
  have hb1 : ∀ ω, ‖X ω - xh‖ ≤ (2 * η / lam) * ‖n ω‖ := by
    intro ω
    rw [hdiff, norm_smul, Real.norm_of_nonneg (by positivity)]
    have h := nphi_lip hl hη u0 (u0 + α • n ω)
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hα0.le] at h
    calc 1 / α * ‖nphi η lam (u0 + α • n ω) - nphi η lam u0‖ ≤ 1 / α * (2 * η / lam * (α * ‖n ω‖)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = (2 * η / lam) * ‖n ω‖ := by field_simp
  have hb2 : ∀ ω, ‖X ω - xh‖ ≤ 2 * η / α := by
    intro ω
    rw [hdiff, norm_smul, Real.norm_of_nonneg (by positivity)]
    have h1 := nphi_norm hl hη (u0 + α • n ω)
    have h2 := nphi_norm hl hη u0
    have h3 := norm_sub_le (nphi η lam (u0 + α • n ω)) (nphi η lam u0)
    calc 1 / α * ‖nphi η lam (u0 + α • n ω) - nphi η lam u0‖ ≤ 1 / α * (η + η) :=
          mul_le_mul_of_nonneg_left (h3.trans (add_le_add h1 h2)) (by positivity)
      _ = 2 * η / α := by ring
  have hXm : Measurable X := by
    have : Measurable (fun ω => u0 + α • n ω) := measurable_const.add (hnm.const_smul α)
    exact measurable_const.add (((measurable_nphi η lam).comp this).const_smul _)
  have hXi : Integrable X q := by
    refine Integrable.of_bound hXm.aestronglyMeasurable (‖xh‖ + 2 * η / α)
      (Filter.Eventually.of_forall fun ω => ?_)
    have := hb2 ω
    have h2 := norm_le_insert' (X ω) xh
    linarith [norm_sub_le (X ω) xh, norm_add_le (X ω - xh) xh, show X ω = (X ω - xh) + xh by abel]
  refine ⟨hb1, hb2, hXi, ?_, ?_⟩
  · set R := fun ω => nphi η lam (u0 + α • n ω) - nphi η lam u0 - dphi η lam u0 (α • n ω)
    have hR : ∀ ω, ‖R ω‖ ≤ (6 * η / lam ^ 2) * (α ^ 2 * ‖n ω‖ ^ 2) := by
      intro ω
      have := nphi_taylor hl hη u0 (α • n ω)
      rw [norm_smul, Real.norm_of_nonneg hα0.le, mul_pow] at this
      exact this
    have hD : Integrable (fun ω => dphi η lam u0 (α • n ω)) q := by
      simp only [dphi]
      exact ((hn.smul α).smul _).add
        (((((hn.smul α).const_inner u0).const_mul η).div_const _).smul_const u0)
    have hdi : Integrable (fun ω => X ω - xh) q := hXi.sub (integrable_const _)
    have hRi : Integrable R q := by
      have e : R = fun ω => α • (X ω - xh) - dphi η lam u0 (α • n ω) := by
        ext ω; simp only [R]; rw [hdiff, smul_smul, mul_one_div_cancel hα0.ne', one_smul]
      rw [e]; exact (hdi.smul α).sub hD
    have e2 : ∀ ω, X ω - xh = (1 / α) • (dphi η lam u0 (α • n ω) + R ω) := by
      intro ω; rw [hdiff]; congr 1
      change _ = _ + (nphi η lam (u0 + α • n ω) - nphi η lam u0 - dphi η lam u0 (α • n ω)); abel
    show ‖∫ ω, (X ω - xh) ∂q‖ ≤ _
    simp_rw [e2]
    rw [integral_smul, integral_add hD hRi, dphi_integral_zero q u0 α n hn hn0, zero_add,
      norm_smul, Real.norm_of_nonneg (by positivity)]
    have hnR := norm_integral_le_integral_norm (μ := q) R
    have hRb : ∫ ω, ‖R ω‖ ∂q ≤ ∫ ω, (6 * η / lam ^ 2) * (α ^ 2 * ‖n ω‖ ^ 2) ∂q :=
      integral_mono hRi.norm ((hn2.const_mul _).const_mul _) hR
    rw [integral_const_mul, integral_const_mul] at hRb
    calc 1 / α * ‖∫ ω, R ω ∂q‖ ≤ 1 / α * ((6 * η / lam ^ 2) * (α ^ 2 * s2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine hnR.trans (hRb.trans ?_)
          gcongr
      _ = 6 * η * α * s2 / lam ^ 2 := by field_simp
  · show ∫ ω, ‖X ω - xh‖ ^ 2 ∂q ≤ _
    have hb : ∀ ω, ‖X ω - xh‖ ^ 2 ≤ (2 * η / lam) ^ 2 * ‖n ω‖ ^ 2 := by
      intro ω; rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hb1 ω) 2
    have hi : Integrable (fun ω => ‖X ω - xh‖ ^ 2) q := by
      refine (hn2.const_mul ((2 * η / lam) ^ 2)).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
      · exact ((hXm.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
      · rw [Real.norm_of_nonneg (by positivity)]; exact hb ω
    calc ∫ ω, ‖X ω - xh‖ ^ 2 ∂q ≤ ∫ ω, (2 * η / lam) ^ 2 * ‖n ω‖ ^ 2 ∂q :=
          integral_mono hi (hn2.const_mul _) hb
      _ = (2 * η / lam) ^ 2 * ∫ ω, ‖n ω‖ ^ 2 ∂q := integral_const_mul _ _
      _ ≤ (2 * η / lam) ^ 2 * s2 := by gcongr

end NoiseX

section YMean

variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F}
  {Hx : E × F → (E × F →L[ℝ] E)} {Hy : E × F → (E × F →L[ℝ] F)} {L μ ρ : ℝ}

omit [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma Hyp.ystar_continuous (H : Hyp f gx gy Hx Hy L μ ρ) : Continuous (ystar H) := by
  have : LipschitzWith (Real.toNNReal (L / μ)) (ystar H) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (div_nonneg H.L_pos.le H.μpos.le)]
    exact H.ystar_lip a b
  exact this.continuous

noncomputable def DylL (H : Hyp f gx gy Hx Hy L μ ρ) (x : E) : E →L[ℝ] F :=
  -((LinearMap.toContinuousLinearMap ((Jinv H x).symm : F →ₗ[ℝ] F)).comp (Cb H x))

omit [BorelSpace E] [SecondCountableTopology E] [BorelSpace F] [SecondCountableTopology F] in
omit [MeasurableSpace F] in
omit [MeasurableSpace E] in
lemma DylL_apply (H : Hyp f gx gy Hx Hy L μ ρ) (x v : E) : DylL H x v = Dyl H x v := rfl

variable {Ω' : Type*} [MeasurableSpace Ω'] (q : Measure Ω') [IsProbabilityMeasure q]

omit [SecondCountableTopology E] in
lemma ystar_mean (H : Hyp f gx gy Hx Hy L μ ρ) (X : Ω' → E) (xh : E) (hXm : Measurable X)
    (hXi : Integrable X q) {B M1 M2 : ℝ} (hb : ∀ ω, ‖X ω - xh‖ ≤ B)
    (hmean : ‖∫ ω, (X ω - xh) ∂q‖ ≤ M1)
    (hsi : Integrable (fun ω => ‖X ω - xh‖ ^ 2) q) (hsec : ∫ ω, ‖X ω - xh‖ ^ 2 ∂q ≤ M2) :
    Integrable (fun ω => ystar H (X ω)) q ∧
      ‖∫ ω, ystar H (X ω) ∂q - ystar H xh‖ ≤ (L / μ) * M1 + (ρ / μ) * (1 + (L / μ) ^ 2) * M2 := by
  have hYm : Measurable (fun ω => ystar H (X ω)) := H.ystar_continuous.measurable.comp hXm
  have hYb : ∀ ω, ‖ystar H (X ω)‖ ≤ ‖ystar H xh‖ + (L / μ) * B := by
    intro ω
    have h1 := H.ystar_lip (X ω) xh
    have h2 := norm_sub_norm_le (ystar H (X ω)) (ystar H xh)
    have hk : 0 ≤ L / μ := div_nonneg H.L_pos.le H.μpos.le
    nlinarith [mul_le_mul_of_nonneg_left (hb ω) hk]
  have hYi : Integrable (fun ω => ystar H (X ω)) q :=
    Integrable.of_bound hYm.aestronglyMeasurable _ (Filter.Eventually.of_forall hYb)
  refine ⟨hYi, ?_⟩
  set R := fun ω => ystar H (X ω) - ystar H xh - Dyl H xh (X ω - xh)
  have hR : ∀ ω, ‖R ω‖ ≤ (ρ / μ) * (1 + (L / μ) ^ 2) * ‖X ω - xh‖ ^ 2 := fun ω => H.ystar_lin (X ω) xh
  have hdi : Integrable (fun ω => X ω - xh) q := hXi.sub (integrable_const _)
  have hLi : Integrable (fun ω => Dyl H xh (X ω - xh)) q := by
    simp_rw [← DylL_apply]; exact (DylL H xh).integrable_comp hdi
  have hRi : Integrable R q := (hYi.sub (integrable_const _)).sub hLi
  have e : ∫ ω, ystar H (X ω) ∂q - ystar H xh = Dyl H xh (∫ ω, (X ω - xh) ∂q) + ∫ ω, R ω ∂q := by
    have e1 : ∀ ω, ystar H (X ω) = ystar H xh + Dyl H xh (X ω - xh) + R ω := by
      intro ω; simp only [R]; abel
    simp_rw [e1]
    rw [integral_add (f := fun ω => ystar H xh + Dyl H xh (X ω - xh)) (g := R)
      ((integrable_const _).add hLi) hRi,
      integral_add (f := fun _ => ystar H xh) (g := fun ω => Dyl H xh (X ω - xh)) (integrable_const _) hLi,
      integral_const]
    simp only [probReal_univ, one_smul]
    rw [← DylL_apply, ← (DylL H xh).integral_comp_comm hdi]
    simp only [DylL_apply]; abel
  rw [e]
  have hk : 0 ≤ L / μ := div_nonneg H.L_pos.le H.μpos.le
  have h1 : ‖Dyl H xh (∫ ω, (X ω - xh) ∂q)‖ ≤ (L / μ) * M1 :=
    (H.Dyl_norm xh _).trans (mul_le_mul_of_nonneg_left hmean hk)
  have h2 : ‖∫ ω, R ω ∂q‖ ≤ (ρ / μ) * (1 + (L / μ) ^ 2) * M2 := by
    refine (norm_integral_le_integral_norm R).trans ?_
    have hc : 0 ≤ (ρ / μ) * (1 + (L / μ) ^ 2) := by have := H.ρnn; have := H.μpos; positivity
    calc ∫ ω, ‖R ω‖ ∂q ≤ ∫ ω, (ρ / μ) * (1 + (L / μ) ^ 2) * ‖X ω - xh‖ ^ 2 ∂q :=
          integral_mono hRi.norm (hsi.const_mul _) hR
      _ = (ρ / μ) * (1 + (L / μ) ^ 2) * ∫ ω, ‖X ω - xh‖ ^ 2 ∂q := integral_const_mul _ _
      _ ≤ (ρ / μ) * (1 + (L / μ) ^ 2) * M2 := mul_le_mul_of_nonneg_left hsec hc
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

end YMean

section TrackStep

variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F}
  {Hx : E × F → (E × F →L[ℝ] E)} {Hy : E × F → (E × F →L[ℝ] F)} {L μ ρ : ℝ}
  {ox : E × F → Ω → E} {oy : E × F → Ω → F} {p : Measure Ω} [IsProbabilityMeasure p] {σ : ℝ}

lemma sq_sub_le_two {V : Type*} [NormedAddCommGroup V] (a b : V) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  have h2 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

set_option maxHeartbeats 2000000 in
lemma track_step (H : Hyp f gx gy Hx Hy L μ ρ) (O : OracleHyp gx gy ox oy p σ)
    {α γ η lam : ℝ} (hα0 : 0 < α) (hγ0 : 0 < γ) (hγ : γ ≤ μ / L ^ 2)
    (hl : 0 < lam) (hη : 0 ≤ η) (w' u : E) (y : F) :
    ∫⁻ ω, ENNReal.ofReal (‖y + γ • oy (w' + ((1 - α) / α) • nphi η lam u, y) ω -
        ystar H (w' + (1 / α) • nphi η lam ((1 - α) • u +
          α • ox (w' + ((1 - α) / α) • nphi η lam u, y) ω))‖ ^ 2) ∂p ≤
      ENNReal.ofReal ((1 - γ * μ / 2) * ‖y - ystar H (w' + ((1 - α) / α) • nphi η lam u)‖ ^ 2 +
        2 * γ ^ 2 * σ ^ 2 + 2 * (L / μ) ^ 2 * ((2 * η / lam) ^ 2 * σ ^ 2) +
        (3 / (γ * μ)) * ((L / μ) * (η + (2 * η / lam) *
            ‖gx (w' + ((1 - α) / α) • nphi η lam u, y) - u‖) +
          ((L / μ) * (6 * η * α * σ ^ 2 / lam ^ 2) +
            (ρ / μ) * (1 + (L / μ) ^ 2) * ((2 * η / lam) ^ 2 * σ ^ 2))) ^ 2) := by
  set xt := w' + ((1 - α) / α) • nphi η lam u
  set z : E × F := (xt, y)
  set e := y - ystar H xt
  set n : Ω → E := fun ω => ox z ω - gx z
  set u0 := (1 - α) • u + α • gx z
  set xh := w' + (1 / α) • nphi η lam u0
  have hμ := H.μpos
  have hL := H.L_pos
  have hk : 0 ≤ L / μ := div_nonneg hL.le hμ.le
  have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg σ
  have hu' : ∀ ω, (1 - α) • u + α • ox z ω = u0 + α • n ω := by
    intro ω; simp only [u0, n, smul_sub]; abel
  have hnm : Measurable n := (O.meas_x z).sub measurable_const
  obtain ⟨hb1, hb2, hXi, hmean, hsec⟩ := noise_x p hl hη hα0 w' u0 n hnm (O.nx_int z) (O.nx_mean z)
    (O.ivx z) (O.vx z)
  set X := fun ω => w' + (1 / α) • nphi η lam (u0 + α • n ω)
  have hXm : Measurable X := by
    have : Measurable (fun ω => u0 + α • n ω) := measurable_const.add (hnm.const_smul α)
    exact measurable_const.add (((measurable_nphi η lam).comp this).const_smul _)
  have hsi : Integrable (fun ω => ‖X ω - xh‖ ^ 2) p := by
    refine Integrable.of_bound ((hXm.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
      ((2 * η / α) ^ 2) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb2 ω) 2
  obtain ⟨hYi, hYmean⟩ := ystar_mean p H X xh hXm hXi hb2 hmean hsi hsec
  set mbar := ∫ ω, ystar H (X ω) ∂p
  have hYm : Measurable (fun ω => ystar H (X ω)) := H.ystar_continuous.measurable.comp hXm
  have hxd : ‖xh - xt‖ ≤ η + (2 * η / lam) * ‖gx z - u‖ := by
    have e1 : xh - xt = nphi η lam u + (1 / α) • (nphi η lam u0 - nphi η lam u) := by
      simp only [xh, xt, smul_sub]
      have : (1 - α) / α = 1 / α - 1 := by field_simp
      rw [this, sub_smul, one_smul]; abel
    rw [e1]
    have h1 := nphi_norm hl hη u
    have h2 := nphi_lip hl hη u u0
    have hu0 : u0 - u = α • (gx z - u) := by simp only [u0, smul_sub, sub_smul, one_smul]; abel
    rw [hu0, norm_smul, Real.norm_of_nonneg hα0.le] at h2
    refine (norm_add_le _ _).trans (add_le_add h1 ?_)
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc 1 / α * ‖nphi η lam u0 - nphi η lam u‖ ≤ 1 / α * (2 * η / lam * (α * ‖gx z - u‖)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (2 * η / lam) * ‖gx z - u‖ := by field_simp
  set Db := (L / μ) * (η + (2 * η / lam) * ‖gx z - u‖) +
    ((L / μ) * (6 * η * α * σ ^ 2 / lam ^ 2) +
      (ρ / μ) * (1 + (L / μ) ^ 2) * ((2 * η / lam) ^ 2 * σ ^ 2))
  have hdbar : ‖mbar - ystar H xt‖ ≤ Db := by
    have h1 := H.ystar_lip xh xt
    have e1 : mbar - ystar H xt = (ystar H xh - ystar H xt) + (mbar - ystar H xh) := by abel
    rw [e1]
    refine (norm_add_le _ _).trans (add_le_add ?_ hYmean)
    exact h1.trans (mul_le_mul_of_nonneg_left hxd hk)
  set a := e + γ • gy z
  have ha : ‖a‖ ^ 2 ≤ (1 - γ * μ) * ‖e‖ ^ 2 := by
    have hy : y = ystar H xt + e := by simp [e]
    have := H.contraction xt e hγ0.le hγ
    rw [← hy] at this; exact this
  set N : Ω → F := fun ω => γ • (oy z ω - gy z) - (ystar H (X ω) - mbar)
  have hint : ∀ ω, y + γ • oy z ω - ystar H (X ω) = (a - (mbar - ystar H xt)) + N ω := by
    intro ω; simp only [a, N, e, smul_sub]; abel
  have hNi : Integrable N p := ((O.ny_int z).smul γ).sub (hYi.sub (integrable_const _))
  have hN0 : ∫ ω, N ω ∂p = 0 := by
    simp only [N]
    rw [integral_sub (f := fun ω => γ • (oy z ω - gy z)) (g := fun ω => ystar H (X ω) - mbar)
      ((O.ny_int z).smul γ) (hYi.sub (integrable_const _)), integral_smul,
      O.ny_mean z, integral_sub (f := fun ω => ystar H (X ω)) (g := fun _ => mbar) hYi (integrable_const _),
      integral_const]
    simp [mbar]
  have hYc : Integrable (fun ω => ‖ystar H (X ω) - mbar‖ ^ 2) p := by
    refine Integrable.of_bound ((hYm.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
      ((‖ystar H xh‖ + (L / μ) * (2 * η / α) + ‖mbar‖) ^ 2) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    have h1 := H.ystar_lip (X ω) xh
    have h2 := norm_sub_le (ystar H (X ω)) mbar
    have h3 := norm_le_insert' (ystar H (X ω)) (ystar H xh)
    nlinarith [mul_le_mul_of_nonneg_left (hb2 ω) hk, norm_sub_norm_le (ystar H (X ω)) (ystar H xh)]
  have hN2 : Integrable (fun ω => ‖N ω‖ ^ 2) p := by
    refine (((O.ivy z).const_mul (2 * γ ^ 2)).add (hYc.const_mul 2)).mono' ?_ ?_
    · exact ((((O.meas_y z).sub measurable_const).const_smul γ).sub
        (hYm.sub measurable_const)).norm.pow_const 2 |>.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      have := sq_sub_le_two (γ • (oy z ω - gy z)) (ystar H (X ω) - mbar)
      rw [norm_smul, Real.norm_of_nonneg hγ0.le, mul_pow] at this
      show ‖N ω‖ ^ 2 ≤ 2 * γ ^ 2 * ‖oy z ω - gy z‖ ^ 2 + 2 * ‖ystar H (X ω) - mbar‖ ^ 2
      nlinarith [this]
  have hsum := sq_add_mean_zero p (a - (mbar - ystar H xt)) N hNi hN0 hN2
  have hNb : ∫ ω, ‖N ω‖ ^ 2 ∂p ≤ 2 * γ ^ 2 * σ ^ 2 + 2 * (L / μ) ^ 2 * ((2 * η / lam) ^ 2 * σ ^ 2) := by
    have hpt : ∀ ω, ‖N ω‖ ^ 2 ≤ 2 * γ ^ 2 * ‖oy z ω - gy z‖ ^ 2 + 2 * ‖ystar H (X ω) - mbar‖ ^ 2 := by
      intro ω
      have := sq_sub_le_two (γ • (oy z ω - gy z)) (ystar H (X ω) - mbar)
      rw [norm_smul, Real.norm_of_nonneg hγ0.le, mul_pow] at this
      nlinarith [this]
    have h1 := integral_mono hN2 (((O.ivy z).const_mul (2 * γ ^ 2)).add (hYc.const_mul 2)) hpt
    simp only [Pi.add_apply] at h1
    rw [integral_add (f := fun ω => 2 * γ ^ 2 * ‖oy z ω - gy z‖ ^ 2)
      (g := fun ω => 2 * ‖ystar H (X ω) - mbar‖ ^ 2) ((O.ivy z).const_mul _) (hYc.const_mul 2),
      integral_const_mul, integral_const_mul] at h1
    have hY2 : Integrable (fun ω => ‖ystar H (X ω)‖ ^ 2) p := by
      refine Integrable.of_bound (hYm.norm.pow_const 2).aestronglyMeasurable
        ((‖ystar H xh‖ + (L / μ) * (2 * η / α)) ^ 2) (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      have h1 := H.ystar_lip (X ω) xh
      nlinarith [mul_le_mul_of_nonneg_left (hb2 ω) hk, norm_sub_norm_le (ystar H (X ω)) (ystar H xh)]
    have hmm := mean_minimizes p (fun ω => ystar H (X ω)) hYi hY2 (ystar H xh)
    have hY3 : Integrable (fun ω => ‖ystar H (X ω) - ystar H xh‖ ^ 2) p := by
      refine Integrable.of_bound ((hYm.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
        (((L / μ) * (2 * η / α)) ^ 2) (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (H.ystar_lip (X ω) xh).trans (mul_le_mul_of_nonneg_left (hb2 ω) hk)
    have hlip2 : ∫ ω, ‖ystar H (X ω) - ystar H xh‖ ^ 2 ∂p ≤ (L / μ) ^ 2 * ((2 * η / lam) ^ 2 * σ ^ 2) := by
      have hpt2 : ∀ ω, ‖ystar H (X ω) - ystar H xh‖ ^ 2 ≤ (L / μ) ^ 2 * ‖X ω - xh‖ ^ 2 := by
        intro ω; rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (H.ystar_lip (X ω) xh) 2
      calc ∫ ω, ‖ystar H (X ω) - ystar H xh‖ ^ 2 ∂p ≤ ∫ ω, (L / μ) ^ 2 * ‖X ω - xh‖ ^ 2 ∂p :=
            integral_mono hY3 (hsi.const_mul _) hpt2
        _ = (L / μ) ^ 2 * ∫ ω, ‖X ω - xh‖ ^ 2 ∂p := integral_const_mul _ _
        _ ≤ (L / μ) ^ 2 * ((2 * η / lam) ^ 2 * σ ^ 2) := by gcongr
    have hvy := O.vy z
    have hA : 2 * γ ^ 2 * ∫ ω, ‖oy z ω - gy z‖ ^ 2 ∂p ≤ 2 * γ ^ 2 * σ ^ 2 :=
      mul_le_mul_of_nonneg_left hvy (by positivity)
    have hB : 2 * ∫ ω, ‖ystar H (X ω) - mbar‖ ^ 2 ∂p ≤ 2 * ((L / μ) ^ 2 * ((2 * η / lam) ^ 2 * σ ^ 2)) := by
      have := hmm.trans hlip2
      linarith
    linarith
  have hgm : γ * μ ≤ 1 := by
    have h1 : γ * μ ≤ μ / L ^ 2 * μ := mul_le_mul_of_nonneg_right hγ hμ.le
    have h2 : μ / L ^ 2 * μ ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]
      nlinarith [H.μL]
    linarith
  have hgm0 : 0 < γ * μ := by positivity
  have hyoung := young_sq a (-(mbar - ystar H xt)) (δ := γ * μ / 2) (by positivity)
  rw [← sub_eq_add_neg, norm_neg] at hyoung
  have hfin : ‖a - (mbar - ystar H xt)‖ ^ 2 ≤ (1 - γ * μ / 2) * ‖e‖ ^ 2 + (3 / (γ * μ)) * Db ^ 2 := by
    have h1 : (1 + γ * μ / 2) * ‖a‖ ^ 2 ≤ (1 - γ * μ / 2) * ‖e‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left ha (by positivity : (0:ℝ) ≤ 1 + γ * μ / 2)
      have h3 : (1 + γ * μ / 2) * ((1 - γ * μ) * ‖e‖ ^ 2) ≤ (1 - γ * μ / 2) * ‖e‖ ^ 2 := by
        have e5 : (1 + γ * μ / 2) * (1 - γ * μ) = 1 - γ * μ / 2 - (γ * μ) ^ 2 / 2 := by ring
        have : (1 + γ * μ / 2) * (1 - γ * μ) ≤ 1 - γ * μ / 2 := by
          rw [e5]; have := sq_nonneg (γ * μ); linarith
        calc (1 + γ * μ / 2) * ((1 - γ * μ) * ‖e‖ ^ 2) = ((1 + γ * μ / 2) * (1 - γ * μ)) * ‖e‖ ^ 2 := by ring
          _ ≤ (1 - γ * μ / 2) * ‖e‖ ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
      linarith
    have h2 : (1 + 1 / (γ * μ / 2)) * ‖mbar - ystar H xt‖ ^ 2 ≤ (3 / (γ * μ)) * Db ^ 2 := by
      have hc : 1 + 1 / (γ * μ / 2) ≤ 3 / (γ * μ) := by
        rw [div_div_eq_mul_div, one_mul, ← sub_nonneg]
        have : 3 / (γ * μ) - (1 + 2 / (γ * μ)) = (1 - γ * μ) / (γ * μ) := by field_simp; ring
        rw [this]; exact div_nonneg (by linarith) hgm0.le
      have hd2 : ‖mbar - ystar H xt‖ ^ 2 ≤ Db ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdbar 2
      calc (1 + 1 / (γ * μ / 2)) * ‖mbar - ystar H xt‖ ^ 2 ≤ (3 / (γ * μ)) * ‖mbar - ystar H xt‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hc (sq_nonneg _)
        _ ≤ (3 / (γ * μ)) * Db ^ 2 := mul_le_mul_of_nonneg_left hd2 (by positivity)
    linarith
  have hfun : (fun ω => ENNReal.ofReal (‖y + γ • oy z ω - ystar H (w' + (1 / α) • nphi η lam
      ((1 - α) • u + α • ox z ω))‖ ^ 2)) = fun ω => ENNReal.ofReal (‖(a - (mbar - ystar H xt)) + N ω‖ ^ 2) := by
    funext ω; rw [hu' ω, ← hint ω]
  rw [hfun]
  have hint2 : Integrable (fun ω => ‖(a - (mbar - ystar H xt)) + N ω‖ ^ 2) p := by
    refine ((integrable_const (2 * ‖a - (mbar - ystar H xt)‖ ^ 2)).add (hN2.const_mul 2)).mono' ?_ ?_
    · exact ((measurable_const.add ((((O.meas_y z).sub measurable_const).const_smul γ).sub
        (hYm.sub measurable_const))).norm.pow_const 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      have := sq_sub_le_two (a - (mbar - ystar H xt)) (-N ω)
      rw [sub_neg_eq_add, norm_neg] at this
      exact this
  rw [← ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall fun ω => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [hsum]
  linarith

end TrackStep

section GenericNoise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  {Ω' : Type*} [MeasurableSpace Ω'] (q : Measure Ω') [IsProbabilityMeasure q]

lemma noise_step (A : V) (c : ℝ) (n : Ω' → V) (hnm : Measurable n) (hn : Integrable n q)
    (hn0 : ∫ ω, n ω ∂q = 0) (hn2 : Integrable (fun ω => ‖n ω‖ ^ 2) q) {s2 : ℝ}
    (hs2 : ∫ ω, ‖n ω‖ ^ 2 ∂q ≤ s2) :
    ∫⁻ ω, ENNReal.ofReal (‖A + c • n ω‖ ^ 2) ∂q ≤ ENNReal.ofReal (‖A‖ ^ 2 + c ^ 2 * s2) := by
  have hcn : Integrable (fun ω => c • n ω) q := hn.smul c
  have hcn0 : ∫ ω, c • n ω ∂q = 0 := by rw [integral_smul, hn0, smul_zero]
  have hcn2 : Integrable (fun ω => ‖c • n ω‖ ^ 2) q := by
    have : (fun ω => ‖c • n ω‖ ^ 2) = fun ω => c ^ 2 * ‖n ω‖ ^ 2 := by
      ext ω; rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [this]; exact hn2.const_mul _
  have h := sq_add_mean_zero q A (fun ω => c • n ω) hcn hcn0 hcn2
  have hint : Integrable (fun ω => ‖A + c • n ω‖ ^ 2) q := by
    refine ((integrable_const (2 * ‖A‖ ^ 2)).add (hcn2.const_mul 2)).mono' ?_ ?_
    · exact ((measurable_const.add (hnm.const_smul c)).norm.pow_const 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_of_nonneg (by positivity)]
      have := sq_sub_le_two A (-(c • n ω))
      rw [sub_neg_eq_add, norm_neg] at this; exact this
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [h]
  have : ∫ ω, ‖c • n ω‖ ^ 2 ∂q = c ^ 2 * ∫ ω, ‖n ω‖ ^ 2 ∂q := by
    rw [← integral_const_mul]; congr 1; ext ω; rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [this]
  have := mul_le_mul_of_nonneg_left hs2 (sq_nonneg c)
  linarith

end GenericNoise

section MNoise

variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F}
  {Hx : E × F → (E × F →L[ℝ] E)} {Hy : E × F → (E × F →L[ℝ] F)} {L μ ρ : ℝ}
  {ox : E × F → Ω → E} {oy : E × F → Ω → F} {p : Measure Ω} [IsProbabilityMeasure p] {σ : ℝ}

noncomputable def MmL (H : Hyp f gx gy Hx Hy L μ ρ) (x : E) : F →L[ℝ] E :=
  (Bb H x).comp (LinearMap.toContinuousLinearMap ((Jinv H x).symm : F →ₗ[ℝ] F))

omit [BorelSpace E] [SecondCountableTopology E] [BorelSpace F] [SecondCountableTopology F] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma MmL_apply (H : Hyp f gx gy Hx Hy L μ ρ) (x : E) (v : F) : MmL H x v = Mm H x v := rfl

lemma m_noise_step (H : Hyp f gx gy Hx Hy L μ ρ) (O : OracleHyp gx gy ox oy p σ)
    (B : E) (c : ℝ) (x : E) (z : E × F) :
    ∫⁻ ω, ENNReal.ofReal (‖B + c • ((ox z ω - gx z) - Mm H x (oy z ω - gy z))‖ ^ 2) ∂p ≤
      ENNReal.ofReal (‖B‖ ^ 2 + c ^ 2 * ((1 + (L / μ) ^ 2) * σ ^ 2)) := by
  set n : Ω → E := fun ω => (ox z ω - gx z) - Mm H x (oy z ω - gy z)
  have hmy : Measurable (fun ω => oy z ω - gy z) := (O.meas_y z).sub measurable_const
  have hnm : Measurable n := by
    simp only [n]; simp_rw [← MmL_apply]
    exact ((O.meas_x z).sub measurable_const).sub ((MmL H x).continuous.measurable.comp hmy)
  have hMi : Integrable (fun ω => Mm H x (oy z ω - gy z)) p := by
    simp_rw [← MmL_apply]; exact (MmL H x).integrable_comp (O.ny_int z)
  have hn : Integrable n p := (O.nx_int z).sub hMi
  have hn0 : ∫ ω, n ω ∂p = 0 := by
    simp only [n]
    rw [integral_sub (O.nx_int z) hMi, O.nx_mean z]
    simp_rw [← MmL_apply]
    rw [(MmL H x).integral_comp_comm (O.ny_int z), O.ny_mean z, map_zero, sub_zero]
  have hk : 0 ≤ L / μ := div_nonneg H.L_pos.le H.μpos.le
  have hpt : ∀ ω, ‖n ω‖ ^ 2 ≤ (1 + (L / μ) ^ 2) * (‖ox z ω - gx z‖ ^ 2 + ‖oy z ω - gy z‖ ^ 2) := by
    intro ω
    have h1 := norm_sub_le (ox z ω - gx z) (Mm H x (oy z ω - gy z))
    have h2 := H.Mm_norm x (oy z ω - gy z)
    have h3 : ‖n ω‖ ≤ ‖ox z ω - gx z‖ + (L / μ) * ‖oy z ω - gy z‖ := h1.trans (by linarith)
    have h4 : ‖n ω‖ ^ 2 ≤ (‖ox z ω - gx z‖ + (L / μ) * ‖oy z ω - gy z‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith [sq_nonneg ((L / μ) * ‖ox z ω - gx z‖ - ‖oy z ω - gy z‖)]
  have hn2 : Integrable (fun ω => ‖n ω‖ ^ 2) p := by
    refine ((O.iv z).const_mul (1 + (L / μ) ^ 2)).mono' (hnm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]; exact hpt ω
  have hs2 : ∫ ω, ‖n ω‖ ^ 2 ∂p ≤ (1 + (L / μ) ^ 2) * σ ^ 2 := by
    calc ∫ ω, ‖n ω‖ ^ 2 ∂p ≤ ∫ ω, (1 + (L / μ) ^ 2) * (‖ox z ω - gx z‖ ^ 2 + ‖oy z ω - gy z‖ ^ 2) ∂p :=
          integral_mono hn2 ((O.iv z).const_mul _) hpt
      _ = (1 + (L / μ) ^ 2) * ∫ ω, (‖ox z ω - gx z‖ ^ 2 + ‖oy z ω - gy z‖ ^ 2) ∂p :=
          integral_const_mul _ _
      _ ≤ (1 + (L / μ) ^ 2) * σ ^ 2 := mul_le_mul_of_nonneg_left (O.v z) (by positivity)
  exact noise_step p B c n hnm hn hn0 hn2 hs2

end MNoise

end OracleTemplate.HessianNcsc
