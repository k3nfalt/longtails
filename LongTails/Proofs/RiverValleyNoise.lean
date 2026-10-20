import LongTails.Proofs.RiverValleyStep
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.RiverValley

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {K : Submodule ℝ E} [K.HasOrthogonalProjection]
variable {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

structure NoiseAt (K : Submodule ℝ E) [K.HasOrthogonalProjection] (p : Measure Ω) (ζ : Ω → E)
    (σu σv : ℝ) : Prop where
  meas : Measurable ζ
  int : Integrable ζ p
  mean : ∫ ω, ζ ω ∂p = 0
  intQ : Integrable (fun ω => ‖Kᗮ.starProjection (ζ ω)‖ ^ 2) p
  intP : Integrable (fun ω => ‖K.starProjection (ζ ω)‖ ^ 2) p
  varQ : ∫ ω, ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 ∂p ≤ σu ^ 2
  varP : ∫ ω, ‖K.starProjection (ζ ω)‖ ^ 2 ∂p ≤ σv ^ 2

namespace NoiseAt

variable {ζ : Ω → E} {σu σv : ℝ} (N : NoiseAt K p ζ σu σv)
include N

omit [BorelSpace E] [IsProbabilityMeasure p] in
lemma clm_mean (L : E →L[ℝ] E) : ∫ ω, L (ζ ω) ∂p = 0 := by
  rw [L.integral_comp_comm N.int, N.mean, map_zero]

omit [BorelSpace E] [IsProbabilityMeasure p] in
lemma inner_mean (L : E →L[ℝ] E) (v : E) : ∫ ω, ⟪v, L (ζ ω)⟫ ∂p = 0 := by
  have := (innerSL ℝ v).integral_comp_comm ((L.integrable_comp N.int))
  simp only [innerSL_apply_apply] at this
  rw [this, N.clm_mean L, inner_zero_right]

omit [FiniteDimensional ℝ E] [BorelSpace E] [IsProbabilityMeasure p] in
lemma sq_int : Integrable (fun ω => ‖ζ ω‖ ^ 2) p := by
  have h : ∀ ω, ‖ζ ω‖ ^ 2 = ‖K.starProjection (ζ ω)‖ ^ 2 + ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 := by
    intro ω
    have h0 : ⟪K.starProjection (ζ ω), Kᗮ.starProjection (ζ ω)⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem _)
        (Kᗮ.starProjection_apply_mem _)
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
    rw [P_add_Q] at this
    simp only [sq]; linarith
  simp_rw [h]; exact N.intP.add N.intQ

omit [FiniteDimensional ℝ E] [IsProbabilityMeasure p] in
lemma clm_sq_int (L : E →L[ℝ] E) : Integrable (fun ω => ‖L (ζ ω)‖ ^ 2) p := by
  refine Integrable.mono' (N.sq_int.const_mul (‖L‖ ^ 2))
    ((L.continuous.measurable.comp N.meas).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (L.le_opNorm _) 2

omit [FiniteDimensional ℝ E] [BorelSpace E] [IsProbabilityMeasure p] in
lemma norm_int : Integrable (fun ω => ‖ζ ω‖) p := N.int.norm

end NoiseAt

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma cs_of_quadratic {A B C : ℝ} (hA : 0 ≤ A) (hq : ∀ t : ℝ, 0 ≤ t ^ 2 * A - 2 * t * C + B) :
    C ^ 2 ≤ A * B := by
  rcases hA.lt_or_eq with hA | hA
  · have h := hq (C / A)
    have e : (C / A) ^ 2 * A - 2 * (C / A) * C + B = B - C ^ 2 / A := by field_simp; ring
    rw [e, sub_nonneg, div_le_iff₀ hA] at h
    linarith
  · subst hA
    have hB := hq 0
    by_contra hc
    replace hc := not_le.mp hc
    have hC : C ≠ 0 := by intro h0; rw [h0] at hc; simp at hc
    have h := hq ((B + 1) / (2 * C))
    have e : ((B + 1) / (2 * C)) ^ 2 * 0 - 2 * ((B + 1) / (2 * C)) * C + B = -1 := by
      field_simp; ring
    rw [e] at h
    linarith

namespace NoiseAt

variable {ζ : Ω → E} {σu σv : ℝ} (N : NoiseAt K p ζ σu σv)
include N

omit [FiniteDimensional ℝ E] [IsProbabilityMeasure p] in
lemma cross_le (hσu : 0 ≤ σu) (hσv : 0 ≤ σv) :
    Integrable (fun ω => ‖Kᗮ.starProjection (ζ ω)‖ * ‖K.starProjection (ζ ω)‖) p ∧
      ∫ ω, ‖Kᗮ.starProjection (ζ ω)‖ * ‖K.starProjection (ζ ω)‖ ∂p ≤ σu * σv := by
  set a : Ω → ℝ := fun ω => ‖Kᗮ.starProjection (ζ ω)‖
  set b : Ω → ℝ := fun ω => ‖K.starProjection (ζ ω)‖
  have hm : Measurable (fun ω => a ω * b ω) :=
    ((Kᗮ.starProjection.continuous.measurable.comp N.meas).norm).mul
      ((K.starProjection.continuous.measurable.comp N.meas).norm)
  have hint : Integrable (fun ω => a ω * b ω) p := by
    refine Integrable.mono' ((N.intQ.add N.intP).div_const 2) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    show a ω * b ω ≤ (a ω ^ 2 + b ω ^ 2) / 2
    nlinarith [sq_nonneg (a ω - b ω)]
  refine ⟨hint, ?_⟩
  set A := ∫ ω, a ω ^ 2 ∂p
  set B := ∫ ω, b ω ^ 2 ∂p
  set C := ∫ ω, a ω * b ω ∂p
  have hA : 0 ≤ A := integral_nonneg fun ω => sq_nonneg _
  have hC : 0 ≤ C := integral_nonneg fun ω => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hq : ∀ t : ℝ, 0 ≤ t ^ 2 * A - 2 * t * C + B := by
    intro t
    have i1 : Integrable (fun ω => t ^ 2 * a ω ^ 2) p := N.intQ.const_mul _
    have i2 : Integrable (fun ω => 2 * t * (a ω * b ω)) p := hint.const_mul _
    have i3 : Integrable (fun ω => b ω ^ 2) p := N.intP
    have i12 : Integrable (fun ω => t ^ 2 * a ω ^ 2 - 2 * t * (a ω * b ω)) p := i1.sub i2
    have h0 : 0 ≤ ∫ ω, (t ^ 2 * a ω ^ 2 - 2 * t * (a ω * b ω) + b ω ^ 2) ∂p :=
      integral_nonneg fun ω => by
        show 0 ≤ t ^ 2 * a ω ^ 2 - 2 * t * (a ω * b ω) + b ω ^ 2
        nlinarith [sq_nonneg (t * a ω - b ω)]
    rw [integral_add i12 i3, integral_sub i1 i2, integral_const_mul,
      integral_const_mul] at h0
    exact h0
  have hcs := cs_of_quadratic hA hq
  have hAB : A * B ≤ (σu * σv) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul N.varQ N.varP (integral_nonneg fun ω => sq_nonneg _) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ hC (mul_nonneg hσu hσv) two_ne_zero).mp (hcs.trans hAB)

end NoiseAt

end OracleTemplate.RiverValley

namespace OracleTemplate.RiverValley

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {K : Submodule ℝ E} [K.HasOrthogonalProjection]
variable {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
variable {h : E → ℝ} {gh : E → E}
  {Hh : E → E →L[ℝ] E} {φ : E → E} {Jφ : E → E →L[ℝ] E} {DJ : E → E →L[ℝ] E →L[ℝ] E}
  {A : E →L[ℝ] E} {Lh ρh G Luv μ Lv LJ ρJ : ℝ}

namespace Model

variable (H : Model K h gh Hh φ Jφ DJ A Lh ρh G Luv μ Lv LJ ρJ)
include H

omit [MeasurableSpace E] [BorelSpace E] in
lemma φ_cont : Continuous φ := continuous_iff_continuousAt.mpr fun y => (H.hJφ y).continuousAt

omit [MeasurableSpace E] [BorelSpace E] in
lemma φ_taylor (y d : E) : ‖φ (y + d) - φ y - Jφ y d‖ ≤ LJ * ‖d‖ ^ 2 :=
  taylor_lip H.hJφ H.LJ_nn H.J_lip y d

omit [MeasurableSpace E] [BorelSpace E] in
lemma φ_river (y d : E) (hd : d ∈ Kᗮ) : ‖φ (y + d) - φ y - Jφ y d‖ ≤ 2 * (Luv / μ) * ‖d‖ := by
  have hdir : ∀ z, ‖Jφ z d‖ ≤ (Luv / μ) * ‖d‖ := fun z => by
    have := H.Jφ_river z d; rwa [Q_of_orth hd] at this
  have h1 := diff_le_of_dir H.hJφ y d hdir
  calc _ ≤ ‖φ (y + d) - φ y‖ + ‖Jφ y d‖ := norm_sub_le _ _
    _ ≤ Luv / μ * ‖d‖ + Luv / μ * ‖d‖ := add_le_add h1 (hdir y)
    _ = _ := by ring

omit [MeasurableSpace E] [BorelSpace E] in
lemma mr_cont : Continuous (mr K gh Jφ) := by
  refine LipschitzWith.continuous (K := ⟨Luv / μ * Lh + LJ * G + 2 * (Luv / μ) ^ 2 * LJ * G,
    by have := H.Lh_nn; have := H.LJ_nn; have := H.G_nn; have := H.Luv_nn; have := H.μpos;
       positivity⟩) ?_
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  simp only [dist_eq_norm]
  exact H.mr_lip y y'

lemma exp_r {ζ : Ω → E} {σu σv : ℝ} (N : NoiseAt K p ζ σu σv) (y d0 : E) (η : ℝ) :
    Integrable (fun ω => φ (y + (d0 + -η • Kᗮ.starProjection (ζ ω))) - φ y -
        Jφ y (d0 + -η • Kᗮ.starProjection (ζ ω))) p ∧
      ‖∫ ω, (φ (y + (d0 + -η • Kᗮ.starProjection (ζ ω))) - φ y -
        Jφ y (d0 + -η • Kᗮ.starProjection (ζ ω))) ∂p‖ ≤
        ‖φ (y + d0) - φ y - Jφ y d0‖ + LJ * η ^ 2 * σu ^ 2 := by
  set e : Ω → E := fun ω => -η • Kᗮ.starProjection (ζ ω)
  set L : E →L[ℝ] E := (Jφ (y + d0) - Jφ y).comp ((-η) • Kᗮ.starProjection)
  set q : Ω → E := fun ω => φ (y + d0 + e ω) - φ (y + d0) - Jφ (y + d0) (e ω)
  have hdec : ∀ ω, φ (y + (d0 + e ω)) - φ y - Jφ y (d0 + e ω) =
      (φ (y + d0) - φ y - Jφ y d0) + L (ζ ω) + q ω := by
    intro ω
    simp only [L, q, e, ContinuousLinearMap.comp_apply, smul_apply,
      sub_apply, map_add, add_assoc]
    abel
  have hem : Measurable e := (Kᗮ.starProjection.continuous.measurable.comp N.meas).const_smul _
  have hqm : Measurable q := by
    have hc := H.φ_cont
    exact ((hc.measurable.comp (measurable_const.add hem)).sub measurable_const).sub
      ((Jφ (y + d0)).continuous.measurable.comp hem)
  have hqb : ∀ ω, ‖q ω‖ ≤ LJ * η ^ 2 * ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 := by
    intro ω
    have := H.φ_taylor (y + d0) (e ω)
    simp only [e, norm_smul, norm_neg, Real.norm_eq_abs, mul_pow, sq_abs] at this
    simp only [q]; linarith
  have hqi : Integrable q p :=
    Integrable.mono' (N.intQ.const_mul (LJ * η ^ 2)) hqm.aestronglyMeasurable
      (Filter.Eventually.of_forall hqb)
  have hLi : Integrable (fun ω => L (ζ ω)) p := L.integrable_comp N.int
  have hint : Integrable (fun ω => φ (y + (d0 + e ω)) - φ y - Jφ y (d0 + e ω)) p := by
    simp_rw [hdec]; exact ((integrable_const _).add hLi).add hqi
  refine ⟨hint, ?_⟩
  change ‖∫ ω, (φ (y + (d0 + e ω)) - φ y - Jφ y (d0 + e ω)) ∂p‖ ≤ _
  simp_rw [hdec]
  have hc : Integrable (fun ω => (φ (y + d0) - φ y - Jφ y d0) + L (ζ ω)) p :=
    (integrable_const _).add hLi
  rw [integral_add hc hqi, integral_add (integrable_const _) hLi, N.clm_mean L, integral_const]
  simp only [probReal_univ, one_smul, add_zero]
  calc _ ≤ ‖φ (y + d0) - φ y - Jφ y d0‖ + ‖∫ ω, q ω ∂p‖ := norm_add_le _ _
    _ ≤ ‖φ (y + d0) - φ y - Jφ y d0‖ + LJ * η ^ 2 * σu ^ 2 := by
        gcongr
        calc ‖∫ ω, q ω ∂p‖ ≤ ∫ ω, ‖q ω‖ ∂p := norm_integral_le_integral_norm _
          _ ≤ ∫ ω, LJ * η ^ 2 * ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 ∂p :=
              integral_mono hqi.norm (N.intQ.const_mul _) hqb
          _ = LJ * η ^ 2 * ∫ ω, ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 ∂p := integral_const_mul _ _
          _ ≤ LJ * η ^ 2 * σu ^ 2 :=
              mul_le_mul_of_nonneg_left N.varQ (mul_nonneg H.LJ_nn (sq_nonneg _))

lemma exp_m {ζ : Ω → E} {σu σv : ℝ} (N : NoiseAt K p ζ σu σv) (y d0 : E) (η : ℝ) :
    Integrable (fun ω => mr K gh Jφ (y + (d0 + -η • Kᗮ.starProjection (ζ ω)))) p ∧
      ‖∫ ω, mr K gh Jφ (y + (d0 + -η • Kᗮ.starProjection (ζ ω))) ∂p - mr K gh Jφ y‖ ≤
        (Luv / μ * Lh + LJ * G + 2 * (Luv / μ) ^ 2 * LJ * G) * ‖d0‖ +
        (G * ρJ + LJ * Lh + Luv / μ * ρh + Luv / μ * G * (2 * (Luv / μ) * ρJ + LJ ^ 2) +
          2 * (Luv / μ) * LJ * (Luv / μ * Lh + LJ * G + 2 * (Luv / μ) ^ 2 * LJ * G)) *
          η ^ 2 * σu ^ 2 := by
  set Lm := Luv / μ * Lh + LJ * G + 2 * (Luv / μ) ^ 2 * LJ * G
  set c2 := G * ρJ + LJ * Lh + Luv / μ * ρh + Luv / μ * G * (2 * (Luv / μ) * ρJ + LJ ^ 2) +
    2 * (Luv / μ) * LJ * Lm
  have hc2 : 0 ≤ c2 := by
    have := H.Lh_nn; have := H.LJ_nn; have := H.G_nn; have := H.Luv_nn; have := H.μpos
    have := H.ρh_nn; have := H.ρJ_nn; positivity
  set e : Ω → E := fun ω => -η • Kᗮ.starProjection (ζ ω)
  set L : E →L[ℝ] E := (Dmr K gh Hh Jφ DJ (y + d0)).comp ((-η) • Kᗮ.starProjection)
  set q : Ω → E := fun ω => mr K gh Jφ (y + d0 + e ω) - mr K gh Jφ (y + d0) -
    Dmr K gh Hh Jφ DJ (y + d0) (e ω)
  have hdec : ∀ ω, mr K gh Jφ (y + (d0 + e ω)) = mr K gh Jφ (y + d0) + L (ζ ω) + q ω := by
    intro ω
    simp only [L, q, e, ContinuousLinearMap.comp_apply, smul_apply, add_assoc]
    abel
  have hem : Measurable e := (Kᗮ.starProjection.continuous.measurable.comp N.meas).const_smul _
  have hqm : Measurable q := by
    have hc := H.mr_cont
    exact ((hc.measurable.comp (measurable_const.add hem)).sub measurable_const).sub
      ((Dmr K gh Hh Jφ DJ (y + d0)).continuous.measurable.comp hem)
  have hqb : ∀ ω, ‖q ω‖ ≤ c2 * η ^ 2 * ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 := by
    intro ω
    have := H.mr_second (y + d0) (e ω)
    simp only [e, norm_smul, norm_neg, Real.norm_eq_abs, mul_pow, sq_abs] at this
    simp only [q]; linarith
  have hqi : Integrable q p :=
    Integrable.mono' (N.intQ.const_mul (c2 * η ^ 2)) hqm.aestronglyMeasurable
      (Filter.Eventually.of_forall hqb)
  have hLi : Integrable (fun ω => L (ζ ω)) p := L.integrable_comp N.int
  have hint : Integrable (fun ω => mr K gh Jφ (y + (d0 + e ω))) p := by
    simp_rw [hdec]; exact ((integrable_const _).add hLi).add hqi
  refine ⟨hint, ?_⟩
  change ‖∫ ω, mr K gh Jφ (y + (d0 + e ω)) ∂p - mr K gh Jφ y‖ ≤ _
  simp_rw [hdec]
  have hc : Integrable (fun ω => mr K gh Jφ (y + d0) + L (ζ ω)) p :=
    (integrable_const _).add hLi
  rw [integral_add hc hqi, integral_add (integrable_const _) hLi, N.clm_mean L, integral_const]
  simp only [probReal_univ, one_smul, add_zero]
  have hq : ‖∫ ω, q ω ∂p‖ ≤ c2 * η ^ 2 * σu ^ 2 :=
    calc ‖∫ ω, q ω ∂p‖ ≤ ∫ ω, ‖q ω‖ ∂p := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, c2 * η ^ 2 * ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 ∂p :=
          integral_mono hqi.norm (N.intQ.const_mul _) hqb
      _ = c2 * η ^ 2 * ∫ ω, ‖Kᗮ.starProjection (ζ ω)‖ ^ 2 ∂p := integral_const_mul _ _
      _ ≤ c2 * η ^ 2 * σu ^ 2 := mul_le_mul_of_nonneg_left N.varQ (by positivity)
  have hl := H.mr_lip (y + d0) y
  rw [add_sub_cancel_left] at hl
  calc _ = ‖(mr K gh Jφ (y + d0) - mr K gh Jφ y) + ∫ ω, q ω ∂p‖ := by congr 1; abel
    _ ≤ ‖mr K gh Jφ (y + d0) - mr K gh Jφ y‖ + ‖∫ ω, q ω ∂p‖ := norm_add_le _ _
    _ ≤ Lm * ‖d0‖ + c2 * η ^ 2 * σu ^ 2 := add_le_add hl hq

end Model

end OracleTemplate.RiverValley
