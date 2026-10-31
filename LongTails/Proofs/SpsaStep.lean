import LongTails.Proofs.SpsaMoments
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpsaStep

open OracleTemplate.ClippedSpsa LongTails.Proofs.RademacherDirections
  LongTails.Proofs.ClippedScalarDescent LongTails.Proofs.SpsaMoments

variable {d : ℕ}

lemma add_rpow_le_two_mul {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 1 ≤ p) :
    (x + y) ^ p ≤ 2 ^ (p - 1) * (x ^ p + y ^ p) := by
  have hc := (convexOn_rpow hp).2 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr hy)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hc
  have e : 1 / 2 * x + 1 / 2 * y = (x + y) / 2 := by ring
  rw [e, Real.div_rpow (by positivity) (by norm_num)] at hc
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  have e2 : (2 : ℝ) ^ p = 2 * 2 ^ (p - 1) := by
    calc (2 : ℝ) ^ p = 2 ^ ((1 : ℝ) + (p - 1)) := by congr 1; ring
      _ = 2 ^ (1 : ℝ) * 2 ^ (p - 1) := Real.rpow_add (by norm_num) _ _
      _ = 2 * 2 ^ (p - 1) := by rw [Real.rpow_one]
  rw [div_le_iff₀ h2, e2] at hc
  nlinarith [Real.rpow_nonneg hx p, Real.rpow_nonneg hy p, Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (p - 1)]

lemma rpow_add_le_add_rpow {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 1 ≤ p) :
    x ^ p + y ^ p ≤ (x + y) ^ p := by
  have e : ∀ z : ℝ, 0 ≤ z → z ^ p = z * z ^ (p - 1) := fun z hz => by
    rcases hz.lt_or_eq with hz | hz
    · calc z ^ p = z ^ ((1 : ℝ) + (p - 1)) := by congr 1; ring
        _ = z ^ (1 : ℝ) * z ^ (p - 1) := Real.rpow_add hz _ _
        _ = z * z ^ (p - 1) := by rw [Real.rpow_one]
    · subst hz; rw [Real.zero_rpow (by linarith), zero_mul]
  rw [e x hx, e y hy, e (x + y) (by positivity)]
  have h1 : x ^ (p - 1) ≤ (x + y) ^ (p - 1) := Real.rpow_le_rpow hx (by linarith) (by linarith)
  have h2 : y ^ (p - 1) ≤ (x + y) ^ (p - 1) := Real.rpow_le_rpow hy (by linarith) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h1 hx, mul_le_mul_of_nonneg_left h2 hy]

lemma two_point_remainder {φ : Point d → ℝ} {g : Point d → Point d} {L : ℝ}
    (hφ : ∀ y, HasGradientAt φ (g y) y) (hlip : ∀ y y', ‖g y - g y'‖ ≤ L * ‖y - y'‖)
    (x u : Point d) {μ0 : ℝ} (hμ0 : 0 < μ0) :
    |(φ (x + μ0 • u) - φ (x - μ0 • u)) / (2 * μ0) - ⟪g x, u⟫| ≤ L * μ0 * ‖u‖ ^ 2 / 2 := by
  have up := fun y => OracleTemplate.Gradient.smooth_upper_bound hφ hlip x y
  have hneg : ∀ y, HasGradientAt (fun z => -φ z) (-g y) y := fun y => by
    rw [hasGradientAt_iff_hasFDerivAt, map_neg]; exact (hφ y).hasFDerivAt.neg
  have hlipn : ∀ y y', ‖-g y - -g y'‖ ≤ L * ‖y - y'‖ := fun y y' => by
    rw [neg_sub_neg, norm_sub_rev]; exact hlip y y'
  have lo := fun y => OracleTemplate.Gradient.smooth_upper_bound hneg hlipn x y
  have h1 := up (x + μ0 • u)
  have h2 := up (x - μ0 • u)
  have h3 := lo (x + μ0 • u)
  have h4 := lo (x - μ0 • u)
  simp only [add_sub_cancel_left, sub_sub_cancel_left, inner_smul_right, inner_neg_right,
    inner_neg_left, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos hμ0] at h1 h2 h3 h4
  rw [abs_le]
  have h2μ : 0 < 2 * μ0 := by linarith
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ h2μ]; nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ h2μ]; nlinarith

section Expect

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

lemma integral_prod_signLaw {h : Sign d × Ω → ℝ} (hh : Integrable h ((signLaw d).prod ν)) :
    ∫ z, h z ∂((signLaw d).prod ν) = (∑ s, ∫ ω, h (s, ω) ∂ν) / 2 ^ d := by
  rw [integral_prod _ hh, integral_signLaw]

lemma integral_fst_signLaw (h : Sign d → ℝ) :
    ∫ z, h z.1 ∂((signLaw d).prod ν) = (∑ s, h s) / 2 ^ d := by
  rw [integral_fun_fst, integral_signLaw]
  simp

lemma measurable_on_signs {β : Type*} [MeasurableSpace β] (h : Sign d → β) : Measurable h :=
  measurable_of_countable h

end Expect

section Instance

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

noncomputable def diffQuot (F : Point d → Ω → ℝ) (μ0 : ℝ) (x : Point d) (z : Sign d × Ω) : ℝ :=
  (F (x + μ0 • signVec z.1) z.2 - F (x - μ0 • signVec z.1) z.2) / (2 * μ0)

structure SampleHyp (ν : Measure Ω) (F : Point d → Ω → ℝ) (G : Point d → Ω → Point d)
    (L σ p : ℝ) : Prop where
  measF : Measurable (Function.uncurry F)
  measG : Measurable (Function.uncurry G)
  grad : ∀ ω y, HasGradientAt (fun y => F y ω) (G y ω) y
  lip : ∀ ω y y', ‖G y ω - G y' ω‖ ≤ L * ‖y - y'‖
  int : ∀ x, Integrable (G x) ν
  mom_int : ∀ x, Integrable (fun ω => ‖G x ω - ∫ ω', G x ω' ∂ν‖ ^ p) ν
  mom : ∀ x, ∫ ω, ‖G x ω - ∫ ω', G x ω' ∂ν‖ ^ p ∂ν ≤ σ ^ p

variable {F : Point d → Ω → ℝ} {G : Point d → Ω → Point d} {L σ p μ0 : ℝ}

omit [IsProbabilityMeasure ν] in
lemma SampleHyp.measurable_diffQuot (H : SampleHyp ν F G L σ p) (x : Point d) :
    Measurable (diffQuot F μ0 x) := by
  unfold diffQuot
  have hu : Measurable (fun z : Sign d × Ω => signVec z.1) :=
    (measurable_on_signs (fun s : Sign d => signVec s)).comp measurable_fst
  have h1 : Measurable (fun z : Sign d × Ω => F (x + μ0 • signVec z.1) z.2) :=
    H.measF.comp ((measurable_const.add (hu.const_smul μ0)).prodMk measurable_snd)
  have h2 : Measurable (fun z : Sign d × Ω => F (x - μ0 • signVec z.1) z.2) :=
    H.measF.comp ((measurable_const.sub (hu.const_smul μ0)).prodMk measurable_snd)
  exact (h1.sub h2).div_const _

omit [IsProbabilityMeasure ν] in
lemma SampleHyp.remainder (H : SampleHyp ν F G L σ p) (hμ0 : 0 < μ0) (x : Point d)
    (z : Sign d × Ω) :
    |diffQuot F μ0 x z - ⟪G x z.2, signVec z.1⟫| ≤ L * μ0 * d / 2 := by
  have h := two_point_remainder (φ := fun y => F y z.2) (g := fun y => G y z.2)
    (H.grad z.2) (H.lip z.2) x (signVec z.1) hμ0
  rwa [norm_sq_signVec] at h

lemma SampleHyp.mean_zero (H : SampleHyp ν F G L σ p) (x : Point d) :
    ∫ ω, (G x ω - ∫ ω', G x ω' ∂ν) ∂ν = 0 := by
  rw [integral_sub (H.int x) (integrable_const _), integral_const]; simp

theorem SampleHyp.moment_hyp (H : SampleHyp ν F G L σ p) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (hL : 0 ≤ L) (hμ0 : 0 < μ0) (x : Point d) :
    MomentHyp ((signLaw d).prod ν)
      (fun z => ⟪∫ ω, G x ω ∂ν, signVec z.1⟫)
      (fun z => diffQuot F μ0 x z - ⟪∫ ω, G x ω ∂ν, signVec z.1⟫)
      ‖∫ ω, G x ω ∂ν‖ (L * μ0 * d / 2) (2 * (σ + L * μ0 * d / 2)) p := by
  set a := ∫ ω, G x ω ∂ν with ha
  set ρ := L * μ0 * d / 2 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hp0 : 0 < p := by linarith
  set ζ : Ω → Point d := fun ω => G x ω - a with hζ
  have hζi : Integrable ζ ν := (H.int x).sub (integrable_const _)
  have hζm : Measurable ζ := (H.measG.comp (measurable_const.prodMk measurable_id)).sub_const _
  have hζ0 : ∫ ω, ζ ω ∂ν = 0 := H.mean_zero x
  have hζp : Integrable (fun ω => ‖ζ ω‖ ^ p) ν := H.mom_int x
  have hζpm : ∫ ω, ‖ζ ω‖ ^ p ∂ν ≤ σ ^ p := H.mom x
  set μZ := (signLaw d).prod ν
  set A : Sign d × Ω → ℝ := fun z => ⟪a, signVec z.1⟫
  set W : Sign d × Ω → ℝ := fun z => ⟪ζ z.2, signVec z.1⟫
  set r : Sign d × Ω → ℝ := fun z => diffQuot F μ0 x z - ⟪G x z.2, signVec z.1⟫
  have hV : ∀ z, diffQuot F μ0 x z - A z = W z + r z := by
    intro z; simp only [A, W, r, ζ, inner_sub_left]; ring
  have hr : ∀ z, |r z| ≤ ρ := fun z => H.remainder hμ0 x z
  have hAm : Measurable A := (measurable_on_signs (fun s : Sign d => ⟪a, signVec s⟫)).comp measurable_fst
  have hum : Measurable (fun z : Sign d × Ω => signVec z.1) :=
    (measurable_on_signs (fun s : Sign d => signVec s)).comp measurable_fst
  have hWm : Measurable W := (hζm.comp measurable_snd).inner hum
  have hdm := H.measurable_diffQuot (μ0 := μ0) x
  have hVm : Measurable (fun z => diffQuot F μ0 x z - A z) := hdm.sub hAm
  have hrm : Measurable r := hdm.sub ((H.measG.comp (measurable_const.prodMk measurable_snd)).inner hum)
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hAbd : ∀ z, |A z| ≤ ‖a‖ * Real.sqrt d := fun z =>
    (abs_real_inner_le_norm _ _).trans (by rw [norm_signVec])
  have hWbd : ∀ z, |W z| ≤ ‖ζ z.2‖ * Real.sqrt d := fun z =>
    (abs_real_inner_le_norm _ _).trans (by rw [norm_signVec])
  have hζn : Integrable (fun ω => ‖ζ ω‖) ν := hζi.norm
  have hζpd : ∀ ω, ∀ s : Sign d, |⟪ζ ω, signVec s⟫| ^ p ≤ Real.sqrt d ^ p * ‖ζ ω‖ ^ p := by
    intro ω s
    rw [← Real.mul_rpow hsd (norm_nonneg _)]
    exact Real.rpow_le_rpow (abs_nonneg _) ((abs_real_inner_le_norm _ _).trans
      (by rw [norm_signVec, mul_comm])) hp0.le
  have hWpi_s : ∀ s : Sign d, Integrable (fun ω => |⟪ζ ω, signVec s⟫| ^ p) ν := by
    intro s
    refine Integrable.mono' (hζp.const_mul (Real.sqrt d ^ p))
      ((measurable_abs_comp (hζm.inner measurable_const)).pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hζpd ω s
  have hWpi : Integrable (fun z : Sign d × Ω => |W z| ^ p) μZ := by
    refine Integrable.mono' ((hζp.comp_snd (signLaw d)).const_mul (Real.sqrt d ^ p))
      ((measurable_abs_comp hWm).pow_const p).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hζpd z.2 z.1
  have hWp : ∫ z, |W z| ^ p ∂μZ ≤ σ ^ p := by
    rw [integral_prod_signLaw hWpi]
    simp only [W]
    rw [← integral_finsetSum _ (fun s _ => hWpi_s s), ← integral_div]
    refine (integral_mono ((integrable_finsetSum _ (fun s _ => hWpi_s s)).div_const _)
      hζp (fun ω => avg_abs_inner_rpow (ζ ω) hp0 hp2)).trans hζpm
  have hWApi_s : ∀ s : Sign d, Integrable (fun ω => |⟪ζ ω, signVec s⟫ * ⟪a, signVec s⟫| ^ p) ν := by
    intro s
    refine Integrable.mono' ((hWpi_s s).mul_const (|⟪a, signVec s⟫| ^ p))
      ((measurable_abs_comp ((hζm.inner measurable_const).mul measurable_const)).pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have hWApi : Integrable (fun z : Sign d × Ω => |W z * A z| ^ p) μZ := by
    refine Integrable.mono' (((hζp.comp_snd (signLaw d)).const_mul (Real.sqrt d ^ p)).mul_const
      ((‖a‖ * Real.sqrt d) ^ p)) ((measurable_abs_comp (hWm.mul hAm)).pow_const p).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    exact mul_le_mul (hζpd z.2 z.1) (Real.rpow_le_rpow (abs_nonneg _) (hAbd z) hp0.le)
      (by positivity) (by positivity)
  have hWAp : ∫ z, |W z * A z| ^ p ∂μZ ≤ (Real.sqrt 3 * ‖a‖) ^ p * σ ^ p := by
    rw [integral_prod_signLaw hWApi]
    simp only [W, A]
    rw [← integral_finsetSum _ (fun s _ => hWApi_s s), ← integral_div]
    have hpt : ∀ ω, (∑ s, |⟪ζ ω, signVec s⟫ * ⟪a, signVec s⟫| ^ p) / 2 ^ d ≤
        (Real.sqrt 3 * ‖a‖) ^ p * ‖ζ ω‖ ^ p := by
      intro ω
      refine (avg_abs_inner_mul_rpow (ζ ω) a hp0 hp2).trans (le_of_eq ?_)
      rw [← Real.mul_rpow (by positivity) (norm_nonneg _)]; ring_nf
    refine (integral_mono ((integrable_finsetSum _ (fun s _ => hWApi_s s)).div_const _)
      (hζp.const_mul _) hpt).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hζpm (by positivity)
  have hApi : Integrable (fun z : Sign d × Ω => |A z| ^ p) μZ :=
    (show Integrable (fun s : Sign d => |⟪a, signVec s⟫| ^ p) (signLaw d) from Integrable.of_finite).comp_fst ν
  have hAp : ∫ z, |A z| ^ p ∂μZ ≤ ‖a‖ ^ p := by
    have h := integral_fst_signLaw (ν := ν) (fun s => |⟪a, signVec s⟫| ^ p)
    rw [h]
    exact avg_abs_inner_rpow a hp0 hp2
  have hA1 : ∫ z, |A z| ∂μZ ≤ ‖a‖ := by
    have h := integral_fst_signLaw (ν := ν) (fun s => |⟪a, signVec s⟫|)
    rw [h]
    have := avg_abs_inner_rpow a zero_lt_one one_le_two
    simpa using this
  have hAi : Integrable (fun z : Sign d × Ω => |A z|) μZ :=
    (show Integrable (fun s : Sign d => |⟪a, signVec s⟫|) (signLaw d) from Integrable.of_finite).comp_fst ν
  have hWAi : Integrable (fun z : Sign d × Ω => W z * A z) μZ := by
    refine Integrable.mono' (((hζn.comp_snd (signLaw d)).mul_const (Real.sqrt d)).mul_const
      (‖a‖ * Real.sqrt d)) (hWm.mul hAm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((hWbd z).trans_eq (by ring)) (hAbd z) (abs_nonneg _) (by positivity)
  have hrAi : Integrable (fun z : Sign d × Ω => r z * A z) μZ := by
    refine Integrable.mono' (hAi.const_mul ρ) (hrm.mul hAm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hr z) (abs_nonneg _)
  have hWA0 : ∫ z, W z * A z ∂μZ = 0 := by
    rw [integral_prod_signLaw hWAi]
    simp only [W, A]
    have hz : ∀ s : Sign d, ∫ ω, ⟪ζ ω, signVec s⟫ * ⟪a, signVec s⟫ ∂ν = 0 := by
      intro s
      rw [integral_mul_const]
      have : ∫ ω, ⟪ζ ω, signVec s⟫ ∂ν = 0 := by
        simp_rw [real_inner_comm (signVec s)]
        rw [integral_inner hζi, hζ0, inner_zero_right]
      rw [this, zero_mul]
    simp [hz]
  have hrA : -(ρ * ‖a‖) ≤ ∫ z, r z * A z ∂μZ := by
    have hm := integral_mono (show Integrable (fun z => -(ρ * |A z|)) μZ from (hAi.const_mul ρ).neg)
      hrAi (fun z => by
      have h1 := hr z
      have := abs_le.mp (show |r z * A z| ≤ ρ * |A z| by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
      simp only; linarith [this.1])
    rw [integral_neg, integral_const_mul] at hm
    nlinarith [hA1]
  have hVA : ∀ z, (diffQuot F μ0 x z - A z) * A z = W z * A z + r z * A z := fun z => by
    rw [hV z]; ring
  have hVbd : ∀ z, |diffQuot F μ0 x z - A z| ≤ |W z| + ρ := fun z => by
    rw [hV z]; exact (abs_add_le _ _).trans (by linarith [hr z])
  have hVAbd : ∀ z, |(diffQuot F μ0 x z - A z) * A z| ≤ |W z * A z| + ρ * |A z| := fun z => by
    rw [abs_mul, abs_mul]
    nlinarith [hVbd z, abs_nonneg (A z), abs_nonneg (W z)]
  have hp1' : 1 ≤ p := hp1.le
  have h2p : (2 : ℝ) ^ (p - 1) ≤ 2 ^ p :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hVpi : Integrable (fun z => |diffQuot F μ0 x z - A z| ^ p) μZ := by
    refine Integrable.mono' ((iadd hWpi (integrable_const (ρ ^ p))).const_mul (2 ^ (p - 1)))
      ((measurable_abs_comp hVm).pow_const p).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (Real.rpow_le_rpow (abs_nonneg _) (hVbd z) hp0.le).trans
      (add_rpow_le_two_mul (abs_nonneg _) hρ0 hp1')
  have hVAm : Measurable (fun z => (diffQuot F μ0 x z - A z) * A z) := hVm.mul hAm
  have hVApi : Integrable (fun z => |(diffQuot F μ0 x z - A z) * A z| ^ p) μZ := by
    refine Integrable.mono' ((iadd hWApi (hApi.const_mul (ρ ^ p))).const_mul (2 ^ (p - 1)))
      ((measurable_abs_comp hVAm).pow_const p).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine (Real.rpow_le_rpow (abs_nonneg _) (hVAbd z) hp0.le).trans ?_
    refine (add_rpow_le_two_mul (abs_nonneg _) (by positivity) hp1').trans (le_of_eq ?_)
    rw [Real.mul_rpow hρ0 (abs_nonneg _)]
  have hsum : σ ^ p + ρ ^ p ≤ (σ + ρ) ^ p := rpow_add_le_add_rpow hσ hρ0 hp1'
  have hS2 : (2 * (σ + ρ)) ^ p = 2 ^ p * (σ + ρ) ^ p := Real.mul_rpow (by norm_num) (by positivity)
  refine ⟨hAm, hVm, ⟨‖a‖ * Real.sqrt d, hAbd⟩, ?_, ?_, ?_, ?_, hVpi, ?_, hVApi, ?_⟩
  · have h := integral_fst_signLaw (ν := ν) (fun s => ⟪a, signVec s⟫ ^ 2)
    rw [h]
    have := avg_inner_mul a a
    simp only [← sq, real_inner_self_eq_norm_sq] at this
    exact this
  · have h := integral_fst_signLaw (ν := ν) (fun s => ⟪a, signVec s⟫ ^ 4)
    rw [h]
    have := avg_inner_sq_mul_sq a a
    have e : ∀ s : Sign d, ⟪a, signVec s⟫ ^ 2 * ⟪a, signVec s⟫ ^ 2 = ⟪a, signVec s⟫ ^ 4 :=
      fun s => by ring
    simp only [e] at this
    linarith [show 3 * (‖a‖ ^ 2 * ‖a‖ ^ 2) = 3 * ‖a‖ ^ 4 by ring]
  · exact (hWAi.add hrAi).congr (Filter.Eventually.of_forall fun z => (hVA z).symm)
  · rw [integral_congr_ae (Filter.Eventually.of_forall hVA), integral_add hWAi hrAi, hWA0]
    linarith
  · have hm := integral_mono hVpi ((iadd hWpi (integrable_const (ρ ^ p))).const_mul (2 ^ (p - 1)))
      (fun z => (Real.rpow_le_rpow (abs_nonneg _) (hVbd z) hp0.le).trans
        (add_rpow_le_two_mul (abs_nonneg _) hρ0 hp1'))
    rw [integral_const_mul, integral_add hWpi (integrable_const _), integral_const] at hm
    simp only [probReal_univ, one_smul] at hm
    rw [hS2]
    have hp2nn : (0 : ℝ) ≤ 2 ^ (p - 1) := by positivity
    calc _ ≤ 2 ^ (p - 1) * (∫ z, |W z| ^ p ∂μZ + ρ ^ p) := hm
      _ ≤ 2 ^ (p - 1) * (σ ^ p + ρ ^ p) := mul_le_mul_of_nonneg_left (by linarith) hp2nn
      _ ≤ 2 ^ (p - 1) * (σ + ρ) ^ p := mul_le_mul_of_nonneg_left hsum hp2nn
      _ ≤ 2 ^ p * (σ + ρ) ^ p := mul_le_mul_of_nonneg_right h2p (by positivity)
  · have hm := integral_mono hVApi ((iadd hWApi (hApi.const_mul (ρ ^ p))).const_mul (2 ^ (p - 1)))
      (fun z => by
        refine (Real.rpow_le_rpow (abs_nonneg _) (hVAbd z) hp0.le).trans ?_
        refine (add_rpow_le_two_mul (abs_nonneg _) (by positivity) hp1').trans (le_of_eq ?_)
        rw [Real.mul_rpow hρ0 (abs_nonneg _)])
    rw [integral_const_mul, integral_add hWApi (hApi.const_mul _), integral_const_mul] at hm
    have hs3 : (1 : ℝ) ≤ Real.sqrt 3 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    have hA3 : ‖a‖ ^ p ≤ (Real.sqrt 3 * ‖a‖) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) (le_mul_of_one_le_left (norm_nonneg _) hs3) hp0.le
    have hp2nn : (0 : ℝ) ≤ 2 ^ (p - 1) := by positivity
    have hk : 0 ≤ (Real.sqrt 3 * ‖a‖) ^ p := by positivity
    have e : (Real.sqrt 3 * (2 * (σ + ρ)) * ‖a‖) ^ p =
        2 ^ p * ((Real.sqrt 3 * ‖a‖) ^ p * (σ + ρ) ^ p) := by
      rw [show Real.sqrt 3 * (2 * (σ + ρ)) * ‖a‖ = 2 * ((Real.sqrt 3 * ‖a‖) * (σ + ρ)) by ring,
        Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
    rw [e]
    calc _ ≤ 2 ^ (p - 1) * (∫ z, |W z * A z| ^ p ∂μZ + ρ ^ p * ∫ z, |A z| ^ p ∂μZ) := hm
      _ ≤ 2 ^ (p - 1) * ((Real.sqrt 3 * ‖a‖) ^ p * σ ^ p + ρ ^ p * (Real.sqrt 3 * ‖a‖) ^ p) := by
          refine mul_le_mul_of_nonneg_left (add_le_add hWAp ?_) hp2nn
          exact mul_le_mul_of_nonneg_left (hAp.trans hA3) (by positivity)
      _ = 2 ^ (p - 1) * ((Real.sqrt 3 * ‖a‖) ^ p * (σ ^ p + ρ ^ p)) := by ring
      _ ≤ 2 ^ (p - 1) * ((Real.sqrt 3 * ‖a‖) ^ p * (σ + ρ) ^ p) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hk) hp2nn
      _ ≤ 2 ^ p * ((Real.sqrt 3 * ‖a‖) ^ p * (σ + ρ) ^ p) :=
          mul_le_mul_of_nonneg_right h2p (by positivity)

end Instance

section Descent

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
  {F : Point d → Ω → ℝ} {G : Point d → Ω → Point d} {L σ p μ0 : ℝ}

lemma SampleHyp.gradient_lipschitz (H : SampleHyp ν F G L σ p) {f : Point d → ℝ}
    (hmean : ∀ x, ∫ ω, G x ω ∂ν = gradient f x) (y y' : Point d) :
    ‖gradient f y - gradient f y'‖ ≤ L * ‖y - y'‖ := by
  rw [← hmean y, ← hmean y', ← integral_sub (H.int y) (H.int y')]
  refine (norm_integral_le_integral_norm _).trans ?_
  have := integral_mono ((H.int y).sub (H.int y')).norm (integrable_const (L * ‖y - y'‖))
    (fun ω => H.lip ω y y')
  simpa using this

noncomputable def stepPoint (F : Point d → Ω → ℝ) (μ0 η c : ℝ) (x : Point d) (z : Sign d × Ω) :
    Point d :=
  x - η • (clipScalar c (diffQuot F μ0 x z) • signVec z.1)

noncomputable def phiFun (c t : ℝ) : ℝ := min (t ^ 2 / 2) (c * t / 128)

noncomputable def biasLevel (L σ p μ0 c : ℝ) (d : ℕ) : ℝ :=
  L * μ0 * d / 2 + Real.sqrt 3 * (2 * (σ + L * μ0 * d / 2)) *
    (2 * (2 * (σ + L * μ0 * d / 2)) / c) ^ (p - 1)

lemma abs_le_of_sandwich {y fx u v M1 M2 : ℝ} (h1 : y ≤ fx - u + v) (h2 : fx - u - v ≤ y)
    (hu : |u| ≤ M1) (hv : v ≤ M2) : |y| ≤ |fx| + M1 + M2 := by
  rw [abs_le] at hu ⊢
  constructor <;> linarith [neg_abs_le fx, le_abs_self fx]

lemma descent_algebra {η L d α B W c I1 I2 : ℝ} (hη0 : 0 ≤ η) (hL : 0 < L) (hdd : 0 ≤ d)
    (hα0 : 0 ≤ α) (hW0 : 0 ≤ W) (hc0 : 0 < c) (hLηd : L * η * d ≤ 1 / 8192)
    (hB : 512 * B ≤ c) (hI1 : phiFun c α - α * B ≤ I1) (hI2a : I2 ≤ c ^ 2)
    (hI2b : I2 ≤ 2 * α ^ 2 + 2 * W) :
    -(η * I1) + L / 2 * η ^ 2 * d * I2 ≤
      -(η / 4 * phiFun c α) + 2 * η * B ^ 2 + L * η ^ 2 * d * W := by
  have hc0' : 0 ≤ c := hc0.le
  have hη2 : 0 ≤ η ^ 2 := sq_nonneg η
  have hηB : 0 ≤ η * B ^ 2 := mul_nonneg hη0 (sq_nonneg B)
  have hLW : 0 ≤ L * η ^ 2 * d * W := mul_nonneg (mul_nonneg (mul_nonneg hL.le hη2) hdd) hW0
  rcases le_total α (c / 64) with hsm | hlg
  · have hφ : phiFun c α = α ^ 2 / 2 := by
      unfold phiFun; apply min_eq_left
      have : α * α ≤ c / 64 * α := mul_le_mul_of_nonneg_right hsm hα0
      have e1 : α ^ 2 / 2 = α * α / 2 := by ring
      have e2 : c * α / 128 = c / 64 * α / 2 := by ring
      rw [e1, e2]; linarith
    rw [hφ] at hI1 ⊢
    have hI2 := hI2b
    have h1 : L / 2 * η ^ 2 * d * I2 ≤ L * η ^ 2 * d * α ^ 2 + L * η ^ 2 * d * W := by
      have := mul_le_mul_of_nonneg_left hI2 (by positivity : (0 : ℝ) ≤ L / 2 * η ^ 2 * d)
      have e : L / 2 * η ^ 2 * d * (2 * α ^ 2 + 2 * W) =
          L * η ^ 2 * d * α ^ 2 + L * η ^ 2 * d * W := by ring
      linarith
    have h2 : L * η ^ 2 * d * α ^ 2 ≤ η * α ^ 2 / 8192 := by
      have e : L * η ^ 2 * d * α ^ 2 = (L * η * d) * (η * α ^ 2) := by ring
      have := mul_le_mul_of_nonneg_right hLηd (by positivity : (0 : ℝ) ≤ η * α ^ 2)
      linarith
    have h3 : α * B ≤ α ^ 2 / 8 + 2 * B ^ 2 := by
      have hsq' := sq_nonneg (α / 4 - B)
      have e : (α / 4 - B) ^ 2 = α ^ 2 / 16 - α * B / 2 + B ^ 2 := by ring
      linarith
    have h4 := mul_le_mul_of_nonneg_left hI1 hη0
    have h5 := mul_le_mul_of_nonneg_left h3 hη0
    have hηα : 0 ≤ η * α ^ 2 := by positivity
    have e1 : η * (α ^ 2 / 2 - α * B) = η * α ^ 2 / 2 - η * (α * B) := by ring
    have e2 : η * (α ^ 2 / 8 + 2 * B ^ 2) = η * α ^ 2 / 8 + 2 * (η * B ^ 2) := by ring
    have e3 : η / 4 * (α ^ 2 / 2) = η * α ^ 2 / 8 := by ring
    have e4 : 2 * η * B ^ 2 = 2 * (η * B ^ 2) := by ring
    rw [e3, e4]
    linarith
  · have hφ : phiFun c α = c * α / 128 := by
      unfold phiFun; apply min_eq_right
      have : c / 64 * α ≤ α * α := mul_le_mul_of_nonneg_right hlg hα0
      have e1 : α ^ 2 / 2 = α * α / 2 := by ring
      have e2 : c * α / 128 = c / 64 * α / 2 := by ring
      rw [e1, e2]; linarith
    rw [hφ] at hI1 ⊢
    have hI2 := hI2a
    have h1 : L / 2 * η ^ 2 * d * I2 ≤ L / 2 * η ^ 2 * d * c ^ 2 :=
      mul_le_mul_of_nonneg_left hI2 (by positivity)
    have hc2 : c ^ 2 ≤ 64 * c * α := by
      have := mul_le_mul_of_nonneg_left (show c ≤ 64 * α by linarith) hc0'
      have e : c ^ 2 = c * c := sq c
      have e' : c * (64 * α) = 64 * c * α := by ring
      linarith
    have h2 : L / 2 * η ^ 2 * d * c ^ 2 ≤ η * c * α / 256 := by
      have e : L / 2 * η ^ 2 * d * c ^ 2 = (L * η * d) * (η * c ^ 2 / 2) := by ring
      have h6 := mul_le_mul_of_nonneg_right hLηd (by positivity : (0 : ℝ) ≤ η * c ^ 2 / 2)
      have h7 := mul_le_mul_of_nonneg_left hc2 (by positivity : (0 : ℝ) ≤ η / 16384)
      have e2 : 1 / 8192 * (η * c ^ 2 / 2) = η / 16384 * c ^ 2 := by ring
      have e3 : η / 16384 * (64 * c * α) = η * c * α / 256 := by ring
      linarith
    have h3 : α * B ≤ c * α / 512 := by
      have hB' : B ≤ c / 512 := by linarith
      have := mul_le_mul_of_nonneg_left hB' hα0
      have e : α * (c / 512) = c * α / 512 := by ring
      linarith
    have h4 := mul_le_mul_of_nonneg_left hI1 hη0
    have h5 := mul_le_mul_of_nonneg_left h3 hη0
    have e1 : η * (c * α / 128 - α * B) = η * c * α / 128 - η * (α * B) := by ring
    have e2 : η * (c * α / 512) = η * c * α / 512 := by ring
    have e3 : η / 4 * (c * α / 128) = η * c * α / 512 := by ring
    rw [e3]
    linarith


theorem SampleHyp.expected_descent (H : SampleHyp ν F G L σ p) {f : Point d → ℝ}
    (hf : ∀ x, HasGradientAt f (gradient f x) x) (hmean : ∀ x, ∫ ω, G x ω ∂ν = gradient f x)
    (hd : 0 < d) (hp1 : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hL : 0 < L) (hμ0 : 0 < μ0) {c η : ℝ}
    (hS : 256 * (2 * (σ + L * μ0 * d / 2)) ≤ c) (hB : 512 * biasLevel L σ p μ0 c d ≤ c)
    (hη0 : 0 ≤ η) (hη : η * (8192 * L * d) ≤ 1) (x : Point d) :
    Integrable (fun z => f (stepPoint F μ0 η c x z)) ((signLaw d).prod ν) ∧
      ∫ z, f (stepPoint F μ0 η c x z) ∂((signLaw d).prod ν) ≤
        f x - η / 4 * phiFun c ‖gradient f x‖ + 2 * η * biasLevel L σ p μ0 c d ^ 2 +
          L * η ^ 2 * d * (c ^ (2 - p) * (2 * (σ + L * μ0 * d / 2)) ^ p) := by
  set ρ := L * μ0 * d / 2 with hρ
  set S := 2 * (σ + ρ) with hSdef
  set B := biasLevel L σ p μ0 c d with hBdef
  set μZ := (signLaw d).prod ν
  have hρ0 : 0 ≤ ρ := by positivity
  have hS0 : 0 < S := by
    have : 0 < ρ := by
      have : (0 : ℝ) < d := by exact_mod_cast hd
      positivity
    linarith
  have hc0 : 0 < c := by linarith
  have hM := H.moment_hyp hp1 hp2 hσ hL.le hμ0 x
  rw [hmean x] at hM
  have hlow := hM.clipped_inner_lower hp1 (norm_nonneg _) hρ0 hS0 hS
  have hsq := hM.clipped_sq_upper hp1 hp2 hc0
  have hDA : ∀ z : Sign d × Ω,
      ⟪gradient f x, signVec z.1⟫ + (diffQuot F μ0 x z - ⟪gradient f x, signVec z.1⟫) = diffQuot F μ0 x z :=
    fun z => by ring
  simp only [hDA] at hlow hsq
  set ψ : Sign d × Ω → ℝ := fun z => clipScalar c (diffQuot F μ0 x z) with hψ
  set A : Sign d × Ω → ℝ := fun z => ⟪gradient f x, signVec z.1⟫ with hA
  have hlip := H.gradient_lipschitz hmean
  have hnlip : ∀ y y', ‖-gradient f y - -gradient f y'‖ ≤ L * ‖y - y'‖ := fun y y' => by
    rw [neg_sub_neg, norm_sub_rev]; exact hlip y y'
  have hneg : ∀ y, HasGradientAt (fun z => -f z) (-gradient f y) y := fun y => by
    rw [hasGradientAt_iff_hasFDerivAt, map_neg]; exact (hf y).hasFDerivAt.neg
  have hpt : ∀ z, f (stepPoint F μ0 η c x z) ≤
      f x - η * (ψ z * A z) + L / 2 * η ^ 2 * d * ψ z ^ 2 := by
    intro z
    have h := OracleTemplate.Gradient.smooth_upper_bound hf hlip x (stepPoint F μ0 η c x z)
    simp only [stepPoint, sub_sub_cancel_left, inner_neg_right, inner_smul_right, norm_neg,
      norm_smul, Real.norm_eq_abs] at h
    have hu := norm_sq_signVec z.1
    have e : (|η| * (|clipScalar c (diffQuot F μ0 x z)| * ‖signVec z.1‖)) ^ 2 =
        η ^ 2 * ψ z ^ 2 * d := by
      rw [mul_pow, mul_pow, sq_abs, sq_abs, hu]
      simp only [ψ]
      ring
    rw [e] at h
    simp only [stepPoint, ψ, A] at h ⊢
    linarith
  have hlo : ∀ z, f x - η * (ψ z * A z) - L / 2 * η ^ 2 * d * ψ z ^ 2 ≤
      f (stepPoint F μ0 η c x z) := by
    intro z
    have h := OracleTemplate.Gradient.smooth_upper_bound hneg hnlip x (stepPoint F μ0 η c x z)
    simp only [stepPoint, sub_sub_cancel_left, inner_neg_right, inner_neg_left, inner_smul_right,
      norm_neg, norm_smul, Real.norm_eq_abs] at h
    have hu := norm_sq_signVec z.1
    have e : (|η| * (|clipScalar c (diffQuot F μ0 x z)| * ‖signVec z.1‖)) ^ 2 =
        η ^ 2 * ψ z ^ 2 * d := by
      rw [mul_pow, mul_pow, sq_abs, sq_abs, hu]
      simp only [ψ]
      ring
    rw [e] at h
    simp only [stepPoint, ψ, A] at h ⊢
    linarith
  have hψb : ∀ z, |ψ z| ≤ c := fun z => clip_abs_le hc0.le _
  have hAb : ∀ z, |A z| ≤ ‖gradient f x‖ * Real.sqrt d := fun z =>
    (abs_real_inner_le_norm _ _).trans (by rw [norm_signVec])
  have hψm : Measurable ψ := by
    simp only [ψ, clipScalar]
    exact measurable_const.max (measurable_const.min (H.measurable_diffQuot x))
  have hAm : Measurable A := (measurable_on_signs (fun s : Sign d => ⟪gradient f x, signVec s⟫)).comp measurable_fst
  have hstepm : Measurable (fun z => f (stepPoint F μ0 η c x z)) := by
    have hfc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hf y).hasFDerivAt.continuousAt
    have hum : Measurable (fun z : Sign d × Ω => signVec z.1) :=
      (measurable_on_signs (fun s : Sign d => signVec s)).comp measurable_fst
    exact hfc.measurable.comp (measurable_const.sub ((hψm.smul hum).const_smul η))
  have hstepi : Integrable (fun z => f (stepPoint F μ0 η c x z)) μZ := by
    refine Integrable.of_bound hstepm.aestronglyMeasurable
      (|f x| + η * (c * (‖gradient f x‖ * Real.sqrt d)) + L / 2 * η ^ 2 * d * c ^ 2)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    have h1 : |η * (ψ z * A z)| ≤ η * (c * (‖gradient f x‖ * Real.sqrt d)) := by
      rw [abs_mul, abs_of_nonneg hη0, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hψb z) (hAb z) (abs_nonneg _) hc0.le) hη0
    have h2 : ψ z ^ 2 ≤ c ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hψb z) 2
    have h3 : (0 : ℝ) ≤ L / 2 * η ^ 2 * d := by positivity
    exact abs_le_of_sandwich (hpt z) (hlo z) h1
      (mul_le_mul_of_nonneg_left h2 h3)
  refine ⟨hstepi, ?_⟩
  have hψAi : Integrable (fun z => ψ z * A z) μZ := by
    refine Integrable.of_bound (hψm.mul hAm).aestronglyMeasurable (c * (‖gradient f x‖ * Real.sqrt d))
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul (hψb z) (hAb z) (abs_nonneg _) hc0.le
  have hrhsi : Integrable (fun z => f x - η * (ψ z * A z) + L / 2 * η ^ 2 * d * ψ z ^ 2) μZ :=
    ((integrable_const _).sub (hψAi.const_mul η)).add (hsq.1.const_mul _)
  have hint := integral_mono hstepi hrhsi hpt
  rw [integral_add (isub (integrable_const _) (hψAi.const_mul η)) (hsq.1.const_mul _),
    integral_sub (integrable_const _) (hψAi.const_mul η), integral_const, integral_const_mul,
    integral_const_mul] at hint
  simp only [probReal_univ, one_smul] at hint
  set α := ‖gradient f x‖ with hα
  set I1 := ∫ z, ψ z * A z ∂μZ
  set I2 := ∫ z, ψ z ^ 2 ∂μZ
  set W := c ^ (2 - p) * S ^ p
  have hW0 : 0 ≤ W := by positivity
  have hB0 : 0 ≤ B := by simp only [hBdef, biasLevel]; positivity
  have hα0 : 0 ≤ α := norm_nonneg _
  have hdd : (0 : ℝ) ≤ d := by positivity
  have hBeq : B = ρ + Real.sqrt 3 * S * (2 * S / c) ^ (p - 1) := by
    simp only [hBdef, biasLevel, hρ, hSdef]
  have hI1 : phiFun c α - α * B ≤ I1 := by
    rw [hBeq]; unfold phiFun; exact hlow
  have hLηd : L * η * d ≤ 1 / 8192 := by
    have e : L * η * d * 8192 = η * (8192 * L * d) := by ring
    linarith
  have hη2 : 0 ≤ η ^ 2 := sq_nonneg η
  have hc0' : 0 ≤ c := hc0.le
  have goalform := descent_algebra hη0 hL hdd hα0 hW0 hc0 hLηd hB hI1 hsq.2.1 hsq.2.2
  linarith

end Descent

end LongTails.Proofs.SpsaStep
