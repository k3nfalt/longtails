import LongTails.Algorithms.StochasticGeneralizedMirror
import LongTails.Proofs.GeneralNormClipping
import LongTails.Proofs.RobustPilotConfidence
import LongTails.Proofs.RobustEnergyConcentration
import LongTails.Proofs.NormSubGaussian
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory OracleTemplate
open OracleTemplate.RobustGradient (centeredClip)
open LongTails.Algorithms.StochasticGeneralizedMirror

namespace LongTails.Proofs.GeneralizedMirrorNoise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma residual_moment {B p : ℝ} (hB : 0 < B) (hp : 1 ≤ p) {u : E}
    (hu : ‖u‖ ≤ B / 2) (v : E) :
    ‖v - clip B v‖ ≤ ‖v - u‖ ^ p / (B / 2) ^ (p - 1) := by
  by_cases hv : ‖v‖ ≤ B
  · simp only [clip, ite_eq_left hv, sub_self, norm_zero]
    positivity
  have ht : B / 2 ≤ ‖v - u‖ := by
    have h := norm_sub_norm_le v u
    linarith [lt_of_not_ge hv]
  have he : 0 < ‖v - u‖ := lt_of_lt_of_le (by positivity) ht
  have hr : ‖v - clip B v‖ ≤ ‖v - u‖ := by
    rw [GeneralNormClipping.residual_norm hB.le,
      max_eq_right (by linarith : 0 ≤ ‖v‖ - B)]
    have := norm_sub_norm_le v u
    linarith
  apply hr.trans
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < B / 2) _)).mpr
  have hh := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity : 0 ≤ B / 2) ht (sub_nonneg.mpr hp)) he.le
  calc
    _ ≤ ‖v - u‖ * ‖v - u‖ ^ (p - 1) := hh
    _ = ‖v - u‖ ^ p := by
      nth_rw 1 [← Real.rpow_one ‖v - u‖]
      rw [← Real.rpow_add he]
      congr 1
      ring

lemma centered_error {B : ℝ} (hB : 0 ≤ B) (c u v : E) (hu : ‖u - c‖ ≤ B) :
    ‖centeredClip B c v - u‖ ≤ 2 * ‖v - u‖ := by
  have he : centeredClip B c v - u = clip B (v - c) - clip B (u - c) := by
    rw [show clip B (u - c) = u - c from ite_eq_left hu]
    unfold centeredClip
    abel
  rw [he]
  simpa only [sub_sub_sub_cancel_right] using
    GeneralNormClipping.difference hB (v - c) (u - c)

lemma centered_error_bounded {B : ℝ} (hB : 0 ≤ B) (c u v : E) (hu : ‖c - u‖ ≤ B / 2) :
    ‖centeredClip B c v - u‖ ≤ 3 * B / 2 := by
  have ht := norm_add_le (c - u) (clip B (v - c))
  have he : centeredClip B c v - u = (c - u) + clip B (v - c) := by
    unfold centeredClip
    abel
  rw [he]
  have hb := GeneralNormClipping.norm_le hB (v - c)
  linarith

lemma centered_error_sq {B p : ℝ} (hB : 0 < B) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (c u v : E) (hu : ‖u - c‖ ≤ B) :
    ‖centeredClip B c v - u‖ ^ 2 ≤ 4 * B ^ (2 - p) * ‖v - u‖ ^ p := by
  have he : centeredClip B c v - u = clip B (v - c) - clip B (u - c) := by
    rw [show clip B (u - c) = u - c from ite_eq_left hu]
    unfold centeredClip
    abel
  rw [he]
  simpa only [sub_sub_sub_cancel_right] using
    GeneralNormClipping.difference_sq_moment hB hp hp2 (v - c) (u - c)

lemma centered_residual {B p : ℝ} (hB : 0 < B) (hp : 1 ≤ p)
    (c u v : E) (hu : ‖u - c‖ ≤ B / 2) :
    ‖centeredClip B c v - v‖ ≤ ‖v - u‖ ^ p / (B / 2) ^ (p - 1) := by
  have he : centeredClip B c v - v = -(v - c - clip B (v - c)) := by
    unfold centeredClip
    abel
  rw [he, norm_neg]
  simpa only [sub_sub_sub_cancel_right] using residual_moment hB hp hu (v - c)

lemma pilot_scale {σ B p : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p) (hB : 96 * σ ≤ B) :
    σ ^ p ≤ (B / 6) ^ p / 16 := by
  have ht : 16 * σ ≤ B / 6 := by linarith
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ 16 * σ) ht (by linarith : 0 ≤ p)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) hσ] at h
  have hc := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16) hp
  rw [Real.rpow_one] at hc
  have hm := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hσ p)
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]

lemma measurable_centered (B : ℝ) (c : E) : Measurable (centeredClip B c) :=
  measurable_const.add ((GeneralNormClipping.measurable_clip B).comp
    (measurable_id.sub_const c))

lemma integrable_centered {V : Ω → E} (hV : Measurable V) {B : ℝ} (hB : 0 ≤ B)
    (c : E) : Integrable (fun ω => centeredClip B c (V ω)) P :=
  (integrable_const c).add (GeneralNormClipping.integrable_clip (hV.sub_const c) hB)

lemma centered_bias {V : Ω → E} (hV : Measurable V)
    (hi : Integrable V P) {B p σ : ℝ} (hB : 0 < B) (hp : 1 ≤ p)
    (c u : E) (hu : ‖u - c‖ ≤ B / 2) (hmean : ∫ ω, V ω ∂P = u)
    (hmi : Integrable (fun ω => ‖V ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖V ω - u‖ ^ p ∂P) ≤ σ ^ p) :
    ‖(∫ ω, centeredClip B c (V ω) ∂P) - u‖ ≤ σ ^ p / (B / 2) ^ (p - 1) := by
  have hc := integrable_centered (P := P) hV hB.le c
  have hb := norm_integral_le_of_norm_le (hmi.div_const ((B / 2) ^ (p - 1)))
    (f := fun ω => centeredClip B c (V ω) - V ω)
    (Filter.Eventually.of_forall (fun ω => centered_residual hB hp c u (V ω) hu))
  rw [integral_sub hc hi, hmean, integral_div] at hb
  exact hb.trans (div_le_div_of_nonneg_right hm (Real.rpow_nonneg (by positivity) _))

omit [IsProbabilityMeasure P] in
lemma centered_second_moment {V : Ω → E} (hV : Measurable V)
    {B p σ : ℝ} (hB : 0 < B) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (c u : E) (hu : ‖u - c‖ ≤ B)
    (hmi : Integrable (fun ω => ‖V ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖V ω - u‖ ^ p ∂P) ≤ σ ^ p) :
    Integrable (fun ω => ‖centeredClip B c (V ω) - u‖ ^ 2) P ∧
      (∫ ω, ‖centeredClip B c (V ω) - u‖ ^ 2 ∂P) ≤ 4 * B ^ (2 - p) * σ ^ p := by
  have hb := fun ω => centered_error_sq hB hp hp2 c u (V ω) hu
  have hi : Integrable (fun ω => ‖centeredClip B c (V ω) - u‖ ^ 2) P := by
    apply (hmi.const_mul (4 * B ^ (2 - p))).mono'
    · exact (((measurable_centered B c).comp hV).sub_const u).norm.pow_const 2
        |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hb ω)
  refine ⟨hi, ?_⟩
  have ht := integral_mono hi (hmi.const_mul (4 * B ^ (2 - p))) hb
  rw [integral_const_mul] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left hm (by positivity))

omit [NormedSpace ℝ E] in
lemma pilot_moment_confidence {V : Ω → E} (hV : Measurable V)
    {B p : ℝ} (hB : 0 < B) (hp : 0 ≤ p) (u : E)
    (hmi : Integrable (fun ω => ‖V ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖V ω - u‖ ^ p ∂P) ≤ (B / 6) ^ p / 16) (k : ℕ) :
    (Measure.pi fun _ : Fin k => P)
      {ξ | B / 2 < ‖RobustGradient.pilotCenter B (fun i => V (ξ i)) - u‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  apply RobustGradient.pilotCenter_failure_probability hV u B ?_ k
  have hthreshold : 0 < (B / 6) ^ p := Real.rpow_pos_of_pos (by positivity) _
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (norm_nonneg (V ω - u)) p))
    hmi ((B / 6) ^ p)
  have hsub : {ω | B / 6 < ‖V ω - u‖} ⊆
      {ω | (B / 6) ^ p ≤ ‖V ω - u‖ ^ p} := by
    intro ω hω
    exact Real.rpow_le_rpow (by positivity) hω.le hp
  have hmeasure := measureReal_mono (μ := P) hsub
  have hmul := mul_le_mul_of_nonneg_left hmeasure hthreshold.le
  nlinarith

omit [SecondCountableTopology E] in
lemma linear_error_mgf [CompleteSpace E] {X : Ω → E} (hX : Measurable X)
    (hi : Integrable X P) (hi2 : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    (l : E →L[ℝ] ℝ) {θ a D M β V : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hD : 0 ≤ D) (hl : ‖l‖ ≤ D) (hb : ∀ ω, ‖X ω‖ ≤ M)
    (hmean : ‖∫ ω, X ω ∂P‖ ≤ β) (hsecond : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ V)
    (hsmall : θ * a * D * M ≤ 1) :
    Integrable (fun ω => Real.exp (θ * a * l (X ω))) P ∧
      (∫ ω, Real.exp (θ * a * l (X ω)) ∂P) ≤
        Real.exp (θ * a * D * β + θ ^ 2 * a ^ 2 * D ^ 2 * V) := by
  have heval (v : E) : |l v| ≤ D * ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact (l.le_opNorm v).trans (mul_le_mul_of_nonneg_right hl (norm_nonneg v))
  have hZ : Measurable (fun ω => θ * a * l (X ω)) :=
    (l.continuous.measurable.comp hX).const_mul (θ * a)
  have hbound (ω : Ω) : |θ * a * l (X ω)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hθ ha)]
    calc
      _ ≤ θ * a * (D * ‖X ω‖) := mul_le_mul_of_nonneg_left (heval _) (mul_nonneg hθ ha)
      _ ≤ θ * a * (D * M) := by gcongr; exact hb ω
      _ ≤ 1 := by nlinarith [hsmall]
  have hm : (∫ ω, θ * a * l (X ω) ∂P) ≤ θ * a * D * β := by
    rw [integral_const_mul, l.integral_comp_comm hi]
    have hh := (le_abs_self (l (∫ ω, X ω ∂P))).trans (heval _)
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hmean hD)
    have ht := mul_le_mul_of_nonneg_left hh' (mul_nonneg hθ ha)
    nlinarith
  have hsq (ω : Ω) : (θ * a * l (X ω)) ^ 2 ≤
      (θ ^ 2 * a ^ 2 * D ^ 2) * ‖X ω‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (heval (X ω)) 2
    rw [sq_abs] at hh
    have ht := mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg θ) (sq_nonneg a))
    nlinarith
  have hiZ2 : Integrable (fun ω => (θ * a * l (X ω)) ^ 2) P := by
    apply (hi2.const_mul (θ ^ 2 * a ^ 2 * D ^ 2)).mono'
    · exact (hZ.pow_const 2).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hsq ω)
  have hs := integral_mono hiZ2 (hi2.const_mul (θ ^ 2 * a ^ 2 * D ^ 2)) hsq
  rw [integral_const_mul] at hs
  have hv := hs.trans (mul_le_mul_of_nonneg_left hsecond (by positivity))
  exact RobustGradient.bounded_increment_mgf hZ hbound hm hv

lemma centered_sample_mgf [CompleteSpace E] {W : Ω → E} (hW : Measurable W)
    (hi : Integrable W P) {B p σ : ℝ} (hB : 0 < B) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (c u : E) (hu : ‖c - u‖ ≤ B / 2) (hmean : ∫ ω, W ω ∂P = u)
    (hmi : Integrable (fun ω => ‖W ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖W ω - u‖ ^ p ∂P) ≤ σ ^ p)
    (l : E →L[ℝ] ℝ) {θ a D : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hD : 0 ≤ D) (hl : ‖l‖ ≤ D) (hsmall : θ * a * D * (3 * B / 2) ≤ 1) :
    Integrable (fun ω => Real.exp (θ * a * l (centeredClip B c (W ω) - u))) P ∧
      (∫ ω, Real.exp (θ * a * l (centeredClip B c (W ω) - u)) ∂P) ≤
        Real.exp (θ * a * D * (σ ^ p / (B / 2) ^ (p - 1)) +
          θ ^ 2 * a ^ 2 * D ^ 2 * (4 * B ^ (2 - p) * σ ^ p)) := by
  have hu' : ‖u - c‖ ≤ B / 2 := by rwa [norm_sub_rev]
  have hc := integrable_centered (P := P) hW hB.le c
  have hX := ((measurable_centered B c).comp hW).sub_const u
  have hXi := hc.sub (integrable_const u)
  have hX2 := centered_second_moment hW hB (by linarith : 0 ≤ p) hp2 c u (by linarith) hmi hm
  have hb := centered_bias hW hi hB hp c u hu' hmean hmi hm
  have hXm : ‖∫ ω, centeredClip B c (W ω) - u ∂P‖ ≤ σ ^ p / (B / 2) ^ (p - 1) := by
    rw [integral_sub hc (integrable_const u), integral_const]
    simpa only [probReal_univ, one_smul] using hb
  exact linear_error_mgf hX hXi hX2.1 l hθ ha hD hl
    (fun ω => centered_error_bounded hB.le c u (W ω) hu) hXm hX2.2 hsmall

lemma centered_pilot_mgf [CompleteSpace E] {Ξ : Type*} [MeasurableSpace Ξ]
    (Q : Measure Ξ) [IsProbabilityMeasure Q] {W : Ω → E} (hW : Measurable W)
    (hi : Integrable W P) {B p σ : ℝ} (hB : 0 < B) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hσ : 0 ≤ σ) (c : Ξ → E) (hc : Measurable c) (u : E)
    (hmean : ∫ ω, W ω ∂P = u) (hmi : Integrable (fun ω => ‖W ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖W ω - u‖ ^ p ∂P) ≤ σ ^ p)
    (l : E →L[ℝ] ℝ) {θ a D : ℝ} (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hD : 0 ≤ D) (hl : ‖l‖ ≤ D) (hsmall : θ * a * D * (3 * B / 2) ≤ 1) :
    let X := fun z : Ξ × Ω => if ‖c z.1 - u‖ ≤ B / 2 then
      centeredClip B (c z.1) (W z.2) - u else 0
    Integrable (fun z => Real.exp (θ * a * l (X z))) (Q.prod P) ∧
      (∫ z, Real.exp (θ * a * l (X z)) ∂Q.prod P) ≤
        Real.exp (θ * a * D * (σ ^ p / (B / 2) ^ (p - 1)) +
          θ ^ 2 * a ^ 2 * D ^ 2 * (4 * B ^ (2 - p) * σ ^ p)) := by
  classical
  dsimp only
  let C := θ * a * D * (σ ^ p / (B / 2) ^ (p - 1)) +
    θ ^ 2 * a ^ 2 * D ^ 2 * (4 * B ^ (2 - p) * σ ^ p)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hX : Measurable (fun z : Ξ × Ω => if ‖c z.1 - u‖ ≤ B / 2 then
      centeredClip B (c z.1) (W z.2) - u else 0) := by
    have hclip : Measurable (fun z : Ξ × Ω => centeredClip B (c z.1) (W z.2)) :=
      (hc.comp measurable_fst).add ((GeneralNormClipping.measurable_clip B).comp
        ((hW.comp measurable_snd).sub (hc.comp measurable_fst)))
    exact (hclip.sub_const u).ite
      (measurableSet_le ((hc.comp measurable_fst).sub_const u).norm measurable_const)
      measurable_const
  have hF := (l.continuous.measurable.comp hX).const_mul (θ * a)
  have hcond (ξ : Ξ) :
      Integrable (fun ω => Real.exp (θ * a * l (if ‖c ξ - u‖ ≤ B / 2 then
        centeredClip B (c ξ) (W ω) - u else 0))) P ∧
      (∫ ω, Real.exp (θ * a * l (if ‖c ξ - u‖ ≤ B / 2 then
        centeredClip B (c ξ) (W ω) - u else 0)) ∂P) ≤ Real.exp C := by
    by_cases hgood : ‖c ξ - u‖ ≤ B / 2
    · simp only [ite_eq_left hgood]
      exact centered_sample_mgf hW hi hB hp hp2 (c ξ) u hgood hmean hmi hm
        l hθ ha hD hl hsmall
    · simp only [ite_eq_right hgood, map_zero, mul_zero, Real.exp_zero]
      exact ⟨integrable_const _, by simpa using Real.one_le_exp_iff.mpr hC⟩
  exact OracleTemplate.LightTail.integral_prod_exp_control hF (fun ξ => (hcond ξ).1)
    (fun ξ => (hcond ξ).2) (integrable_const (Real.exp C)) (by simp only [integral_const, probReal_univ, one_smul]; rfl)

lemma centered_pilot_second_moment {Ξ : Type*} [MeasurableSpace Ξ]
    (Q : Measure Ξ) [IsProbabilityMeasure Q] {W : Ω → E} (hW : Measurable W)
    {B p σ : ℝ} (hB : 0 < B) (hp : 0 ≤ p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (c : Ξ → E) (hc : Measurable c) (u : E)
    (hmi : Integrable (fun ω => ‖W ω - u‖ ^ p) P)
    (hm : (∫ ω, ‖W ω - u‖ ^ p ∂P) ≤ σ ^ p) :
    let X := fun z : Ξ × Ω => if ‖c z.1 - u‖ ≤ B / 2 then
      centeredClip B (c z.1) (W z.2) - u else 0
    Integrable (fun z => ‖X z‖ ^ 2) (Q.prod P) ∧
      (∫ z, ‖X z‖ ^ 2 ∂Q.prod P) ≤ 4 * B ^ (2 - p) * σ ^ p := by
  classical
  intro X
  have hX : Measurable X := by
    have hclip : Measurable (fun z : Ξ × Ω => centeredClip B (c z.1) (W z.2)) :=
      (hc.comp measurable_fst).add ((GeneralNormClipping.measurable_clip B).comp
        ((hW.comp measurable_snd).sub (hc.comp measurable_fst)))
    exact (hclip.sub_const u).ite
      (measurableSet_le ((hc.comp measurable_fst).sub_const u).norm measurable_const)
      measurable_const
  have hb (z : Ξ × Ω) : ‖X z‖ ≤ 3 * B / 2 := by
    dsimp [X]
    split_ifs with h
    · exact centered_error_bounded hB.le (c z.1) u (W z.2) h
    · simp only [norm_zero]; positivity
  have hi : Integrable (fun z => ‖X z‖ ^ 2) (Q.prod P) := by
    apply Integrable.of_bound (hX.norm.pow_const 2).aestronglyMeasurable ((3 * B / 2) ^ 2)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb z) 2
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  have hb' (ξ : Ξ) : (∫ ω, ‖X (ξ, ω)‖ ^ 2 ∂P) ≤ 4 * B ^ (2 - p) * σ ^ p := by
    by_cases h : ‖c ξ - u‖ ≤ B / 2
    · simp only [X, ite_eq_left h]
      exact (centered_second_moment hW hB hp hp2 (c ξ) u
        (by rw [norm_sub_rev]; linarith) hmi hm).2
    · simp only [X, ite_eq_right h, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, integral_zero]
      positivity
  exact (integral_mono hi.integral_prod_left (integrable_const _) hb').trans_eq (by simp)

end LongTails.Proofs.GeneralizedMirrorNoise
