import LongTails.Proofs.BlumGladyshevHardInstance
import LongTails.Proofs.BlumGladyshevTesting
import LongTails.Proofs.PolynomialMixingLowerBound

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open LongTails.Setups.TerminalClippingConvex LongTails.Proofs.BlumGladyshevValley
open LongTails.Proofs.BlumGladyshevTesting
open LongTails.Proofs.PolynomialMixingLowerBound (integral_two_atoms integrable_two_atoms)

namespace LongTails.Proofs.BlumGladyshevHardInstance

lemma slope_continuous : Continuous slope := by
  unfold BlumGladyshevValley.slope
  exact continuous_id.div (continuous_const.add (continuous_id.pow 2)).sqrt
    (fun x : ℝ => (Real.sqrt_pos.2 (by positivity)).ne')

lemma ridgeGradient_continuous (a b : ℝ) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (e x₀ : E) : Continuous (ridgeGradient a b e x₀) :=
  (continuous_const.mul (slope_continuous.comp
    ((continuous_const.inner (continuous_id.sub continuous_const)).sub continuous_const))).smul
    continuous_const

lemma field_measurable (p : Public) (e w : Vector p.d) (q : ℝ) :
    Measurable (Function.uncurry (field p e w q)) := by
  have hbase := (ridgeGradient_continuous (512 * p.ε) (1/2) (axis p e) p.x0).measurable
  have htilt := (ridgeGradient_continuous (512 * p.ε) 0 (axis p (e+w)) p.x0).measurable
  have hz : Measurable (fun z : Bool => if z then q⁻¹ else 0) := Measurable.of_discrete
  exact (hbase.comp measurable_fst).add ((hz.comp measurable_snd).smul (htilt.comp measurable_fst))

lemma field_mean (p : Public) (e w x : Vector p.d) (q : unitInterval) (hq : 0 < (q : ℝ)) :
    (∫ z, field p e w q x z ∂(marginal q : Measure Bool)) =
      baseField p e x + tiltField p e w x := by
  rw [show (marginal q : Measure Bool) = bernoulliMeasure true false q from rfl,
    integral_two_atoms _ _ (measurableSet_singleton _) (measurableSet_singleton _)]
  simp [field, smul_add, smul_smul, hq.ne', sub_smul]
  module

lemma loss_mean (p : Public) (e w x : Vector p.d) (q : unitInterval) (hq : 0 < (q : ℝ)) :
    (∫ z, loss p e w q z x ∂(marginal q : Measure Bool)) = objective p e w x := by
  rw [show (marginal q : Measure Bool) = bernoulliMeasure true false q from rfl,
    integral_two_atoms _ _ (measurableSet_singleton _) (measurableSet_singleton _)]
  simp [loss, objective, smul_eq_mul]
  field_simp
  ring

lemma field_sizes (p : Public) (hR : 0 < p.R) (hε : 0 < p.ε)
    {e w : Vector p.d} (he : ‖e‖ = 1) (hw : ‖w‖ = 1) (x : Vector p.d) :
    let a := 512 * p.ε / p.R
    ‖baseField p e x‖ ≤ a ∧ ‖tiltField p e w x‖ ≤ 2 * a ∧
      ‖tiltField p e w x‖ ≤ 4 * a * ‖x - p.x0‖ / p.R := by
  have ha : ‖axis p e‖ = p.R⁻¹ := by simp [axis, norm_smul, he, abs_of_pos hR]
  have hb : ‖axis p (e + w)‖ ≤ 2 / p.R := by
    have h := norm_add_le e w
    rw [he, hw] at h
    rw [axis, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
    norm_num at h
    simpa [div_eq_inv_mul] using mul_le_mul_of_nonneg_left h (inv_nonneg.2 hR.le)
  have hcoord := (abs_real_inner_le_norm (axis p (e+w)) (x-p.x0)).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have h1 := slope_abs_le_one (⟪axis p e, x-p.x0⟫-1/2)
  have h2 := slope_abs_le_one ⟪axis p (e+w), x-p.x0⟫
  have h3 := (slope_abs_le_abs _).trans hcoord
  have hpos : 0 ≤ 512 * p.ε := by positivity
  simp only [baseField, tiltField, ridgeGradient, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg hpos, sub_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [ha]
    calc
      _ ≤ (512 * p.ε * 1) * p.R⁻¹ := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ (512 * p.ε * 1) * (2 / p.R) := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ (512 * p.ε * (2 / p.R * ‖x - p.x0‖)) * (2 / p.R) := by gcongr
      _ = _ := by ring

lemma moment_calibration {a G B R D Y q : ℝ} (hR : 0 < R) (ha : 0 < a) (hY : 0 ≤ Y)
    (hq : 0 < q) (haG : 128 * a ≤ G)
    (hqeq : q * (G^2 + B^2*R^2) = 64*a^2)
    (h₁ : Y ≤ 2*a) (h₂ : Y ≤ 4*a*D/R) :
    2*a^2 + 2*Y^2/q ≤ G^2 + B^2*D^2 := by
  have hG : 0 ≤ G := le_trans (by positivity) haG
  have ha2 := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ) ≤ 128) ha.le) haG 2
  have h1 := pow_le_pow_left₀ hY h₁ 2
  have h2 := pow_le_pow_left₀ (mul_nonneg hY hR.le) ((le_div_iff₀ hR).mp h₂) 2
  have hy : (G^2 + B^2*R^2)*Y^2 ≤ 16*a^2*(G^2 + B^2*D^2) := by
    nlinarith only [mul_le_mul_of_nonneg_left h1 (sq_nonneg G),
      mul_le_mul_of_nonneg_left h2 (sq_nonneg B), sq_nonneg (a*G)]
  have hgpos : 0 < G := lt_of_lt_of_le (by positivity) haG
  have hd : 0 < G^2+B^2*R^2 := by positivity
  have ht : 4*Y^2 ≤ q*(G^2+B^2*D^2) := by
    apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith only [hy, congrArg (fun z : ℝ => z * (G^2+B^2*D^2)) hqeq]
  have hyq : 2*Y^2/q ≤ (G^2+B^2*D^2)/2 := by
    apply (div_le_iff₀ hq).mpr
    nlinarith only [ht]
  nlinarith only [ha2, hyq, sq_nonneg (B*D)]

lemma field_second (p : Public) {e w : Vector p.d} (he : ‖e‖ = 1) (hw : ‖w‖ = 1)
    (hG : 0 < p.G) (hR : 0 < p.R) (hε : 0 < p.ε) (hscale : 65536*p.ε ≤ p.G*p.R)
    (q : unitInterval) (hqeq : (q : ℝ) = BlumGladyshevMask.probability p.G p.B p.R p.ε)
    (x : Vector p.d) :
    (∫ z, ‖field p e w q x z‖^2 ∂(marginal q : Measure Bool)) ≤
      p.B^2 * ‖x-p.x0‖^2 + p.G^2 := by
  have hq : 0 < (q : ℝ) := hqeq ▸ (BlumGladyshevMask.mask_bounds hG hR hε hscale).1
  let U := baseField p e x
  let Y := tiltField p e w x
  let a := 512*p.ε/p.R
  have ha : 0 < a := div_pos (by positivity) hR
  have hag : 128*a ≤ p.G := by
    dsimp [a]
    rw [← mul_div_assoc, div_le_iff₀ hR]
    linarith only [hscale]
  have hqcal : (q : ℝ)*(p.G^2+p.B^2*p.R^2) = 64*a^2 := by
    rw [hqeq]
    unfold BlumGladyshevMask.probability a
    field_simp
    ring
  obtain ⟨hU,hY,hY'⟩ := field_sizes p hR hε he hw x
  have hc := moment_calibration hR ha (norm_nonneg Y) hq hag hqcal hY hY'
  have hUs : ‖U‖^2 ≤ a^2 := pow_le_pow_left₀ (norm_nonneg _) hU 2
  rw [show (marginal q : Measure Bool) = bernoulliMeasure true false q from rfl,
    integral_two_atoms _ _ (measurableSet_singleton _) (measurableSet_singleton _)]
  simp only [field, ↓reduceIte, Bool.false_eq_true, zero_smul, add_zero, smul_eq_mul]
  change (q : ℝ)*‖U+ (q : ℝ)⁻¹ • Y‖^2 + (1-q)*‖U‖^2 ≤ _
  have hs := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le U ((q:ℝ)⁻¹ • Y)) 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hq)] at hs
  have hh : ‖U + (q:ℝ)⁻¹ • Y‖^2 ≤ 2*‖U‖^2 + 2*((q:ℝ)⁻¹*‖Y‖)^2 := by
    nlinarith only [hs, sq_nonneg (‖U‖-(q:ℝ)⁻¹*‖Y‖)]
  have ht := mul_le_mul_of_nonneg_left hh hq.le
  have heq : (q : ℝ) * (2*‖U‖^2 + 2*((q:ℝ)⁻¹*‖Y‖)^2) =
      (q : ℝ)*2*‖U‖^2 + 2*‖Y‖^2/q := by field_simp
  rw [heq] at ht
  have hqu := mul_nonneg (sub_nonneg.mpr q.2.2) (sq_nonneg ‖U‖)
  linarith only [ht, hc, hUs, hqu]

end LongTails.Proofs.BlumGladyshevHardInstance
