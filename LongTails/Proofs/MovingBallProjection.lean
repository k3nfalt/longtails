import LongTails.Proofs.ExtragradientStep
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.MovingBallProjection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma transfer_mem {C : Set E} (hc : Convex ℝ C) {r : ℝ} (hr : 0 < r)
    {x z z' : E} (hx : x ∈ C) (hz' : z' ∈ C) (hball : ‖x - z‖ ≤ r) :
    let d := ‖z' - z‖
    let v := (r / (r + d)) • x + (d / (r + d)) • z'
    v ∈ C ∧ ‖v - z'‖ ≤ r ∧ ‖v - x‖ = d / (r + d) * ‖z' - x‖ := by
  let d := ‖z' - z‖
  have hd : 0 ≤ d := norm_nonneg _
  have hden : 0 < r + d := add_pos_of_pos_of_nonneg hr hd
  have ha : 0 ≤ r / (r + d) := div_nonneg hr.le hden.le
  have hb : 0 ≤ d / (r + d) := div_nonneg hd hden.le
  have hsum : r / (r + d) + d / (r + d) = 1 := by
    rw [← add_div, div_self hden.ne']
  have hfirst : d / (r + d) = 1 - r / (r + d) := by linarith
  have hsecond : r / (r + d) = 1 - d / (r + d) := by linarith
  have hcenter : (r / (r + d)) • x + (d / (r + d)) • z' - z' =
      (r / (r + d)) • (x - z') := by
    rw [hfirst]
    module
  have hmove : (r / (r + d)) • x + (d / (r + d)) • z' - x =
      (d / (r + d)) • (z' - x) := by
    rw [hsecond]
    module
  have hdist : ‖x - z'‖ ≤ r + d := by
    have ht := norm_sub_le_norm_sub_add_norm_sub x z z'
    rw [norm_sub_rev z z'] at ht
    exact ht.trans (add_le_add hball (le_refl d))
  refine ⟨hc hx hz' ha hb hsum, ?_, ?_⟩
  · change ‖(r / (r + d)) • x + (d / (r + d)) • z' - z'‖ ≤ r
    rw [hcenter, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    calc
      r / (r + d) * ‖x - z'‖ ≤ r / (r + d) * (r + d) :=
        mul_le_mul_of_nonneg_left hdist ha
      _ = r := div_mul_cancel₀ _ hden.ne'
  · change ‖(r / (r + d)) • x + (d / (r + d)) • z' - x‖ = _
    rw [hmove, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]

lemma perturbed_projection_distance {y y' p q u v : E} {h : ℝ}
    (hp : ⟪y - p, u - p⟫ ≤ 0) (hq : ⟪y' - q, v - q⟫ ≤ 0)
    (hu : ‖u - q‖ ≤ h) (hv : ‖v - p‖ ≤ h) :
    ‖p - q‖ ^ 2 ≤ ⟪y - y', p - q⟫ + (‖y - p‖ + ‖y' - q‖) * h := by
  have hu' : ‖q - u‖ ≤ h := by simpa only [norm_sub_rev q u] using hu
  have hv' : ‖p - v‖ ≤ h := by simpa only [norm_sub_rev p v] using hv
  have hpu := (real_inner_le_norm (y - p) (q - u)).trans
    (mul_le_mul_of_nonneg_left hu' (norm_nonneg _))
  have hqv := (real_inner_le_norm (y' - q) (p - v)).trans
    (mul_le_mul_of_nonneg_left hv' (norm_nonneg _))
  have hpi : ⟪y - p, q - p⟫ = ⟪y - p, u - p⟫ + ⟪y - p, q - u⟫ := by
    simp only [inner_sub_right]
    ring
  have hqi : ⟪y' - q, p - q⟫ = ⟪y' - q, v - q⟫ + ⟪y' - q, p - v⟫ := by
    simp only [inner_sub_right]
    ring
  have hid : ‖p - q‖ ^ 2 - ⟪y - y', p - q⟫ =
      ⟪y - p, q - p⟫ + ⟪y' - q, p - q⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  nlinarith only [hp, hq, hpu, hqv, hpi, hqi, hid]

lemma moving_project_bound {C : Set E}
    (hc : Convex ℝ C) (hcompact : IsCompact C) {M r : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x ∈ C, ‖x‖ ≤ M) (hr : 0 < r)
    {z z' : E} (hz : z ∈ C) (hz' : z' ∈ C) (y y' : E) :
    let p := OracleTemplate.SaddlePoint.project (C ∩ Metric.closedBall z r) y
    let q := OracleTemplate.SaddlePoint.project (C ∩ Metric.closedBall z' r) y'
    let d := ‖z' - z‖
    ‖p - q‖ ^ 2 ≤ 2 * M * ‖y - y'‖ +
      (‖y‖ + ‖y'‖ + 2 * M) * (2 * M * d / (r + d)) := by
  let p := OracleTemplate.SaddlePoint.project (C ∩ Metric.closedBall z r) y
  let q := OracleTemplate.SaddlePoint.project (C ∩ Metric.closedBall z' r) y'
  let d := ‖z' - z‖
  let h := 2 * M * d / (r + d)
  have hd : 0 ≤ d := norm_nonneg _
  have hh : 0 ≤ h := div_nonneg (by positivity) (by positivity)
  have hne (w : E) (hw : w ∈ C) : (C ∩ Metric.closedBall w r).Nonempty :=
    ⟨w, hw, Metric.mem_closedBall_self hr.le⟩
  have hp := OracleTemplate.SaddlePoint.project_spec (hne z hz)
    (hcompact.inter_right Metric.isClosed_closedBall) (hc.inter (convex_closedBall z r)) y
  have hq := OracleTemplate.SaddlePoint.project_spec (hne z' hz')
    (hcompact.inter_right Metric.isClosed_closedBall) (hc.inter (convex_closedBall z' r)) y'
  change p ∈ C ∩ Metric.closedBall z r ∧ _ at hp
  change q ∈ C ∩ Metric.closedBall z' r ∧ _ at hq
  have hpball : ‖p - z‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hp.1.2
  have hqball : ‖q - z'‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hq.1.2
  let u := (r / (r + d)) • q + (d / (r + d)) • z
  let v := (r / (r + d)) • p + (d / (r + d)) • z'
  have hu := transfer_mem hc hr hq.1.1 hz hqball
  have hv := transfer_mem hc hr hp.1.1 hz' hpball
  rw [norm_sub_rev z z'] at hu
  change u ∈ C ∧ ‖u - z‖ ≤ r ∧ ‖u - q‖ = d / (r + d) * ‖z - q‖ at hu
  change v ∈ C ∧ ‖v - z'‖ ≤ r ∧ ‖v - p‖ = d / (r + d) * ‖z' - p‖ at hv
  have hdiam {a b : E} (ha : a ∈ C) (hb : b ∈ C) : ‖a - b‖ ≤ 2 * M := by
    have ht := norm_sub_le a b
    linarith [hbound a ha, hbound b hb]
  have hum : ‖u - q‖ ≤ h := by
    rw [hu.2.2]
    have ht := mul_le_mul_of_nonneg_left (hdiam hz hq.1.1)
      (div_nonneg hd (by positivity : 0 ≤ r + d))
    exact ht.trans_eq (by dsimp [h]; ring)
  have hvm : ‖v - p‖ ≤ h := by
    rw [hv.2.2]
    have ht := mul_le_mul_of_nonneg_left (hdiam hz' hp.1.1)
      (div_nonneg hd (by positivity : 0 ≤ r + d))
    exact ht.trans_eq (by dsimp [h]; ring)
  have hpu := hp.2 u ⟨hu.1, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu.2.1⟩
  have hqv := hq.2 v ⟨hv.1, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hv.2.1⟩
  have hs := perturbed_projection_distance hpu hqv hum hvm
  have hi := (real_inner_le_norm (y - y') (p - q)).trans
    (mul_le_mul_of_nonneg_left (hdiam hp.1.1 hq.1.1) (norm_nonneg _))
  have hyp : ‖y - p‖ ≤ ‖y‖ + M :=
    (norm_sub_le y p).trans (add_le_add (le_refl _) (hbound p hp.1.1))
  have hyq : ‖y' - q‖ ≤ ‖y'‖ + M :=
    (norm_sub_le y' q).trans (add_le_add (le_refl _) (hbound q hq.1.1))
  have hm := mul_le_mul_of_nonneg_right (add_le_add hyp hyq) hh
  change ‖p - q‖ ^ 2 ≤ 2 * M * ‖y - y'‖ + (‖y‖ + ‖y'‖ + 2 * M) * h
  nlinarith only [hs, hi, hm]

lemma continuous_moving_project {C : Set E}
    (hc : Convex ℝ C) (hcompact : IsCompact C) {M r : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x ∈ C, ‖x‖ ≤ M) (hr : 0 < r) :
    Continuous (fun w : C × E =>
      OracleTemplate.SaddlePoint.project (C ∩ Metric.closedBall w.1.val r) w.2) := by
  let P : C × E → E := fun w =>
    OracleTemplate.SaddlePoint.project (C ∩ Metric.closedBall w.1.val r) w.2
  change Continuous P
  apply continuous_iff_continuousAt.2
  intro w0
  let rhs : C × E → ℝ := fun w => 2 * M * ‖w.2 - w0.2‖ +
    (‖w.2‖ + ‖w0.2‖ + 2 * M) *
      (2 * M * ‖w0.1.val - w.1.val‖ / (r + ‖w0.1.val - w.1.val‖))
  have hdcont : Continuous (fun w : C × E => ‖w0.1.val - w.1.val‖) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).norm
  have hycont : Continuous (fun w : C × E => ‖w.2 - w0.2‖) :=
    (continuous_snd.sub continuous_const).norm
  have hcont : Continuous rhs := by
    exact (continuous_const.mul hycont).add
      (((continuous_snd.norm.add continuous_const).add continuous_const).mul
        ((continuous_const.mul hdcont).div (continuous_const.add hdcont)
          (fun w => (add_pos_of_pos_of_nonneg hr (norm_nonneg _)).ne')))
  have hzero : rhs w0 = 0 := by simp [rhs]
  have hlim : Filter.Tendsto (fun w => Real.sqrt (rhs w)) (nhds w0)
      (nhds (Real.sqrt (rhs w0))) :=
    (Real.continuous_sqrt.comp hcont).continuousAt
  rw [hzero, Real.sqrt_zero] at hlim
  apply tendsto_iff_dist_tendsto_zero.2
  apply squeeze_zero (fun _ => dist_nonneg) _ hlim
  intro w
  have hb := moving_project_bound hc hcompact hM hbound hr w.1.property w0.1.property w.2 w0.2
  change ‖P w - P w0‖ ^ 2 ≤ rhs w at hb
  simpa only [dist_eq_norm] using Real.le_sqrt_of_sq_le hb

lemma measurable_moving_project [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {C : Set E}
    (hc : Convex ℝ C) (hcompact : IsCompact C) {M r : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ x ∈ C, ‖x‖ ≤ M) (hr : 0 < r) :
    Measurable (fun w : C × E =>
      OracleTemplate.SaddlePoint.project (C ∩ Metric.closedBall w.1.val r) w.2) :=
  (continuous_moving_project hc hcompact hM hbound hr).measurable

end LongTails.Proofs.MovingBallProjection
