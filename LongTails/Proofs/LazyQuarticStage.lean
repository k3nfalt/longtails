import LongTails.Proofs.LazyQuarticDecay

namespace LongTails.Proofs.LazyQuarticStage

open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric
open LongTails.Proofs.LazyQuarticStageParameters
open LongTails.Proofs.LazyQuarticCurvature
open LongTails.Proofs.QuarticStageInvariant
open scoped RealInnerProductSpace

noncomputable def hypotheses (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ContDiff ℝ 3 f)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x -
      fderiv ℝ (fderiv ℝ (_root_.gradient f)) y‖ ≤ p.L₃ * ‖x - y‖)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ)
    (hH : ‖fderiv ℝ (_root_.gradient f) p.x0‖ ≤ p.H₀)
    (st : State p) (hc : Faithful f st.point) (hvalue : f st.point.x ≤ f p.x0)
    (hsnapshot : f st.snapshot ≤ f p.x0)
    (hcoords : st.coordinates = coordinates p (fderiv ℝ (_root_.gradient f) st.snapshot))
    (hguard : ‖st.coordinates (st.point.x - st.snapshot)‖ ≤ radius p / 4)
    (hpath : ‖st.snapshot - p.x0‖ ^ 2 ≤ pathCap p) :
    QuarticStageGuarantee.Hypotheses (parameters p st) f (innerSteps p) := by
  have hα := LazyQuarticParameters.alpha_pos p hp
  have hβ := LazyQuarticParameters.beta_pos p hp
  have hq := LazyQuarticParameters.decrease_pos p hp
  have hr := LazyQuarticParameters.radius_pos p hp
  have hb := basic_scales p hp st
  have hradii := radii_square p hp st
  have hguards := guard_scales p hp
  have hesc := escape_scales p hp st
  have hshort := short_scales p hp
  have hs := LazyQuarticSnapshot.sigma_relations p hp
  have hnewgap (y : p.E) : f st.snapshot - f y ≤ p.Δ := by linarith [hgap y]
  have hS (v : p.E) : ‖st.coordinates v‖ ^ 2 =
      ⟪fderiv ℝ (_root_.gradient f) st.snapshot v, v⟫ + 8 * p.L₃ * (beta p / p.L₃) * ‖v‖ ^ 2 := by
    rw [mul_assoc 8 p.L₃ (beta p / p.L₃), hs.2.2, hcoords]
    exact LazyQuarticSnapshot.coordinates_metric p hp f hf hT st.snapshot hnewgap v
  have hαβ : alpha p ≤ p.L₃ * (beta p / p.L₃) := by
    rw [hs.2.2]
    have hh := LazyQuarticParameters.alpha_cap p
    norm_num at hh
    linarith
  refine {
    A := metricRadius p
    τ := euclideanRadius p
    β := beta p
    M := curvatureCap p
    L₃ := p.L₃
    Δ := p.Δ
    smooth := hf
    third_lipschitz := hT
    third_nonneg := hp.1.le
    gap := ?_
    center_faithful := hc
    a_nonneg := hb.2.1
    a_le_one := hb.2.2.1
    mu_pos := hb.1
    smoothness_pos := by norm_num [parameters]
    mu_le_smoothness := ?_
    alpha_pos := hα
    radius_pos := hr
    epsilon_pos := hp.2.2.2
    beta_pos := hβ
    metric_nonneg := ?_
    A_nonneg := Real.sqrt_nonneg _
    tau_nonneg := Real.sqrt_nonneg _
    q_nonneg := hq.le
    A_square := hradii.1
    tau_square := hradii.2
    A_guard := hguards.1
    q_guard := ?_
    acceleration := hb.2.2.2.1
    mu_small := hb.2.2.2.2.1
    mu_beta := hb.2.2.2.2.2.le
    interpolation_scale := hshort.1
    witness_scale := hshort.2
    escape_small := hesc.1.le
    escape_decrease := hesc.2.1
    escape_energy := hesc.2.2
    accuracy_scale := accuracy_scale p hp
    metric_upper := ?_
    decay := LazyQuarticDecay.certificate_decay p hp st
    model := ?_
    lower := ?_
  }
  · intro x
    change st.point.value - f x ≤ p.Δ
    rw [hc.1]
    linarith [hgap x]
  · change (parameters p st).μ ≤ 4
    linarith [hb.2.2.2.2.1]
  · have hH₀ := hp.2.2.1
    have hL := hp.1.le
    unfold curvatureCap
    positivity
  · change decrease p ≤ 4 * radius p ^ 2 / 16
    nlinarith only [hguards.2]
  · intro v
    change ‖st.coordinates v‖ ^ 2 ≤ curvatureCap p * ‖v‖ ^ 2
    rw [hcoords]
    exact metric_cap p hp f hf hT hgap hH st.snapshot hsnapshot hpath v
  · intro y next hy hn hyr hnext
    exact QuarticStageModels.snapshot_model (parameters p st) f st.snapshot hf hp.1 hs.1
      (Real.sqrt_pos.mpr hp.2.1) hs.2.1 (Real.sq_sqrt hp.2.1.le) hT hnewgap hS hαβ rfl rfl
      hguards.1 hguard y next hy hn hyr hnext
  · intro u v hu hv
    have hh := QuarticStageModels.snapshot_lower (parameters p st) f st.snapshot hf hp.1 hs.1
      (Real.sqrt_pos.mpr hp.2.1) hs.2.1 (Real.sq_sqrt hp.2.1.le) hT hnewgap hS rfl hguards.1 hguard u v hu hv
    rwa [hs.2.2] at hh

end LongTails.Proofs.LazyQuarticStage
