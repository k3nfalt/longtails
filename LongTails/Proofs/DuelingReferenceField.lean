import LongTails.Proofs.DuelingReferenceSmoothing

open MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Setups.StronglyConvexDueling
open LongTails.Algorithms.DuelingReferenceDescent
open LongTails.Proofs.DuelingReferenceDrift
open LongTails.Proofs.DuelingReferenceSmoothing
open OracleTemplate.ZerothOrder

namespace LongTails.Proofs.DuelingReferenceField

lemma tuning {p : Params} (hp : spec.valid p) :
    0 < slope p ∧ 0 < radius p ∧ radius p ≤ spacing p ∧
    4*p.M*p.L*radius p ≤ slope p * Real.sqrt (p.μ*p.ε) := by
  obtain ⟨hμ,hL,_,hr,hc,hM,hε⟩ := hp
  obtain ⟨hs,_,_⟩ := spacing_bounds hr
  have hm : 0 < slope p := by unfold LongTails.Algorithms.DuelingReferenceDescent.slope; positivity
  refine ⟨hm,lt_min hs (by positivity),min_le_left _ _, ?_⟩
  have hi := (le_div_iff₀ (show 0 < 4*p.M*p.L by positivity)).mp
    (min_le_right (spacing p) (slope p * Real.sqrt (p.μ*p.ε)/(4*p.M*p.L)))
  change _ * min _ _ ≤ _
  linarith

noncomputable def target {p : Params} (f : Point p.d → ℝ) (x u : Point p.d) : ℝ :=
  slope p * (f x-f u) + slope p * p.μ / 4 * ‖x-u‖^2 - slope p * p.ε / 4

lemma pointwise_drift {p : Params} {f : Point p.d → ℝ} {ρ : ℝ → ℝ}
    (hp : spec.valid p) (hf : Objective p f) (hr : Transfer p ρ)
    {x u y : Point p.d} (hx : x ∈ Ball p.d) (hu : u ∈ Ball p.d) (hy : y ∈ Ball p.d)
    (hmin : f u ≤ f x) (hd : ‖y-x‖ ≤ 2*radius p) :
    target (p := p) f x u ≤ ⟪x-u, weight (p := p) f ρ x y • gradient f y⟫ := by
  obtain ⟨hm, hh, hrs, hpar⟩ := tuning hp
  obtain ⟨hlo,hhi⟩ := weight_bounds hp hf hr hx hy (by linarith)
  let w := weight (p := p) f ρ x y
  have hw : 0 ≤ w := hm.le.trans hlo
  have hM : 0 ≤ p.M := hw.trans hhi
  have hsc := hf.strongly_convex x hx u hu
  rw [show u-x = -(x-u) by abel, inner_neg_right, norm_neg, real_inner_comm] at hsc
  have hbase : slope p*(f x-f u + p.μ/2*‖x-u‖^2) ≤ w*⟪x-u,gradient f x⟫ := by
    apply mul_le_mul hlo (by linarith)
      (add_nonneg (sub_nonneg.mpr hmin) (mul_nonneg (by linarith [hp.1]) (sq_nonneg _))) hw
  have hl := (hf.smooth y hy x hx).trans (mul_le_mul_of_nonneg_left hd hp.2.1.le)
  have herr := (abs_le.mp (abs_real_inner_le_norm (x-u) (gradient f y-gradient f x))).1
  rw [inner_sub_right] at herr
  have hnoise : w * (⟪x-u,gradient f x⟫ - ⟪x-u,gradient f y⟫) ≤
      ‖x-u‖ * (p.M * (p.L*(2*radius p))) := by
    calc
      _ ≤ w*(‖x-u‖*‖gradient f y-gradient f x‖) := by gcongr; linarith
      _ ≤ p.M*(‖x-u‖*(p.L*(2*radius p))) := by gcongr
      _ = _ := by ring
  have hs := Real.sq_sqrt (show 0 ≤ p.μ*p.ε from mul_nonneg hp.1.le hp.2.2.2.2.2.2.le)
  have hyoung := sq_nonneg (p.μ * ‖x-u‖ - Real.sqrt (p.μ*p.ε))
  have hy' : 2 * ‖x-u‖ * Real.sqrt (p.μ*p.ε) ≤ p.μ * ‖x-u‖^2 + p.ε := by
    apply le_of_mul_le_mul_left (a := p.μ) _ hp.1
    nlinarith
  have hsmall := mul_le_mul_of_nonneg_left hpar (norm_nonneg (x-u))
  unfold target
  rw [inner_smul_right]
  change _ ≤ w * _
  nlinarith only [hbase, hnoise, hsmall, mul_le_mul_of_nonneg_left hy' hm.le]

lemma continuous_weight {p : Params} {f : Point p.d → ℝ} {ρ : ℝ → ℝ}
    (hf : Objective p f) (hr : Transfer p ρ) (x : Point p.d) :
    Continuous (weight (p := p) f ρ x) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf.differentiable t).continuousAt
  unfold weight mean3
  have hh (i : Fin 3) := hr.continuous_derivative.comp (hfc.sub (continuous_const (y := f (anchor p x i))))
  exact (((hh 1).add (hh 2)).add (hh 0)).div_const _

lemma sphere_drift {p : Params} {f : Point p.d → ℝ} {ρ : ℝ → ℝ}
    (hp : spec.valid p) (hf : Objective p f) (hr : Transfer p ρ)
    {x u : Point p.d} (hx : x ∈ Ball p.d) (hu : u ∈ Ball p.d) (hmin : f u ≤ f x) :
    target (p := p) f x u ≤ ⟪x-u, ∫ v : Direction p.d,
      ((p.d / radius p) * value (p := p) f ρ x ((1-radius p) • x+radius p • (v : Point p.d))) •
        (v : Point p.d) ∂(sphereLaw (Point p.d) : Measure _)⟫ := by
  let F := value (p := p) f ρ x
  let g := fun y => weight (p := p) f ρ x y • gradient f y
  have hg : Continuous g := (continuous_weight hf hr x).smul hf.continuous_gradient
  have hd : ∀ y, HasGradientAt F (g y) y := value_gradient hf hr x
  have hF := continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt
  obtain ⟨_, hh, hs, _⟩ := tuning hp
  have h1 := (spacing_bounds hp.2.2.2.1).2.1
  let z := (1-radius p) • x
  rw [← ball_boundary_gradient hF hg hd z hh.ne']
  have hi := ball_offset_continuous_integrable hg z (radius p)
  rw [← integral_inner (𝕜 := ℝ) hi]
  calc
    _ = ∫ _v : ℝ × Direction p.d, target (p := p) f x u ∂(radialLaw p.d (NeZero.pos p.d) : Measure ℝ).prod (sphereLaw (Point p.d) : Measure _) := by simp
    _ ≤ _ := integral_mono (integrable_const _) (hi.const_inner (x-u)) (fun v => ?_)
  have hv := mem_ball (ballOffset_norm v)
  exact pointwise_drift hp hf hr hx hu (convex_ball hx hv hh.le (hs.trans h1)) hmin
    (perturb_dist hx hv hh.le)

end LongTails.Proofs.DuelingReferenceField
