import LongTails.Proofs.WassersteinForwardIntegration
import LongTails.Proofs.GdConvex

open MeasureTheory
open LongTails.Setups.WassersteinSmoothComposite
open LongTails.Proofs.WassersteinForwardIntegration
open scoped NNReal

namespace LongTails.Proofs.WassersteinOracleGeometry

lemma transport_exists {p : Params} {I : Instance p.toPublic}
    {O : OracleTemplate.Oracle (Query p.d) (Reply p.d)} (h : Admissible p I O)
    (ξ : (k : ℕ) → O.Seed k) (μ ν : Distribution p.d) (hμ : μ ∈ I.Q) :
    Nonempty (OptimalTransport μ ν) := by
  obtain ⟨T, _⟩ := h.replies [] (ξ 0) (.transport μ ν) hμ
  exact ⟨T⟩

lemma potential_measurable {p : Params} {I : Instance p.toPublic}
    {O : OracleTemplate.Oracle (Query p.d) (Reply p.d)} (h : Admissible p I O) :
    Measurable I.V :=
  (continuous_iff_continuousAt.mpr (fun x => (h.gradient x).differentiableAt.continuousAt)).measurable

lemma gradient_measurable {p : Params} {I : Instance p.toPublic}
    {O : OracleTemplate.Oracle (Query p.d) (Reply p.d)} (h : Admissible p I O)
    (hL : 0 ≤ p.L) : Measurable I.gradient := by
  have hl : LipschitzWith (⟨p.L, hL⟩ : ℝ≥0) I.gradient := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [dist_eq_norm]
    change ‖I.gradient x - I.gradient y‖ ≤ p.L * ‖x - y‖
    exact h.smooth x y
  exact hl.continuous.measurable

lemma split_evi {p : Params} {I : Instance p.toPublic}
    {O : OracleTemplate.Oracle (Query p.d) (Reply p.d)} (h : Admissible p I O)
    (hL : 0 < p.L) (ξ : (k : ℕ) → O.Seed k) (μ b u v : Distribution p.d)
    (hu : u ∈ I.Q) (hv : v ∈ I.Q)
    (hf : (μ.law : Measure (Space p.d)).map
      (fun x => x - (1 / (2 * p.L)) • I.gradient x) = b.law)
    (hp : ∀ ρ ∈ I.Q, 2 * (1 / (2 * p.L)) * I.H u + squaredDistance b u ≤
      2 * (1 / (2 * p.L)) * I.H ρ + squaredDistance b ρ) :
    (1 / p.L) * (objective I u - objective I v) ≤
      squaredDistance μ v - squaredDistance u v - (1 / 2 : ℝ) * squaredDistance μ u := by
  have hc : ∀ x y, I.V x + inner ℝ (I.gradient x) (y - x) ≤ I.V y := by
    intro x y
    have hs := OracleTemplate.Gradient.convex_support h.convex h.gradient x y
    linarith
  have hs := OracleTemplate.Gradient.smooth_upper_bound h.gradient h.smooth
  have hi := fun μ => potential_integrable μ I.V I.gradient p.L hL.le
    (potential_measurable h) hc hs
  obtain ⟨Tu⟩ := transport_exists h ξ u b hu
  obtain ⟨Tv⟩ := transport_exists h ξ v μ hv
  have hscale : 2 * (1 / (2 * p.L)) = 1 / p.L := by ring
  have hprod : (1 / (2 * p.L)) * p.L = (1 / 2 : ℝ) := by
    field_simp
  have he := split_proximal_evi I.H h.generalizedConvex μ b u v hu hv I.V I.gradient
    (1 / (2 * p.L)) p.L (by positivity) hL.le (by rw [hprod]; norm_num)
    (potential_measurable h) (gradient_measurable h hL.le) (hi μ) (hi u) (hi v)
    h.smooth hc hs hf hp Tu Tv
  rw [hscale, hprod] at he
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at he
  exact he

end LongTails.Proofs.WassersteinOracleGeometry
