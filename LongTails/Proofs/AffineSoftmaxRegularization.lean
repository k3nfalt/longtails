import Mathlib.Analysis.Convex.Extrema
import LongTails.Proofs.ConstrainedStochasticAcceleration
import LongTails.Proofs.HessianAdaptiveCubicModel
import LongTails.Proofs.NearZeroSumCalculus
import LongTails.Proofs.RecursiveEnvelopeGeometry
import LongTails.Proofs.FrankWolfeDescent

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineSoftmaxRegularization

open LongTails.Proofs.RecursiveEnvelopeGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
lemma regularized_hasGradientAt {f : E → ℝ} {g x : E} (hg : HasGradientAt f g x)
    (μ : ℝ) (c : E) :
    HasGradientAt (regularized f μ c) (g + μ • (x - c)) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hg ⊢
  unfold regularized
  convert! hg.add ((((hasFDerivAt_id x).sub_const c).norm_sq).const_mul (μ / 2)) using 1
  ext y
  simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  ring

omit [CompleteSpace E] in
lemma regularized_strongConvexOn {C : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ C f) (μ : ℝ) (c : E) :
    StrongConvexOn C μ (regularized f μ c) := by
  have hh := OracleTemplate.NearZeroSum.strong_convex_add_quadratic
    (strongConvexOn_zero.mpr hf) (β := μ) (k := 0) c
  change StrongConvexOn C μ (fun x => f x + μ / 2 * ‖x - c‖ ^ 2)
  simpa only [zero_add, add_zero] using hh

omit [CompleteSpace E] in
lemma regularized_convexOn {C : Set E} {f : E → ℝ} {μ : ℝ}
    (hf : ConvexOn ℝ C f) (hμ : 0 ≤ μ) (c : E) : ConvexOn ℝ C (regularized f μ c) :=
  strongConvexOn_zero.mp (StrongConvexOn.mono hμ (regularized_strongConvexOn hf μ c))

lemma regularized_support_on {C : Set E} {f : E → ℝ} {g : E → E}
    (hf : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    (μ : ℝ) (c : E) {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    regularized f μ c x + ⟪g x + μ • (x - c), y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤
      regularized f μ c y := by
  have hh := OracleTemplate.FrankWolfe.convex_support_on hf hx hy (hg x hx)
  unfold regularized
  rw [squared_shift x y c, inner_add_left, real_inner_smul_left]
  linarith

lemma regularized_growth_on {C : Set E} {f : E → ℝ} {g : E → E}
    (hf : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    (μ : ℝ) (c : E) {u x : E} (hu : u ∈ C) (hx : x ∈ C)
    (hmin : IsMinOn (regularized f μ c) C u) :
    μ / 2 * ‖x - u‖ ^ 2 ≤ regularized f μ c x - regularized f μ c u := by
  have hnormal := OracleTemplate.NearZeroSum.minimizer_gradient_normal hf.1 hu hmin
    (hasGradientWithinAt_iff_hasFDerivWithinAt.mpr
      (regularized_hasGradientAt (hg u hu) μ c).hasFDerivAt.hasFDerivWithinAt) x hx
  have hh := regularized_support_on hf hg μ c hu hx
  linarith

omit [CompleteSpace E] in
lemma regularized_field_lipschitz {C : Set E} {g : E → E} {L μ : ℝ}
    (hlip : ∀ x ∈ C, ∀ y ∈ C, ‖g x - g y‖ ≤ L * ‖x - y‖) (hμ : 0 ≤ μ)
    (c : E) {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    ‖(g x + μ • (x - c)) - (g y + μ • (y - c))‖ ≤ (L + μ) * ‖x - y‖ := by
  have he : (g x + μ • (x - c)) - (g y + μ • (y - c)) =
      (g x - g y) + μ • (x - y) := by module
  rw [he]
  calc
    _ ≤ ‖g x - g y‖ + ‖μ • (x - y)‖ := norm_add_le _ _
    _ ≤ L * ‖x - y‖ + μ * ‖x - y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hμ]
      linarith [hlip x hx y hy]
    _ = (L + μ) * ‖x - y‖ := by ring

noncomputable def exactProx (C : Set E) (f : E → ℝ) (μ : ℝ) (c : E) : E :=
  Classical.epsilon (fun x => x ∈ C ∧ IsMinOn (regularized f μ c) C x)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma exactProx_spec {C : Set E} {f : E → ℝ} (hC : IsCompact C)
    (hne : C.Nonempty) (hf : ContinuousOn f C) (μ : ℝ) (c : E) :
    exactProx C f μ c ∈ C ∧ IsMinOn (regularized f μ c) C (exactProx C f μ c) := by
  have hc : ContinuousOn (regularized f μ c) C :=
    hf.add (((continuous_id.sub continuous_const).norm.pow 2).continuousOn.const_mul (μ / 2))
  exact Classical.epsilon_spec (hC.exists_isMinOn hne hc)

omit [CompleteSpace E] in
lemma exactProx_unique {C : Set E} {f : E → ℝ} (hf : ConvexOn ℝ C f)
    {μ : ℝ} (hμ : 0 < μ) (c : E) {x y : E} (hx : x ∈ C) (hy : y ∈ C)
    (hxm : IsMinOn (regularized f μ c) C x) (hym : IsMinOn (regularized f μ c) C y) : x = y :=
  ((regularized_strongConvexOn hf μ c).strictConvexOn hμ).eq_of_isMinOn hxm hym hx hy

omit [CompleteSpace E] in
lemma exactProx_continuous {X : Type*} [TopologicalSpace X]
    {C : Set E} {f : E → ℝ} (hC : IsCompact C) (hne : C.Nonempty)
    (hf : ConvexOn ℝ C f) (hfc : ContinuousOn f C)
    (μ : X → ℝ) (c : X → E) (hμ : Continuous μ) (hc : Continuous c)
    (hμpos : ∀ z, 0 < μ z) : Continuous (fun z => exactProx C f (μ z) (c z)) := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let m : X → C := fun z => ⟨exactProx C f (μ z) (c z), (exactProx_spec hC hne hfc _ _).1⟩
  have hm : Continuous m := by
    apply HessianAdaptiveCubicModel.continuous_unique_minimizer
      (fun z (x : C) => regularized f (μ z) (c z) x) m
    · have hv : Continuous (fun z : X × C => f z.2) := hfc.domRestrict.comp continuous_snd
      have hd : Continuous (fun z : X × C => (z.2 : E) - c z.1) :=
        (continuous_subtype_val.comp continuous_snd).sub (hc.comp continuous_fst)
      exact hv.add (((hμ.comp continuous_fst).div_const 2).mul (hd.norm.pow 2))
    · intro z x
      exact (exactProx_spec hC hne hfc _ _).2 x.property
    · intro z x hx
      apply Subtype.ext
      apply exactProx_unique hf (hμpos z) (c z) x.property (m z).property
      · intro y hy
        exact hx ⟨y, hy⟩
      · exact (exactProx_spec hC hne hfc _ _).2
  exact continuous_subtype_val.comp hm

lemma expected_regularized_distance_le [MeasurableSpace E] [BorelSpace E]
    {Ω : Type*} [MeasurableSpace Ω] (Q : MeasureTheory.ProbabilityMeasure Ω)
    {C : Set E} (hC : IsCompact C) {f : E → ℝ} {g : E → E}
    (hf : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    {μ d : ℝ} (hμ : 0 < μ) (c : E) {u : E} (hu : u ∈ C)
    (hmin : IsMinOn (regularized f μ c) C u) (initial : Ω → E)
    (hm : Measurable initial) (hi : ∀ ω, initial ω ∈ C)
    (hgap : (∫ ω, regularized f μ c (initial ω) - regularized f μ c u
      ∂(Q : MeasureTheory.Measure Ω)) ≤ d) :
    (∫ ω, ‖initial ω - u‖ ^ 2 ∂(Q : MeasureTheory.Measure Ω)) ≤ 2 * d / μ := by
  have hfc : ContinuousOn f C := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hrc : ContinuousOn (regularized f μ c) C :=
    hfc.add (((continuous_id.sub continuous_const).norm.pow 2).continuousOn.const_mul (μ / 2))
  have hFi := ConstrainedStochasticAcceleration.integrable_compact_image Q hC
    (fun x => regularized f μ c x - regularized f μ c u) (hrc.sub continuousOn_const)
    initial hm hi
  have hdi := ConstrainedStochasticAcceleration.integrable_compact_image Q hC
    (fun x => ‖x - u‖ ^ 2) ((continuous_id.sub continuous_const).norm.pow 2).continuousOn
    initial hm hi
  have hh := MeasureTheory.integral_mono (hdi.const_mul (μ / 2)) hFi
    (fun ω => regularized_growth_on hf hg μ c hu (hi ω) hmin)
  rw [MeasureTheory.integral_const_mul] at hh
  apply (le_div_iff₀ hμ).2
  linarith

omit [CompleteSpace E] in
lemma local_min_global_of_interior_ball {X : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ X f) {y v : E} {r : ℝ} (hv : v ∈ X)
    (hvr : ‖v - y‖ < r) (hmin : IsMinOn f (X ∩ Metric.closedBall y r) v) :
    IsMinOn f X v := by
  apply IsMinOn.of_isLocalMinOn_of_convexOn hv _ hf
  have hn : Metric.ball y r ∈ nhds v := Metric.isOpen_ball.mem_nhds (by
    simpa only [Metric.mem_ball, dist_eq_norm] using hvr)
  have hn' : ∀ᶠ x in nhdsWithin v X, x ∈ Metric.ball y r :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hn
  filter_upwards [hn', self_mem_nhdsWithin] with x hx hX
  exact hmin ⟨hX, Metric.ball_subset_closedBall hx⟩

omit [CompleteSpace E] in
lemma local_min_displacement {X : Set E} {f : E → ℝ} (hf : ConvexOn ℝ X f)
    {y u v : E} {r : ℝ} (hu : u ∈ X) (hglobal : IsMinOn f X u)
    (hunique : ∀ w ∈ X, IsMinOn f X w → w = u)
    (hv : v ∈ X ∩ Metric.closedBall y r)
    (hlocal : IsMinOn f (X ∩ Metric.closedBall y r) v) :
    ‖v - y‖ = min r ‖u - y‖ := by
  have hvr : ‖v - y‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hv.2
  by_cases hur : ‖u - y‖ ≤ r
  · have huK : u ∈ X ∩ Metric.closedBall y r :=
      ⟨hu, by simpa only [Metric.mem_closedBall, dist_eq_norm] using hur⟩
    have hvglobal : IsMinOn f X v := by
      intro x hx
      change f v ≤ f x
      exact le_trans (show f v ≤ f u from hlocal huK) (show f u ≤ f x from hglobal hx)
    rw [hunique v hv.1 hvglobal, min_eq_right hur]
  · have hboundary : ‖v - y‖ = r := by
      by_contra hne
      have hvglobal := local_min_global_of_interior_ball hf hv.1 (lt_of_le_of_ne hvr hne) hlocal
      have he := hunique v hv.1 hvglobal
      exact hur (he ▸ hvr)
    rw [hboundary, min_eq_left (le_of_not_ge hur)]

end LongTails.Proofs.AffineSoftmaxRegularization
