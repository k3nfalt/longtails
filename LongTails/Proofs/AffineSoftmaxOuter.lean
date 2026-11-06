import LongTails.Proofs.ExtragradientStep
import LongTails.Proofs.NondualProjection
import LongTails.Proofs.AffineSoftmaxRegularization
import LongTails.Proofs.ClippedSubgradientStep
import LongTails.Proofs.CappedProximalGeometry

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineSoftmaxOuter

open LongTails.Proofs.RecursiveEnvelopeGeometry (regularized)
open LongTails.Proofs.AffineSoftmaxRegularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma proximal_support {C : Set E} {f : E → ℝ} {g : E → E}
    (hf : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    (μ : ℝ) (y : E) {u z : E} (hu : u ∈ C) (hz : z ∈ C)
    (hmin : IsMinOn (regularized f μ y) C u) :
    f u + ⟪μ • (y - u), z - u⟫ ≤ f z := by
  have hn := OracleTemplate.NearZeroSum.minimizer_gradient_normal hf.1 hu hmin
    (hasGradientWithinAt_iff_hasFDerivWithinAt.mpr
      (regularized_hasGradientAt (hg u hu) μ y).hasFDerivAt.hasFDerivWithinAt) z hz
  have hv : g u + μ • (u - y) = g u - μ • (y - u) := by module
  rw [hv, inner_sub_left] at hn
  have hs := OracleTemplate.FrankWolfe.convex_support_on hf hu hz (hg u hu)
  linarith

lemma proximal_displacement_bound {C : Set E} {f : E → ℝ} {g : E → E}
    (hf : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    {μ G : ℝ} (hμ : 0 < μ) (hG : 0 ≤ G) {y u : E} (hy : y ∈ C) (hu : u ∈ C)
    (hmin : IsMinOn (regularized f μ y) C u)
    (hlip : f y - f u ≤ G * ‖y - u‖) : ‖y - u‖ ≤ G / μ := by
  have hs := proximal_support hf hg μ y hu hy hmin
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq] at hs
  apply (le_div_iff₀ hμ).2
  by_cases hn : ‖y - u‖ = 0
  · simpa only [hn, zero_mul] using hG
  · have hnpos : 0 < ‖y - u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    nlinarith

lemma proximal_residual_monotone {C : Set E} {f : E → ℝ} {g : E → E}
    (hf : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    (μ ν : ℝ) (y z : E) {u w : E} (hu : u ∈ C) (hw : w ∈ C)
    (humin : IsMinOn (regularized f μ y) C u)
    (hwmin : IsMinOn (regularized f ν z) C w) :
    0 ≤ ⟪μ • (y - u) - ν • (z - w), u - w⟫ := by
  have h1 := proximal_support hf hg μ y hu hw humin
  have h2 := proximal_support hf hg ν z hw hu hwmin
  rw [show w - u = -(u - w) by module, inner_neg_right] at h1
  rw [inner_sub_left]
  linarith

lemma proximal_parameter_distance {C : Set E} {f : E → ℝ} {g : E → E}
    (hf : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    {μ : ℝ} (hμ : 0 < μ) (ν : ℝ) (y z : E) {u w : E}
    (hu : u ∈ C) (hw : w ∈ C)
    (humin : IsMinOn (regularized f μ y) C u)
    (hwmin : IsMinOn (regularized f ν z) C w) :
    μ * ‖u - w‖ ≤ μ * ‖y - z‖ + |μ - ν| * ‖z - w‖ := by
  have hmono := proximal_residual_monotone hf hg μ ν y z hu hw humin hwmin
  have he : μ • (y - u) - ν • (z - w) =
      (μ • (y - z) + (μ - ν) • (z - w)) - μ • (u - w) := by module
  rw [he, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hmono
  have hn := norm_add_le (μ • (y - z)) ((μ - ν) • (z - w))
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hμ] at hn
  have hi := (real_inner_le_norm (μ • (y - z) + (μ - ν) • (z - w)) (u - w)).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg (u - w)))
  by_cases hd : ‖u - w‖ = 0
  · rw [hd, mul_zero]
    positivity
  · have hdpos : 0 < ‖u - w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    nlinarith only [hmono, hi, hdpos]

lemma proximal_coupling {C : Set E} {f : E → ℝ} {g : E → E}
    (hf : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (g x) x)
    {A a T μ : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hT : T = A + a)
    (x v y u xs : E) (hx : x ∈ C) (hu : u ∈ C) (hxs : xs ∈ C)
    (hcenter : T • y = A • x + a • v)
    (hmin : IsMinOn (regularized f μ y) C u) :
    T * f u - A * f x - a * f xs ≤
      a * ⟪μ • (y - u), v - xs⟫ - μ * T * ‖y - u‖ ^ 2 := by
  have hxbound := mul_le_mul_of_nonneg_left (proximal_support hf hg μ y hu hx hmin) hA
  have hsbound := mul_le_mul_of_nonneg_left (proximal_support hf hg μ y hu hxs hmin) ha
  have hb : A • (x - u) + a • (xs - u) = T • (y - u) - a • (v - xs) := by
    calc
      _ = (A • x + a • v) - T • u - a • (v - xs) := by rw [hT]; module
      _ = _ := by rw [← hcenter]; module
  have hi : A * ⟪μ • (y - u), x - u⟫ + a * ⟪μ • (y - u), xs - u⟫ =
      T * ⟪μ • (y - u), y - u⟫ - a * ⟪μ • (y - u), v - xs⟫ := by
    calc
      _ = ⟪μ • (y - u), A • (x - u) + a • (xs - u)⟫ := by
        rw [inner_add_right, inner_smul_right, inner_smul_right]
      _ = _ := by rw [hb, inner_sub_right, inner_smul_right, inner_smul_right]
  have hn : ⟪μ • (y - u), y - u⟫ = μ * ‖y - u‖ ^ 2 := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [hn] at hi
  rw [hT]
  rw [hT] at hi
  nlinarith

omit [CompleteSpace E] in
lemma projected_momentum_distance {C : Set E} (hC : IsCompact C) (hc : Convex ℝ C)
    {xs : E} (hxs : xs ∈ C) (v g : E) (a : ℝ) :
    ‖OracleTemplate.SaddlePoint.project C (v - (a / 2) • g) - xs‖ ^ 2 ≤
      ‖v - xs‖ ^ 2 - a * ⟪g, v - xs⟫ + a ^ 2 / 4 * ‖g‖ ^ 2 := by
  have hp := OracleTemplate.WeaklyConvexHeavyTailed.projection_nonexpansive_point
    (fun y z hz => (OracleTemplate.SaddlePoint.project_spec ⟨xs, hxs⟩ hC hc y).2 z hz)
    hxs (v - (a / 2) • g)
  simp only [norm_sub_rev xs] at hp
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hp
  have he : v - (a / 2) • g - xs = (v - xs) - (a / 2) • g := by module
  rw [he, norm_sub_sq_real (v - xs) ((a / 2) • g), norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_right,
    real_inner_comm g (v - xs)] at hs
  nlinarith only [hs]

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
lemma norm_add_square_split (x e : E) :
    ‖x + e‖ ^ 2 ≤ (3 / 2 : ℝ) * ‖x‖ ^ 2 + 3 * ‖e‖ ^ 2 := by
  have hs : ‖x + e‖ ^ 2 ≤ (‖x‖ + ‖e‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (norm_add_le x e)
  nlinarith [sq_nonneg (‖x‖ - 2 * ‖e‖)]

lemma outer_pointwise_energy {C : Set E} (hcompact : IsCompact C)
    {f : E → ℝ} {field : E → E} (hf : ConvexOn ℝ C f)
    (hg : ∀ x ∈ C, HasGradientAt f (field x) x)
    {A a T μ : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hμ : 0 ≤ μ)
    (hT : T = A + a) (hweight : μ * a ^ 2 = T)
    (x v y u xs xp estimate : E) (hx : x ∈ C) (hu : u ∈ C) (hxs : xs ∈ C)
    (hcenter : T • y = A • x + a • v)
    (hmin : IsMinOn (regularized f μ y) C u) :
    T * (f xp - f xs) +
        ‖OracleTemplate.SaddlePoint.project C (v - (a / 2) • estimate) - xs‖ ^ 2 +
        μ * T / 8 * ‖y - u‖ ^ 2 ≤
      A * (f x - f xs) + ‖v - xs‖ ^ 2 +
        T * (regularized f μ y xp - regularized f μ y u) -
        a * ⟪estimate - μ • (y - u), v - xs⟫ +
        3 * a ^ 2 / 4 * ‖estimate - μ • (y - u)‖ ^ 2 := by
  have hprox := proximal_coupling hf hg hA ha hT x v y u xs hx hu hxs hcenter hmin
  have happ : f xp ≤ f u + (regularized f μ y xp - regularized f μ y u) + μ / 2 * ‖y - u‖ ^ 2 := by
    unfold regularized
    rw [norm_sub_rev u y]
    nlinarith [mul_nonneg hμ (sq_nonneg ‖xp - y‖)]
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have happT := mul_le_mul_of_nonneg_left happ hT0
  have hproj := projected_momentum_distance hcompact hf.1 hxs v estimate a
  have hinner : ⟪estimate, v - xs⟫ =
      ⟪μ • (y - u), v - xs⟫ + ⟪estimate - μ • (y - u), v - xs⟫ := by
    rw [← inner_add_left]
    congr 1
    module
  rw [hinner] at hproj
  have hnorm := norm_add_square_split (μ • (y - u)) (estimate - μ • (y - u))
  rw [show μ • (y - u) + (estimate - μ • (y - u)) = estimate by module,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hnorm
  have hscaled := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ a ^ 2 / 4 by positivity)
  have hw : a ^ 2 * μ ^ 2 * ‖y - u‖ ^ 2 = μ * T * ‖y - u‖ ^ 2 := by
    rw [← hweight]
    ring
  rw [hT] at hprox happT hw ⊢
  nlinarith only [hprox, happT, hproj, hscaled, hw]

lemma integrate_outer_energy {Ω : Type*} [MeasurableSpace Ω]
    (Q : ProbabilityMeasure Ω) (energy gap : Ω → ℝ) (e : Ω → E)
    (v : E) {c T a D β σ φ : ℝ} (hT : 0 ≤ T) (ha : 0 ≤ a)
    (hβ : 0 ≤ β) (hv : ‖v‖ ≤ D)
    (henergy : Integrable energy (Q : Measure Ω))
    (hgap : Integrable gap (Q : Measure Ω))
    (he : Integrable e (Q : Measure Ω))
    (he2 : Integrable (fun ω => ‖e ω‖ ^ 2) (Q : Measure Ω))
    (hbias : ‖∫ ω, e ω ∂(Q : Measure Ω)‖ ≤ β)
    (hmse : (∫ ω, ‖e ω‖ ^ 2 ∂(Q : Measure Ω)) ≤ σ ^ 2)
    (hprox : (∫ ω, gap ω ∂(Q : Measure Ω)) ≤ φ)
    (hstep : ∀ ω, energy ω ≤ c + T * gap ω - a * ⟪e ω, v⟫ +
      3 * a ^ 2 / 4 * ‖e ω‖ ^ 2) :
    (∫ ω, energy ω ∂(Q : Measure Ω)) ≤
      c + T * φ + a * D * β + 3 * a ^ 2 / 4 * σ ^ 2 := by
  have hlin := (he.inner_const v).const_mul a
  have hquad := he2.const_mul (3 * a ^ 2 / 4)
  have hbase : Integrable (fun ω => c + T * gap ω) (Q : Measure Ω) :=
    (integrable_const c).add (hgap.const_mul T)
  have hsub : Integrable (fun ω => c + T * gap ω - a * ⟪e ω, v⟫) (Q : Measure Ω) :=
    hbase.sub hlin
  have hi := integral_mono henergy (hsub.add hquad) hstep
  simp only [Pi.add_apply] at hi
  rw [integral_add hsub hquad, integral_sub hbase hlin,
    integral_add (integrable_const c) (hgap.const_mul T), integral_const_mul,
    integral_const_mul, integral_const_mul] at hi
  simp only [integral_const, probReal_univ, one_smul] at hi
  have hinner : (∫ ω, ⟪e ω, v⟫ ∂(Q : Measure Ω)) =
      ⟪v, ∫ ω, e ω ∂(Q : Measure Ω)⟫ := by
    calc
      _ = ∫ ω, ⟪v, e ω⟫ ∂(Q : Measure Ω) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun ω => real_inner_comm _ _))
      _ = _ := integral_inner he v
  rw [hinner] at hi
  have hcauchy := abs_real_inner_le_norm v (∫ ω, e ω ∂(Q : Measure Ω))
  have hprod : ‖v‖ * ‖∫ ω, e ω ∂(Q : Measure Ω)‖ ≤ D * β :=
    (mul_le_mul_of_nonneg_left hbias (norm_nonneg v)).trans
      (mul_le_mul_of_nonneg_right hv hβ)
  have hb : -a * ⟪v, ∫ ω, e ω ∂(Q : Measure Ω)⟫ ≤ a * D * β := by
    have hl := neg_abs_le ⟪v, ∫ ω, e ω ∂(Q : Measure Ω)⟫
    have hm := mul_le_mul_of_nonneg_left (hcauchy.trans hprod) ha
    have hn := mul_le_mul_of_nonneg_left hl ha
    nlinarith only [hm, hn]
  have hp := mul_le_mul_of_nonneg_left hprox hT
  have hs := mul_le_mul_of_nonneg_left hmse (show 0 ≤ 3 * a ^ 2 / 4 by positivity)
  linarith

lemma outer_expected_energy [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Ω : Type*} [MeasurableSpace Ω] (Q : ProbabilityMeasure Ω)
    {C : Set E} (hcompact : IsCompact C) {f : E → ℝ} {field : E → E}
    (hf : ConvexOn ℝ C f) (hg : ∀ x ∈ C, HasGradientAt f (field x) x)
    {A a T μ D β σ φ : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hμ : 0 ≤ μ)
    (hβ : 0 ≤ β) (hT : T = A + a) (hweight : μ * a ^ 2 = T)
    (x v y u xs : E) (hx : x ∈ C) (hu : u ∈ C) (hxs : xs ∈ C)
    (hdiam : ‖v - xs‖ ≤ D) (hcenter : T • y = A • x + a • v)
    (hmin : IsMinOn (regularized f μ y) C u)
    (xp estimate : Ω → E) (hxp : Measurable xp) (hest : Measurable estimate)
    (hxpmem : ∀ ω, xp ω ∈ C)
    (hesti : Integrable estimate (Q : Measure Ω))
    (he2 : Integrable (fun ω => ‖estimate ω - μ • (y - u)‖ ^ 2) (Q : Measure Ω))
    (hbias : ‖(∫ ω, estimate ω ∂(Q : Measure Ω)) - μ • (y - u)‖ ≤ β)
    (hmse : (∫ ω, ‖estimate ω - μ • (y - u)‖ ^ 2 ∂(Q : Measure Ω)) ≤ σ ^ 2)
    (hprox : (∫ ω, regularized f μ y (xp ω) - regularized f μ y u
      ∂(Q : Measure Ω)) ≤ φ) :
    (∫ ω, T * (f (xp ω) - f xs) +
      ‖OracleTemplate.SaddlePoint.project C (v - (a / 2) • estimate ω) - xs‖ ^ 2 +
      μ * T / 8 * ‖y - u‖ ^ 2 ∂(Q : Measure Ω)) ≤
      A * (f x - f xs) + ‖v - xs‖ ^ 2 + T * φ + a * D * β +
      3 * a ^ 2 / 4 * σ ^ 2 := by
  have hfc : ContinuousOn f C := fun z hz => (hg z hz).continuousAt.continuousWithinAt
  have hrc : ContinuousOn (regularized f μ y) C :=
    hfc.add (((continuous_id.sub continuous_const).norm.pow 2).continuousOn.const_mul (μ / 2))
  have hgap := ConstrainedStochasticAcceleration.integrable_compact_image Q hcompact
    (fun z => regularized f μ y z - regularized f μ y u) (hrc.sub continuousOn_const)
    xp hxp hxpmem
  have hfi := ConstrainedStochasticAcceleration.integrable_compact_image Q hcompact
    (fun z => f z - f xs) (hfc.sub continuousOn_const) xp hxp hxpmem
  have hp : Continuous (OracleTemplate.SaddlePoint.project C) :=
    (LongTails.Proofs.NondualProjection.project_lipschitz ⟨xs, hxs⟩ hcompact hf.1).continuous
  have hpm : Measurable (fun ω => OracleTemplate.SaddlePoint.project C
      (v - (a / 2) • estimate ω)) :=
    hp.measurable.comp (measurable_const.sub (hest.const_smul (a / 2)))
  have hpi := ConstrainedStochasticAcceleration.integrable_compact_image Q hcompact
    (fun z => ‖z - xs‖ ^ 2) ((continuous_id.sub continuous_const).norm.pow 2).continuousOn
    _ hpm (fun ω => (OracleTemplate.SaddlePoint.project_spec ⟨xs, hxs⟩ hcompact hf.1 _).1)
  have henergy := ((hfi.const_mul T).add hpi).add
    (integrable_const (μ * T / 8 * ‖y - u‖ ^ 2))
  have he := hesti.sub (integrable_const (μ • (y - u)))
  have hb : ‖∫ ω, estimate ω - μ • (y - u) ∂(Q : Measure Ω)‖ ≤ β := by
    rw [integral_sub hesti (integrable_const _), integral_const, probReal_univ, one_smul]
    exact hbias
  exact integrate_outer_energy Q _ _ _ (v - xs) (by rw [hT]; positivity) ha hβ hdiam
    henergy hgap he he2 hb hmse hprox (fun ω =>
      outer_pointwise_energy hcompact hf hg hA ha hμ hT hweight
        x v y u xs (xp ω) (estimate ω) hx hu hxs hcenter hmin)

end LongTails.Proofs.AffineSoftmaxOuter
