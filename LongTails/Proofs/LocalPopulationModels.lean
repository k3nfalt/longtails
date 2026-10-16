import LongTails.Proofs.LocalPopulationSmoothing
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.Algebra.Group.Pointwise
import LongTails.Proofs.NearZeroSumCalculus

open MeasureTheory Set
open scoped RealInnerProductSpace Pointwise

namespace LongTails.Proofs.LocalPopulationModels

open LongTails.Proofs.LocalPopulationSmoothing OracleTemplate.ZerothOrder

variable {d : ℕ} [NeZero d]
local notation "H" => EuclideanSpace ℝ (Fin d)
local notation "S" => Metric.sphere (0 : H) 1
local notation "Q" => (sphereLaw H : Measure S)
local notation "P" => (Measure.prod (radialLaw d (NeZero.pos d) : Measure ℝ) (Q))

lemma ball_smoothing_lower_on {f : H → ℝ} {C : Set H} (hf : Continuous f)
    (hc : ConvexOn ℝ C f) (hclosed : IsClosed C) (x : H) (γ : ℝ)
    (hlegal : ∀ v : ℝ × S, x + γ • ballOffset v ∈ C) : f x ≤ ballSmooth f γ x := by
  have hz : Integrable (fun v : ℝ × S => γ • ballOffset v) (P) := by
    simpa only [zero_add, id_eq] using ball_offset_continuous_integrable (f := id) continuous_id (0 : H) γ
  have hi : Integrable (fun v : ℝ × S => x + γ • ballOffset v) (P) := (integrable_const x).add hz
  have hh := hc.map_integral_le hf.continuousOn hclosed (Filter.Eventually.of_forall hlegal) hi
    (ball_offset_continuous_integrable hf x γ)
  rw [integral_add (integrable_const x) hz] at hh
  simpa only [ballSmooth, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul,
    integral_smul, ball_offset_mean_zero, smul_zero, add_zero] using hh

lemma ball_smoothing_lipschitz_bias {f : H → ℝ} {M : NNReal} (hL : LipschitzWith M f)
    (x : H) (γ : ℝ) : |ballSmooth f γ x - f x| ≤ (M : ℝ) * |γ| := by
  have hi := ball_offset_continuous_integrable hL.continuous x γ
  have hb (v : ℝ × S) : ‖f (x + γ • ballOffset v) - f x‖ ≤ (M : ℝ) * |γ| := by
    have h := hL.dist_le_mul (x + γ • ballOffset v) x
    rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left (ballOffset_norm v) (abs_nonneg γ)).trans_eq (mul_one _)) M.coe_nonneg)
  have hh := norm_integral_le_of_norm_le_const (μ := P) (Filter.Eventually.of_forall hb)
  rw [integral_sub hi (integrable_const (f x))] at hh
  simpa only [ballSmooth, integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul, mul_one, Real.norm_eq_abs] using hh

lemma ball_smoothing_local_smooth_bias {f : H → ℝ} (hf : Continuous f) {L γ : ℝ}
    (hL : 0 ≤ L) (x g : H)
    (hmodel : ∀ v : ℝ × S, f (x + γ • ballOffset v) ≤
      f x + ⟪g, γ • ballOffset v⟫ + L / 2 * ‖γ • ballOffset v‖ ^ 2) :
    ballSmooth f γ x ≤ f x + L * γ ^ 2 / 2 := by
  have hi := ball_offset_continuous_integrable hf x γ
  have hz : Integrable (fun v : ℝ × S => γ • ballOffset v) (P) := by
    simpa only [zero_add, id_eq] using ball_offset_continuous_integrable (f := id) continuous_id (0 : H) γ
  have hu (v : ℝ × S) : f (x + γ • ballOffset v) ≤ f x + ⟪g, γ • ballOffset v⟫ + L * γ ^ 2 / 2 := by
    have hn : ‖γ • ballOffset v‖ ≤ |γ| := by
      rw [norm_smul, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (ballOffset_norm v) (abs_nonneg γ)).trans_eq (mul_one _)
    have hs : ‖γ • ballOffset v‖ ^ 2 ≤ γ ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [hmodel v, mul_le_mul_of_nonneg_left hs hL]
  have hh := integral_mono hi (((integrable_const _).add (hz.const_inner g)).add (integrable_const _)) hu
  simp only [Pi.add_apply] at hh
  rw [integral_add ((integrable_const _).add (hz.const_inner g)) (integrable_const _),
    integral_add (integrable_const _) (hz.const_inner g), integral_inner (𝕜 := ℝ) hz g] at hh
  simpa only [ballSmooth, integral_smul, ball_offset_mean_zero, smul_zero, inner_zero_right,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul, add_zero] using hh


omit [NeZero d] in
lemma convex_on_of_support {f : H → ℝ} {g : H → H} {C : Set H} (hC : Convex ℝ C)
    (hs : ∀ x ∈ C, ∀ y ∈ C, f x + ⟪g x, y - x⟫ ≤ f y) : ConvexOn ℝ C f := by
  refine ⟨hC, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hz : z ∈ C := hC hx hy ha hb hab
  have h1 := mul_le_mul_of_nonneg_left (hs z hz x hx) ha
  have h2 := mul_le_mul_of_nonneg_left (hs z hz y hy) hb
  have he : a • (x - z) + b • (y - z) = (0 : H) := by
    calc
      _ = (a • x + b • y) - (a + b) • z := by module
      _ = 0 := by rw [hab, one_smul]; exact sub_self z
  have hi := congrArg (fun v => ⟪g z, v⟫) he
  simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at hi
  change f z ≤ a * f x + b * f y
  have heq := congrArg (fun r : ℝ => r * f z) hab
  nlinarith only [h1, h2, hi, heq]

omit [NeZero d] in
lemma quadratic_complement_convex {f : H → ℝ} {g : H → H} {C : Set H} {L : ℝ}
    (hC : Convex ℝ C)
    (hmodel : ∀ x ∈ C, ∀ y ∈ C, f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2) :
    ConvexOn ℝ C (fun x => L / 2 * ‖x‖ ^ 2 - f x) := by
  apply convex_on_of_support (g := fun x => L • x - g x) hC
  intro x hx y hy
  have hm := hmodel x hx y hy
  have he : L / 2 * ‖x‖ ^ 2 - f x + ⟪L • x - g x, y - x⟫ -
      (L / 2 * ‖y‖ ^ 2 - f y) = f y - f x - ⟪g x, y - x⟫ - L / 2 * ‖y - x‖ ^ 2 := by
    rw [norm_sub_sq_real]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [real_inner_comm y x]
    ring
  change L / 2 * ‖x‖ ^ 2 - f x + ⟪L • x - g x, y - x⟫ ≤ L / 2 * ‖y‖ ^ 2 - f y
  linarith only [he, hm]


lemma ball_smooth_quadratic_complement {f : H → ℝ} (hf : Continuous f) (L γ : ℝ) (x : H) :
    ballSmooth (fun z => L / 2 * ‖z‖ ^ 2 - f z) γ x =
      L / 2 * ‖x‖ ^ 2 - ballSmooth f γ x +
        ∫ v : ℝ × S, L / 2 * ‖γ • ballOffset v‖ ^ 2 ∂P := by
  have hi := ball_offset_continuous_integrable hf x γ
  have hz : Integrable (fun v : ℝ × S => γ • ballOffset v) (P) := by
    simpa only [zero_add, id_eq] using ball_offset_continuous_integrable (f := id) continuous_id (0 : H) γ
  have hsq : Integrable (fun v : ℝ × S => L / 2 * ‖γ • ballOffset v‖ ^ 2) (P) := by
    simpa only [zero_add] using ball_offset_continuous_integrable
      (f := fun z : H => L / 2 * ‖z‖ ^ 2) (by fun_prop) (0 : H) γ
  have he (v : ℝ × S) : L / 2 * ‖x + γ • ballOffset v‖ ^ 2 - f (x + γ • ballOffset v) =
      (L / 2 * ‖x‖ ^ 2 - f (x + γ • ballOffset v)) + L * ⟪x, γ • ballOffset v⟫ +
        L / 2 * ‖γ • ballOffset v‖ ^ 2 := by rw [norm_add_sq_real]; ring
  unfold ballSmooth
  simp_rw [he]
  have hsub : Integrable (fun v : ℝ × S => L / 2 * ‖x‖ ^ 2 - f (x + γ • ballOffset v)) (P) :=
    (integrable_const _).sub hi
  have hlin : Integrable (fun v : ℝ × S => L * ⟪x, γ • ballOffset v⟫) (P) := (hz.const_inner x).const_mul L
  have hsum : Integrable (fun v : ℝ × S => L / 2 * ‖x‖ ^ 2 - f (x + γ • ballOffset v) + L * ⟪x, γ • ballOffset v⟫) (P) := hsub.add hlin
  rw [integral_add hsum hsq, integral_add hsub hlin,
    integral_sub (integrable_const (L / 2 * ‖x‖ ^ 2)) hi, integral_const_mul L, integral_inner (𝕜 := ℝ) hz x]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul,
    integral_smul, ball_offset_mean_zero, smul_zero, inner_zero_right, mul_zero, add_zero]

lemma ball_smooth_complement_convex {f : H → ℝ} {g : H → H} {C D : Set H} {L γ : ℝ}
    (hf : Continuous f) (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hmodel : ∀ x ∈ C, ∀ y ∈ C, f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hlegal : ∀ x ∈ D, ∀ v : ℝ × S, x + γ • ballOffset v ∈ C) :
    ConvexOn ℝ D (fun x => L / 2 * ‖x‖ ^ 2 - ballSmooth f γ x) := by
  have hq : Continuous (fun x : H => L / 2 * ‖x‖ ^ 2 - f x) := by fun_prop
  have hc := ball_smooth_convex_on hq (quadratic_complement_convex hC hmodel) hD hlegal
  refine ⟨hD, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hc.2 hx hy ha hb hab
  simp only [ball_smooth_quadratic_complement hf, smul_eq_mul] at hh
  have he := congrArg (fun r : ℝ => r * (∫ v : ℝ × S, L / 2 * ‖γ • ballOffset v‖ ^ 2 ∂P)) hab
  simp only [one_mul] at he
  change L / 2 * ‖a • x + b • y‖ ^ 2 - ballSmooth f γ (a • x + b • y) ≤
    a * (L / 2 * ‖x‖ ^ 2 - ballSmooth f γ x) + b * (L / 2 * ‖y‖ ^ 2 - ballSmooth f γ y)
  nlinarith only [hh, he]


lemma ball_smooth_local_upper_model {f : H → ℝ} {g : H → H} {C D : Set H} {M : NNReal} {L γ : ℝ}
    (hLip : LipschitzWith M f) (hC : Convex ℝ C) (hD : Convex ℝ D) (hγ : 0 < γ)
    (hmodel : ∀ x ∈ C, ∀ y ∈ C, f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2)
    (hlegal : ∀ x ∈ D, ∀ v : ℝ × S, x + γ • ballOffset v ∈ C)
    {x y : H} (hx : x ∈ D) (hy : y ∈ D) :
    ballSmooth f γ y ≤ ballSmooth f γ x + ⟪boundaryField f γ x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  have hc := ball_smooth_complement_convex hLip.continuous hC hD hmodel hlegal
  have hg : HasGradientAt (fun z => L / 2 * ‖z‖ ^ 2 - ballSmooth f γ z)
      (L • x - boundaryField f γ x) x := by
    have hh := (OracleTemplate.NearZeroSum.gradient_quadratic L x).hasFDerivAt.sub
      (ball_smooth_gradient_lipschitz_function hLip hγ x).hasFDerivAt
    rw [hasGradientAt_iff_hasFDerivAt]
    convert hh using 1
    simp only [map_sub]
  have hs := OracleTemplate.FrankWolfe.convex_support_on hc hx hy hg
  simp only [inner_sub_left, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq] at hs
  rw [norm_sub_sq_real, real_inner_comm x y]
  simp only [inner_sub_right]
  nlinarith only [hs]

lemma ball_smooth_local_upper_of_gradient {f : H → ℝ} {g : H → H} {C D : Set H} {M : NNReal} {L γ : ℝ}
    (hLip : LipschitzWith M f) (hC : Convex ℝ C) (hD : Convex ℝ D) (hγ : 0 < γ)
    (hg : ∀ x ∈ C, HasGradientWithinAt f (g x) C x)
    (hglip : ∀ x ∈ C, ∀ y ∈ C, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hlegal : ∀ x ∈ D, ∀ v : ℝ × S, x + γ • ballOffset v ∈ C)
    {x y : H} (hx : x ∈ D) (hy : y ∈ D) :
    ballSmooth f γ y ≤ ballSmooth f γ x + ⟪boundaryField f γ x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 :=
  ball_smooth_local_upper_model hLip hC hD hγ
    (fun _ hx _ hy => OracleTemplate.NearZeroSum.smooth_upper_within hC hg hglip hx hy) hlegal hx hy

omit [NeZero d] in
lemma continuous_convex_on_closure {f : H → ℝ} {C : Set H}
    (hf : Continuous f) (hc : ConvexOn ℝ C f) : ConvexOn ℝ (closure C) f := by
  refine ⟨hc.1.closure, ?_⟩
  intro x hx y hy a b ha hb hab
  have hclosed : IsClosed {p : H × H | f (a • p.1 + b • p.2) ≤ a * f p.1 + b * f p.2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hsub : C ×ˢ C ⊆ {p : H × H | f (a • p.1 + b • p.2) ≤ a * f p.1 + b * f p.2} := by
    intro p hp
    exact hc.2 hp.1 hp.2 ha hb hab
  have hh := closure_minimal hsub hclosed
  rw [closure_prod_eq] at hh
  exact hh (show (x, y) ∈ closure C ×ˢ closure C from ⟨hx, hy⟩)

omit [NeZero d] in
lemma quadratic_complement_convex_of_interior {f : H → ℝ} {g : H → H}
    {C : Set H} {L : ℝ} (hf : Continuous f) (hC : Convex ℝ C)
    (hclosed : IsClosed C) (hne : (interior C).Nonempty)
    (hg : ∀ x ∈ interior C, HasGradientWithinAt f (g x) (interior C) x)
    (hglip : ∀ x ∈ interior C, ∀ y ∈ interior C, ‖g x - g y‖ ≤ L * ‖x - y‖) :
    ConvexOn ℝ C (fun x => L / 2 * ‖x‖ ^ 2 - f x) := by
  have hm := quadratic_complement_convex hC.interior
    (fun _ hx _ hy => OracleTemplate.NearZeroSum.smooth_upper_within hC.interior hg hglip hx hy)
  have hh := continuous_convex_on_closure (f := fun x => L / 2 * ‖x‖ ^ 2 - f x)
    (by fun_prop) hm
  rwa [hC.closure_interior_eq_closure_of_nonempty_interior hne, hclosed.closure_eq] at hh

omit [NeZero d] in
lemma local_taylor_to_boundary {f : H → ℝ} {g : H → H} {C : Set H} {L : ℝ}
    (hf : Continuous f) (hC : Convex ℝ C) (hclosed : IsClosed C)
    (hne : (interior C).Nonempty)
    (hg : ∀ x ∈ interior C, HasGradientWithinAt f (g x) (interior C) x)
    (hglip : ∀ x ∈ interior C, ∀ y ∈ interior C, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {x y : H} (hx : x ∈ interior C) (hy : y ∈ C) :
    f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  have hs : IsClosed {y : H | f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2} :=
    isClosed_le hf (by fun_prop)
  have hi : interior C ⊆ {y : H | f y ≤ f x + ⟪g x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2} := by
    intro y hy
    exact OracleTemplate.NearZeroSum.smooth_upper_within hC.interior hg hglip hx hy
  have hh := closure_minimal hi hs
  rw [hC.closure_interior_eq_closure_of_nonempty_interior hne, hclosed.closure_eq] at hh
  exact hh hy

lemma ball_smooth_upper_of_complement {f : H → ℝ} {C D : Set H} {M : NNReal} {L γ : ℝ}
    (hLip : LipschitzWith M f) (hc : ConvexOn ℝ C (fun x => L / 2 * ‖x‖ ^ 2 - f x))
    (hD : Convex ℝ D) (hγ : 0 < γ)
    (hlegal : ∀ x ∈ D, ∀ v : ℝ × S, x + γ • ballOffset v ∈ C)
    {x y : H} (hx : x ∈ D) (hy : y ∈ D) :
    ballSmooth f γ y ≤ ballSmooth f γ x + ⟪boundaryField f γ x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  have hf := hLip.continuous
  have hq : Continuous (fun x : H => L / 2 * ‖x‖ ^ 2 - f x) := by fun_prop
  have hs := ball_smooth_convex_on hq hc hD hlegal
  have hc' : ConvexOn ℝ D (fun x => L / 2 * ‖x‖ ^ 2 - ballSmooth f γ x) := by
    refine ⟨hD, ?_⟩
    intro u hu v hv a b ha hb hab
    have hh := hs.2 hu hv ha hb hab
    simp only [ball_smooth_quadratic_complement hLip.continuous, smul_eq_mul] at hh
    have he := congrArg (fun r : ℝ => r * (∫ v : ℝ × S, L / 2 * ‖γ • ballOffset v‖ ^ 2 ∂P)) hab
    simp only [one_mul] at he
    change L / 2 * ‖a • u + b • v‖ ^ 2 - ballSmooth f γ (a • u + b • v) ≤
      a * (L / 2 * ‖u‖ ^ 2 - ballSmooth f γ u) + b * (L / 2 * ‖v‖ ^ 2 - ballSmooth f γ v)
    nlinarith only [hh, he]
  have hg : HasGradientAt (fun z => L / 2 * ‖z‖ ^ 2 - ballSmooth f γ z)
      (L • x - boundaryField f γ x) x := by
    have hh := (OracleTemplate.NearZeroSum.gradient_quadratic L x).hasFDerivAt.sub
      (ball_smooth_gradient_lipschitz_function hLip hγ x).hasFDerivAt
    rw [hasGradientAt_iff_hasFDerivAt]
    convert hh using 1
    simp only [map_sub]
  have hh := OracleTemplate.FrankWolfe.convex_support_on hc' hx hy hg
  simp only [inner_sub_left, real_inner_smul_left, inner_sub_right, real_inner_self_eq_norm_sq] at hh
  rw [norm_sub_sq_real, real_inner_comm x y]
  simp only [inner_sub_right]
  nlinarith only [hh]

lemma ball_smooth_upper_of_interior_gradient {f : H → ℝ} {g : H → H}
    {C D : Set H} {M : NNReal} {L γ : ℝ}
    (hLip : LipschitzWith M f) (hC : Convex ℝ C) (hclosed : IsClosed C)
    (hne : (interior C).Nonempty) (hD : Convex ℝ D) (hγ : 0 < γ)
    (hg : ∀ x ∈ interior C, HasGradientWithinAt f (g x) (interior C) x)
    (hglip : ∀ x ∈ interior C, ∀ y ∈ interior C, ‖g x - g y‖ ≤ L * ‖x - y‖)
    (hlegal : ∀ x ∈ D, ∀ v : ℝ × S, x + γ • ballOffset v ∈ C)
    {x y : H} (hx : x ∈ D) (hy : y ∈ D) :
    ballSmooth f γ y ≤ ballSmooth f γ x + ⟪boundaryField f γ x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 :=
  ball_smooth_upper_of_complement hLip
    (quadratic_complement_convex_of_interior hLip.continuous hC hclosed hne hg hglip) hD hγ hlegal hx hy

omit [NeZero d] in
lemma thickening_closed_ball {C : Set H} {x : H} (hx : x ∈ C) {γ r : ℝ} (hγ : γ ≤ r) :
    Metric.closedBall x γ ⊆ C + Metric.closedBall 0 r := by
  intro y hy
  refine ⟨x, hx, y - x, ?_, by abel⟩
  simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using
    (Metric.mem_closedBall.mp hy).trans hγ

omit [NeZero d] in
lemma thickening_ball_interior {C : Set H} {x : H} (hx : x ∈ C) (r : ℝ) :
    Metric.ball x r ⊆ interior (C + Metric.closedBall 0 r) := by
  apply Metric.isOpen_ball.subset_interior_iff.mpr
  exact Metric.ball_subset_closedBall.trans (thickening_closed_ball hx le_rfl)

omit [NeZero d] in
lemma thickening_uniform_margin {C : Set H} {x : H} (hx : x ∈ C) {η r : ℝ} (hη : η < r) :
    Metric.closedBall x η ⊆ interior (C + Metric.closedBall 0 r) := by
  exact (Metric.closedBall_subset_ball hη).trans (thickening_ball_interior hx r)

omit [NeZero d] in
lemma thickening_compact {C : Set H} (hC : IsCompact C) (r : ℝ) :
    IsCompact (C + Metric.closedBall 0 r) :=
  hC.add (isCompact_closedBall 0 r)

omit [NeZero d] in
lemma thickening_convex {C : Set H} (hC : Convex ℝ C) (r : ℝ) :
    Convex ℝ (C + Metric.closedBall 0 r) :=
  hC.add (convex_closedBall 0 r)

omit [NeZero d] in
lemma nearest_projection_lipschitz {C : Set H} (hC : Convex ℝ C) {project : H → H}
    (hp : ∀ x, project x ∈ C)
    (hnearest : ∀ x, ‖x - project x‖ = ⨅ y : C, ‖x - y‖) : LipschitzWith 1 project := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have hx := (norm_eq_iInf_iff_real_inner_le_zero hC (hp x)).mp (hnearest x) (project y) (hp y)
  have hy := (norm_eq_iInf_iff_real_inner_le_zero hC (hp y)).mp (hnearest y) (project x) (hp x)
  have hid : ⟪project x - project y, x - y⟫ - ‖project x - project y‖ ^ 2 =
      -⟪x - project x, project y - project x⟫ - ⟪y - project y, project x - project y⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm (project x) x, real_inner_comm (project x) y,
      real_inner_comm (project y) x, real_inner_comm (project y) y]
    ring
  have hi := real_inner_le_norm (project x - project y) (x - y)
  have hs : ‖project x - project y‖ ^ 2 ≤ ‖project x - project y‖ * ‖x - y‖ := by
    linarith only [hx, hy, hid, hi]
  by_cases hz : ‖project x - project y‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hpos : 0 < ‖project x - project y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith only [hs, hpos]

lemma local_extension_models {f : H → ℝ} {C D : Set H} {M : NNReal} {γ : ℝ}
    (hLip : LipschitzOnWith M f C) (hc : ConvexOn ℝ C f) (hclosed : IsClosed C)
    (hne : (interior C).Nonempty) (hD : Convex ℝ D) (hDC : D ⊆ interior C)
    (hγ : 0 < γ) (hball : ∀ x ∈ D, Metric.closedBall x γ ⊆ C) :
    ∃ F : H → ℝ, LipschitzWith M F ∧ EqOn f F C ∧
      (∀ x ∈ D, ∀ y ∈ D,
        ballSmooth F γ x + ⟪boundaryField F γ x, y - x⟫ ≤ ballSmooth F γ y ∧
        ballSmooth F γ y ≤ ballSmooth F γ x + ⟪boundaryField F γ x, y - x⟫ +
          (Real.sqrt d * (M : ℝ) / γ) / 2 * ‖y - x‖ ^ 2) ∧
      (∀ x ∈ D, f x ≤ ballSmooth F γ x ∧ ballSmooth F γ x ≤ f x + (M : ℝ) * γ) ∧
      ∀ (g : H → H) (L : ℝ), 0 ≤ L →
        (∀ x ∈ interior C, HasGradientWithinAt f (g x) (interior C) x) →
        (∀ x ∈ interior C, ∀ y ∈ interior C, ‖g x - g y‖ ≤ L * ‖x - y‖) →
        (∀ x ∈ D, ∀ y ∈ D, ballSmooth F γ y ≤ ballSmooth F γ x +
          ⟪boundaryField F γ x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2) ∧
        (∀ x ∈ D, ballSmooth F γ x ≤ f x + L * γ ^ 2 / 2) := by
  obtain ⟨F, hF, he⟩ := hLip.extend_real
  have hcF : ConvexOn ℝ C F := hc.congr he
  have hlegal (x : H) (hx : x ∈ D) (v : ℝ × S) : x + γ • ballOffset v ∈ C := by
    apply hball x hx
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hγ]
    exact (mul_le_mul_of_nonneg_left (ballOffset_norm v) hγ.le).trans_eq (mul_one γ)
  refine ⟨F, hF, he, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact ⟨ball_smooth_relative_support hF hcF hD hγ hlegal hx hy,
      ball_smooth_relative_upper hF hD hγ hx hy⟩
  · intro x hx
    have hxC := interior_subset (hDC hx)
    have hlo := ball_smoothing_lower_on hF.continuous hcF hclosed x γ (hlegal x hx)
    have hhi := ball_smoothing_lipschitz_bias hF x γ
    rw [abs_of_pos hγ] at hhi
    have hup := (le_abs_self (ballSmooth F γ x - F x)).trans hhi
    rw [he hxC]
    exact ⟨hlo, by linarith only [hup]⟩
  · intro g L hL hg hglip
    have hgF (x : H) (hx : x ∈ interior C) : HasGradientWithinAt F (g x) (interior C) x :=
      (hg x hx).congr_of_mem (fun y hy => (he (interior_subset hy)).symm) hx
    refine ⟨fun x hx y hy => ball_smooth_upper_of_interior_gradient hF hc.1 hclosed hne hD
      hγ hgF hglip hlegal hx hy, ?_⟩
    intro x hx
    have hmodel (v : ℝ × S) : F (x + γ • ballOffset v) ≤
        F x + ⟪g x, γ • ballOffset v⟫ + L / 2 * ‖γ • ballOffset v‖ ^ 2 := by
      simpa only [add_sub_cancel_left] using local_taylor_to_boundary hF.continuous hc.1 hclosed
        hne hgF hglip (hDC hx) (hlegal x hx v)
    have hb := ball_smoothing_local_smooth_bias hF.continuous hL x (g x) hmodel
    rw [← he (interior_subset (hDC hx))] at hb
    exact hb

end LongTails.Proofs.LocalPopulationModels
