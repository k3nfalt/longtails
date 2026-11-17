import LongTails.Proofs.KnownGapParameters
import LongTails.Proofs.SmoothConvexFiniteLowerBound
import LongTails.Proofs.SmoothConvexFiniteSimulation
import LongTails.Proofs.SmoothConvexFiniteAveraging
import LongTails.Proofs.CompactMollification
import LongTails.Proofs.GeneralizedSmoothMollification
import LongTails.Proofs.FinitePrefixExpectation
import LongTails.Proofs.GdConvex
import LongTails.TemplateLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate Set Metric
open scoped RealInnerProductSpace

namespace LongTails.Proofs.KnownGapAccuracyInstance

open LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension
open CompactMollification

section Mollification

variable {d : ℕ}

lemma lipschitz_continuous (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ)
    (hL : 0 ≤ L) (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) : Continuous g := by
  have h : LipschitzWith (Real.toNNReal L) g := LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL]
    exact hlip x y
  exact h.continuous

lemma noise_coordinate (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (z : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |noise φ z i| ≤ φ.rOut :=
  (PiLp.norm_apply_le (noise φ z) i).trans (noise_norm φ z)

lemma average_ge (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Continuous f) (c : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ z, c ≤ f (x - noise φ z)) : c ≤ CompactMollification.average φ f x := by
  have hh := integral_mono (integrable_const c) (average_integrable φ f hf x) h
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    CompactMollification.average] using hh

lemma average_le (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Continuous f) (c : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ z, f (x - noise φ z) ≤ c) : CompactMollification.average φ f x ≤ c := by
  have hh := integral_mono (average_integrable φ f hf x) (integrable_const c) h
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    CompactMollification.average] using hh

lemma average_congr (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (f₁ f₂ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ z, f₁ (x - noise φ z) = f₂ (x - noise φ z)) : CompactMollification.average φ f₁ x = CompactMollification.average φ f₂ x :=
  integral_congr_ae (ae_of_all _ h)

lemma average_lipschitz (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖CompactMollification.average φ g x - CompactMollification.average φ g y‖ ≤ L * ‖x - y‖ := by
  have hcont := lipschitz_continuous g L hL hlip
  unfold CompactMollification.average
  rw [← integral_sub (average_integrable φ g hcont x) (average_integrable φ g hcont y)]
  have hb : ∀ z, ‖g (x - noise φ z) - g (y - noise φ z)‖ ≤ L * ‖x - y‖ := fun z => by
    simpa only [sub_sub_sub_cancel_right] using hlip (x - noise φ z) (y - noise φ z)
  have hh := norm_integral_le_of_norm_le_const (μ := (probability φ : Measure _)) (ae_of_all _ hb)
  simpa only [probReal_univ, mul_one] using hh

lemma average_fderiv_bound (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (CompactMollification.average φ g) x‖ ≤ L :=
  norm_fderiv_le_of_lip' ℝ hL (Filter.Eventually.of_forall fun y =>
    average_lipschitz φ g L hL hlip y x)

lemma average_gradient (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : ℝ) (hL : 0 ≤ L) (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (CompactMollification.average φ f) (CompactMollification.average φ g x) x := by
  have hcf : Continuous f :=
    continuous_iff_continuousAt.mpr fun y => (hg y).differentiableAt.continuousAt
  exact GeneralizedSmoothMollification.average_hasGradient_of_remainder (probability φ) (noise φ)
    f g (L / 2) (average_integrable φ f hcf)
    (average_integrable φ g (lipschitz_continuous g L hL hlip))
    (fun u v => ⟨by linarith [OracleTemplate.Gradient.convex_support hc hg u v],
      by linarith [OracleTemplate.Gradient.smooth_upper_bound hg hlip u v]⟩) x

end Mollification

noncomputable def chainRadius (p : Params) (N : ℕ) : ℝ :=
  256 * ((N : ℝ) + 1) * Real.sqrt (p.ε / p.L0)

noncomputable def step (p : Params) (N : ℕ) : ℝ := chainRadius p N / Real.sqrt ((N : ℝ) + 1)

noncomputable def zone (p : Params) (N : ℕ) : ℝ := step p N / (8 * ((N : ℝ) + 1))

noncomputable def smoothing (p : Params) (N : ℕ) : ℝ := zone p N / 64

section Parameters

variable (p : Params) (hp : spec.valid p) (N : ℕ)

include hp

lemma root_pos : 0 < Real.sqrt (p.ε / p.L0) :=
  Real.sqrt_pos.mpr (div_pos (KnownGapParameters.ε_pos p hp) (KnownGapParameters.L0_pos p hp))

lemma root_sq : Real.sqrt (p.ε / p.L0) ^ 2 = p.ε / p.L0 :=
  Real.sq_sqrt (div_pos (KnownGapParameters.ε_pos p hp) (KnownGapParameters.L0_pos p hp)).le

lemma chainRadius_pos : 0 < chainRadius p N :=
  mul_pos (by positivity) (root_pos p hp)

lemma step_pos : 0 < step p N := by
  have := chainRadius_pos p hp N
  unfold step
  exact div_pos this (Real.sqrt_pos.mpr (by positivity))

lemma zone_pos : 0 < zone p N :=
  div_pos (step_pos p hp N) (by positivity)

lemma smoothing_pos : 0 < smoothing p N :=
  div_pos (zone_pos p hp N) (by norm_num)

omit hp in
lemma step_sq : ((N : ℝ) + 1) * step p N ^ 2 = chainRadius p N ^ 2 := by
  have hK : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  unfold step
  rw [div_pow, Real.sq_sqrt hK.le, mul_div_cancel₀ _ hK.ne']

lemma energy : p.L0 * step p N ^ 2 = 65536 * ((N : ℝ) + 1) * p.ε := by
  have hK : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hL0 := KnownGapParameters.L0_pos p hp
  have hL0' := hL0.ne'
  have hs := step_sq p N
  have hr : chainRadius p N ^ 2 = 65536 * ((N : ℝ) + 1) ^ 2 * (p.ε / p.L0) := by
    unfold chainRadius
    rw [mul_pow, mul_pow, root_sq p hp]
    ring
  have ha : step p N ^ 2 = 65536 * ((N : ℝ) + 1) * (p.ε / p.L0) := by
    apply mul_left_cancel₀ hK.ne'
    rw [hs, hr]
    ring
  rw [ha]
  field_simp

lemma gap_eq : p.L0 * step p N ^ 2 / (8192 * ((N : ℝ) + 1)) = 8 * p.ε := by
  have hK : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [energy p hp N]
  field_simp
  ring

omit hp in
lemma zone_scale : ((N : ℝ) + 1) * zone p N = step p N / 8 := by
  have hK : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  unfold zone
  field_simp

lemma smoothing_le_zone : smoothing p N ≤ zone p N / 8 := by
  have := zone_pos p hp N
  unfold smoothing
  linarith

lemma zone_le_step : zone p N ≤ step p N := by
  have hK : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hs := step_pos p hp N
  unfold zone
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma step_le_radius : step p N ≤ chainRadius p N := by
  have hK : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hr := chainRadius_pos p hp N
  have h1 : 1 ≤ Real.sqrt ((N : ℝ) + 1) := Real.one_le_sqrt.mpr hK
  unfold step
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma smoothing_le_radius : smoothing p N ≤ chainRadius p N := by
  have h1 := smoothing_le_zone p hp N
  have h2 := zone_le_step p hp N
  have h3 := step_le_radius p hp N
  have h4 := zone_pos p hp N
  linarith

lemma smoothing_le_half_step : smoothing p N ≤ step p N / 2 := by
  have h1 := smoothing_le_zone p hp N
  have h2 := zone_le_step p hp N
  have h4 := zone_pos p hp N
  linarith

lemma smoothing_energy : p.L0 / 2 * smoothing p N ^ 2 ≤ p.ε / 8 := by
  have hK : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hε := KnownGapParameters.ε_pos p hp
  have he := energy p hp N
  have hsm : smoothing p N * (512 * ((N : ℝ) + 1)) = step p N := by
    unfold smoothing zone
    field_simp
    ring
  have hval : p.L0 / 2 * smoothing p N ^ 2 * (524288 * ((N : ℝ) + 1) ^ 2) =
      65536 * ((N : ℝ) + 1) * p.ε := by
    rw [← he, ← hsm]
    ring
  have hpos : 0 < 524288 * ((N : ℝ) + 1) ^ 2 := by positivity
  have hKK : (N : ℝ) + 1 ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
  have h1 : 65536 * ((N : ℝ) + 1) * p.ε ≤ p.ε / 8 * (524288 * ((N : ℝ) + 1) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hKK hε.le]
  have h2 : p.L0 / 2 * smoothing p N ^ 2 * (524288 * ((N : ℝ) + 1) ^ 2) ≤
      p.ε / 8 * (524288 * ((N : ℝ) + 1) ^ 2) := by linarith
  exact le_of_mul_le_mul_right h2 hpos

lemma accuracy_root : Real.sqrt (p.L0 * p.R ^ 2 / p.ε) * Real.sqrt (p.ε / p.L0) = p.R := by
  have hε := KnownGapParameters.ε_pos p hp
  have hL0 := KnownGapParameters.L0_pos p hp
  have hR := KnownGapParameters.R_pos p hp
  have hε' := hε.ne'
  have hL0' := hL0.ne'
  rw [← Real.sqrt_mul (div_nonneg (mul_nonneg hL0.le (sq_nonneg _)) hε.le)]
  have : p.L0 * p.R ^ 2 / p.ε * (p.ε / p.L0) = p.R ^ 2 := by field_simp
  rw [this, Real.sqrt_sq hR.le]

variable (hN : (N : ℝ) + 1 ≤ Real.sqrt (p.L0 * p.R ^ 2 / p.ε) / 4096)

include hN

lemma radius_small : 16 * chainRadius p N ≤ p.R := by
  have hroot := root_pos p hp
  have hmul := mul_le_mul_of_nonneg_right hN hroot.le
  rw [div_mul_eq_mul_div, accuracy_root p hp] at hmul
  unfold chainRadius
  nlinarith

lemma initial_small : p.L0 * step p N ^ 2 / 1024 ≤ p.Δ := by
  have hε := KnownGapParameters.ε_pos p hp
  have hg := KnownGapParameters.accuracy_gap_ge p hp
  rw [energy p hp N]
  have h1 := mul_le_mul_of_nonneg_left hN hε.le
  have h0 : 0 ≤ p.ε * Real.sqrt (p.L0 * p.R ^ 2 / p.ε) := mul_nonneg hε.le (Real.sqrt_nonneg _)
  nlinarith

lemma dimension_ok :
    2 * ((N + 1 : ℕ) : ℝ) ^ 2 * ((4 * chainRadius p N) ^ 2 / (zone p N / 8) ^ 2) + (N + 1 : ℕ) ≤
      (p.d : ℝ) := by
  have hK : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hr := chainRadius_pos p hp N
  have hs := step_sq p N
  have hstep := step_pos p hp N
  have hstep' := hstep.ne'
  have hK0 : (N : ℝ) + 1 ≠ 0 := by positivity
  have hratio : (4 * chainRadius p N) ^ 2 / (zone p N / 8) ^ 2 = 65536 * ((N : ℝ) + 1) ^ 3 := by
    have hzd : zone p N / 8 = step p N / (64 * ((N : ℝ) + 1)) := by
      unfold zone
      field_simp
      ring
    rw [hzd, mul_pow, ← hs, div_pow]
    field_simp
    ring
  rw [hratio]
  push_cast
  set s := Real.sqrt (p.L0 * p.R ^ 2 / p.ε)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsK : (N : ℝ) + 1 ≤ s := by linarith
  have hs1 : 1 ≤ s := hK.trans hsK
  have hq : 0 ≤ KnownGapParameters.q p := (KnownGapParameters.q_pos p hp).le
  have hd : (⌈70368744177664 * (1 + KnownGapParameters.q p + s) ^ 6⌉₊ : ℝ) ≤ p.d := by
    exact_mod_cast KnownGapParameters.full_dim_ge p hp
  have hceil := Nat.le_ceil (70368744177664 * (1 + KnownGapParameters.q p + s) ^ 6)
  have h5 : ((N : ℝ) + 1) ^ 5 ≤ s ^ 5 := pow_le_pow_left₀ (by linarith) hsK 5
  have h56 : s ^ 5 ≤ s ^ 6 := pow_le_pow_right₀ hs1 (by norm_num)
  have h6 : s ^ 6 ≤ (1 + KnownGapParameters.q p + s) ^ 6 := pow_le_pow_left₀ hs0 (by linarith) 6
  have hKs6 : (N : ℝ) + 1 ≤ s ^ 6 := hsK.trans (by
    simpa using pow_le_pow_right₀ hs1 (show 1 ≤ 6 by norm_num))
  have hexp : 2 * ((N : ℝ) + 1) ^ 2 * (65536 * ((N : ℝ) + 1) ^ 3) = 131072 * ((N : ℝ) + 1) ^ 5 := by
    ring
  have hs6 : 0 ≤ s ^ 6 := by positivity
  rw [hexp]
  linarith

end Parameters

noncomputable def kernel (p : Params) (hp : spec.valid p) (N : ℕ) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin p.d)) where
  rIn := smoothing p N / 2
  rOut := smoothing p N
  rIn_pos := div_pos (smoothing_pos p hp N) (by norm_num)
  rIn_lt_rOut := by have := smoothing_pos p hp N; linarith

noncomputable def objective (p : Params) (hp : spec.valid p) (N : ℕ) (π : Fin (N + 1) ↪ Fin p.d) :
    EuclideanSpace ℝ (Fin p.d) → ℝ :=
  CompactMollification.average (kernel p hp N) (SmoothConvexFiniteWall.objective p.L0 (chainRadius p N) (zone p N) (step p N) π)

noncomputable def field (p : Params) (hp : spec.valid p) (N : ℕ) (π : Fin (N + 1) ↪ Fin p.d) :
    EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d) :=
  CompactMollification.average (kernel p hp N) (SmoothConvexFiniteWall.field p.L0 (chainRadius p N) (zone p N) (step p N) π)

noncomputable def partialReply (p : Params) (hp : spec.valid p) (N : ℕ) (π : Fin (N + 1) ↪ Fin p.d)
    (r : ℕ) (x : EuclideanSpace ℝ (Fin p.d)) : EuclideanSpace ℝ (Fin p.d) :=
  if 4 * chainRadius p N ≤ ‖x‖ then CompactMollification.average (kernel p hp N) (fun y => (p.L0 / 128) • y) x
  else CompactMollification.average (kernel p hp N)
    (SmoothConvexFiniteSimulation.partialField p.L0 (chainRadius p N) (zone p N) (step p N) π r) x

section Instance

variable (p : Params) (hp : spec.valid p) (N : ℕ) (π : Fin (N + 1) ↪ Fin p.d)

include hp

omit hp in
lemma radius_hidden : ((N : ℝ) + 1) * step p N ^ 2 ≤ chainRadius p N ^ 2 := (step_sq p N).le

lemma base_gradient (x : EuclideanSpace ℝ (Fin p.d)) :
    HasGradientAt (SmoothConvexFiniteWall.objective p.L0 (chainRadius p N) (zone p N) (step p N) π)
      (SmoothConvexFiniteWall.field p.L0 (chainRadius p N) (zone p N) (step p N) π x) x :=
  SmoothConvexFiniteWall.objective_gradient _ _ _ _ (chainRadius_pos p hp N) (zone_pos p hp N).le π x

lemma base_convex :
    ConvexOn ℝ univ (SmoothConvexFiniteWall.objective p.L0 (chainRadius p N) (zone p N) (step p N) π) :=
  SmoothConvexFiniteWall.objective_convex _ _ _ _ (KnownGapParameters.L0_pos p hp).le (chainRadius_pos p hp N)
    (zone_pos p hp N).le π

lemma base_lipschitz (x y : EuclideanSpace ℝ (Fin p.d)) :
    ‖SmoothConvexFiniteWall.field p.L0 (chainRadius p N) (zone p N) (step p N) π x -
      SmoothConvexFiniteWall.field p.L0 (chainRadius p N) (zone p N) (step p N) π y‖ ≤
      p.L0 * ‖x - y‖ :=
  SmoothConvexFiniteWall.field_lipschitz _ _ _ _ (KnownGapParameters.L0_pos p hp).le (chainRadius_pos p hp N)
    (zone_pos p hp N).le π (radius_hidden p N) x y

lemma base_continuous :
    Continuous (SmoothConvexFiniteWall.objective p.L0 (chainRadius p N) (zone p N) (step p N) π) :=
  continuous_iff_continuousAt.mpr fun y => (base_gradient p hp N π y).differentiableAt.continuousAt

lemma base_field_continuous :
    Continuous (SmoothConvexFiniteWall.field p.L0 (chainRadius p N) (zone p N) (step p N) π) :=
  lipschitz_continuous _ p.L0 (KnownGapParameters.L0_pos p hp).le (base_lipschitz p hp N π)

lemma objective_hasGradientAt (x : EuclideanSpace ℝ (Fin p.d)) :
    HasGradientAt (objective p hp N π) (field p hp N π x) x :=
  average_gradient (kernel p hp N) _ _ p.L0 (KnownGapParameters.L0_pos p hp).le
    (base_convex p hp N π) (base_gradient p hp N π) (base_lipschitz p hp N π) x

lemma objective_continuous : Continuous (objective p hp N π) :=
  (average_contDiff (kernel p hp N) _ (base_continuous p hp N π) 0).continuous

lemma field_differentiable : Differentiable ℝ (field p hp N π) :=
  (average_contDiff (kernel p hp N) _ (base_field_continuous p hp N π) 1).differentiable
    (by norm_num)

lemma field_curvature (x : EuclideanSpace ℝ (Fin p.d)) : ‖fderiv ℝ (field p hp N π) x‖ ≤ p.L0 :=
  average_fderiv_bound (kernel p hp N) _ p.L0 (KnownGapParameters.L0_pos p hp).le
    (base_lipschitz p hp N π) x

lemma objective_convex' : ConvexOn ℝ univ (objective p hp N π) :=
  average_convex (kernel p hp N) _ (base_continuous p hp N π) (base_convex p hp N π)

lemma objective_nonneg' (x : EuclideanSpace ℝ (Fin p.d)) : 0 ≤ objective p hp N π x :=
  average_ge (kernel p hp N) _ (base_continuous p hp N π) 0 x fun _ =>
    SmoothConvexFiniteWall.objective_nonneg _ _ _ _ (KnownGapParameters.L0_pos p hp).le
      (chainRadius_pos p hp N) π _

lemma shifted_far (x z : EuclideanSpace ℝ (Fin p.d)) (M : ℝ) (hx : M ≤ ‖x‖) :
    M - smoothing p N ≤ ‖x - noise (kernel p hp N) z‖ := by
  have h1 := norm_sub_norm_le x (noise (kernel p hp N) z)
  have h2 : ‖noise (kernel p hp N) z‖ ≤ smoothing p N := noise_norm (kernel p hp N) z
  linarith

lemma objective_near_gap (x : EuclideanSpace ℝ (Fin p.d))
    (hx : |x (π (Fin.last N))| ≤ zone p N / 8) :
    p.L0 * step p N ^ 2 / (8192 * ((N : ℝ) + 1)) ≤ objective p hp N π x := by
  apply average_ge (kernel p hp N) _ (base_continuous p hp N π) _ x
  intro z
  have hK : (0 : ℝ) < 8192 * ((N : ℝ) + 1) := by positivity
  rw [div_le_iff₀ hK]
  have htail : |(x - noise (kernel p hp N) z) (π (Fin.last N))| ≤ zone p N / 4 := by
    have hn := noise_coordinate (kernel p hp N) z (π (Fin.last N))
    change |noise (kernel p hp N) z (π (Fin.last N))| ≤ smoothing p N at hn
    have hs := smoothing_le_zone p hp N
    have hz := zone_pos p hp N
    rw [PiLp.sub_apply]
    have := abs_sub (x (π (Fin.last N))) (noise (kernel p hp N) z (π (Fin.last N)))
    linarith
  have hg := SmoothConvexFiniteWall.objective_gap _ _ _ _ (KnownGapParameters.L0_pos p hp).le
    (chainRadius_pos p hp N) (zone_pos p hp N).le (step_pos p hp N).le π _
    (zone_scale p N).le htail
  linarith

lemma objective_far_gap' (x : EuclideanSpace ℝ (Fin p.d)) (hx : 4 * chainRadius p N ≤ ‖x‖) :
    p.L0 * step p N ^ 2 / (8192 * ((N : ℝ) + 1)) ≤ objective p hp N π x := by
  apply average_ge (kernel p hp N) _ (base_continuous p hp N π) _ x
  intro z
  have hK : (0 : ℝ) < 8192 * ((N : ℝ) + 1) := by positivity
  rw [div_le_iff₀ hK]
  have h1 := shifted_far p hp N x z _ hx
  have h2 := smoothing_le_radius p hp N
  have hg := SmoothConvexFiniteAveraging.objective_far_gap p.L0 (chainRadius p N) (zone p N) (step p N)
    (KnownGapParameters.L0_pos p hp).le
    (chainRadius_pos p hp N) π (radius_hidden p N) _ (by linarith)
  linarith

lemma partialReply_prefix (ρ : Fin (N + 1) ↪ Fin p.d) (r : ℕ) (x : EuclideanSpace ℝ (Fin p.d))
    (h : ∀ i : Fin (N + 1), i.val ≤ r → π i = ρ i) :
    partialReply p hp N π r x = partialReply p hp N ρ r x := by
  unfold partialReply
  split_ifs
  · rfl
  · exact average_congr (kernel p hp N) _ _ x fun _ =>
      SmoothConvexFiniteSimulation.partialField_prefix _ _ _ _ π ρ r _ h

lemma partialReply_eq (r : ℕ) (x : EuclideanSpace ℝ (Fin p.d))
    (hs : ‖x‖ < 4 * chainRadius p N → ∀ i : Fin (N + 1), r ≤ i.val → |x (π i)| ≤ zone p N / 8) :
    partialReply p hp N π r x = field p hp N π x := by
  unfold partialReply field
  have hRc := chainRadius_pos p hp N
  have hsr := smoothing_le_radius p hp N
  split_ifs with hx
  · apply average_congr
    intro z
    have hf := shifted_far p hp N x z _ hx
    exact (SmoothConvexFiniteWall.field_outside _ _ _ _ hRc (zone_pos p hp N).le π
      (radius_hidden p N) _ (by linarith)).symm
  · apply average_congr
    intro z
    apply SmoothConvexFiniteSimulation.partialField_eq _ _ _ _ hRc (zone_pos p hp N).le π
      (radius_hidden p N) r
    intro _ j hj
    have h1 := hs (lt_of_not_ge hx) j hj
    have hn := noise_coordinate (kernel p hp N) z (π j)
    change |noise (kernel p hp N) z (π j)| ≤ smoothing p N at hn
    have hsz := smoothing_le_zone p hp N
    have hz := zone_pos p hp N
    rw [PiLp.sub_apply]
    have := abs_sub (x (π j)) (noise (kernel p hp N) z (π j))
    linarith

lemma hidden_value (z : EuclideanSpace ℝ (Fin p.d)) :
    SmoothConvexFiniteWall.objective p.L0 (chainRadius p N) (zone p N) (step p N) π
      (FiniteSumNondualLowerComponents.hiddenPoint π (step p N) - noise (kernel p hp N) z) ≤
      p.ε / 8 := by
  have hmin := SmoothConvexFiniteWall.objective_minimum p.L0 (chainRadius p N) (zone p N) (step p N)
    (KnownGapParameters.L0_pos p hp).le (chainRadius_pos p hp N) (zone_pos p hp N).le π
    (radius_hidden p N)
  have hzero : SmoothConvexFiniteWall.field p.L0 (chainRadius p N) (zone p N) (step p N) π
      (FiniteSumNondualLowerComponents.hiddenPoint π (step p N)) = 0 := by
    have hl := (hmin.2.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero
      (base_gradient p hp N π _).hasFDerivAt
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin p.d))).injective (by rw [hl, map_zero])
  have hup := OracleTemplate.Gradient.smooth_upper_bound (base_gradient p hp N π)
    (base_lipschitz p hp N π) (FiniteSumNondualLowerComponents.hiddenPoint π (step p N))
    (FiniteSumNondualLowerComponents.hiddenPoint π (step p N) - noise (kernel p hp N) z)
  rw [hzero, inner_zero_left, hmin.1, sub_sub_cancel_left, norm_neg] at hup
  have hn : ‖noise (kernel p hp N) z‖ ≤ smoothing p N := noise_norm (kernel p hp N) z
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have he := smoothing_energy p hp N
  have hL0 := KnownGapParameters.L0_pos p hp
  have hm := mul_le_mul_of_nonneg_left hsq (by linarith : 0 ≤ p.L0 / 2)
  linarith

lemma small_value (y : EuclideanSpace ℝ (Fin p.d)) (hy : ‖y‖ ≤ smoothing p N) :
    SmoothConvexFiniteWall.objective p.L0 (chainRadius p N) (zone p N) (step p N) π y ≤
      p.L0 * step p N ^ 2 / 1024 := by
  have hRc := chainRadius_pos p hp N
  have hsr := smoothing_le_radius p hp N
  have hsa := smoothing_le_half_step p hp N
  have hL0 := KnownGapParameters.L0_pos p hp
  have hsm := smoothing_pos p hp N
  have hh := FiniteSumNondualLowerComponents.hardComponent_nonneg 1 (zone p N) (step p N) (by norm_num) π
    (fun _ => (0 : Fin 1)) 0 y
  have hu := SmoothConvexFiniteChain.chain_upper (zone p N) (step p N) (zone_pos p hp N).le π y
  have hyR : ‖y‖ ≤ chainRadius p N := hy.trans hsr
  have hy2 := pow_le_pow_left₀ (norm_nonneg y) hyR 2
  have hR2 := pow_pos hRc 2
  have hloc := (SmoothConvexFiniteGeometry.smoothMax_eq_left (chainRadius p N ^ 2)
    (FiniteSumNondualLowerComponents.hardComponent 1 (zone p N) (step p N) π (fun _ => (0 : Fin 1)) 0 y)
    (SmoothConvexFiniteWall.wall (chainRadius p N) y) (pow_pos hRc 2)
    (by unfold SmoothConvexFiniteWall.wall; linarith)).1
  unfold SmoothConvexFiniteWall.objective SmoothConvexFiniteWall.localized
  rw [hloc]
  have hys := pow_le_pow_left₀ (norm_nonneg y) hy 2
  have hsq : smoothing p N ^ 2 ≤ step p N ^ 2 / 4 := by
    have := pow_le_pow_left₀ hsm.le hsa 2
    nlinarith
  have hb : FiniteSumNondualLowerComponents.hardComponent 1 (zone p N) (step p N) π
      (fun _ => (0 : Fin 1)) 0 y ≤ step p N ^ 2 / 2 := by linarith
  have := mul_le_mul_of_nonneg_left hb (div_nonneg hL0.le (by norm_num) : (0 : ℝ) ≤ p.L0 / 512)
  linarith

end Instance

lemma exists_failure (p : Params) (hp : spec.valid p) (N : ℕ)
    (hN : (N : ℝ) + 1 ≤ Real.sqrt (p.L0 * p.R ^ 2 / p.ε) / 4096)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p f O ∧
        ¬ spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => N) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  have hε := KnownGapParameters.ε_pos p hp
  have hL0 := KnownGapParameters.L0_pos p hp
  have hL1 := KnownGapParameters.L1_pos p hp
  have hR := KnownGapParameters.R_pos p hp
  have hRc := chainRadius_pos p hp N
  have hz := zone_pos p hp N
  let B := 4 * chainRadius p N
  let θ := zone p N / 8
  let D := 2 * ((N + 1 : ℕ) : ℝ) ^ 2 * (B ^ 2 / θ ^ 2)
  let gap := p.L0 * step p N ^ 2 / (8192 * ((N : ℝ) + 1))
  have hB : 0 < B := mul_pos (by norm_num) hRc
  have hθ : 0 < θ := div_pos hz (by norm_num)
  have hD : 0 < D := mul_pos (mul_pos (by norm_num) (by positivity)) (div_pos (pow_pos hB 2) (pow_pos hθ 2))
  have hDs : D + (N + 1 : ℕ) ≤ (p.d : ℝ) := dimension_ok p hp N hN
  have hgap : gap = 8 * p.ε := gap_eq p hp N
  let reply := fun π : Fin (N + 1) ↪ Fin p.d => field p hp N π
  let loss := fun π : Fin (N + 1) ↪ Fin p.d => objective p hp N π
  let query := fun s => (A.query s).2 - p.x0
  let output := fun s => A.output s - p.x0
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure A.Seed).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  obtain ⟨π, hbad⟩ := FinitePrefixExpectation.exists_failure B θ D gap (2 * p.ε) hB.le hθ hD
    (by rw [hgap]; linarith) hDs le_rfl (by rw [hgap]; linarith)
    (partialReply p hp N) reply loss (fun π ρ r x h => partialReply_prefix p hp N π ρ r x h)
    (fun π r x _ hs => partialReply_eq p hp N π r x hs)
    (fun π x => objective_nonneg' p hp N π x)
    (fun π x hx => objective_near_gap p hp N π x hx)
    (fun π x hx => objective_far_gap' p hp N π x hx)
    query output A.update (fun w : A.Seed × (ℕ → Unit) => A.initial w.1) P
  let F := loss π
  let g := reply π
  let c := FiniteSumNondualLowerComponents.hiddenPoint π (step p N)
  let O := SmoothConvexFiniteLowerBound.oracle p.x0 g
  have hc : ‖c‖ ≤ chainRadius p N :=
    SmoothConvexFiniteWall.hiddenPoint_radius _ _ hRc.le π (radius_hidden p N)
  have hrad := radius_small p hp N hN
  have hFc : F c ≤ p.ε / 8 :=
    average_le (kernel p hp N) _ (base_continuous p hp N π) _ c (hidden_value p hp N π)
  obtain ⟨u, hu, humin⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin p.d)) p.R).exists_isMinOn
    (nonempty_closedBall.mpr hR.le) (objective_continuous p hp N π).continuousOn
  have hcball : c ∈ closedBall (0 : EuclideanSpace ℝ (Fin p.d)) p.R := by
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hglobal : IsMinOn F univ u := by
    intro y _
    by_cases hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin p.d)) p.R
    · exact humin hy
    · rw [mem_closedBall, dist_zero_right, not_le] at hy
      have hfar := objective_far_gap' p hp N π y (by linarith)
      change gap ≤ F y at hfar
      have hcu := humin hcball
      change F u ≤ F c at hcu
      change F u ≤ F y
      rw [hgap] at hfar
      linarith
  have hu' : ‖u‖ ≤ p.R := by rwa [mem_closedBall, dist_zero_right] at hu
  have hFu : F u ≤ p.ε / 8 := (humin hcball).trans hFc
  have hF0 : F 0 ≤ p.Δ := by
    apply average_le (kernel p hp N) _ (base_continuous p hp N π) _ 0
    intro z
    apply (small_value p hp N π _ _).trans (initial_small p hp N hN)
    rw [zero_sub, norm_neg]
    exact noise_norm (kernel p hp N) z
  have hadm : spec.admissible p (fun x : EuclideanSpace ℝ (Fin p.d) => F (x - p.x0)) O := by
    refine ⟨SmoothConvexFiniteLowerBound.convex_translate p.x0 _ (objective_convex' p hp N π),
      ?_, ?_, ?_, p.x0 + u, ?_, ?_, ?_⟩
    · intro k ω x
      exact SmoothConvexFiniteLowerBound.gradient_translate p.x0 _ _
        (objective_hasGradientAt p hp N π) x
    · intro k ω
      exact (field_differentiable p hp N π).comp (differentiable_id.sub_const p.x0)
    · intro k ω x
      change ‖fderiv ℝ (fun y => g (y - p.x0)) x‖ ≤ p.L0 + p.L1 * ‖g (x - p.x0)‖
      have ht := ((field_differentiable p hp N π) (x - p.x0)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const p.x0)
      change HasFDerivAt (fun y => g (y - p.x0)) _ x at ht
      rw [ht.fderiv, ContinuousLinearMap.comp_id]
      have h1 := field_curvature p hp N π (x - p.x0)
      have h2 : 0 ≤ p.L1 * ‖g (x - p.x0)‖ := mul_nonneg hL1.le (norm_nonneg _)
      linarith
    · intro x _
      change F (p.x0 + u - p.x0) ≤ F (x - p.x0)
      rw [add_sub_cancel_left]
      exact hglobal (mem_univ _)
    · change ‖p.x0 - (p.x0 + u)‖ ≤ p.R
      rw [sub_add_cancel_left, norm_neg]
      exact hu'
    · change F (p.x0 - p.x0) - F (p.x0 + u - p.x0) ≤ p.Δ
      rw [sub_self, add_sub_cancel_left]
      have := objective_nonneg' p hp N π u
      change 0 ≤ F u at this
      linarith
  refine ⟨fun x : EuclideanSpace ℝ (Fin p.d) => F (x - p.x0), O, hadm, ?_⟩
  rintro ⟨xstar, hmin, hi, he⟩
  change EuclideanSpace ℝ (Fin p.d) at xstar
  let v := F (xstar - p.x0)
  have hv : v ≤ p.ε / 8 := by
    have hh := hmin (mem_univ (p.x0 + u))
    change F (xstar - p.x0) ≤ F (p.x0 + u - p.x0) at hh
    rw [add_sub_cancel_left] at hh
    exact hh.trans hFu
  have hout :
      (fun w : A.Seed × (ℕ → Unit) => F (execute O A (fun _ => N) w.1 w.2 - p.x0)) =
      fun w : A.Seed × (ℕ → Unit) =>
        F (output ((fun s => A.update s (g (query s)))^[N] (A.initial w.1))) := by
    funext w
    rw [SmoothConvexFiniteLowerBound.execute_translated p.x0 g A N w.1 w.2]
  have hi' : Integrable (fun w : A.Seed × (ℕ → Unit) =>
      F (execute O A (fun _ => N) w.1 w.2 - p.x0) - v) (P : Measure _) := hi
  have he' : (∫ w : A.Seed × (ℕ → Unit), F (execute O A (fun _ => N) w.1 w.2 - p.x0) - v ∂(P : Measure _)) ≤ p.ε := he
  have hint : Integrable (fun w : A.Seed × (ℕ → Unit) =>
      F (execute O A (fun _ => N) w.1 w.2 - p.x0)) (P : Measure _) := by
    refine (hi'.add (integrable_const v)).congr (ae_of_all _ fun w => ?_)
    simp only [Pi.add_apply, sub_add_cancel]
  have hrepr : (∫ w : A.Seed × (ℕ → Unit), F (execute O A (fun _ => N) w.1 w.2 - p.x0) ∂(P : Measure _)) =
      (∫ w : A.Seed × (ℕ → Unit), F (execute O A (fun _ => N) w.1 w.2 - p.x0) - v ∂(P : Measure _)) + v := by
    rw [integral_sub hint (integrable_const v), integral_const, probReal_univ, one_smul]
    ring
  apply hbad
  constructor
  · change Integrable (fun w : A.Seed × (ℕ → Unit) =>
      F (output ((fun s => A.update s (g (query s)))^[N] (A.initial w.1)))) (P : Measure _)
    rw [← hout]
    exact hint
  · change (∫ w : A.Seed × (ℕ → Unit),
      F (output ((fun s => A.update s (g (query s)))^[N] (A.initial w.1))) ∂(P : Measure _)) ≤
        2 * p.ε
    rw [← hout, hrepr]
    linarith

end LongTails.Proofs.KnownGapAccuracyInstance
