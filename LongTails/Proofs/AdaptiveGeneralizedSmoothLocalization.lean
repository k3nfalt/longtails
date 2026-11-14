import LongTails.Proofs.AdaptivePolynomialLocalization
import LongTails.Proofs.AdaptiveLocalizationBounds
import LongTails.Proofs.GeneralizedSmoothShield

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdaptiveGeneralizedSmoothLocalization

open AdaptivePolynomialLocalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure Seed where
  f : E → ℝ
  g : E → E
  z : E
  G : ℝ
  r : ℝ
  L₀ : ℝ
  L₁ : ℝ
  G_nonneg : 0 ≤ G
  r_pos : 0 < r
  L₀_pos : 0 < L₀
  L₁_pos : 0 < L₁
  convex : ConvexOn ℝ univ f
  gradient : ∀ x, HasGradientAt f (g x) x
  differentiable : Differentiable ℝ g
  curvature : ∀ x, ‖fderiv ℝ g x‖ ≤ L₀ / 3 + L₁ / 3 * ‖g x‖
  bounded : ∀ x, ‖g x‖ ≤ G
  nonnegative : ∀ x, 0 ≤ f x
  zero : f z = 0
  radius : ‖z‖ ≤ r

lemma seed_upper (s : Seed (E := E)) (x : E) : s.f x ≤ s.G * (‖x‖ + s.r) := by
  have hs := OracleTemplate.Gradient.convex_support s.convex s.gradient x s.z
  have hi := (abs_le.mp (abs_real_inner_le_norm (s.g x) (s.z - x))).1
  have hn : ‖s.z - x‖ ≤ ‖x‖ + s.r := by
    have hh := norm_sub_le s.z x
    have hz := s.radius
    linarith
  calc
    s.f x ≤ ‖s.g x‖ * ‖s.z - x‖ := by rw [s.zero] at hs; linarith
    _ ≤ s.G * (‖x‖ + s.r) := mul_le_mul (s.bounded x) hn (norm_nonneg _) s.G_nonneg

lemma mixingDerivative_nonnegative (s : Seed (E := E)) (n : ℕ) (hn : 2 ≤ n)
    (a B : ℝ) (ha : 0 < a) (hB : 0 < B) (x : E) :
    0 ≤ mixingDerivative s.f n a B (a * B ^ 2) x :=
  div_nonneg (AdaptivePolynomialHinge.curvature_bounds n hn _).1 (by positivity)

lemma transition_term (s : Seed (E := E)) (n : ℕ) (hn : 2 ≤ n) (a B : ℝ)
    (ha : 0 < a) (hB : 0 < B) (hrB : 2 * s.r ≤ B) (hGa : s.G ≤ a * B) (x : E) :
    mixingDerivative s.f n a B (a * B ^ 2) x * ‖a • x - s.g x‖ ^ 2 ≤
      50 * ((n : ℝ) * (n + 1 : ℕ)) * a *
        (mixing s.f n a B (a * B ^ 2) x + (1 / 2 : ℝ) ^ n) := by
  have hW : 0 < a * B ^ 2 := by positivity
  have hp := AdaptivePolynomialHinge.mixing_bounds n ((wall a B x - s.f x) / (a * B ^ 2))
  change 0 ≤ mixing s.f n a B (a * B ^ 2) x ∧ _ at hp
  have hpn := hp.1
  by_cases hl : wall a B x ≤ s.f x
  · rw [(mixing_interior s.f n a B _ hW x hl).2, zero_mul]
    positivity
  by_cases hr : a * B ^ 2 ≤ wall a B x - s.f x
  · rw [(mixing_exterior s.f n a B _ hW x hr).2, zero_mul]
    positivity
  have hrad := AdaptiveLocalizationBounds.transition_radius a B s.r s.G ‖x‖ (s.f x)
    ha hB (norm_nonneg x) s.r_pos.le hrB hGa (s.nonnegative x) (seed_upper s x)
    (by change 0 ≤ wall a B x - s.f x; linarith)
    (by change wall a B x - s.f x ≤ a * B ^ 2; linarith)
  have hsize : ‖a • x - s.g x‖ ≤ 5 * a * B := by
    have hh := norm_sub_le (a • x) (s.g x)
    rw [norm_smul, Real.norm_of_nonneg ha.le] at hh
    have hg := s.bounded x
    have hb := mul_le_mul_of_nonneg_left hrad.2 ha.le
    linarith
  apply AdaptiveLocalizationBounds.transition_curvature_term _ a B _ _ _ _ ha hB
    (norm_nonneg _) (mixingDerivative_nonnegative s n hn a B ha hB x) hsize
  apply div_le_div_of_nonneg_right _ hW.le
  simpa only [mixing, mul_assoc] using (AdaptivePolynomialHinge.curvature_bounds n hn
    ((wall a B x - s.f x) / (a * B ^ 2))).2

lemma weighted_norm (s : Seed (E := E)) (n : ℕ) (a B W : ℝ) (ha : 0 ≤ a)
    (x : E) (hr : 2 * s.r ≤ ‖x‖) :
    (1 - mixing s.f n a B W x) * ‖s.g x‖ + mixing s.f n a B W x * ‖a • x‖ ≤
      2 * ‖field s.f s.g n a B W x‖ := by
  have hp := AdaptivePolynomialHinge.mixing_bounds n ((wall a B x - s.f x) / W)
  change 0 ≤ mixing s.f n a B W x ∧ mixing s.f n a B W x ≤ 1 at hp
  have hs := OracleTemplate.Gradient.convex_support s.convex s.gradient x s.z
  have hangle := GeneralizedSmoothShield.radial_angle_of_minimizer s.f (s.g x) x s.z s.r
    (by linarith) (by rw [s.zero]; exact s.nonnegative x) s.radius hr
  have ham := mul_le_mul_of_nonneg_left hangle ha
  have hangle' : -(‖s.g x‖ * ‖a • x‖) ≤ 2 * ⟪s.g x, a • x⟫ := by
    rw [norm_smul, Real.norm_of_nonneg ha, real_inner_smul_right]
    nlinarith only [ham]
  have hh := GeneralizedSmoothShield.weighted_norm_control (s.g x) (a • x)
    (1 - mixing s.f n a B W x) (sub_nonneg.mpr hp.2) (by linarith [hp.1]) hangle'
  simpa only [sub_sub_cancel, field_convex_combination] using hh

lemma gradient_curvature (s : Seed (E := E)) (n : ℕ) (hn : 2 ≤ n) (a B : ℝ)
    (ha : 0 < a) (hB : 0 < B) (hrB : 2 * s.r ≤ B)
    (hwidth : 256 * ((n : ℝ) * (n + 1 : ℕ)) ≤ s.L₁ * B)
    (htune : a * B = s.G + s.L₀ * B / 1000)
    (hpeak : s.G * (1 / 2 : ℝ) ^ n * s.L₁ ≤ s.L₀) (x : E) :
    ‖fderiv ℝ (field s.f s.g n a B (a * B ^ 2)) x‖ ≤
      s.L₀ + s.L₁ * ‖field s.f s.g n a B (a * B ^ 2) x‖ := by
  have hW : 0 < a * B ^ 2 := by positivity
  have hp := AdaptivePolynomialHinge.mixing_bounds n ((wall a B x - s.f x) / (a * B ^ 2))
  change 0 ≤ mixing s.f n a B (a * B ^ 2) x ∧ mixing s.f n a B (a * B ^ 2) x ≤ 1 at hp
  have hd := field_derivative_norm_bound s.f s.g n hn a B _ ha.le hW x
    (fderiv ℝ s.g x) (s.gradient x) (s.differentiable x).hasFDerivAt
  by_cases hl : wall a B x ≤ s.f x
  · obtain ⟨h0, h1⟩ := mixing_interior s.f n a B _ hW x hl
    rw [h0, h1] at hd
    rw [field_interior s.f s.g n a B _ hW x hl]
    have hc := s.curvature x
    have hL₀ := s.L₀_pos
    have hL₁ := mul_nonneg s.L₁_pos.le (norm_nonneg (s.g x))
    nlinarith only [hd, hc, hL₀, hL₁]
  have hrad : B ≤ ‖x‖ := by
    have hnon := s.nonnegative x
    have hwall : 0 ≤ a / 2 * (‖x‖ ^ 2 - B ^ 2) := by change 0 ≤ wall a B x; linarith
    have hsq : B ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith
    nlinarith [norm_nonneg x]
  have hGa : s.G ≤ a * B := by
    have hz := mul_nonneg s.L₀_pos.le hB.le
    linarith only [htune, hz]
  have ht := transition_term s n hn a B ha hB hrB hGa x
  have hc := mul_le_mul_of_nonneg_left (s.curvature x) (sub_nonneg.mpr hp.2)
  have hbase : ‖fderiv ℝ (field s.f s.g n a B (a * B ^ 2)) x‖ ≤
      (1 - mixing s.f n a B (a * B ^ 2) x) * (s.L₀ / 3 + s.L₁ / 3 * ‖s.g x‖) +
      mixing s.f n a B (a * B ^ 2) x * a +
      50 * ((n : ℝ) * (n + 1 : ℕ)) * a *
        (mixing s.f n a B (a * B ^ 2) x + (1 / 2 : ℝ) ^ n) := by
    linarith only [hd, ht, hc]
  have hD : 1 ≤ (n : ℝ) * (n + 1 : ℕ) := by
    have hh : (2 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    nlinarith
  have hw := AdaptiveLocalizationBounds.wall_curvature_coefficient _ a B s.L₁ ‖x‖
    hD ha.le s.L₁_pos.le hwidth hrad
  have hdegree : (n : ℝ) * (n + 1 : ℕ) * (1 / 2 : ℝ) ^ n ≤ 3 / 2 := by
    have hh := AdaptiveLocalizationBounds.degree_le_geometric n hn
    rw [div_pow, one_pow, ← div_eq_mul_one_div]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mpr hh
  have hleak := AdaptiveLocalizationBounds.leakage_coefficient _ a B s.G s.L₀ s.L₁ _
    htune hB s.G_nonneg s.L₀_pos.le (by positivity) hwidth hdegree hpeak
  have hweight := weighted_norm s n a B (a * B ^ 2) ha.le x (hrB.trans hrad)
  rw [norm_smul, Real.norm_of_nonneg ha.le] at hweight
  exact AdaptiveLocalizationBounds.curvature_absorption _ _ _ _ s.L₀ s.L₁ a _ _ _
    s.L₀_pos.le s.L₁_pos.le (norm_nonneg _) hp.1 hbase hw hleak hweight

lemma value_interior (s : Seed (E := E)) (n : ℕ) (a B : ℝ)
    (ha : 0 < a) (hB : 0 < B) (x : E) (hx : ‖x‖ ≤ B) :
    value s.f n a B (a * B ^ 2) x = s.f x := by
  apply AdaptivePolynomialLocalization.value_interior s.f n a B _ (by positivity) x
  have hs : ‖x‖ ^ 2 ≤ B ^ 2 := by nlinarith [norm_nonneg x]
  have hw : wall a B x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  exact hw.trans (s.nonnegative x)

lemma value_minimizer (s : Seed (E := E)) (n : ℕ) (hn : 2 ≤ n) (a B : ℝ)
    (ha : 0 < a) (hB : 0 < B) (hrB : s.r ≤ B) :
    IsMinOn (value s.f n a B (a * B ^ 2)) univ s.z := by
  intro x _
  rw [value_interior s n a B ha hB s.z (s.radius.trans hrB), s.zero]
  exact (s.nonnegative x).trans (value_above s.f n hn a B _ (by positivity) x)

lemma field_differentiable (s : Seed (E := E)) (n : ℕ) (hn : 2 ≤ n) (a B W : ℝ) :
    Differentiable ℝ (field s.f s.g n a B W) := by
  intro x
  exact (field_hasFDerivAt s.f s.g n hn a B W x _ (s.gradient x)
    (s.differentiable x).hasFDerivAt).differentiableAt

lemma field_exterior (s : Seed (E := E)) (n : ℕ) (a B : ℝ)
    (ha : 0 < a) (hB : 0 < B) (hrB : 2 * s.r ≤ B) (hGa : s.G ≤ a * B)
    (x : E) (hx : 4 * B ≤ ‖x‖) : field s.f s.g n a B (a * B ^ 2) x = a • x := by
  apply AdaptivePolynomialLocalization.field_exterior s.f s.g n a B _ (by positivity) x
  exact AdaptiveLocalizationBounds.exterior_separation a B s.r s.G ‖x‖ (s.f x)
    ha hB s.r_pos.le hrB hGa (seed_upper s x) hx

end LongTails.Proofs.AdaptiveGeneralizedSmoothLocalization
