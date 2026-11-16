import LongTails.Proofs.GapBoundedSmoothChain
import LongTails.Proofs.SmoothConvexMollification
import LongTails.Proofs.GapBoundedSmoothLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GapBoundedSmoothMollification

open GapBoundedSmoothChain CompactMollification

noncomputable def center {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (b : ℝ) : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun i => -shift m b i - φ.rOut)

lemma objective_continuous {m : ℕ} (L G b : ℝ) (hL : 0 < L) (hG : 0 < G) :
    Continuous (objective (m := m) L G b) :=
  continuous_iff_continuousAt.mpr (fun x => (objective_hasGradientAt L G b hL hG x).continuousAt)

lemma center_zero {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (L G b : ℝ) (hL : 0 < L) (hG : 0 < G) :
    CompactMollification.average φ (objective L G b) (center φ b) = 0 := by
  have hz (z : EuclideanSpace ℝ (Fin m)) : objective L G b (center φ b - noise φ z) = 0 := by
    apply objective_zero L G b hL hG
    intro i
    have hn := (abs_le.mp ((PiLp.norm_apply_le (noise φ z) i).trans (noise_norm φ z))).1
    change -shift m b i - φ.rOut - noise φ z i + shift m b i ≤ 0
    linarith
  simp only [CompactMollification.average, hz, integral_zero]

lemma center_radius {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (b : ℝ) (hb : 0 ≤ b) :
    ‖center φ b‖ ≤ Real.sqrt m * (2 * (m : ℝ) * b + φ.rOut) := by
  have hρ := φ.rOut_pos
  apply GeneralizedSmoothHardChainRadius.norm_bound_of_coordinate_bound _ _ (by positivity)
  intro i
  have hs := shift_bounds b hb i
  change |-shift m b i - φ.rOut| ≤ _
  apply abs_le.mpr
  constructor <;> nlinarith [Nat.cast_nonneg m (α := ℝ), φ.rOut_pos]

lemma origin_gap {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (L G b : ℝ) (hL : 0 < L) (hG : 0 < G) (hb : 0 ≤ b) :
    CompactMollification.average φ (objective L G b) 0 ≤ 2 * (m : ℝ) * b * G + G * φ.rOut := by
  have hc := objective_convex (m := m) L G b hG
  have hg := objective_hasGradientAt (m := m) L G b hL hG
  have hp (z : EuclideanSpace ℝ (Fin m)) :
      objective L G b (0 - noise φ z) ≤ 2 * (m : ℝ) * b * G + G * φ.rOut := by
    have hs := OracleTemplate.Gradient.convex_support hc hg (0 - noise φ z) 0
    have hi := (abs_le.mp (abs_real_inner_le_norm (field L G b (0 - noise φ z))
      (0 - (0 - noise φ z)))).1
    have hn : ‖0 - (0 - noise φ z)‖ ≤ φ.rOut := by simpa using noise_norm φ z
    have hm := mul_le_mul (field_bounded L G b hG (0 - noise φ z)) hn
      (norm_nonneg _) hG.le
    have h0 := origin_upper (m := m) L G b hL hG hb
    linarith
  have hi := integral_mono (average_integrable φ _ (objective_continuous L G b hL hG) 0)
    (integrable_const (2 * (m : ℝ) * b * G + G * φ.rOut)) hp
  simpa only [CompactMollification.average, integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

lemma hidden_gap {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (L G b τ : ℝ) (hL : 0 < L) (hG : 0 < G) (hb : 0 ≤ b)
    (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) (hx : -τ ≤ x i) :
    G * ((m : ℝ) * b - τ - φ.rOut) - G ^ 2 / (2 * L) ≤ CompactMollification.average φ (objective L G b) x := by
  have hp (z : EuclideanSpace ℝ (Fin m)) :
      G * ((m : ℝ) * b - τ - φ.rOut) - G ^ 2 / (2 * L) ≤ objective L G b (x - noise φ z) := by
    have hv := vertex_bound L G b hG (x - noise φ z) i
    have hn := (abs_le.mp ((PiLp.norm_apply_le (noise φ z) i).trans (noise_norm φ z))).2
    have hs := (shift_bounds b hb i).1
    change G * (x i - noise φ z i + shift m b i) - _ ≤ _ at hv
    nlinarith
  have hi := integral_mono
    (integrable_const (G * ((m : ℝ) * b - τ - φ.rOut) - G ^ 2 / (2 * L)))
    (average_integrable φ _ (objective_continuous L G b hL hG) x) hp
  simpa only [CompactMollification.average, integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

noncomputable def seed {m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L G b : ℝ)
    (hL : 0 < L) (hG : 0 < G) (hb : 0 ≤ b) :
    AdaptiveGeneralizedSmoothLocalization.Seed (E := EuclideanSpace ℝ (Fin m)) where
  f := CompactMollification.average φ (objective L G b)
  g := CompactMollification.average φ (field L G b)
  z := center φ b
  G := G
  r := Real.sqrt m * (2 * (m : ℝ) * b + φ.rOut)
  L₀ := 3 * L
  L₁ := 1
  G_nonneg := hG.le
  r_pos := by have hρ := φ.rOut_pos; positivity
  L₀_pos := by positivity
  L₁_pos := by norm_num
  convex := average_convex φ _ (objective_continuous L G b hL hG) (objective_convex L G b hG)
  gradient := SmoothConvexMollification.average_gradient φ _ _ L (objective_convex L G b hG)
    (objective_hasGradientAt L G b hL hG) (field_lipschitz L G b hL hG)
  differentiable := SmoothConvexMollification.average_field_differentiable φ _ L
    (field_lipschitz L G b hL hG)
  curvature := fun x => by
    have hh := SmoothConvexMollification.average_curvature φ _ L hL.le
      (field_lipschitz L G b hL hG) x
    have hn := norm_nonneg (CompactMollification.average φ (field L G b) x)
    linarith
  bounded := average_norm_bound φ _
    (SmoothConvexMollification.field_continuous _ L (field_lipschitz L G b hL hG)) G
    (field_bounded L G b hG)
  nonnegative := fun x => integral_nonneg (fun z => objective_nonnegative L G b hG (x - noise φ z))
  zero := center_zero φ L G b hL hG
  radius := center_radius φ b hb

end LongTails.Proofs.GapBoundedSmoothMollification
