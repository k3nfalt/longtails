import LongTails.Proofs.SmoothConvexMollification
import LongTails.Proofs.SmoothConvexFiniteSimulation
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace LongTails.Proofs.MollifiedSmoothHardFamily

open CompactMollification SmoothConvexMollification SmoothConvexFiniteWall
open SmoothConvexFiniteSimulation FiniteSumNondualLowerComponents

variable {d k : ℕ}

noncomputable def value (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (L r δ a : ℝ) (π : Fin (k + 1) ↪ Fin d) := average φ (objective L r δ a π)

noncomputable def grad (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (L r δ a : ℝ) (π : Fin (k + 1) ↪ Fin d) := average φ (field L r δ a π)

noncomputable def partialReply (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (L r δ a : ℝ) (π : Fin (k + 1) ↪ Fin d) (t : ℕ) :=
  average φ (partialField L r δ a π t)

lemma partial_prefix (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (L r δ a : ℝ) (π ρ : Fin (k + 1) ↪ Fin d) (t : ℕ)
    (h : ∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) (x : EuclideanSpace ℝ (Fin d)) :
    partialReply φ L r δ a π t x = partialReply φ L r δ a ρ t x := by
  apply integral_congr_ae
  exact ae_of_all _ (fun u => partialField_prefix L r δ a π ρ t _ h)

lemma partial_eq (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (L r δ a : ℝ) (hr : 0 < r) (hδ : 0 ≤ δ)
    (hρ : φ.rOut ≤ δ / 16) (hρr : φ.rOut ≤ r)
    (π : Fin (k + 1) ↪ Fin d) (ha : ((k : ℝ) + 1) * a ^ 2 ≤ r ^ 2)
    (t : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ < 4 * r → ∀ j : Fin (k + 1), t ≤ j.val → |x (π j)| ≤ δ / 8) :
    partialReply φ L r δ a π t x = grad φ L r δ a π x := by
  apply integral_congr_ae
  apply ae_of_all
  intro u
  apply partialField_eq L r δ a hr hδ π ha t
  intro hy j hj
  have hn := noise_norm φ u
  have hnorm := norm_sub_le (x - noise φ u) (-noise φ u)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hnorm
  have hxx : ‖x‖ < 4 * r := by linarith
  have hc : |noise φ u (π j)| ≤ φ.rOut :=
    by simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (noise φ u) (π j)).trans hn
  have hh := abs_sub (x (π j)) (noise φ u (π j))
  change |x (π j) - noise φ u (π j)| ≤ δ / 4
  linarith [hx hxx j hj]

lemma value_continuous (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (L r δ a : ℝ) (hr : 0 < r) (hδ : 0 ≤ δ) (π : Fin (k + 1) ↪ Fin d) :
    Continuous (value φ L r δ a π) :=
  (average_contDiff φ _ (continuous_iff_continuousAt.mpr
    (fun x => (objective_gradient L r δ a hr hδ π x).continuousAt)) 1).continuous

lemma value_nonneg (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (L r δ a : ℝ) (hL : 0 ≤ L) (hr : 0 < r) (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ value φ L r δ a π x :=
  integral_nonneg (fun u => objective_nonneg L r δ a hL hr π (x - noise φ u))

lemma value_gradient (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (L r δ a : ℝ) (hL : 0 ≤ L) (hr : 0 < r) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (ha : ((k : ℝ) + 1) * a ^ 2 ≤ r ^ 2)
    (x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (value φ L r δ a π) (grad φ L r δ a π x) x :=
  average_gradient φ _ _ L (objective_convex L r δ a hL hr hδ π)
    (objective_gradient L r δ a hr hδ π) (field_lipschitz L r δ a hL hr hδ π ha) x

lemma value_at_hidden (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (L r δ a : ℝ) (hL : 0 ≤ L) (hr : 0 < r) (hδ : 0 ≤ δ)
    (π : Fin (k + 1) ↪ Fin d) (ha : ((k : ℝ) + 1) * a ^ 2 ≤ r ^ 2) :
    value φ L r δ a π (hiddenPoint π a) ≤ L / 2 * φ.rOut ^ 2 := by
  have hm := objective_minimum L r δ a hL hr hδ π ha
  have hg := objective_gradient L r δ a hr hδ π (hiddenPoint π a)
  have hz : field L r δ a π (hiddenPoint π a) = 0 := by
    have hmin : IsLocalMin (objective L r δ a π) (hiddenPoint π a) :=
      hm.2.isLocalMin (by simp)
    have hh := hmin.hasFDerivAt_eq_zero hg.hasFDerivAt
    have hv := congrArg (fun A : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ =>
      A (field L r δ a π (hiddenPoint π a))) hh
    simpa only [InnerProductSpace.toDual_apply_apply, zero_apply,
      real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] using hv
  exact average_at_minimum φ _ _ L hL (objective_gradient L r δ a hr hδ π)
    (field_lipschitz L r δ a hL hr hδ π ha) _ hm.1 hz

lemma value_far (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (L r δ a : ℝ) (hL : 0 ≤ L) (hr : 0 < r) (hδ : 0 ≤ δ)
    (hρr : φ.rOut ≤ r) (π : Fin (k + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (hx : 4 * r ≤ ‖x‖) :
    L * r ^ 2 / 64 ≤ value φ L r δ a π x := by
  have hp (u : EuclideanSpace ℝ (Fin d)) : L * r ^ 2 / 64 ≤ objective L r δ a π (x - noise φ u) := by
    have hn := noise_norm φ u
    have hnorm := norm_sub_le (x - noise φ u) (-noise φ u)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at hnorm
    have hs : 3 * r ≤ ‖x - noise φ u‖ := by linarith
    have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * r) hs 2
    have hw := (le_max_right _ _).trans
      (SmoothConvexFiniteGeometry.smoothMax_ge (r ^ 2)
        (hardComponent 1 δ a π (fun _ => (0 : Fin 1)) 0 (x - noise φ u))
        (wall r (x - noise φ u)) (sq_pos_of_pos hr))
    have hh := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ L / 512)
    change L / 512 * (2 * ‖x - noise φ u‖ ^ 2 - 4 * r ^ 2) ≤
      objective L r δ a π (x - noise φ u) at hh
    have hm := mul_le_mul_of_nonneg_left hs2 hL
    nlinarith [mul_nonneg hL (sq_nonneg r)]
  have hi := average_integrable φ (objective L r δ a π)
    (continuous_iff_continuousAt.mpr (fun x => (objective_gradient L r δ a hr hδ π x).continuousAt)) x
  have hh := integral_mono (integrable_const (L * r ^ 2 / 64)) hi hp
  simp only [integral_const, probReal_univ, one_smul] at hh
  exact hh

lemma value_minimum (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (L r δ a : ℝ) (hL : 0 ≤ L) (hr : 0 < r) (hδ : 0 ≤ δ)
    (hρr : φ.rOut ≤ r / 128) (π : Fin (k + 1) ↪ Fin d)
    (ha : ((k : ℝ) + 1) * a ^ 2 ≤ r ^ 2) :
    ∃ z, ‖z‖ ≤ 4 * r ∧ IsMinOn (value φ L r δ a π) univ z ∧
      value φ L r δ a π z ≤ L / 2 * φ.rOut ^ 2 := by
  have hz := hiddenPoint_radius r a hr.le π ha
  have hv := value_at_hidden φ L r δ a hL hr hδ π ha
  have hsmall : L / 2 * φ.rOut ^ 2 ≤ L * r ^ 2 / 64 := by
    have hs := pow_le_pow_left₀ φ.rOut_pos.le hρr 2
    have hm := mul_le_mul_of_nonneg_left hs hL
    nlinarith [mul_nonneg hL (sq_nonneg r)]
  obtain ⟨z, hz, hm, hvz⟩ := exists_minimum_in_ball (value φ L r δ a π) (4 * r)
    (value_continuous φ L r δ a hr hδ π) (hiddenPoint π a) (by linarith) (by
      intro x hx
      exact hv.trans (hsmall.trans (value_far φ L r δ a hL hr hδ (by linarith) π x hx.le)))
  exact ⟨z, hz, hm, hvz.trans hv⟩

lemma value_near (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (L r δ a : ℝ) (hL : 0 ≤ L) (hr : 0 < r) (hδ : 0 ≤ δ) (ha : 0 ≤ a)
    (hρ : φ.rOut ≤ δ / 16) (π : Fin (k + 1) ↪ Fin d)
    (hscale : ((k : ℝ) + 1) * δ ≤ a / 8)
    (x : EuclideanSpace ℝ (Fin d)) (hx : |x (π (Fin.last k))| ≤ δ / 8) :
    L * a ^ 2 / (8192 * ((k : ℝ) + 1)) ≤ value φ L r δ a π x := by
  have hp (u : EuclideanSpace ℝ (Fin d)) :
      L * a ^ 2 / (8192 * ((k : ℝ) + 1)) ≤ objective L r δ a π (x - noise φ u) := by
    apply (div_le_iff₀ (by positivity : 0 < 8192 * ((k : ℝ) + 1))).mpr
    have hn := (PiLp.norm_apply_le (noise φ u) (π (Fin.last k))).trans (noise_norm φ u)
    simp only [Real.norm_eq_abs] at hn
    have ht : |(x - noise φ u) (π (Fin.last k))| ≤ δ / 4 := by
      change |x (π (Fin.last k)) - noise φ u (π (Fin.last k))| ≤ δ / 4
      linarith [abs_sub (x (π (Fin.last k))) (noise φ u (π (Fin.last k)))]
    have hh := objective_gap L r δ a hL hr hδ ha π (x - noise φ u) hscale ht
    nlinarith only [hh]
  have hi := average_integrable φ (objective L r δ a π)
    (continuous_iff_continuousAt.mpr (fun x => (objective_gradient L r δ a hr hδ π x).continuousAt)) x
  have hh := integral_mono (integrable_const (L * a ^ 2 / (8192 * ((k : ℝ) + 1)))) hi hp
  simp only [integral_const, probReal_univ, one_smul] at hh
  exact hh

end LongTails.Proofs.MollifiedSmoothHardFamily
