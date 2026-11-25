import LongTails.Proofs.RhoSmoothHardChain
import LongTails.Proofs.CompactMollification
import LongTails.Proofs.GeneralizedSmoothMollification

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory hiding average
open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.RhoSmoothHardSmoothed

open RhoSmoothLocal RhoSmoothHardDual RhoSmoothHardChain CompactMollification
open GeneralizedSmoothMollification

section

variable {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))

lemma noise_coordinate_bound (z : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    |noise φ z i| ≤ φ.rOut :=
  (PiLp.norm_apply_le (noise φ z) i).trans (noise_norm φ z)

lemma average_deviation (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (Λ : ℝ)
    (hΛ : 0 ≤ Λ) (hlip : ∀ x y, ‖g x - g y‖ ≤ Λ * ‖x - y‖) (hcont : Continuous g)
    (x z : EuclideanSpace ℝ (Fin m)) :
    ‖g (x - noise φ z) - average φ g x‖ ≤ Λ * (2 * φ.rOut) := by
  have hi := average_integrable φ g hcont x
  have he : g (x - noise φ z) - average φ g x =
      ∫ w, g (x - noise φ z) - g (x - noise φ w) ∂(probability φ : Measure _) := by
    rw [integral_sub (integrable_const _) hi, integral_const]
    simp only [probReal_univ, one_smul, CompactMollification.average]
  rw [he]
  have hb : ∀ᵐ w ∂(probability φ : Measure _),
      ‖g (x - noise φ z) - g (x - noise φ w)‖ ≤ Λ * (2 * φ.rOut) := by
    apply ae_of_all
    intro w
    apply (hlip _ _).trans
    apply mul_le_mul_of_nonneg_left _ hΛ
    rw [sub_sub_sub_cancel_left]
    have := norm_sub_le (noise φ w) (noise φ z)
    linarith [noise_norm φ w, noise_norm φ z]
  have h := norm_integral_le_of_norm_le_const hb
  simpa only [probReal_univ, mul_one] using h

lemma average_curvature (L₀ L₁ ρ : ℝ) (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hρ : 0 ≤ ρ)
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ Λ * ‖x - y‖) (hcont : Continuous g)
    (hpair : ∀ x y, ‖g x - g y‖ ≤ curv L₀ L₁ ρ (max ‖g x‖ ‖g y‖) * ‖x - y‖)
    (x : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ (average φ g) x‖ ≤ curv L₀ L₁ ρ (‖average φ g x‖ + Λ * (4 * φ.rOut)) := by
  set τ := Λ * (2 * φ.rOut)
  set a := ‖average φ g x‖
  have hr := φ.rOut_pos
  have hτ : 0 ≤ τ := by positivity
  have hd := ((average_contDiff φ g hcont 1).differentiable (by norm_num)).differentiableAt.hasFDerivAt
    (x := x)
  have hC : 0 ≤ curv L₀ L₁ ρ (a + Λ * (4 * φ.rOut)) := (curv_pos hL₀ hL₁.le (by positivity)).le
  apply derivative_bound_of_quadratic_increment (average φ g) x _ _ (Λ / (2 * φ.rOut)) hd hC
    (by positivity)
  intro y
  have hiy := average_integrable φ g hcont y
  have hix := average_integrable φ g hcont x
  have he : average φ g y - average φ g x =
      ∫ u, g (y - noise φ u) - g (x - noise φ u) ∂(probability φ : Measure _) := by
    rw [integral_sub hiy hix]
    rfl
  rw [he]
  by_cases hyx : ‖y - x‖ ≤ 2 * φ.rOut
  · have hb : ∀ᵐ u ∂(probability φ : Measure _), ‖g (y - noise φ u) - g (x - noise φ u)‖ ≤
        curv L₀ L₁ ρ (a + Λ * (4 * φ.rOut)) * ‖y - x‖ := by
      apply ae_of_all
      intro u
      have h1 := average_deviation φ g Λ hΛ hlip hcont x u
      have hx1 : ‖g (x - noise φ u)‖ ≤ a + τ := by
        have := norm_le_insert' (g (x - noise φ u)) (average φ g x)
        linarith [norm_sub_norm_le (g (x - noise φ u)) (average φ g x)]
      have hyu : ‖g (y - noise φ u) - g (x - noise φ u)‖ ≤ Λ * ‖y - x‖ := by
        have := hlip (y - noise φ u) (x - noise φ u)
        rwa [sub_sub_sub_cancel_right] at this
      have hy1 : ‖g (y - noise φ u)‖ ≤ a + Λ * (4 * φ.rOut) := by
        have h2 := norm_le_insert' (g (y - noise φ u)) (g (x - noise φ u))
        have h3 : Λ * ‖y - x‖ ≤ Λ * (2 * φ.rOut) := mul_le_mul_of_nonneg_left hyx hΛ
        have h4 : τ = Λ * (2 * φ.rOut) := rfl
        nlinarith [norm_sub_norm_le (g (y - noise φ u)) (g (x - noise φ u))]
      have hmax : max ‖g (y - noise φ u)‖ ‖g (x - noise φ u)‖ ≤ a + Λ * (4 * φ.rOut) := by
        apply max_le hy1
        have : τ ≤ Λ * (4 * φ.rOut) := by
          change Λ * (2 * φ.rOut) ≤ Λ * (4 * φ.rOut)
          exact mul_le_mul_of_nonneg_left (by linarith) hΛ
        linarith
      have hp := hpair (y - noise φ u) (x - noise φ u)
      rw [sub_sub_sub_cancel_right] at hp
      apply hp.trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact curv_mono hL₁.le hρ (le_max_of_le_left (norm_nonneg _)) hmax
    have h := norm_integral_le_of_norm_le_const hb
    simp only [probReal_univ, mul_one] at h
    apply h.trans
    have : 0 ≤ Λ / (2 * φ.rOut) * ‖y - x‖ * ‖y - x‖ := by positivity
    nlinarith [norm_nonneg (y - x)]
  · push Not at hyx
    have hb : ∀ᵐ u ∂(probability φ : Measure _), ‖g (y - noise φ u) - g (x - noise φ u)‖ ≤
        Λ * ‖y - x‖ := by
      apply ae_of_all
      intro u
      have := hlip (y - noise φ u) (x - noise φ u)
      rwa [sub_sub_sub_cancel_right] at this
    have h := norm_integral_le_of_norm_le_const hb
    simp only [probReal_univ, mul_one] at h
    apply h.trans
    have h1 : Λ * ‖y - x‖ ≤ Λ / (2 * φ.rOut) * ‖y - x‖ * ‖y - x‖ := by
      have h2 : 1 ≤ ‖y - x‖ / (2 * φ.rOut) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have h3 : Λ / (2 * φ.rOut) * ‖y - x‖ * ‖y - x‖ =
          Λ * ‖y - x‖ * (‖y - x‖ / (2 * φ.rOut)) := by ring
      rw [h3]
      have h4 : 0 ≤ Λ * ‖y - x‖ := by positivity
      nlinarith
    nlinarith [norm_nonneg (y - x)]

end

noncomputable def smoothObjective {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (A G ρ g σ : ℝ) : EuclideanSpace ℝ (Fin m) → ℝ := average φ (objective m A G ρ g σ)

noncomputable def smoothField {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
    (A G ρ g σ : ℝ) : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
  average φ (field m A G ρ g σ)

noncomputable def center {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (σ : ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun _ => -σ - φ.rOut)

section

variable {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
  (A G ρ L₀ L₁ g σ : ℝ) (hA : 0 < A) (hG : 0 < G) (hρ : 1 < ρ) (hρ2 : ρ ≤ 2)
  (hL₀ : 0 < L₀) (hL₁ : 0 < L₁) (hAG : A * (ρ - 1) = 2 * G / L₀) (hGL : G ^ ρ * L₁ = L₀)
  (hg : 0 < g)

include hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg

lemma objective_continuous : Continuous (objective m A G ρ g σ) :=
  continuous_iff_continuousAt.mpr (fun x =>
    (objective_hasGradientAt A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg x).differentiableAt.continuousAt)

lemma field_continuous : Continuous (field m A G ρ g σ) :=
  (field_lipschitz A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg).continuous

lemma smooth_hasGradientAt (x : EuclideanSpace ℝ (Fin m)) :
    HasGradientAt (smoothObjective φ A G ρ g σ) (smoothField φ A G ρ g σ x) x :=
  average_hasGradient_of_remainder (probability φ) (noise φ) _ _ (curv L₀ L₁ ρ (peak m g))
    (average_integrable φ _ (objective_continuous A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg))
    (average_integrable φ _ (field_continuous A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg))
    (objective_remainder A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg) x

lemma smoothField_contDiff (n : ℕ∞) : ContDiff ℝ n (smoothField φ A G ρ g σ) :=
  average_contDiff φ _ (field_continuous A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg) n

lemma smoothField_norm_bound (x : EuclideanSpace ℝ (Fin m)) :
    ‖smoothField φ A G ρ g σ x‖ ≤ peak m g :=
  average_norm_bound φ _ (field_continuous A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg) _
    (field_norm_bound A G ρ g σ hG hg) x

lemma smooth_convex : ConvexOn ℝ univ (smoothObjective φ A G ρ g σ) :=
  average_convex φ _ (objective_continuous A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg)
    (objective_convex A G ρ g σ hG hg)

lemma smooth_curvature (x : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ (smoothField φ A G ρ g σ) x‖ ≤
      curv L₀ L₁ ρ (‖smoothField φ A G ρ g σ x‖ + curv L₀ L₁ ρ (peak m g) * (4 * φ.rOut)) := by
  have hlip := field_lipschitz (m := m) A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg
  apply average_curvature φ L₀ L₁ ρ hL₀ hL₁ (by linarith) _ _
    (curv_pos hL₀ hL₁.le (peak_pos hg).le).le
    (fun x y => by
      have h := hlip.dist_le_mul x y
      rw [dist_eq_norm, dist_eq_norm] at h
      exact h)
    hlip.continuous (field_pair A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg) x

omit hA hρ hρ2 hL₀ hL₁ hAG hGL in
lemma smooth_nonnegative (x : EuclideanSpace ℝ (Fin m)) :
    0 ≤ smoothObjective φ A G ρ g σ x :=
  integral_nonneg (fun z => objective_nonnegative A G ρ g σ hG hg (x - noise φ z))

lemma smooth_gap (θ : ℝ) (hσ : θ + A ≤ σ) (hδ : 2 * φ.rOut ≤ θ) (i : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) (hx : -(θ / 2) ≤ x i) :
    g * (σ - θ - A) ≤ smoothObjective φ A G ρ g σ x := by
  have hp (z : EuclideanSpace ℝ (Fin m)) :
      g * (σ - θ - A) ≤ objective m A G ρ g σ (x - noise φ z) := by
    apply objective_gap A G ρ g σ hA hG hg θ hσ i
    have hz := (abs_le.mp (noise_coordinate_bound φ z i)).2
    change -θ ≤ x i - noise φ z i
    linarith
  have hh := integral_mono (integrable_const (g * (σ - θ - A)))
    (average_integrable φ _
      (objective_continuous A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg) x) hp
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, smoothObjective,
    CompactMollification.average] using hh

omit hρ2 hL₀ hL₁ hAG hGL in
lemma smooth_center_zero : smoothObjective φ A G ρ g σ (center φ σ) = 0 := by
  have hz (z : EuclideanSpace ℝ (Fin m)) :
      objective m A G ρ g σ (center φ σ - noise φ z) = 0 := by
    apply objective_zero A G ρ g σ hA hG hρ hg
    intro i
    have hh := (abs_le.mp (noise_coordinate_bound φ z i)).1
    change -σ - φ.rOut - noise φ z i + σ ≤ 0
    linarith
  simp only [smoothObjective, CompactMollification.average, hz, integral_zero]

lemma smoothField_prefix_eq (θ : ℝ) (hθ : 0 ≤ θ) (hσ : 3 * θ + 2 * A < σ)
    (hδ : 2 * φ.rOut ≤ θ) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -(θ / 2) ≤ x j) (hxt : ∀ i, j < i → x i ≤ θ / 2) (hyt : ∀ i, j < i → y i ≤ θ / 2) :
    smoothField φ A G ρ g σ x = smoothField φ A G ρ g σ y := by
  apply integral_congr_ae
  apply ae_of_all
  intro z
  have hn (i : Fin m) := abs_le.mp (noise_coordinate_bound φ z i)
  apply field_prefix_eq A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg θ hθ hσ j
  · intro i hi
    change x i - noise φ z i = y i - noise φ z i
    rw [hxy i hi]
  · change -θ ≤ x j - noise φ z j
    linarith [(hn j).2]
  · intro i hi
    change x i - noise φ z i ≤ θ
    linarith [(hn i).1, hxt i hi]
  · intro i hi
    change y i - noise φ z i ≤ θ
    linarith [(hn i).1, hyt i hi]

lemma smoothObjective_prefix_eq (θ : ℝ) (hθ : 0 ≤ θ) (hσ : 3 * θ + 2 * A < σ)
    (hδ : 2 * φ.rOut ≤ θ) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -(θ / 2) ≤ x j) (hxt : ∀ i, j < i → x i ≤ θ / 2) (hyt : ∀ i, j < i → y i ≤ θ / 2) :
    smoothObjective φ A G ρ g σ x = smoothObjective φ A G ρ g σ y := by
  apply integral_congr_ae
  apply ae_of_all
  intro z
  have hn (i : Fin m) := abs_le.mp (noise_coordinate_bound φ z i)
  apply objective_prefix_eq A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg θ hθ hσ j
  · intro i hi
    change x i - noise φ z i = y i - noise φ z i
    rw [hxy i hi]
  · change -θ ≤ x j - noise φ z j
    linarith [(hn j).2]
  · intro i hi
    change x i - noise φ z i ≤ θ
    linarith [(hn i).1, hxt i hi]
  · intro i hi
    change y i - noise φ z i ≤ θ
    linarith [(hn i).1, hyt i hi]

lemma smoothField_tail_zero (θ : ℝ) (hθ : 0 ≤ θ) (hσ : 3 * θ + 2 * A < σ)
    (hδ : 2 * φ.rOut ≤ θ) (j : Fin m)
    (x : EuclideanSpace ℝ (Fin m)) (hxj : -(θ / 2) ≤ x j)
    (hxt : ∀ l, j < l → x l ≤ θ / 2) (l : Fin m) (hjl : j < l) :
    smoothField φ A G ρ g σ x l = 0 := by
  have hz (z : EuclideanSpace ℝ (Fin m)) : field m A G ρ g σ (x - noise φ z) l = 0 := by
    have hn (i : Fin m) := abs_le.mp (noise_coordinate_bound φ z i)
    apply field_tail_zero A G ρ g σ hA hG hρ hg θ hθ hσ j _ _ _ l hjl
    · change -θ ≤ x j - noise φ z j
      linarith [(hn j).2]
    · intro i hi
      change x i - noise φ z i ≤ θ
      linarith [(hn i).1, hxt i hi]
  have hi := average_integrable φ _
    (field_continuous A G ρ L₀ L₁ g σ hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg) x
  have hp := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) l).integral_comp_comm hi
  change (∫ z, field m A G ρ g σ (x - noise φ z) l ∂(probability φ : Measure _)) =
    smoothField φ A G ρ g σ x l at hp
  rw [← hp]
  simp only [hz, integral_zero]

end

end LongTails.Proofs.RhoSmoothHardSmoothed
