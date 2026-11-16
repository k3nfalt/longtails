import LongTails.Proofs.GeneralizedSmoothChainPrefix
import LongTails.Proofs.AdaptiveGeneralizedSmoothLocalization
import LongTails.Proofs.SmoothConvexFiniteLowerBound
import LongTails.Setups.GapGeneralizedSmoothConvex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace LongTails.Proofs.GapLocalizedChain

open FiniteSumNondualLowerComponents GeneralizedSmoothCoordinateEmbedding
open GeneralizedSmoothChainPrefix AdaptiveGeneralizedSmoothLocalization

noncomputable def liftSeed {d m : ℕ} (s : Seed (E := EuclideanSpace ℝ (Fin m)))
    (π : Fin m ↪ Fin d) : Seed (E := EuclideanSpace ℝ (Fin d)) where
  f := fun x => s.f (coordinateMap π x)
  g := fun x => (coordinateMap π).adjoint (s.g (coordinateMap π x))
  z := (coordinateMap π).adjoint s.z
  G := s.G
  r := s.r
  L₀ := s.L₀
  L₁ := s.L₁
  G_nonneg := s.G_nonneg
  r_pos := s.r_pos
  L₀_pos := s.L₀_pos
  L₁_pos := s.L₁_pos
  convex := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hh := s.convex.2 (mem_univ (coordinateMap π x)) (mem_univ (coordinateMap π y)) ha hb hab
    simpa only [map_add, map_smul] using hh
  gradient := composed_gradient π s.f s.g s.gradient
  differentiable := (coordinateMap π).adjoint.differentiable.comp
    (s.differentiable.comp (coordinateMap π).differentiable)
  curvature := composed_curvature π s.g s.differentiable _ _ s.curvature
  bounded := fun x => by rw [adjoint_norm]; exact s.bounded _
  nonnegative := fun x => s.nonnegative _
  zero := by rw [projection_adjoint]; exact s.zero
  radius := by rw [adjoint_norm]; exact s.radius

noncomputable def partialField {d m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (n : ℕ) (a B : ℝ) (π : Fin m ↪ Fin d) (r : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if 4 * B ≤ ‖x‖ then a • x else
    let v := (coordinateMap π).adjoint (truncate r (g (truncate r (coordinateMap π x))))
    v + AdaptivePolynomialHinge.mixing n
      ((AdaptivePolynomialLocalization.wall a B x - f (truncate r (coordinateMap π x))) / (a * B ^ 2)) • (a • x - v)

lemma partialField_prefix {d m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (n : ℕ) (a B : ℝ) (π ρ : Fin m ↪ Fin d) (r : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ i, i.val ≤ r → π i = ρ i) :
    partialField f g n a B π r x = partialField f g n a B ρ r x := by
  unfold partialField
  rw [truncate_prefix π ρ r h x, adjoint_truncate_prefix π ρ r h]

lemma partialField_eq {d m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (n : ℕ) (a B θ : ℝ) (π : Fin m ↪ Fin d) (r : Fin m) (x : EuclideanSpace ℝ (Fin d))
    (hf : ∀ y, (∀ i, r ≤ i → |y i| ≤ θ) → f (truncate r.val y) = f y)
    (hg : ∀ y, (∀ i, r ≤ i → |y i| ≤ θ) → truncate r.val (g (truncate r.val y)) = g y)
    (hfar : 4 * B ≤ ‖x‖ →
      AdaptivePolynomialLocalization.field (fun y => f (coordinateMap π y))
        (fun y => (coordinateMap π).adjoint (g (coordinateMap π y))) n a B (a * B ^ 2) x = a • x)
    (hsmall : ‖x‖ < 4 * B → ∀ i, r ≤ i → |x (π i)| ≤ θ) :
    partialField f g n a B π r.val x =
      AdaptivePolynomialLocalization.field (fun y => f (coordinateMap π y))
        (fun y => (coordinateMap π).adjoint (g (coordinateMap π y))) n a B (a * B ^ 2) x := by
  unfold partialField
  split_ifs with hx
  · exact (hfar hx).symm
  · have hcoords : ∀ i, r ≤ i → |coordinateMap π x i| ≤ θ := hsmall (lt_of_not_ge hx)
    rw [hf _ hcoords, hg _ hcoords]
    rfl

lemma admissible (p : LongTails.Setups.GapGeneralizedSmoothConvex.Params)
    (s : Seed (E := EuclideanSpace ℝ (Fin p.d))) (n : ℕ) (hn : 2 ≤ n) (a B : ℝ)
    (ha : 0 < a) (hB : 0 < B) (hrB : s.r ≤ B) (hrR : s.r ≤ p.R) (hgap : s.f 0 ≤ p.Δ)
    (hcurv : ∀ x, ‖fderiv ℝ (AdaptivePolynomialLocalization.field s.f s.g n a B (a * B ^ 2)) x‖ ≤
      p.L0 + p.L1 * ‖AdaptivePolynomialLocalization.field s.f s.g n a B (a * B ^ 2) x‖) :
    LongTails.Setups.GapGeneralizedSmoothConvex.spec.admissible p
      (fun x : EuclideanSpace ℝ (Fin p.d) => AdaptivePolynomialLocalization.value s.f n a B (a * B ^ 2) (x - p.x0))
      (SmoothConvexFiniteLowerBound.oracle p.x0
        (AdaptivePolynomialLocalization.field s.f s.g n a B (a * B ^ 2))) := by
  let f := AdaptivePolynomialLocalization.value s.f n a B (a * B ^ 2)
  let g := AdaptivePolynomialLocalization.field s.f s.g n a B (a * B ^ 2)
  have hW : 0 < a * B ^ 2 := by positivity
  have hg := AdaptivePolynomialLocalization.value_hasGradientAt s.f s.g n hn a B _ hW
  have hd := AdaptiveGeneralizedSmoothLocalization.field_differentiable s n hn a B (a * B ^ 2)
  have hz : f s.z = 0 := (AdaptiveGeneralizedSmoothLocalization.value_interior s n a B ha hB
    s.z (s.radius.trans hrB)).trans s.zero
  have hzero : f 0 = s.f 0 := AdaptiveGeneralizedSmoothLocalization.value_interior s n a B ha hB
    0 (by simpa using hB.le)
  refine ⟨SmoothConvexFiniteLowerBound.convex_translate p.x0 _
    (AdaptivePolynomialLocalization.value_convex s.f s.g n hn a B _ ha.le hW s.convex s.gradient),
    ?_, ?_, ?_, p.x0 + s.z, ?_, ?_, ?_⟩
  · intro k ω x
    exact SmoothConvexFiniteLowerBound.gradient_translate p.x0 _ _ (fun y => hg y (s.gradient y)) x
  · intro k ω
    exact hd.comp (differentiable_id.sub_const p.x0)
  · intro k ω x
    change ‖fderiv ℝ (fun y => g (y - p.x0)) x‖ ≤ _
    have ht := (hd (x - p.x0)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p.x0)
    change HasFDerivAt (fun y => g (y - p.x0)) _ x at ht
    rw [ht.fderiv, ContinuousLinearMap.comp_id]
    exact hcurv (x - p.x0)
  · intro x _
    change f (p.x0 + s.z - p.x0) ≤ f (x - p.x0)
    rw [add_sub_cancel_left]
    exact AdaptiveGeneralizedSmoothLocalization.value_minimizer s n hn a B ha hB hrB
      (mem_univ (x - p.x0))
  · change ‖p.x0 - (p.x0 + s.z)‖ ≤ p.R
    simpa only [sub_add_cancel_left, norm_neg] using s.radius.trans hrR
  · change f (p.x0 - p.x0) - f (p.x0 + s.z - p.x0) ≤ p.Δ
    rw [sub_self, add_sub_cancel_left, hz, sub_zero, hzero]
    exact hgap

end LongTails.Proofs.GapLocalizedChain
