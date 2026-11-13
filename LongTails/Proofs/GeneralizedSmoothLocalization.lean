import LongTails.Proofs.GeneralizedSmoothShieldBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace LongTails.Proofs.GeneralizedSmoothLocalization

open GeneralizedSmoothShieldCalculus GeneralizedSmoothShieldGeometry GeneralizedSmoothShieldBounds

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
  L₀_nonneg : 0 ≤ L₀
  L₁_nonneg : 0 ≤ L₁
  convex : ConvexOn ℝ univ f
  gradient : ∀ x, HasGradientAt f (g x) x
  differentiable : Differentiable ℝ g
  curvature : ∀ x, ‖fderiv ℝ g x‖ ≤ L₀ + L₁ * ‖g x‖
  bounded : ∀ x, ‖g x‖ ≤ G
  nonnegative : ∀ x, 0 ≤ f x
  zero : f z = 0
  radius : ‖z‖ ≤ r

noncomputable def strength (s : Seed (E := E)) (a : ℝ) : ℝ := s.G + a * s.r

noncomputable def objective (s : Seed (E := E)) (a : ℝ) : E → ℝ :=
  value s.f a (16 * strength s a / a) (64 * strength s a ^ 2 / a)

noncomputable def gradient (s : Seed (E := E)) (a : ℝ) : E → E :=
  field s.f s.g a (16 * strength s a / a) (64 * strength s a ^ 2 / a)

lemma strength_pos (s : Seed (E := E)) (a : ℝ) (ha : 0 < a) : 0 < strength s a := by
  have := s.G_nonneg
  have := s.r_pos
  unfold strength
  positivity

lemma strength_radius (s : Seed (E := E)) (a : ℝ) : a * s.r ≤ strength s a := by
  have := s.G_nonneg
  unfold strength
  linarith

lemma seed_upper (s : Seed (E := E)) (a : ℝ) (ha : 0 < a) (x : E) :
    s.f x ≤ strength s a * ‖x‖ + strength s a ^ 2 / a :=
  (convex_value_upper s.f s.g s.G s.r s.convex s.gradient s.z x s.zero s.radius (s.bounded x)).trans
    (enlarged_upper a s.G s.r ha s.G_nonneg s.r_pos.le x)

lemma objective_gradient (s : Seed (E := E)) (a : ℝ) (ha : 0 < a) (x : E) :
    HasGradientAt (objective s a) (gradient s a x) x :=
  value_hasGradientAt s.f s.g a _ _ (by have := strength_pos s a ha; positivity) x (s.gradient x)

lemma gradient_differentiable (s : Seed (E := E)) (a : ℝ) : Differentiable ℝ (gradient s a) := by
  intro x
  exact (field_hasFDerivAt s.f s.g a _ _ x _ (s.gradient x) (s.differentiable x).hasFDerivAt).differentiableAt

lemma objective_convex (s : Seed (E := E)) (a : ℝ) (ha : 0 < a) :
    ConvexOn ℝ univ (objective s a) :=
  value_convex s.f s.g a _ _ ha.le (by have := strength_pos s a ha; positivity) s.convex s.gradient

lemma objective_above (s : Seed (E := E)) (a : ℝ) (ha : 0 < a) (x : E) :
    s.f x ≤ objective s a x :=
  (value_above s.f a _ _ (by have := strength_pos s a ha; positivity) x).1

lemma objective_nonnegative (s : Seed (E := E)) (a : ℝ) (ha : 0 < a) (x : E) :
    0 ≤ objective s a x := (s.nonnegative x).trans (objective_above s a ha x)

lemma objective_interior (s : Seed (E := E)) (a : ℝ) (ha : 0 < a) (x : E)
    (hx : ‖x‖ ≤ 2 * s.r) : objective s a x = s.f x :=
  value_eq_left s.f a _ _ (by have := strength_pos s a ha; positivity) x
    (interior_separation s.f a _ s.r ha (strength_pos s a ha) (strength_radius s a) x hx (s.nonnegative x))

lemma objective_zero (s : Seed (E := E)) (a : ℝ) (ha : 0 < a) : objective s a s.z = 0 := by
  rw [objective_interior s a ha s.z (by have := s.radius; have := s.r_pos; linarith), s.zero]

lemma objective_minimizer (s : Seed (E := E)) (a : ℝ) (ha : 0 < a) :
    IsMinOn (objective s a) univ s.z := by
  intro x _
  rw [objective_zero s a ha]
  exact objective_nonnegative s a ha x

lemma gradient_curvature (s : Seed (E := E)) (a : ℝ) (ha : 0 < a) (x : E) :
    ‖fderiv ℝ (gradient s a) x‖ ≤ s.L₀ + 10 * a + 2 * s.L₁ * ‖gradient s a x‖ := by
  apply curvature_bound s.f s.g s.L₀ s.L₁ a (strength s a) s.r s.L₀_nonneg s.L₁_nonneg
    ha (strength_pos s a ha) (strength_radius s a) s.convex s.gradient s.differentiable s.curvature
    s.z x s.zero s.radius _ (s.nonnegative x) (seed_upper s a ha x)
  have hh : s.G ≤ strength s a := by
    have := s.r_pos
    unfold strength
    have := mul_nonneg ha.le s.r_pos.le
    linarith
  exact (s.bounded x).trans hh

lemma objective_exterior (s : Seed (E := E)) (a : ℝ) (ha : 0 < a) (x : E)
    (hx : 24 * strength s a / a ≤ ‖x‖) : objective s a x = wall a (16 * strength s a / a) x :=
  value_eq_wall s.f a _ _ (by have := strength_pos s a ha; positivity) x
    (exterior_separation s.f a _ ha (strength_pos s a ha) x hx (seed_upper s a ha x))

lemma gradient_exterior (s : Seed (E := E)) (a : ℝ) (ha : 0 < a) (x : E)
    (hx : 24 * strength s a / a ≤ ‖x‖) : gradient s a x = a • x := by
  have hm := (mixing_left s.f a _ _ (show 0 < 64 * strength s a ^ 2 / a by
    have := strength_pos s a ha; positivity) x
    (exterior_separation s.f a _ ha (strength_pos s a ha) x hx (seed_upper s a ha x))).1
  change field s.f s.g a _ _ x = _
  rw [field, hm, zero_smul, add_zero]

end LongTails.Proofs.GeneralizedSmoothLocalization
