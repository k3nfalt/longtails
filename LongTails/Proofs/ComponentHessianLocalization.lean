import LongTails.Proofs.ComponentHessianChain
import LongTails.Proofs.RelativeHessianCutoffBounds
import LongTails.Proofs.ProductCompositionJets

namespace LongTails.Proofs.ComponentHessianLocalization

open scoped RealInnerProductSpace
open ComponentHessianChain RelativeHessianCutoffSpatial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma product_direction_bound {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (x u : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (fun y => f y * g y))) x u‖ ≤
      |f x| * ‖fderiv ℝ (fderiv ℝ (gradient g)) x u‖ +
      (|g x| * ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ +
      3 * ‖gradient f x‖ * ‖fderiv ℝ (gradient g) x‖ +
      3 * ‖gradient g x‖ * ‖fderiv ℝ (gradient f) x‖) * ‖u‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have ht (T : E →L[ℝ] E →L[ℝ] E) : ‖T u v‖ ≤ ‖T‖ * ‖u‖ * ‖v‖ :=
    ((T u).le_opNorm v).trans (mul_le_mul_of_nonneg_right (T.le_opNorm u) (norm_nonneg v))
  have hh (H : E →L[ℝ] E) : |⟪H u, v⟫| ≤ ‖H‖ * ‖u‖ * ‖v‖ :=
    (abs_real_inner_le_norm (H u) v).trans
      (mul_le_mul_of_nonneg_right (H.le_opNorm u) (norm_nonneg v))
  have hs {c A B : ℝ} {z : E} (hc : |c| ≤ A) (hz : ‖z‖ ≤ B) (hA : 0 ≤ A) :
      ‖c • z‖ ≤ A * B := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hc hz (norm_nonneg z) hA
  rw [ProductCompositionJets.product_third_apply hf hg]
  calc
    _ ≤ ‖f x • fderiv ℝ (fderiv ℝ (gradient g)) x u v‖ +
        ‖⟪gradient f x, u⟫ • fderiv ℝ (gradient g) x v‖ +
        ‖⟪gradient f x, v⟫ • fderiv ℝ (gradient g) x u‖ +
        ‖⟪fderiv ℝ (gradient f) x u, v⟫ • gradient g x‖ +
        ‖g x • fderiv ℝ (fderiv ℝ (gradient f)) x u v‖ +
        ‖⟪gradient g x, u⟫ • fderiv ℝ (gradient f) x v‖ +
        ‖⟪gradient g x, v⟫ • fderiv ℝ (gradient f) x u‖ +
        ‖⟪fderiv ℝ (gradient g) x u, v⟫ • gradient f x‖ := by
      grw [norm_add_le, norm_add_le, norm_add_le, norm_add_le, norm_add_le, norm_add_le, norm_add_le]
    _ ≤ |f x| * (‖fderiv ℝ (fderiv ℝ (gradient g)) x u‖ * ‖v‖) +
        (‖gradient f x‖ * ‖u‖) * (‖fderiv ℝ (gradient g) x‖ * ‖v‖) +
        (‖gradient f x‖ * ‖v‖) * (‖fderiv ℝ (gradient g) x‖ * ‖u‖) +
        (‖fderiv ℝ (gradient f) x‖ * ‖u‖ * ‖v‖) * ‖gradient g x‖ +
        |g x| * (‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ * ‖u‖ * ‖v‖) +
        (‖gradient g x‖ * ‖u‖) * (‖fderiv ℝ (gradient f) x‖ * ‖v‖) +
        (‖gradient g x‖ * ‖v‖) * (‖fderiv ℝ (gradient f) x‖ * ‖u‖) +
        (‖fderiv ℝ (gradient g) x‖ * ‖u‖ * ‖v‖) * ‖gradient f x‖ := by
      exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
        (hs le_rfl ((fderiv ℝ (fderiv ℝ (gradient g)) x u).le_opNorm v) (abs_nonneg _))
        (hs (abs_real_inner_le_norm _ _) ((fderiv ℝ (gradient g) x).le_opNorm v) (by positivity)))
        (hs (abs_real_inner_le_norm _ _) ((fderiv ℝ (gradient g) x).le_opNorm u) (by positivity)))
        (hs (hh _) le_rfl (by positivity)))
        (hs le_rfl (ht _) (abs_nonneg _)))
        (hs (abs_real_inner_le_norm _ _) ((fderiv ℝ (gradient f) x).le_opNorm v) (by positivity)))
        (hs (abs_real_inner_le_norm _ _) ((fderiv ℝ (gradient f) x).le_opNorm u) (by positivity)))
        (hs (hh _) le_rfl (by positivity))
    _ = _ := by ring

variable {J : Type*} [Fintype J]

noncomputable def masked (B : ℝ) (s : Finset J) (a : J → E) (b : J → ℝ) (x : E) :=
  value B x * raw s a b x

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Fintype J] in
lemma masked_smooth (B : ℝ) (s : Finset J) (a : J → E) (b : J → ℝ) :
    ContDiff ℝ 3 (masked B s a b) := (smooth B).mul (raw_smooth s a b)

lemma direction_bound {B K : ℝ} (hK : 1 ≤ K) (hB : K ≤ B)
    (s : Finset J) (hs : (s.card : ℝ) ≤ K) (a : J → E) (b : J → ℝ)
    (ha : ∀ j, ‖a j‖ ≤ 2) (hb : ∀ j, |b j| ≤ 4 * K)
    (hframe : ∀ u, ∑ j, ⟪a j, u⟫ ^ 2 ≤ 4 * ‖u‖ ^ 2) (x u : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (masked B s a b))) x u‖ ≤
      2 ^ 26 * energy s a u + 2 ^ 62 * K / B * ‖u‖ := by
  have hp : 0 < B := by linarith
  have hrad := RelativeHessianCutoffBounds.bounds hp x
  have hh := product_direction_bound (smooth B) (raw_smooth s a b) x u
  have hval := RelativeHessianCutoff.bounds (argument B x)
  change 0 ≤ value B x ∧ value B x ≤ 1 at hval
  have hraw := raw_third_bound s a b hframe x u
  have he : 0 ≤ energy s a u := Real.sqrt_nonneg _
  by_cases hx : ‖x‖ ≤ 2 * B
  · have hv : |raw s a b x| ≤ 8 * K * B := calc
      _ ≤ s.card * (4 * K + 2 * ‖x‖) := raw_value_bound s a b ha hb x
      _ ≤ K * (4 * B + 2 * (2 * B)) := by gcongr
      _ = _ := by ring
    have hg : ‖gradient (raw s a b) x‖ ≤ 2 * K := (raw_gradient_bound s a b ha x).trans (by gcongr)
    have hH := raw_hessian_bound s a b hframe x
    refine hh.trans ?_
    rw [abs_of_nonneg hval.1]
    apply add_le_add
    · simpa using mul_le_mul hval.2 hraw (norm_nonneg _) zero_le_one
    · apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
      calc
        _ ≤ 8*K*B * (2^32/B^3) + 3*(2^32/B)*(2^26) + 3*(2*K)*(2^32/B^2) := by
          gcongr <;> first | exact hv | exact hrad.1 | exact hrad.2.1 | exact hrad.2.2
        _ ≤ _ := by
          field_simp
          nlinarith [mul_nonneg (sub_nonneg.mpr hK) (sq_nonneg B),
            mul_nonneg (show 0 ≤ B * (B - 1) from mul_nonneg hp.le (by linarith)) (show 0 ≤ K by linarith)]
  · have hz := outside_jets hp x (le_of_not_ge hx)
    rw [hz.1, hz.2.1, hz.2.2.1, hz.2.2.2] at hh
    have hzero : ‖(0 : E →L[ℝ] E →L[ℝ] E)‖ = 0 := @norm_zero (E →L[ℝ] E →L[ℝ] E) _
    simp only [hzero, norm_zero, abs_zero, zero_mul, mul_zero, add_zero] at hh
    apply hh.trans
    positivity

omit [Fintype J] in
lemma masked_curvature {B K : ℝ} (hK : 1 ≤ K) (hB : K ≤ B)
    (s : Finset J) (hs : (s.card : ℝ) ≤ K) (a : J → E) (b : J → ℝ)
    (ha : ∀ j, ‖a j‖ ≤ 2) (hb : ∀ j, |b j| ≤ 4 * K) (x u : E) :
    -(2 ^ 37 * K / B) * ‖u‖ ^ 2 ≤ ⟪fderiv ℝ (gradient (masked B s a b)) x u, u⟫ := by
  have hp : 0 < B := by linarith
  have hk : 0 ≤ K := by linarith
  unfold masked
  rw [ProductCompositionJets.product_hessian_apply (smooth B) (raw_smooth s a b)]
  simp only [inner_add_left, real_inner_smul_left]
  have h0 := mul_nonneg (RelativeHessianCutoff.bounds (argument B x)).1
    (raw_hessian_nonneg s a b x u)
  change 0 ≤ value B x * _ at h0
  by_cases hx : ‖x‖ ≤ 2 * B
  · have hv : |raw s a b x| ≤ 8 * K * B := calc
      _ ≤ s.card * (4 * K + 2 * ‖x‖) := raw_value_bound s a b ha hb x
      _ ≤ K * (4 * B + 2 * (2 * B)) := by gcongr
      _ = _ := by ring
    have rad := RelativeHessianCutoffBounds.bounds hp x
    have hg : ‖gradient (raw s a b) x‖ ≤ 2 * K := (raw_gradient_bound s a b ha x).trans (by gcongr)
    have hc : |⟪gradient (value B) x, u⟫ * ⟪gradient (raw s a b) x, u⟫| ≤
        (2^32/B * ‖u‖) * (2*K * ‖u‖) := by
      rw [abs_mul]
      gcongr
      · exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact rad.1)
      · exact (abs_real_inner_le_norm _ _).trans (by gcongr)
    have hbnd : |raw s a b x * ⟪fderiv ℝ (gradient (value B)) x u, u⟫| ≤
        (8*K*B) * (2^32/B^2 * ‖u‖ * ‖u‖) := by
      rw [abs_mul]
      apply mul_le_mul hv _ (abs_nonneg _) (by positivity)
      calc
        _ ≤ ‖fderiv ℝ (gradient (value B)) x u‖ * ‖u‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖fderiv ℝ (gradient (value B)) x‖ * ‖u‖) * ‖u‖ := by
          gcongr; exact (fderiv ℝ (gradient (value B)) x).le_opNorm u
        _ ≤ _ := by gcongr; exact rad.2.1
    have hh : (8*K*B) * (2^32/B^2 * ‖u‖ * ‖u‖) +
        2 * (2^32/B * ‖u‖) * (2*K * ‖u‖) ≤ 2^37*K/B * ‖u‖^2 := by
      field_simp
      nlinarith [mul_nonneg (mul_nonneg hk hp.le) (sq_nonneg ‖u‖)]
    linarith only [h0, (abs_le.mp hc).1, (abs_le.mp hbnd).1, hh,
      mul_comm ⟪gradient (value B) x, u⟫ ⟪gradient (raw s a b) x, u⟫]
  · have hz := outside_jets hp x (le_of_not_ge hx)
    simp [hz.1, hz.2.1, hz.2.2.1]
    positivity

lemma convex_of_curvature {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hH : ∀ x v, 0 ≤ ⟪fderiv ℝ (gradient f) x v, v⟫) : ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let v := y - x
  let line := fun t : ℝ => x + t • v
  have hl (t : ℝ) : HasDerivAt line v t := by
    simpa [line] using ((hasDerivAt_id t).smul_const v).const_add x
  have h₁ (t : ℝ) : HasDerivAt (f ∘ line) ⟪gradient f (line t), v⟫ t :=
    ((GradientDependentLocal.derivative_chain hf).1 _).comp_hasDerivAt t (hl t)
  have h₂ (t : ℝ) : HasDerivAt (fun r => ⟪gradient f (line r), v⟫)
      ⟪fderiv ℝ (gradient f) (line t) v, v⟫ t := by
    simpa [Function.comp_def] using (((GradientDependentLocal.derivative_chain hf).2.1
      (line t)).comp_hasDerivAt t (hl t)).inner ℝ (hasDerivAt_const t v)
  have hc : ConvexOn ℝ Set.univ (f ∘ line) := by
    apply Monotone.convexOn_univ_of_deriv (fun t => (h₁ t).differentiableAt)
    rw [show deriv (f ∘ line) = _ from funext (fun t => (h₁ t).deriv)]
    exact monotone_of_hasDerivAt_nonneg h₂ (fun t => hH (line t) v)
  have hh := hc.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ)) ha hb hab
  have eq : x + b • v = a • x + b • y := by
    dsimp [v]
    rw [show a = 1 - b by linarith]
    module
  simpa [line, Function.comp_def, eq, v, smul_eq_mul] using hh

lemma segment_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x y : E) {D : ℝ}
    (hD : ∀ z, ‖fderiv ℝ (fderiv ℝ (gradient f)) z (x - y)‖ ≤ D) :
    ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ D := by
  let w := x - y
  have h (t : ℝ) : HasDerivAt (fun r : ℝ => y + r • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add y
  have hd (t : ℝ) := ((GradientDependentLocal.derivative_chain hf).2.2
    (y + t • w)).comp_hasDerivAt t (h t)
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => hD (y + t • w))
  simpa [w] using hm

end LongTails.Proofs.ComponentHessianLocalization
