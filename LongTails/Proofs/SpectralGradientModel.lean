import LongTails.Proofs.HessianLipschitzModel

open scoped RealInnerProductSpace

namespace OracleTemplate.SpectralGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

lemma hessian_symmetric {f : E → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ (gradient f)) (u : E) :
    (fderiv ℝ (gradient f) u).toLinearMap.IsSymmetric := by
  have hh := (InnerProductSpace.toDual ℝ E).toContinuousLinearMap.hasFDerivAt.comp u
    (hg u).hasFDerivAt
  have he : HasFDerivAt (fderiv ℝ f)
      ((InnerProductSpace.toDual ℝ E).toContinuousLinearMap.comp
        (fderiv ℝ (gradient f) u)) u := by
    change HasFDerivAt ((InnerProductSpace.toDual ℝ E) ∘ gradient f) _ u at hh
    rw [toDual_comp_gradient] at hh
    exact hh
  intro x y
  have hs := second_derivative_symmetric (fun y => (hf y).hasFDerivAt) he x y
  change ⟪fderiv ℝ (gradient f) u x, y⟫ = ⟪fderiv ℝ (gradient f) u y, x⟫ at hs
  exact hs.trans (real_inner_comm _ _)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma anchored_linearization {g : E → E} {M r : ℝ} (hM : 0 ≤ M)
    (hg : Differentiable ℝ g) (u x y : E)
    (hH : ∀ z, ‖fderiv ℝ g z - fderiv ℝ g u‖ ≤ M * ‖z - u‖)
    (hx : ‖x - u‖ ≤ r) (hy : ‖y - u‖ ≤ r) :
    ‖g y - g x - fderiv ℝ g u (y - x)‖ ≤ M * r * ‖y - x‖ := by
  let R := fun z => g z - fderiv ℝ g u z
  have hR (z : E) : HasFDerivAt R (fderiv ℝ g z - fderiv ℝ g u) z :=
    (hg z).hasFDerivAt.sub (fderiv ℝ g u).hasFDerivAt
  have hb (z : E) (hz : z ∈ Metric.closedBall u r) :
      ‖fderiv ℝ g z - fderiv ℝ g u‖ ≤ M * r :=
    (hH z).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz) hM)
  have hh := (convex_closedBall u r).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hR z).hasFDerivWithinAt) hb
    (show x ∈ Metric.closedBall u r by simpa only [Metric.mem_closedBall, dist_eq_norm])
    (show y ∈ Metric.closedBall u r by simpa only [Metric.mem_closedBall, dist_eq_norm])
  dsimp [R] at hh
  convert hh using 1
  congr 1
  rw [map_sub]
  abel

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma step_lipschitz {g : E → E} {a ρ : ℝ} (hρ : 0 ≤ ρ)
    (hg : Differentiable ℝ g)
    (hstep : ∀ z v, ‖v - a • fderiv ℝ g z v‖ ≤ ρ * ‖v‖) (x y : E) :
    ‖(y - a • g y) - (x - a • g x)‖ ≤ ρ * ‖y - x‖ := by
  let S := fun z => z - a • g z
  have hd (z : E) : HasFDerivAt S
      (ContinuousLinearMap.id ℝ E - a • fderiv ℝ g z) z :=
    (hasFDerivAt_id z).sub ((hg z).hasFDerivAt.const_smul a)
  have hb (z : E) : ‖ContinuousLinearMap.id ℝ E - a • fderiv ℝ g z‖ ≤ ρ := by
    apply ContinuousLinearMap.opNorm_le_bound _ hρ
    exact hstep z
  exact (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hd z).hasFDerivWithinAt) (fun z _ => hb z) (Set.mem_univ x) (Set.mem_univ y)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma step_gradient_contract {g : E → E} {a ρ : ℝ} (ha : 0 < a)
    (hstep : ∀ x y, ‖(y - a • g y) - (x - a • g x)‖ ≤ ρ * ‖y - x‖) (x : E) :
    ‖g (x - a • g x)‖ ≤ ρ * ‖g x‖ := by
  have hh := hstep (x - a • g x) x
  have he : (x - a • g x) - ((x - a • g x) - a • g (x - a • g x)) =
      a • g (x - a • g x) := by abel
  have he' : x - (x - a • g x) = a • g x := by abel
  rw [he, he', norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hh
  apply (mul_le_mul_iff_right₀ ha).mp
  nlinarith only [hh]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma distance_from_gradient {f : E → ℝ} {g : E → E} {μ : ℝ} (hμ : 0 < μ)
    (hs : ∀ x y, f x + ⟪g x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (u : E) (hu : g u = 0) (x : E) : ‖x - u‖ ≤ ‖g x‖ / μ := by
  have hm := NonlinearTemporalDiscrepancy.gradient_strong_monotonicity hs u x
  rw [hu, sub_zero] at hm
  have hb := real_inner_le_norm (g x) (x - u)
  apply (le_div_iff₀ hμ).mpr
  by_cases hz : ‖x - u‖ = 0
  · simp [hz]
  · have hp : 0 < ‖x - u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ hp).mp
    nlinarith only [hm, hb]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma gap_from_gradient {f : E → ℝ} {g : E → E} {μ : ℝ} (hμ : 0 < μ)
    (hs : ∀ x y, f x + ⟪g x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (u x : E) : f x - f u ≤ ‖g x‖ ^ 2 / (2 * μ) := by
  have hh := hs x u
  have hb := real_inner_le_norm (g x) (x - u)
  have he : ⟪g x, u - x⟫ = -⟪g x, x - u⟫ := by rw [← inner_neg_right]; congr 1; abel
  rw [he, norm_sub_rev u x] at hh
  apply (le_div_iff₀ (by positivity : 0 < 2 * μ)).mpr
  nlinarith [sq_nonneg (‖g x‖ - μ * ‖x - u‖)]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma gradient_growth {g : E → E} {μ L η : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / μ)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (x : E) :
    ‖g (x - η • g x)‖ ≤ (2 * L / μ) * ‖g x‖ := by
  have hL : 0 < L := hμ.trans_le hμL
  have hh := hlip (x - η • g x) x
  have he : x - η • g x - x = -η • g x := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη0] at hh
  have hfactor : 1 + L * η ≤ 2 * L / μ := by
    have h1 := mul_le_mul_of_nonneg_left hη hL.le
    have h2 : 1 ≤ L / μ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
    simp only [div_eq_mul_inv, one_mul] at h1 h2 ⊢
    nlinarith only [h1, h2]
  calc
    _ = ‖(g (x - η • g x) - g x) + g x‖ := by congr 1; abel
    _ ≤ ‖g (x - η • g x) - g x‖ + ‖g x‖ := norm_add_le _ _
    _ ≤ L * (η * ‖g x‖) + ‖g x‖ := add_le_add hh le_rfl
    _ = (1 + L * η) * ‖g x‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma step_remainder {f : E → ℝ} {g : E → E} {μ M b η : ℝ}
    (hμ : 0 < μ) (hM : 0 ≤ M) (hb : 1 ≤ b) (hη0 : 0 ≤ η) (hη : η ≤ 1 / μ)
    (hg : Differentiable ℝ g)
    (hs : ∀ x y, f x + ⟪g x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (u : E) (hu : g u = 0)
    (hH : ∀ z, ‖fderiv ℝ g z - fderiv ℝ g u‖ ≤ M * ‖z - u‖)
    (x : E) (hgrowth : ‖g (x - η • g x)‖ ≤ b * ‖g x‖) :
    ‖g (x - η • g x) - (g x - η • fderiv ℝ g u (g x))‖ ≤
      (M / μ ^ 2) * b * ‖g x‖ ^ 2 := by
  have hb0 : 0 ≤ b := by linarith
  have hx : ‖x - u‖ ≤ b * ‖g x‖ / μ := by
    apply (distance_from_gradient hμ hs u hu x).trans
    gcongr
    simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg (g x))
  have hy : ‖x - η • g x - u‖ ≤ b * ‖g x‖ / μ :=
    (distance_from_gradient hμ hs u hu _).trans (div_le_div_of_nonneg_right hgrowth hμ.le)
  have hh := anchored_linearization hM hg u x (x - η • g x) hH hx hy
  have he : x - η • g x - x = -η • g x := by module
  rw [he, map_smul, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη0] at hh
  have he' : g (x - η • g x) - g x - -η • fderiv ℝ g u (g x) =
      g (x - η • g x) - (g x - η • fderiv ℝ g u (g x)) := by module
  rw [he'] at hh
  calc
    _ ≤ M * (b * ‖g x‖ / μ) * (η * ‖g x‖) := hh
    _ ≤ M * (b * ‖g x‖ / μ) * ((1 / μ) * ‖g x‖) := by gcongr
    _ = _ := by ring

end OracleTemplate.SpectralGradient
