import LongTails.Proofs.ZerothOrderSmoothing
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.SphereRotationMeasure

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]

abbrev Rotation := unitary (E →L[ℝ] E)

instance rotationCompactSpace : CompactSpace (Rotation E) := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : E →L[ℝ] E) 1).of_isClosed_subset isClosed_unitary
  intro u hu
  simpa only [mem_closedBall, dist_zero_right, CStarRing.norm_of_mem_unitary hu] using
    (le_refl (1 : ℝ))

instance rotationMeasurableSpace : MeasurableSpace (Rotation E) := borel (Rotation E)

instance rotationBorelSpace : BorelSpace (Rotation E) := ⟨rfl⟩

noncomputable def rotationCompact : TopologicalSpace.PositiveCompacts (Rotation E) :=
  ⟨⟨univ, isCompact_univ⟩, by simp⟩

noncomputable def rotationMeasure : Measure (Rotation E) :=
  (Measure.haarMeasure (rotationCompact E)).inv

instance rotationMeasureProbability : IsProbabilityMeasure (rotationMeasure E) := by
  constructor
  simp only [rotationMeasure, Measure.inv_def, Measure.map_apply measurable_inv MeasurableSet.univ,
    preimage_univ]
  exact Measure.haarMeasure_self (K₀ := rotationCompact E)

instance rotationMeasureRightInvariant : (rotationMeasure E).IsMulRightInvariant := by
  unfold rotationMeasure
  infer_instance

lemma integral_rotation_right (f : Rotation E → ℝ) (R : Rotation E) :
    (∫ U, f (U * R) ∂rotationMeasure E) = ∫ U, f U ∂rotationMeasure E :=
  integral_mul_right_eq_self f R

lemma integral_action_right (f : E → ℝ) (R : E ≃ₗᵢ[ℝ] E) (x : E) :
    (∫ U : Rotation E, f ((U : E →L[ℝ] E) (R x)) ∂rotationMeasure E) =
      ∫ U : Rotation E, f ((U : E →L[ℝ] E) x) ∂rotationMeasure E := by
  have h := integral_rotation_right E (fun U : Rotation E => f ((U : E →L[ℝ] E) x))
    (Unitary.linearIsometryEquiv.symm R)
  simpa using h

lemma integral_frame_right (f : E → E → ℝ) (R : E ≃ₗᵢ[ℝ] E) (x y : E) :
    (∫ U : Rotation E, f ((U : E →L[ℝ] E) (R x)) ((U : E →L[ℝ] E) (R y))
      ∂rotationMeasure E) =
      ∫ U : Rotation E, f ((U : E →L[ℝ] E) x) ((U : E →L[ℝ] E) y)
        ∂rotationMeasure E := by
  have h := integral_rotation_right E
    (fun U : Rotation E => f ((U : E →L[ℝ] E) x) ((U : E →L[ℝ] E) y))
    (Unitary.linearIsometryEquiv.symm R)
  simpa using h

lemma integral_action_eq_of_norm_eq (f : E → ℝ) {x y : E} (hxy : ‖x‖ = ‖y‖) :
    (∫ U : Rotation E, f ((U : E →L[ℝ] E) x) ∂rotationMeasure E) =
      ∫ U : Rotation E, f ((U : E →L[ℝ] E) y) ∂rotationMeasure E := by
  have h := integral_action_right E f (Submodule.reflection (ℝ ∙ (x - y))ᗮ) x
  rw [Submodule.reflection_sub hxy] at h
  exact h.symm

omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma exists_isometry_pair {x y x' y' : E} (hx : ‖x‖ = ‖x'‖) (hy : ‖y‖ = ‖y'‖)
    (hinner : ⟪x, y⟫ = ⟪x', y'⟫) :
    ∃ R : E ≃ₗᵢ[ℝ] E, R x = x' ∧ R y = y' := by
  let A := Submodule.reflection (ℝ ∙ (x - x'))ᗮ
  have hAx : A x = x' := Submodule.reflection_sub hx
  let B := Submodule.reflection (ℝ ∙ (A y - y'))ᗮ
  have hBy : B (A y) = y' := Submodule.reflection_sub ((A.norm_map y).trans hy)
  have hBx : B x' = x' := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left, inner_sub_right]
    rw [← hAx, A.inner_map_map, hAx, hinner, sub_self]
  refine ⟨A.trans B, ?_, hBy⟩
  change B (A x) = x'
  rw [hAx, hBx]

lemma integral_frame_eq_of_gram_eq (f : E → E → ℝ) {x y x' y' : E}
    (hx : ‖x‖ = ‖x'‖) (hy : ‖y‖ = ‖y'‖) (hinner : ⟪x, y⟫ = ⟪x', y'⟫) :
    (∫ U : Rotation E, f ((U : E →L[ℝ] E) x) ((U : E →L[ℝ] E) y)
      ∂rotationMeasure E) =
    (∫ U : Rotation E, f ((U : E →L[ℝ] E) x') ((U : E →L[ℝ] E) y')
      ∂rotationMeasure E) := by
  obtain ⟨R, hRx, hRy⟩ := exists_isometry_pair E hx hy hinner
  have h := integral_frame_right E f R x y
  rw [hRx, hRy] at h
  exact h.symm

omit [FiniteDimensional ℝ E] [Nontrivial E] in
lemma norm_orthogonal_combination {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫ = 0) (c s : ℝ) : ‖c • x + s • y‖ ^ 2 = c ^ 2 + s ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs, hx, hy, inner_smul_left, inner_smul_right, hxy]
  ring

lemma integral_frame_circle (f : E → E → ℝ) {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ⟪x, y⟫ = 0) (t : ℝ) :
    (∫ U : Rotation E,
      f ((U : E →L[ℝ] E) (Real.cos t • x + Real.sin t • y))
        ((U : E →L[ℝ] E) (-Real.sin t • x + Real.cos t • y)) ∂rotationMeasure E) =
      ∫ U : Rotation E, f ((U : E →L[ℝ] E) x) ((U : E →L[ℝ] E) y)
        ∂rotationMeasure E := by
  apply (integral_frame_eq_of_gram_eq E f ?_ ?_ ?_).symm
  · rw [hx]
    apply (sq_eq_sq₀ zero_le_one (norm_nonneg _)).mp
    rw [norm_orthogonal_combination E hx hy hxy, one_pow]
    exact (Real.cos_sq_add_sin_sq t).symm
  · rw [hy]
    apply (sq_eq_sq₀ zero_le_one (norm_nonneg _)).mp
    rw [norm_orthogonal_combination E hx hy hxy, neg_sq, one_pow]
    exact (Real.sin_sq_add_cos_sq t).symm
  · rw [hxy]
    have hyx : ⟪y, x⟫ = 0 := by rw [real_inner_comm, hxy]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, hx, hy, hxy, hyx, one_pow]
    ring

variable [MeasurableSpace E] [BorelSpace E]

open OracleTemplate.ZerothOrder

lemma rotation_sphere_integral {f : E → ℝ} (hf : Continuous f) {x : E} (hx : ‖x‖ = 1) :
    (∫ U : Rotation E, f ((U : E →L[ℝ] E) x) ∂rotationMeasure E) =
      ∫ u : sphere (0 : E) 1, f u ∂(sphereLaw E : Measure _) := by
  let S := sphere (0 : E) 1
  let Q : Measure S := sphereLaw E
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E) 1)
  have hc (u : S) :
      (∫ U : Rotation E, f ((U : E →L[ℝ] E) u) ∂rotationMeasure E) =
        ∫ U : Rotation E, f ((U : E →L[ℝ] E) x) ∂rotationMeasure E :=
    integral_action_eq_of_norm_eq E f ((mem_sphere_zero_iff_norm.mp u.property).trans hx.symm)
  have hcontinuous : Continuous (fun w : S × Rotation E => f ((w.2 : E →L[ℝ] E) w.1)) := by
    apply hf.comp
    fun_prop
  have hi : Integrable (fun w : S × Rotation E => f ((w.2 : E →L[ℝ] E) w.1))
      (Q.prod (rotationMeasure E)) :=
    hcontinuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hr (U : Rotation E) : (∫ u : S, f ((U : E →L[ℝ] E) u) ∂Q) = ∫ u : S, f u ∂Q := by
    exact sphereLaw_integral_rotate E (Unitary.linearIsometryEquiv U) (fun u => f u)
  calc
    _ = ∫ u : S, ∫ U : Rotation E, f ((U : E →L[ℝ] E) u) ∂rotationMeasure E ∂Q := by
      simp_rw [hc]
      simp [Q, S]
    _ = ∫ U : Rotation E, ∫ u : S, f ((U : E →L[ℝ] E) u) ∂Q ∂rotationMeasure E :=
      integral_integral_swap hi
    _ = _ := by simp_rw [hr]; simp [Q, S]

section Coordinates

variable {d : ℕ} [NeZero d]
local notation "H" => EuclideanSpace ℝ (Fin d)
local notation "e" => (fun i : Fin d => EuclideanSpace.single i (1 : ℝ))

lemma frame_coordinate_integrals_equal (g : H → H) (i j k : Fin d)
    (hij : i ≠ j) (hik : i ≠ k) :
    (∫ U : Rotation H, ⟪g ((U : H →L[ℝ] H) (e i)), (U : H →L[ℝ] H) (e j)⟫ ^ 2
      ∂rotationMeasure H) =
    (∫ U : Rotation H, ⟪g ((U : H →L[ℝ] H) (e i)), (U : H →L[ℝ] H) (e k)⟫ ^ 2
      ∂rotationMeasure H) := by
  have h := integral_frame_right H (fun x y => ⟪g x, y⟫ ^ 2)
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap j k)) (e i) (e j)
  simpa [EuclideanSpace.piLpCongrLeft_single, Equiv.swap_apply_of_ne_of_ne hij hik] using h.symm

lemma frame_second_moment_bound {g : H → H} (hg : Continuous g)
    (i j : Fin d) (hij : i ≠ j) :
    ((d : ℝ) - 1) *
      (∫ U : Rotation H, ⟪g ((U : H →L[ℝ] H) (e i)), (U : H →L[ℝ] H) (e j)⟫ ^ 2
        ∂rotationMeasure H) ≤
      ∫ u : sphere (0 : H) 1, ‖g u‖ ^ 2 ∂(sphereLaw H : Measure _) := by
  let F := fun k : Fin d => fun U : Rotation H =>
    ⟪g ((U : H →L[ℝ] H) (e i)), (U : H →L[ℝ] H) (e k)⟫ ^ 2
  have hcont (k : Fin d) : Continuous (F k) := by dsimp [F]; fun_prop
  have hint (k : Fin d) : Integrable (F k) (rotationMeasure H) :=
    (hcont k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq (k : Fin d) : (∫ U, F k U ∂rotationMeasure H) =
      (∫ U, F j U ∂rotationMeasure H) +
        if k = i then (∫ U, F i U ∂rotationMeasure H) -
          (∫ U, F j U ∂rotationMeasure H) else 0 := by
    by_cases hki : k = i
    · subst k
      simp
    · rw [ite_eq_right hki, add_zero]
      exact frame_coordinate_integrals_equal g i k j (Ne.symm hki) hij
  have hsum (U : Rotation H) : (∑ k : Fin d, F k U) =
      ‖g ((U : H →L[ℝ] H) (e i))‖ ^ 2 := by
    have h := ((EuclideanSpace.basisFun (Fin d) ℝ).map
      (Unitary.linearIsometryEquiv U)).sum_sq_inner_left
      (g ((U : H →L[ℝ] H) (e i)))
    simp only [OrthonormalBasis.map_apply, EuclideanSpace.basisFun_apply] at h
    have he (v : H) : (Unitary.linearIsometryEquiv U) v = (U : H →L[ℝ] H) v := rfl
    simp_rw [he] at h
    change (∑ k : Fin d, F k U) = _ at h
    exact h
  have h := integral_finsetSum Finset.univ (fun k _ => hint k)
  simp_rw [hsum] at h
  rw [Finset.sum_congr rfl (fun k _ => heq k)] at h
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  have hr := rotation_sphere_integral H (f := fun x => ‖g x‖ ^ 2)
    (by fun_prop) (x := e i) (by simp)
  have hn : 0 ≤ ∫ U, F i U ∂rotationMeasure H :=
    integral_nonneg (fun U => sq_nonneg _)
  dsimp [F] at h hn
  linarith only [h, hr, hn]

end Coordinates

end LongTails.Proofs.SphereRotationMeasure
