import LongTails.Proofs.FiniteSumNondualLowerComponents
import LongTails.Proofs.GeneralizedSmoothSmoothedChain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralizedSmoothCoordinateEmbedding

open FiniteSumNondualLowerComponents

lemma projection_single {d m : ℕ} (π : Fin m ↪ Fin d) (j : Fin m) :
    coordinateMap π (EuclideanSpace.single (π j) (1 : ℝ)) = EuclideanSpace.single j 1 := by
  ext i
  simp [coordinateMap, π.injective.eq_iff]

lemma projection_adjoint {d m : ℕ} (π : Fin m ↪ Fin d)
    (z : EuclideanSpace ℝ (Fin m)) : coordinateMap π ((coordinateMap π).adjoint z) = z := by
  ext j
  have h := (coordinateMap π).adjoint_inner_left (EuclideanSpace.single (π j) 1) z
  rw [projection_single] at h
  simpa [EuclideanSpace.inner_single_right, coordinateMap] using h

lemma adjoint_norm {d m : ℕ} (π : Fin m ↪ Fin d) (z : EuclideanSpace ℝ (Fin m)) :
    ‖(coordinateMap π).adjoint z‖ = ‖z‖ := by
  have h := (coordinateMap π).adjoint_inner_left ((coordinateMap π).adjoint z) z
  rw [projection_adjoint, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg ((coordinateMap π).adjoint z), norm_nonneg z]

lemma projection_opNorm {d m : ℕ} (π : Fin m ↪ Fin d) : ‖coordinateMap π‖ ≤ 1 := by
  apply (coordinateMap π).opNorm_le_bound (by norm_num)
  intro x
  simpa using coordinateMap_norm π x

lemma composed_gradient {d m : ℕ} (π : Fin m ↪ Fin d)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hg : ∀ x, HasGradientAt f (g x) x) (x : EuclideanSpace ℝ (Fin d)) :
    HasGradientAt (fun y => f (coordinateMap π y))
      ((coordinateMap π).adjoint (g (coordinateMap π x))) x := by
  have hd := (hg (coordinateMap π x)).hasFDerivAt.comp x (coordinateMap π).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hd using 1
  · rfl
  · ext v
    exact (coordinateMap π).adjoint_inner_left v (g (coordinateMap π x))

lemma composed_curvature {d m : ℕ} (π : Fin m ↪ Fin d)
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hg : Differentiable ℝ g) (L₀ L₁ : ℝ)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L₀ + L₁ * ‖g x‖) (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (fun y => (coordinateMap π).adjoint (g (coordinateMap π y))) x‖ ≤
      L₀ + L₁ * ‖(coordinateMap π).adjoint (g (coordinateMap π x))‖ := by
  let A := coordinateMap π
  have hd := A.adjoint.hasFDerivAt.comp x ((hg (A x)).hasFDerivAt.comp x A.hasFDerivAt)
  change HasFDerivAt (fun y => (coordinateMap π).adjoint (g (coordinateMap π y))) _ x at hd
  rw [hd.fderiv, adjoint_norm]
  have hA := projection_opNorm π
  have hAt : ‖A.adjoint‖ ≤ 1 := by simpa [A] using hA
  have h₁ := ContinuousLinearMap.opNorm_comp_le A.adjoint ((fderiv ℝ g (A x)).comp A)
  have h₂ := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ g (A x)) A
  have h₃ : ‖(fderiv ℝ g (A x)).comp A‖ ≤ ‖fderiv ℝ g (A x)‖ := by
    exact h₂.trans (by simpa using mul_le_mul_of_nonneg_left hA (norm_nonneg (fderiv ℝ g (A x))))
  exact (h₁.trans ((mul_le_mul_of_nonneg_right hAt (norm_nonneg _)).trans (by simpa using h₃))).trans (hH (A x))

lemma adjoint_prefix_eq {d m : ℕ} (π ρ : Fin m ↪ Fin d) (j : ℕ)
    (z : EuclideanSpace ℝ (Fin m)) (hπ : ∀ i, i.val < j → π i = ρ i)
    (hz : ∀ i, j ≤ i.val → z i = 0) :
    (coordinateMap π).adjoint z = (coordinateMap ρ).adjoint z := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < j
  · simp [coordinateMap, hπ i hi]
  · simp [hz i (Nat.le_of_not_gt hi)]

end LongTails.Proofs.GeneralizedSmoothCoordinateEmbedding
