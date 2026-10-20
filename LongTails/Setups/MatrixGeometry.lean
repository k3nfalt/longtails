import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.MeasurableSpace

namespace LongTails.Setups.MatrixGeometry

abbrev Space (m n : ℕ) := EuclideanSpace ℝ (Fin m × Fin n)

instance (m n : ℕ) : MeasurableSpace (Space m n) := borel _

instance (m n : ℕ) : BorelSpace (Space m n) := ⟨rfl⟩

noncomputable def matrixEquiv (m n : ℕ) : Space m n ≃ₗ[ℝ] Matrix (Fin m) (Fin n) ℝ where
  toFun X := fun i j => X (i, j)
  invFun M := WithLp.toLp 2 (fun p => M p.1 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv X := by ext p; rfl
  right_inv M := rfl

noncomputable def operatorEquiv (m n : ℕ) :
    Space m n ≃L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
  ((matrixEquiv m n).trans (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap)).toContinuousLinearEquiv

noncomputable def spectralNorm {m n : ℕ} (X : Space m n) : ℝ :=
  ‖operatorEquiv m n X‖

noncomputable def spectralBall (m n : ℕ) : Set (Space m n) :=
  {X | spectralNorm X ≤ 1}

noncomputable def dualMap (m n : ℕ) : Space m n →L[ℝ]
    ((EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (innerSL ℝ X).comp (operatorEquiv m n).symm.toContinuousLinearMap
      map_add' := by
        intro X Y
        ext U
        simp
      map_smul' := by
        intro t X
        ext U
        simp }

noncomputable def nuclearNorm {m n : ℕ} (X : Space m n) : ℝ :=
  ‖(innerSL ℝ X).comp (operatorEquiv m n).symm.toContinuousLinearMap‖

end LongTails.Setups.MatrixGeometry
