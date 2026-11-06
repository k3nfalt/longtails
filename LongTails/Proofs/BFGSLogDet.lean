import LongTails.Proofs.BFGSLogPotential
import Mathlib.Analysis.Matrix.Order

open Matrix
open scoped MatrixOrder

namespace LongTails.Proofs.BFGSLogDet

open LongTails.Setups.LinearPredictorBFGS LongTails.Proofs.BFGSMatrix
open LongTails.Proofs.BFGSLogPotential

variable {d : ℕ}

lemma one_le_det_one_add {P : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) :
    1 ≤ det (1 + P) := by
  have hH : (1 + P).IsHermitian := (PosSemidef.one.add hP).isHermitian
  rw [hH.det_eq_prod_eigenvalues]
  have hge : ∀ i, 1 ≤ hH.eigenvalues i := by
    intro i
    rw [hH.eigenvalues_eq i]
    have hn : ‖hH.eigenvectorBasis i‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
    have hdot : star ⇑(hH.eigenvectorBasis i) ⬝ᵥ ⇑(hH.eigenvectorBasis i) = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, real_inner_self_eq_norm_sq,
        hn, one_pow]
    have hq := hP.dotProduct_mulVec_nonneg (hH.eigenvectorBasis i)
    rw [add_mulVec, one_mulVec, dotProduct_add, hdot]
    simp only [RCLike.re_to_real]
    linarith
  calc (1 : ℝ) = ∏ _i : Fin d, (1 : ℝ) := by simp
    _ ≤ ∏ i, ((hH.eigenvalues i : ℝ) : ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => by simpa using hge i)

lemma det_le_det_add {A E : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef) (hE : E.PosSemidef) :
    det A ≤ det (A + E) := by
  set R := CFC.sqrt E
  have hR : R.PosSemidef := (CFC.sqrt_nonneg E).posSemidef
  have hRR : R * R = E := CFC.sqrt_mul_sqrt_self E hE.nonneg
  have hu : IsUnit A.det := (isUnit_iff_isUnit_det _).mp hA.isUnit
  have hRh : Rᴴ = R := hR.isHermitian
  have hP : (R * A⁻¹ * R).PosSemidef := by
    have := hA.inv.posSemidef.conjTranspose_mul_mul_same R
    rwa [hRh] at this
  rw [← hRR, det_add_mul R R hu]
  have h1 := one_le_det_one_add hP
  have h0 := hA.det_pos
  nlinarith

def LeQ (A A' : Matrix (Fin d) (Fin d) ℝ) : Prop := ∀ v : Fin d → ℝ, v ⬝ᵥ (A *ᵥ v) ≤ v ⬝ᵥ (A' *ᵥ v)

lemma det_mono {A A' : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef) (hA' : A'ᵀ = A')
    (h : LeQ A A') : det A ≤ det A' := by
  have hAt := posDef_symm hA
  have hE : (A' - A).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub, hA', hAt]
    · simp only [star_trivial, sub_mulVec, dotProduct_sub]
      linarith [h v]
  have := det_le_det_add hA hE
  rwa [add_sub_cancel] at this

lemma inv_anti {A A' : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef) (hA' : A'.PosDef)
    (h : LeQ A A') (g : Fin d → ℝ) :
    g ⬝ᵥ (A'⁻¹ *ᵥ g) ≤ g ⬝ᵥ (A⁻¹ *ᵥ g) := by
  set z := A'⁻¹ *ᵥ g with hz
  set w := A⁻¹ *ᵥ g with hw
  have hA'z : A' *ᵥ z = g := mulVec_inv_mulVec hA' g
  have hAw : A *ᵥ w = g := mulVec_inv_mulVec hA g
  have hAt := posDef_symm hA
  have hzg : g ⬝ᵥ z = z ⬝ᵥ (A' *ᵥ z) := by rw [hA'z, dotProduct_comm]
  have hwg : g ⬝ᵥ w = w ⬝ᵥ (A *ᵥ w) := by rw [hAw, dotProduct_comm]
  have hcs := cs_posDef hA z w
  rw [hAw] at hcs
  have hzz : z ⬝ᵥ (A *ᵥ z) ≤ z ⬝ᵥ (A' *ᵥ z) := h z
  have hz0 : 0 ≤ g ⬝ᵥ z := by rw [hzg]; exact posDef_quad_nonneg hA' z
  have hw0 : 0 ≤ g ⬝ᵥ w := by rw [hwg]; exact posDef_quad_nonneg hA w
  have hzg' : z ⬝ᵥ g = g ⬝ᵥ z := dotProduct_comm _ _
  rw [hzg', dotProduct_comm w g] at hcs
  rw [← hzg] at hzz
  have : (g ⬝ᵥ z) ^ 2 ≤ (g ⬝ᵥ z) * (g ⬝ᵥ w) := by
    calc (g ⬝ᵥ z) ^ 2 ≤ z ⬝ᵥ (A *ᵥ z) * (g ⬝ᵥ w) := hcs
      _ ≤ (g ⬝ᵥ z) * (g ⬝ᵥ w) := mul_le_mul_of_nonneg_right hzz hw0
  nlinarith

lemma det_smul_fin (c : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) : det (c • A) = c ^ d * det A := by
  rw [det_smul, Fintype.card_fin]

lemma leQ_smul_left {A A' : Matrix (Fin d) (Fin d) ℝ} {c : ℝ} (h : ∀ v : Fin d → ℝ,
    v ⬝ᵥ (A *ᵥ v) ≤ c * (v ⬝ᵥ (A' *ᵥ v))) : LeQ A (c • A') := fun v => by
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]; exact h v

end LongTails.Proofs.BFGSLogDet
