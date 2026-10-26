import LongTails.Setups.LinearPredictorBFGS
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Matrix

namespace LongTails.Proofs.BFGSMatrix

open LongTails.Setups.LinearPredictorBFGS

variable {d : ℕ}

lemma vecMulVec_mulVec' (u w v : Fin d → ℝ) : vecMulVec u w *ᵥ v = (w ⬝ᵥ v) • u := by
  ext i
  simp [vecMulVec, mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

lemma symm_dot {B : Matrix (Fin d) (Fin d) ℝ} (hB : Bᵀ = B) (u v : Fin d → ℝ) :
    (B *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (B *ᵥ v) := by
  have hBij : ∀ i j, B j i = B i j := fun i j => by rw [← transpose_apply B i j, hB]
  simp only [dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hBij j i]
  ring

lemma upd_mulVec (B : Matrix (Fin d) (Fin d) ℝ) (s y v : Fin d → ℝ) :
    bfgsUpdate B s y *ᵥ v =
      B *ᵥ v - (((B *ᵥ s) ⬝ᵥ v) / (s ⬝ᵥ (B *ᵥ s))) • (B *ᵥ s) + ((y ⬝ᵥ v) / (y ⬝ᵥ s)) • y := by
  rw [bfgsUpdate, add_mulVec, sub_mulVec, smul_mulVec, smul_mulVec, vecMulVec_mulVec',
    vecMulVec_mulVec', smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]

lemma upd_quad {B : Matrix (Fin d) (Fin d) ℝ} (s y v : Fin d → ℝ) :
    v ⬝ᵥ (bfgsUpdate B s y *ᵥ v) =
      v ⬝ᵥ (B *ᵥ v) - ((B *ᵥ s) ⬝ᵥ v) ^ 2 / (s ⬝ᵥ (B *ᵥ s)) + (y ⬝ᵥ v) ^ 2 / (y ⬝ᵥ s) := by
  rw [upd_mulVec, dotProduct_add, dotProduct_sub, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, dotProduct_comm v (B *ᵥ s), dotProduct_comm v y]
  ring

lemma upd_transpose {B : Matrix (Fin d) (Fin d) ℝ} (hB : Bᵀ = B) (s y : Fin d → ℝ) :
    (bfgsUpdate B s y)ᵀ = bfgsUpdate B s y := by
  rw [bfgsUpdate, transpose_add, transpose_sub, transpose_smul, transpose_smul,
    transpose_vecMulVec, transpose_vecMulVec, hB]

lemma upd_decomp {B : Matrix (Fin d) (Fin d) ℝ} (hB : Bᵀ = B) (s y v : Fin d → ℝ)
    (hs : s ⬝ᵥ (B *ᵥ s) ≠ 0) :
    v ⬝ᵥ (bfgsUpdate B s y *ᵥ v) =
      (v - (((B *ᵥ s) ⬝ᵥ v) / (s ⬝ᵥ (B *ᵥ s))) • s) ⬝ᵥ
          (B *ᵥ (v - (((B *ᵥ s) ⬝ᵥ v) / (s ⬝ᵥ (B *ᵥ s))) • s))
        + (y ⬝ᵥ v) ^ 2 / (y ⬝ᵥ s) := by
  rw [upd_quad]
  set t := ((B *ᵥ s) ⬝ᵥ v) / (s ⬝ᵥ (B *ᵥ s))
  have h1 : (B *ᵥ s) ⬝ᵥ v = s ⬝ᵥ (B *ᵥ v) := symm_dot hB s v
  rw [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
    smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, ← h1]
  have ht : t * (s ⬝ᵥ (B *ᵥ s)) = (B *ᵥ s) ⬝ᵥ v := by
    simp only [t]
    field_simp
  have h2 : v ⬝ᵥ (B *ᵥ s) = (B *ᵥ s) ⬝ᵥ v := dotProduct_comm _ _
  rw [h2]
  have e : ((B *ᵥ s) ⬝ᵥ v) ^ 2 / (s ⬝ᵥ (B *ᵥ s)) = t * ((B *ᵥ s) ⬝ᵥ v) := by
    simp only [t]
    field_simp
  rw [e, ← ht]
  ring

lemma upd_posDef {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) {s y : Fin d → ℝ}
    (hs : s ≠ 0) (hys : 0 < y ⬝ᵥ s) : (bfgsUpdate B s y).PosDef := by
  have hBt : Bᵀ = B := by
    have h := hB.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  have hsB : 0 < s ⬝ᵥ (B *ᵥ s) := by
    simpa using hB.dotProduct_mulVec_pos hs
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact upd_transpose hBt s y
  · simp only [star_trivial]
    rw [upd_decomp hBt s y v hsB.ne']
    set t := ((B *ᵥ s) ⬝ᵥ v) / (s ⬝ᵥ (B *ᵥ s))
    have hq : 0 ≤ (v - t • s) ⬝ᵥ (B *ᵥ (v - t • s)) := by
      simpa using hB.posSemidef.dotProduct_mulVec_nonneg (v - t • s)
    have hy : 0 ≤ (y ⬝ᵥ v) ^ 2 / (y ⬝ᵥ s) := div_nonneg (sq_nonneg _) hys.le
    rcases lt_or_eq_of_le hq with hq | hq
    · linarith
    · have hw : v - t • s = 0 := by
        by_contra hw
        have := hB.dotProduct_mulVec_pos hw
        simp only [star_trivial] at this
        linarith
      have hv' : v = t • s := sub_eq_zero.mp hw
      have ht0 : t ≠ 0 := by
        rintro h0
        apply hv
        rw [hv', h0, zero_smul]
      have hyv : y ⬝ᵥ v = t * (y ⬝ᵥ s) := by
        rw [hv', dotProduct_smul, smul_eq_mul]
      rw [← hq, zero_add, hyv]
      have : 0 < (t * (y ⬝ᵥ s)) ^ 2 := by positivity
      exact div_pos this hys

lemma trace_vecMulVec' (u w : Fin d → ℝ) : trace (vecMulVec u w) = u ⬝ᵥ w := by
  simp [trace, vecMulVec, dotProduct]

lemma upd_trace (B : Matrix (Fin d) (Fin d) ℝ) (s y : Fin d → ℝ) :
    trace (bfgsUpdate B s y) =
      trace B - ((B *ᵥ s) ⬝ᵥ (B *ᵥ s)) / (s ⬝ᵥ (B *ᵥ s)) + (y ⬝ᵥ y) / (y ⬝ᵥ s) := by
  rw [bfgsUpdate, trace_add, trace_sub, trace_smul, trace_smul, trace_vecMulVec',
    trace_vecMulVec', smul_eq_mul, smul_eq_mul, div_eq_inv_mul, div_eq_inv_mul]

lemma upd_trace_le {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) {s y : Fin d → ℝ}
    (hs : s ≠ 0) :
    trace (bfgsUpdate B s y) ≤ trace B + (y ⬝ᵥ y) / (y ⬝ᵥ s) := by
  rw [upd_trace]
  have hsB : 0 < s ⬝ᵥ (B *ᵥ s) := by
    simpa using hB.dotProduct_mulVec_pos hs
  have : 0 ≤ ((B *ᵥ s) ⬝ᵥ (B *ᵥ s)) / (s ⬝ᵥ (B *ᵥ s)) := by
    apply div_nonneg _ hsB.le
    simp only [dotProduct, ← sq]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

lemma upd_distance {B : Matrix (Fin d) (Fin d) ℝ} (hB : Bᵀ = B) (s y e : Fin d → ℝ)
    (hs : s ⬝ᵥ (B *ᵥ s) ≠ 0) :
    (e + s) ⬝ᵥ (bfgsUpdate B s y *ᵥ (e + s)) =
      e ⬝ᵥ (B *ᵥ e) - (s ⬝ᵥ (B *ᵥ e)) ^ 2 / (s ⬝ᵥ (B *ᵥ s)) + (y ⬝ᵥ (e + s)) ^ 2 / (y ⬝ᵥ s) := by
  rw [upd_quad]
  have h1 : (B *ᵥ s) ⬝ᵥ (e + s) = s ⬝ᵥ (B *ᵥ e) + s ⬝ᵥ (B *ᵥ s) := by
    rw [dotProduct_add, symm_dot hB s e, symm_dot hB s s]
  have hes : e ⬝ᵥ (B *ᵥ s) = s ⬝ᵥ (B *ᵥ e) := by
    rw [← symm_dot hB s e, dotProduct_comm]
  have h2 : (e + s) ⬝ᵥ (B *ᵥ (e + s)) =
      e ⬝ᵥ (B *ᵥ e) + 2 * (s ⬝ᵥ (B *ᵥ e)) + s ⬝ᵥ (B *ᵥ s) := by
    rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hes]
    ring
  rw [h1, h2]
  field_simp
  ring

lemma mulVec_inv_mulVec {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (g : Fin d → ℝ) :
    B *ᵥ (B⁻¹ *ᵥ g) = g := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det B).mp hB.isUnit), one_mulVec]

lemma upd_det {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) {s y : Fin d → ℝ}
    (hs : s ≠ 0) (hys : 0 < y ⬝ᵥ s) :
    det (bfgsUpdate B s y) = det B * ((y ⬝ᵥ s) / (s ⬝ᵥ (B *ᵥ s))) := by
  have hBt : Bᵀ = B := by
    have h := hB.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  have hsB : 0 < s ⬝ᵥ (B *ᵥ s) := by
    simpa using hB.dotProduct_mulVec_pos hs
  have hu : IsUnit B.det := (isUnit_iff_isUnit_det B).mp hB.isUnit
  set a := (s ⬝ᵥ (B *ᵥ s))⁻¹
  set b := (y ⬝ᵥ s)⁻¹
  set w := B⁻¹ *ᵥ y
  let U : Matrix (Fin d) (Fin 2) ℝ := Matrix.of fun i j => if j = 0 then s i else w i
  let V : Matrix (Fin 2) (Fin d) ℝ := Matrix.of fun i j => if i = 0 then -a * (B *ᵥ s) j else b * y j
  have hfac : bfgsUpdate B s y = B * (1 + U * V) := by
    have hBw : B *ᵥ w = y := mulVec_inv_mulVec hB y
    ext i j
    simp only [bfgsUpdate, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
      smul_eq_mul, Matrix.mul_add, Matrix.mul_one]
    have hrow : ∀ k, (U * V) k j = s k * (-a * (B *ᵥ s) j) + w k * (b * y j) := by
      intro k
      simp [U, V, Matrix.mul_apply, Fin.sum_univ_two]
    have hBUV : (B * (U * V)) i j = (B *ᵥ s) i * (-a * (B *ᵥ s) j) + (B *ᵥ w) i * (b * y j) := by
      simp only [Matrix.mul_apply, hrow, mulVec, dotProduct, Finset.sum_add_distrib,
        Finset.sum_mul, mul_add]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by ring
      · exact Finset.sum_congr rfl fun k _ => by ring
    rw [hBUV, hBw]
    ring
  have h2 : det (1 + V * U) = (y ⬝ᵥ s) / (s ⬝ᵥ (B *ᵥ s)) := by
    have hBw : B *ᵥ w = y := mulVec_inv_mulVec hB y
    have e00 : (V * U) 0 0 = -1 := by
      simp only [U, V, Matrix.mul_apply, Matrix.of_apply, ite_true]
      have : (∑ k, -a * (B *ᵥ s) k * s k) = -a * (s ⬝ᵥ (B *ᵥ s)) := by
        rw [dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this]
      simp only [a]
      field_simp
    have e01 : (V * U) 0 1 = -a * (s ⬝ᵥ y) := by
      simp only [U, V, Matrix.mul_apply, Matrix.of_apply, ite_true, one_ne_zero,
        ite_false]
      have hsym : (B *ᵥ s) ⬝ᵥ w = s ⬝ᵥ y := by
        rw [symm_dot hBt, hBw]
      rw [← hsym, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp; ring
    have e10 : (V * U) 1 0 = 1 := by
      simp only [U, V, Matrix.mul_apply, Matrix.of_apply, ite_true, one_ne_zero,
        ite_false]
      have : (∑ k, b * y k * s k) = b * (y ⬝ᵥ s) := by
        rw [dotProduct, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this]
      simp only [b]
      field_simp
    rw [det_fin_two, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, e00,
      e01, e10]
    simp only [Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
    simp only [a]
    rw [dotProduct_comm s y]
    field_simp
    ring
  rw [hfac, det_mul, det_one_add_mul_comm, h2]

lemma log_det_le {B : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) {c : ℝ} (hc : 0 < c) :
    Real.log (det B) ≤ d * Real.log c + trace B / c - d := by
  have hH := hB.isHermitian
  rw [hH.det_eq_prod_eigenvalues, hH.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  have hpos : ∀ i, 0 < hH.eigenvalues i := hB.eigenvalues_pos
  rw [Real.log_prod (fun i _ => (hpos i).ne')]
  have hlog : ∀ i, Real.log (hH.eigenvalues i) ≤ Real.log c + hH.eigenvalues i / c - 1 := by
    intro i
    have h1 := Real.log_le_sub_one_of_pos (div_pos (hpos i) hc)
    rw [Real.log_div (hpos i).ne' hc.ne'] at h1
    linarith
  calc ∑ i, Real.log (hH.eigenvalues i)
      ≤ ∑ i : Fin d, (Real.log c + hH.eigenvalues i / c - 1) := Finset.sum_le_sum fun i _ => hlog i
    _ = d * Real.log c + (∑ i, hH.eigenvalues i) / c - d := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_div]
      simp

end LongTails.Proofs.BFGSMatrix
