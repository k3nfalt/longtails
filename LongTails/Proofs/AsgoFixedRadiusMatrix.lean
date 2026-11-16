import LongTails.Setups.AsgoFixedRadius
import LongTails.Proofs.MuonMatrix
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace OracleTemplate.AsgoFixedRadius

open LongTails.Setups.AsgoFixedRadius

lemma trace_cyclic {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (A * B).trace = (B * A).trace := by
  exact Matrix.trace_mul_comm A B

lemma trace_transpose {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    (Aᵀ).trace = A.trace := by
  rfl

lemma trace_mul_nonneg {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  let S := CFC.sqrt A
  have hS : S.PosSemidef := (CFC.sqrt_nonneg A).posSemidef
  have hs : S * S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have ht := (hB.conjTranspose_mul_mul_same S).trace_nonneg
  rw [hS.isHermitian.eq, Matrix.trace_mul_cycle, hs] at ht
  exact ht

lemma quadratic_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (X : Muon.Mat m n)
    (hA : A.PosSemidef) :
    0 ≤ Core.weightedQuadratic A X := by
  open Matrix in
  open scoped BigOperators in
  (
    change 0 ≤ ((Muon.toMatrix X)ᵀ * A * Muon.toMatrix X).trace
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hA.conjTranspose_mul_mul_same (Muon.toMatrix X)).trace_nonneg
  )

lemma inner_trace {m n : ℕ} (X Y : Muon.Mat m n) :
    inner ℝ X Y = ((Muon.toMatrix X)ᵀ * Muon.toMatrix Y).trace := by
  open Matrix in
  open scoped BigOperators in
  (
    exact Muon.inner_mat_trace X Y
  )

lemma trace_eq_nuclear {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) :
    A.trace = Muon.nuclearNorm (Muon.ofMatrix A) := by
  open Matrix in
  open scoped BigOperators in
  (
    classical
    have hs : CFC.sqrt (Aᴴ * A) = A := by
      rw [hA.isHermitian.eq, CFC.sqrt_mul_self A hA.nonneg]
    calc
      A.trace = (CFC.sqrt (Aᴴ * A)).trace := congrArg Matrix.trace hs.symm
      _ = ∑ i, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) := by
        rw [CFC.sqrt_eq_cfc,
          cfc_nnreal_eq_real _ _ (Matrix.posSemidef_conjTranspose_mul_self A).nonneg,
          (Matrix.isHermitian_conjTranspose_mul_self A).cfc_eq, Matrix.IsHermitian.cfc,
          Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
          Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
        simp only [Function.comp_apply, Real.coe_sqrt, Real.coe_toNNReal']
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [max_eq_left ((Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg i)]
        rfl
      _ = Muon.nuclearNorm (Muon.ofMatrix A) := rfl
  )

lemma spectral_gram_iff {m n : ℕ} (X : Muon.Mat m n) (R : ℝ) (hR : 0 < R) :
    Muon.spectralNorm X ≤ R ↔
      Core.loewner (Core.gram X) (R ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  open Matrix in
  open scoped BigOperators in
  (
    classical
    let U := Muon.toMatrix X
    have hn : ‖Uᵀ‖ = Muon.spectralNorm X := by
      calc
        ‖Uᵀ‖ = ‖U‖ := by
          simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
            Matrix.l2_opNorm_conjTranspose U
        _ = Muon.spectralNorm X := by
          rw [Matrix.l2_opNorm_def]
          rfl
    have hg : (Core.gram X).PosSemidef := by
      change (Muon.toMatrix X * (Muon.toMatrix X)ᵀ).PosSemidef
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose (Muon.toMatrix X)
    have hI : (R ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef :=
      Matrix.PosSemidef.one.smul (sq_nonneg R)
    have hq (u : Fin m → ℝ) :
        u ⬝ᵥ (Core.gram X *ᵥ u) = (Uᵀ *ᵥ u) ⬝ᵥ (Uᵀ *ᵥ u) := by
      change u ⬝ᵥ ((U * Uᵀ) *ᵥ u) = (Uᵀ *ᵥ u) ⬝ᵥ (Uᵀ *ᵥ u)
      simpa only [Matrix.transpose_transpose, Matrix.mulVec_mulVec] using
        Matrix.dotProduct_transpose_mulVec Uᵀ u (Uᵀ *ᵥ u)
    have hd (u : Fin m → ℝ) :
        u ⬝ᵥ ((R ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - Core.gram X) *ᵥ u) =
          R ^ 2 * (u ⬝ᵥ u) - (Uᵀ *ᵥ u) ⬝ᵥ (Uᵀ *ᵥ u) := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_smul, smul_eq_mul, hq]
    constructor
    · intro h
      change (R ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - Core.gram X).PosSemidef
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
        (hI.isHermitian.sub hg.isHermitian) (fun u => ?_)
      rw [star_trivial, hd]
      apply sub_nonneg.mpr
      have hb := Muon.mulVec_dot_le Uᵀ u
      change (Uᵀ *ᵥ u) ⬝ᵥ (Uᵀ *ᵥ u) ≤ ‖Uᵀ‖ ^ 2 * (u ⬝ᵥ u) at hb
      have hu : 0 ≤ u ⬝ᵥ u := by
        rw [← Muon.norm_toLp_sq u]
        positivity
      have hnorm : ‖Uᵀ‖ ≤ R := hn.trans_le h
      exact hb.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hu)
    · intro h
      change (R ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ) - Core.gram X).PosSemidef at h
      rw [← hn]
      change ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Uᵀ)‖ ≤ R
      refine ContinuousLinearMap.opNorm_le_bound _ hR.le (fun u => ?_)
      change ‖(WithLp.toLp 2 (Uᵀ *ᵥ u.ofLp) : EuclideanSpace ℝ (Fin n))‖ ≤ R * ‖u‖
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hR.le (norm_nonneg u))
        two_ne_zero).mp ?_
      rw [Muon.norm_toLp_sq, mul_pow]
      have hu : ‖u‖ ^ 2 = u.ofLp ⬝ᵥ u.ofLp := Muon.norm_toLp_sq u.ofLp
      rw [hu]
      have hh := h.dotProduct_mulVec_nonneg u.ofLp
      rw [star_trivial, hd] at hh
      linarith
  )

lemma root_psd {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    (Core.matrixRoot A).PosSemidef := by
  open Matrix in
  open scoped BigOperators in
  (
    exact (CFC.sqrt_nonneg A).posSemidef
  )

lemma root_square {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosSemidef) :
    Core.matrixRoot A * Core.matrixRoot A = A ∧
      Core.matrixRoot A * A = A * Core.matrixRoot A := by
  open Matrix in
  open scoped BigOperators in
  (
    have h : Core.matrixRoot A * Core.matrixRoot A = A :=
      CFC.sqrt_mul_sqrt_self A hA.nonneg
    refine ⟨h, ?_⟩
    calc
      Core.matrixRoot A * A = Core.matrixRoot A * (Core.matrixRoot A * Core.matrixRoot A) :=
        congrArg (fun M => Core.matrixRoot A * M) h.symm
      _ = (Core.matrixRoot A * Core.matrixRoot A) * Core.matrixRoot A :=
        (Matrix.mul_assoc _ _ _).symm
      _ = A * Core.matrixRoot A := congrArg (fun M => M * Core.matrixRoot A) h
  )

lemma root_mono {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.PosSemidef) (hAB : Core.loewner A B) :
    Core.loewner (Core.matrixRoot A) (Core.matrixRoot B) := by
  open Matrix in
  open scoped BigOperators in
  (
    classical
    change (B - A).PosSemidef at hAB
    have hB : B.PosSemidef := by
      have hh := hA.add hAB
      rw [← add_sub_assoc, add_sub_cancel_left] at hh
      exact hh
    let S := Core.matrixRoot B
    let P := Core.matrixRoot A
    have hS : S.PosSemidef := root_psd B
    have hP : P.PosSemidef := root_psd A
    have hST : Sᵀ = S := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
    have hPT : Pᵀ = P := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hP.isHermitian.eq
    have hSq : S * S = B := (root_square B hB).1
    have hPq : P * P = A := (root_square A hA).1
    have hD : (S - P).IsHermitian := hS.isHermitian.sub hP.isHermitian
    change (S - P).PosSemidef
    apply hD.posSemidef_iff_eigenvalues_nonneg.mpr
    intro i
    let u : Fin m → ℝ := (hD.eigenvectorBasis i).ofLp
    let l : ℝ := hD.eigenvalues i
    have hu : u ⬝ᵥ u = 1 := by
      rw [← Muon.norm_toLp_sq u]
      change ‖hD.eigenvectorBasis i‖ ^ 2 = 1
      rw [hD.eigenvectorBasis.orthonormal.1 i]
      norm_num
    have he : S *ᵥ u - P *ᵥ u = l • u := by
      simpa only [Matrix.sub_mulVec, u, l] using hD.mulVec_eigenvectorBasis i
    have hs0 : 0 ≤ u ⬝ᵥ (S *ᵥ u) := by
      simpa only [star_trivial] using hS.dotProduct_mulVec_nonneg u
    have hp0 : 0 ≤ u ⬝ᵥ (P *ᵥ u) := by
      simpa only [star_trivial] using hP.dotProduct_mulVec_nonneg u
    have hd : u ⬝ᵥ (S *ᵥ u) - u ⬝ᵥ (P *ᵥ u) = l := by
      have hh := congrArg (fun v : Fin m → ℝ => u ⬝ᵥ v) he
      simpa only [dotProduct_sub, dotProduct_smul, smul_eq_mul, hu, mul_one] using hh
    have hsq : u ⬝ᵥ ((S * S) *ᵥ u) = (S *ᵥ u) ⬝ᵥ (S *ᵥ u) := by
      simpa only [hST, Matrix.mulVec_mulVec] using
        Matrix.dotProduct_transpose_mulVec S u (S *ᵥ u)
    have hpq : u ⬝ᵥ ((P * P) *ᵥ u) = (P *ᵥ u) ⬝ᵥ (P *ᵥ u) := by
      simpa only [hPT, Matrix.mulVec_mulVec] using
        Matrix.dotProduct_transpose_mulVec P u (P *ᵥ u)
    have hc : (S *ᵥ u) ⬝ᵥ (S *ᵥ u) - (P *ᵥ u) ⬝ᵥ (P *ᵥ u) =
        l * (u ⬝ᵥ (S *ᵥ u) + u ⬝ᵥ (P *ᵥ u)) := by
      have hh := congrArg (fun v : Fin m → ℝ => v ⬝ᵥ (S *ᵥ u + P *ᵥ u)) he
      simp only [sub_dotProduct, dotProduct_add, smul_dotProduct, smul_eq_mul] at hh
      have hsym := dotProduct_comm (S *ᵥ u) (P *ᵥ u)
      nlinarith
    have hn := hAB.dotProduct_mulVec_nonneg u
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, ← hSq, ← hPq, hsq, hpq, hc] at hn
    change 0 ≤ l
    by_contra hnot
    have hl : l < 0 := lt_of_not_ge hnot
    have hsum : 0 < u ⬝ᵥ (S *ᵥ u) + u ⬝ᵥ (P *ᵥ u) := by nlinarith
    have hneg := mul_neg_of_neg_of_pos hl hsum
    linarith
  )

lemma root_measurable {m : ℕ} :
    ContinuousOn (Core.matrixRoot (m := m)) {A | A.PosSemidef} ∧
      Measurable (Core.matrixRoot (m := m)) := by
  open Matrix in
  open scoped BigOperators in
  (
    constructor
    · convert! (CFC.continuousOn_sqrt (A := Matrix (Fin m) (Fin m) ℝ)) using 1
      simp only [Matrix.nonneg_iff_posSemidef]
    · exact CFC.measurable_sqrt
  )

lemma inverse_posDef {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef) :
    (A⁻¹).PosDef ∧ A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 := by
  open Matrix in
  open scoped BigOperators in
  (
    have hd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit
    exact ⟨hA.inv, Matrix.mul_nonsing_inv A hd, Matrix.nonsing_inv_mul A hd⟩
  )

lemma inverse_measurable {m : ℕ} :
    ContinuousOn (fun A : Matrix (Fin m) (Fin m) ℝ => A⁻¹) {A | A.PosDef} ∧
      Measurable (fun A : Matrix (Fin m) (Fin m) ℝ => A⁻¹) := by
  open Matrix in
  open scoped BigOperators in
  (
    constructor
    · intro A hA
      apply (continuousAt_matrix_inv A ?_).continuousWithinAt
      have hi : (Ring.inverse : ℝ → ℝ) = fun x => x⁻¹ := funext Ring.inverse_eq_inv
      rw [hi]
      exact continuousAt_id.inv₀ (ne_of_gt hA.det_pos)
    · have hd : Measurable (fun A : Matrix (Fin m) (Fin m) ℝ => A.det⁻¹) :=
        continuous_id.matrix_det.measurable.inv
      have ha : Measurable (fun A : Matrix (Fin m) (Fin m) ℝ => A.adjugate) :=
        continuous_id.matrix_adjugate.measurable
      convert hd.smul ha using 1
      funext A
      exact Matrix.inv_def A |>.trans (congrArg (fun c : ℝ => c • A.adjugate) (Ring.inverse_eq_inv _))
  )

lemma inverse_order {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.PosDef) (hB : B.PosDef) (hBA : Core.loewner B A) :
    Core.loewner A⁻¹ B⁻¹ := by
  open Matrix in
  open scoped BigOperators in
  (
    classical
    obtain ⟨hAi, hAAi, hAiA⟩ := inverse_posDef A hA
    obtain ⟨hBi, hBBi, hBiB⟩ := inverse_posDef B hB
    have hAT : (A⁻¹)ᵀ = A⁻¹ := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hAi.isHermitian.eq
    have hDT : (B⁻¹ - A⁻¹)ᵀ = B⁻¹ - A⁻¹ := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        (hBi.isHermitian.sub hAi.isHermitian).eq
    have h1 := hBA.conjTranspose_mul_mul_same A⁻¹
    have h2 := hB.posSemidef.conjTranspose_mul_mul_same (B⁻¹ - A⁻¹)
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, hAT] at h1
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial, hDT] at h2
    have he : A⁻¹ * (A-B) * A⁻¹ + (B⁻¹-A⁻¹) * B * (B⁻¹-A⁻¹) = B⁻¹ - A⁻¹ := by
      calc
        _ = A⁻¹ * A * A⁻¹ - A⁻¹ * B * A⁻¹ +
            B⁻¹ * B * B⁻¹ - B⁻¹ * B * A⁻¹ - A⁻¹ * (B * B⁻¹) + A⁻¹ * B * A⁻¹ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
          module
        _ = _ := by
          rw [hAiA, hBiB, hBBi]
          simp only [one_mul, mul_one]
          module
    change (B⁻¹ - A⁻¹).PosSemidef
    rw [← he]
    exact h1.add h2
  )

lemma inverse_quadratic_order {m n : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (X : Muon.Mat m n)
    (hA : A.PosDef) (hB : B.PosDef) (hBA : Core.loewner B A) :
    Core.weightedQuadratic A⁻¹ X ≤ Core.weightedQuadratic B⁻¹ X := by
  open Matrix in
  open scoped BigOperators in
  (
    have h := quadratic_nonneg (B⁻¹ - A⁻¹) X (inverse_order A B hA hB hBA)
    change 0 ≤ ((Muon.toMatrix X)ᵀ*(B⁻¹-A⁻¹)*Muon.toMatrix X).trace at h
    change ((Muon.toMatrix X)ᵀ*A⁻¹*Muon.toMatrix X).trace ≤
      ((Muon.toMatrix X)ᵀ*B⁻¹*Muon.toMatrix X).trace
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub,
      sub_nonneg] using h
  )

lemma weighted_trace_young {m : ℕ} (A Q : Matrix (Fin m) (Fin m) ℝ) (a : ℝ)
    (hA : A.PosDef) (hQ : Q.PosSemidef) :
    a * (Core.matrixRoot Q).trace ≤ (A⁻¹ * Q).trace / 4 + a ^ 2 * A.trace := by
  open Matrix in
  open scoped BigOperators in
  (
    classical
    let S := Core.matrixRoot Q
    have hS : S.PosSemidef := root_psd Q
    have hSq : S*S=Q := (root_square Q hQ).1
    have hST : Sᵀ = S := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
    have hAT : Aᵀ = A := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
    obtain ⟨hAi, hAAi, hAiA⟩ := inverse_posDef A hA
    have h := quadratic_nonneg A⁻¹ (Muon.ofMatrix (S - (2*a) • A)) hAi.posSemidef
    change 0 ≤ ((S - (2*a) • A)ᵀ * A⁻¹ * (S - (2*a) • A)).trace at h
    rw [Matrix.transpose_sub, Matrix.transpose_smul, hST, hAT] at h
    have h1 : (S*A⁻¹*S).trace = (A⁻¹*Q).trace := by
      rw [Matrix.trace_mul_cycle, hSq, Matrix.trace_mul_comm]
    have h2 : (S*A⁻¹*A).trace = S.trace := by
      rw [Matrix.mul_assoc, hAiA, mul_one]
    have h3 : (A*A⁻¹*S).trace = S.trace := by rw [hAAi, one_mul]
    have h4 : (A*A⁻¹*A).trace = A.trace := by rw [hAAi, one_mul]
    simp only [Matrix.sub_mul, Matrix.mul_sub, smul_mul_assoc, mul_smul_comm,
      Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, h1, h2, h3, h4] at h
    change a * S.trace ≤ (A⁻¹ * Q).trace / 4 + a ^ 2 * A.trace
    nlinarith
  )

end OracleTemplate.AsgoFixedRadius
