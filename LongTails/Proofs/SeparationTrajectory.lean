import LongTails.Proofs.SeparationModel

namespace LongTails.Proofs.SeparationTrajectory

open MeasureTheory ProbabilityTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.BatchedDirection
open LongTails.Proofs.DiagonalSpectral LongTails.Proofs.SeparationInstance
open LongTails.Proofs.SeparationModel LongTails.Proofs.GaussianBlocks
open LongTails.Proofs.BatchedDirectionExecution

variable {m n : ℕ}

lemma sum_stiff_split {r : ℕ} (hr : 0 < r) (A C : ℝ) :
    (∑ i : Fin r, if i.val = 0 then A else C) = A + (r - 1 : ℕ) * C := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [Fin.sum_univ_succ]
  simp [Finset.sum_const, Finset.card_univ]

lemma norm_sq_diagMat (a : Fin (min m n) → ℝ) : ‖diagMat a‖ ^ 2 = ∑ i, a i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_diagMat]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagMat_apply_dg]
  ring

noncomputable def sgdScalar (ℓ c s η : ℝ) (φ : FlatShape) (B : ℕ) (ξ : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | t + 1 =>
      let p := sgdScalar ℓ c s η φ B ξ t
      (p.1 - η * (ℓ * p.1 + s * blockMean B t ξ), p.2 - η * (c * φ.slope p.2))

noncomputable def nsgdScalar (r : ℕ) (ℓ c s η : ℝ) (φ : FlatShape) (B : ℕ) (ξ : ℕ → ℝ) :
    ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | t + 1 =>
      let p := nsgdScalar r ℓ c s η φ B ξ t
      let a := ℓ * p.1 + s * blockMean B t ξ
      let N := Real.sqrt (a ^ 2 + (r - 1 : ℕ) * (c * φ.slope p.2) ^ 2)
      (p.1 - η * (a / N), p.2 - η * (c * φ.slope p.2 / N))

lemma batch_mean_sample (ℓ c s : ℝ) (φ : FlatShape) (x0 X : Space m n) {B : ℕ} (hB : 0 < B)
    (t : ℕ) (ξ : ℕ → ℝ) :
    (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, sample ℓ c s φ x0 X (ξ (B * t + j)) =
      diagMat (coefficients ℓ c φ (offset x0 X) + noiseVec (s * blockMean B t ξ)) := by
  simp_rw [sample_eq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    ← Finset.sum_smul, smul_add, diagMat_add, gradient_objective]
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  rw [noiseVec_smul, diagMat_smul, smul_smul]
  congr 1
  · rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div, inv_mul_cancel₀ hb, one_smul]
  · simp only [blockMean, Finset.mul_sum]
    ring_nf
    conv_rhs => rw [noiseVec_smul]
    rw [diagMat_smul, one_smul]

lemma offset_sub_smul (x0 X : Space m n) (η : ℝ) (a : Fin (min m n) → ℝ) (i : Fin (min m n)) :
    offset x0 (X - η • diagMat a) i = offset x0 X i - η * a i := by
  simp only [offset, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, diagMat_apply_dg]
  ring

lemma sgd_reduction (ℓ c s η : ℝ) (φ : FlatShape) (x0 : Space m n) {B : ℕ} (hB : 0 < B)
    (ξ : ℕ → ℝ) (t : ℕ) (i : Fin (min m n)) :
    offset x0 (sampledIterate id η B x0 (sample ℓ c s φ x0) ξ t) i =
      if stiff i then (sgdScalar ℓ c s η φ B ξ t).1 else (sgdScalar ℓ c s η φ B ξ t).2 := by
  induction t generalizing i with
  | zero => simp [sampledIterate, offset, sgdScalar]
  | succ t ih =>
      simp only [sampledIterate, id]
      rw [batch_mean_sample ℓ c s φ x0 _ hB, offset_sub_smul, ih i]
      simp only [Pi.add_apply, coefficients, noiseVec, ih i]
      by_cases hi : stiff i
      · simp [hi, sgdScalar]
      · simp [hi, sgdScalar]

lemma nsgd_reduction (ℓ c s η : ℝ) (φ : FlatShape) (x0 : Space m n) (hr : 0 < min m n)
    {B : ℕ} (hB : 0 < B) (ξ : ℕ → ℝ) (t : ℕ) (i : Fin (min m n)) :
    offset x0 (sampledIterate frobeniusNormalize η B x0 (sample ℓ c s φ x0) ξ t) i =
      if stiff i then (nsgdScalar (min m n) ℓ c s η φ B ξ t).1
      else (nsgdScalar (min m n) ℓ c s η φ B ξ t).2 := by
  induction t generalizing i with
  | zero => simp [sampledIterate, offset, nsgdScalar]
  | succ t ih =>
      simp only [sampledIterate]
      rw [batch_mean_sample ℓ c s φ x0 _ hB]
      set v := coefficients ℓ c φ (offset x0 (sampledIterate frobeniusNormalize η B x0
        (sample ℓ c s φ x0) ξ t)) + noiseVec (s * blockMean B t ξ)
      have hv : v = fun j => if stiff j then
          ℓ * (nsgdScalar (min m n) ℓ c s η φ B ξ t).1 + s * blockMean B t ξ
        else c * φ.slope (nsgdScalar (min m n) ℓ c s η φ B ξ t).2 := by
        funext j
        simp only [v, Pi.add_apply, coefficients, noiseVec, ih j]
        by_cases hj : stiff j <;> simp [hj]
      have hnorm : ‖diagMat v‖ = Real.sqrt ((ℓ * (nsgdScalar (min m n) ℓ c s η φ B ξ t).1 +
          s * blockMean B t ξ) ^ 2 + (min m n - 1 : ℕ) *
            (c * φ.slope (nsgdScalar (min m n) ℓ c s η φ B ξ t).2) ^ 2) := by
        rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_diagMat, hv]
        congr 1
        rw [← sum_stiff_split hr]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : stiff j <;> simp [stiff] at * <;> simp_all
      have hdir : frobeniusNormalize (diagMat v) = diagMat (‖diagMat v‖⁻¹ • v) := by
        rw [frobeniusNormalize, diagMat_smul]
      rw [hdir, offset_sub_smul, ih i, hnorm]
      simp only [Pi.smul_apply, smul_eq_mul, hv]
      by_cases hi : stiff i
      · simp only [hi, ↓reduceIte, nsgdScalar]
        ring
      · simp only [hi, ↓reduceIte, nsgdScalar]
        ring

lemma nuclear_scalar (ℓ c : ℝ) (φ : FlatShape) (x0 X : Space m n) (hr : 0 < min m n)
    (x y : ℝ) (hX : ∀ i, offset x0 X i = if stiff i then x else y) :
    nuclearNorm (gradient (objective ℓ c φ x0) X) =
      |ℓ * x| + (min m n - 1 : ℕ) * |c * φ.slope y| := by
  rw [nuclear_gradient_objective, ← sum_stiff_split hr]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coefficients, hX i]
  by_cases hi : stiff i <;> simp [stiff] at * <;> simp_all

end LongTails.Proofs.SeparationTrajectory
