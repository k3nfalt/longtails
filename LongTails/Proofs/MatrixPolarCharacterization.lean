import LongTails.Proofs.MatrixPolarGeometry

namespace LongTails.Proofs.MatrixPolarCharacterization

open LongTails.Setups.MatrixGeometry LongTails.Algorithms.MatrixPolar

lemma inner_eq_sum_columns {m n : ℕ} (X Y : Space m n)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    inner ℝ X Y = ∑ i, inner ℝ (operatorEquiv m n Y (b i)) (operatorEquiv m n X (b i)) := by
  rw [inner_eq_trace_pair, ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm',
    ← ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_eq_sum_inner _ b]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

lemma norm_sq_eq_sum_columns {m n : ℕ} (X : Space m n)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n))) :
    ‖X‖ ^ 2 = ∑ i, ‖operatorEquiv m n X (b i)‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_eq_sum_columns X X b

lemma normalized_norm_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E) : ‖‖w‖⁻¹ • w‖ ≤ 1 := by
  by_cases hw : w = 0
  · simp [hw]
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]

lemma normalized_norm_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E) : ‖‖w‖⁻¹ • w‖ ^ 2 ≤ 1 := by
  nlinarith [normalized_norm_le_one w, norm_nonneg (‖w‖⁻¹ • w)]

lemma normalized_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (w : E) : inner ℝ (‖w‖⁻¹ • w) w = ‖w‖ := by
  by_cases hw : w = 0
  · simp [hw]
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp

lemma orthogonal_synthesis_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} (u : Fin n → E) (c : Fin n → ℝ)
    (hu : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0) :
    ‖∑ i, c i • u i‖ ^ 2 = ∑ i, (c i) ^ 2 * ‖u i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq]
    ring
  · intro j _ hji
    rw [hu j i hji]
    ring
  · simp

lemma normalized_synthesis_contracts {m n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (w : Fin n → EuclideanSpace ℝ (Fin m))
    (hw : ∀ i j, i ≠ j → inner ℝ (w i) (w j) = 0)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖∑ i, inner ℝ (b i) z • (‖w i‖⁻¹ • w i)‖ ≤ ‖z‖ := by
  have hu : ∀ i j, i ≠ j →
      inner ℝ (‖w i‖⁻¹ • w i) (‖w j‖⁻¹ • w j) = 0 := by
    intro i j hij
    rw [real_inner_smul_left, real_inner_smul_right, hw i j hij, mul_zero, mul_zero]
  have hs := orthogonal_synthesis_norm_sq (fun i => ‖w i‖⁻¹ • w i)
    (fun i => inner ℝ (b i) z) hu
  have hb : (∑ i, (inner ℝ (b i) z) ^ 2 * ‖‖w i‖⁻¹ • w i‖ ^ 2) ≤
      ∑ i, (inner ℝ (b i) z) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_of_le_one_right (sq_nonneg _) (normalized_norm_sq_le (w i))
  have hz := b.sum_sq_norm_inner_right z
  simp only [Real.norm_eq_abs, sq_abs] at hz
  nlinarith [norm_nonneg z, norm_nonneg (∑ i, inner ℝ (b i) z • (‖w i‖⁻¹ • w i))]

lemma normalized_norm_le_of_support {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (w v : E) (hv : inner ℝ v w = ‖w‖) :
    ‖‖w‖⁻¹ • w‖ ≤ ‖v‖ := by
  by_cases hw : w = 0
  · simp [hw]
  · have hp := norm_pos_iff.mpr hw
    have hc := real_inner_le_norm v w
    rw [hv] at hc
    have h1 : 1 ≤ ‖v‖ := by nlinarith
    exact (normalized_norm_le_one w).trans h1

lemma polar_apply_of_orthogonal_images {m n : ℕ} (X : Space m n)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (horth : ∀ i j, i ≠ j →
      inner ℝ (operatorEquiv m n X (b i)) (operatorEquiv m n X (b j)) = 0) (i : Fin n) :
    operatorEquiv m n (polar X) (b i) =
      ‖operatorEquiv m n X (b i)‖⁻¹ • operatorEquiv m n X (b i) := by
  classical
  let w := fun j => operatorEquiv m n X (b j)
  let A := ∑ j, InnerProductSpace.rankOne ℝ (‖w j‖⁻¹ • w j) (b j)
  let P := (operatorEquiv m n).symm A
  have hA (z : EuclideanSpace ℝ (Fin n)) :
      A z = ∑ j, inner ℝ (b j) z • (‖w j‖⁻¹ • w j) := by
    simp [A, smul_smul, mul_comm]
  have hcol (j : Fin n) : operatorEquiv m n P (b j) = ‖w j‖⁻¹ • w j := by
    simp only [P, ContinuousLinearEquiv.apply_symm_apply, hA, b.inner_eq_ite]
    simp
  have hP : P ∈ spectralBall m n := by
    change ‖operatorEquiv m n P‖ ≤ 1
    simp only [P, ContinuousLinearEquiv.apply_symm_apply]
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa only [hA, one_mul] using normalized_synthesis_contracts b w horth z
  have hpair : inner ℝ X P = ∑ j, ‖w j‖ := by
    rw [inner_eq_sum_columns X P b]
    simp only [hcol, ← show (fun j => operatorEquiv m n X (b j)) = w from rfl,
      normalized_inner]
  have hbound (Y : Space m n) (hY : Y ∈ spectralBall m n) (j : Fin n) :
      inner ℝ (operatorEquiv m n Y (b j)) (w j) ≤ ‖w j‖ := by
    have hn := (operatorEquiv m n Y).le_opNorm (b j)
    have hy : ‖operatorEquiv m n Y‖ ≤ 1 := hY
    simp only [b.norm_eq_one, mul_one] at hn
    have hc := real_inner_le_norm (operatorEquiv m n Y (b j)) (w j)
    nlinarith [norm_nonneg (w j)]
  have hface : P ∈ supportFace (spectralBall m n) (innerSL ℝ X) := by
    refine ⟨hP, ?_⟩
    intro Y hY
    change inner ℝ X Y ≤ inner ℝ X P
    rw [hpair, inner_eq_sum_columns X Y b]
    exact Finset.sum_le_sum (fun j _ => hbound Y hY j)
  have hmin (Y : Space m n) (hY : Y ∈ supportFace (spectralBall m n) (innerSL ℝ X)) :
      ‖P‖ ≤ ‖Y‖ := by
    have hsum : ∑ j, (‖w j‖ - inner ℝ (operatorEquiv m n Y (b j)) (w j)) = 0 := by
      rw [Finset.sum_sub_distrib]
      have hy := hY.2 P hP
      have hp := hface.2 Y hY.1
      change inner ℝ X P ≤ inner ℝ X Y at hy
      change inner ℝ X Y ≤ inner ℝ X P at hp
      have he : inner ℝ X Y = inner ℝ X P := le_antisymm hp hy
      rw [inner_eq_sum_columns X Y b, hpair] at he
      exact sub_eq_zero.mpr he.symm
    have he (j : Fin n) : inner ℝ (operatorEquiv m n Y (b j)) (w j) = ‖w j‖ := by
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sub_nonneg.mpr (hbound Y hY.1 j))).mp hsum j (Finset.mem_univ _)
      linarith
    have hs : ‖P‖ ^ 2 ≤ ‖Y‖ ^ 2 := by
      rw [norm_sq_eq_sum_columns P b, norm_sq_eq_sum_columns Y b]
      apply Finset.sum_le_sum
      intro j _
      rw [hcol]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (normalized_norm_le_of_support (w j) _ (he j)) 2
    nlinarith [norm_nonneg P, norm_nonneg Y]
  have heq : P = polar X :=
    minimumNormSupport_unique (spectralBall_compact m n) ⟨0, zero_mem_spectralBall m n⟩
      (spectralBall_convex m n) (innerSL ℝ X) hface hmin
  rw [← heq, hcol]

lemma exists_orthogonal_image_basis {m n : ℕ} (X : Space m n) :
    ∃ b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ i j, i ≠ j →
        inner ℝ (operatorEquiv m n X (b i)) (operatorEquiv m n X (b j)) = 0 := by
  let A := (operatorEquiv m n X).toLinearMap
  have hA := LinearMap.isSymmetric_adjoint_comp_self A
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  refine ⟨hA.eigenvectorBasis hn, ?_⟩
  intro i j hij
  change inner ℝ (A (hA.eigenvectorBasis hn i)) (A (hA.eigenvectorBasis hn j)) = 0
  rw [← LinearMap.adjoint_inner_right]
  change inner ℝ (hA.eigenvectorBasis hn i)
    ((A.adjoint ∘ₗ A) (hA.eigenvectorBasis hn j)) = 0
  rw [hA.apply_eigenvectorBasis hn, real_inner_smul_right,
    (hA.eigenvectorBasis hn).inner_eq_zero hij, mul_zero]

lemma polar_singular_basis {m n : ℕ} (X : Space m n) :
    ∃ b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      (∀ i j, i ≠ j →
        inner ℝ (operatorEquiv m n X (b i)) (operatorEquiv m n X (b j)) = 0) ∧
      ∀ i, operatorEquiv m n (polar X) (b i) =
        ‖operatorEquiv m n X (b i)‖⁻¹ • operatorEquiv m n X (b i) := by
  obtain ⟨b, hb⟩ := exists_orthogonal_image_basis X
  exact ⟨b, hb, polar_apply_of_orthogonal_images X b hb⟩

end LongTails.Proofs.MatrixPolarCharacterization
