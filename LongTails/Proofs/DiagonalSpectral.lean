import LongTails.Proofs.MatrixPolarGeometry
import LongTails.Proofs.MatrixCovariance

namespace LongTails.Proofs.DiagonalSpectral

open LongTails.Algorithms.MatrixPolar

variable {m n : ℕ}

def dg (i : Fin (min m n)) : Fin m × Fin n :=
  (⟨i.val, lt_of_lt_of_le i.isLt (min_le_left m n)⟩,
    ⟨i.val, lt_of_lt_of_le i.isLt (min_le_right m n)⟩)

lemma dg_injective : Function.Injective (dg (m := m) (n := n)) := by
  intro i j h
  apply Fin.ext
  have := congrArg (fun k : Fin m × Fin n => k.1.val) h
  simpa [dg] using this

noncomputable def diagMat (a : Fin (min m n) → ℝ) : Space m n :=
  WithLp.toLp 2 fun k : Fin m × Fin n =>
    if h : k.1.val = k.2.val ∧ k.1.val < min m n then a ⟨k.1.val, h.2⟩ else 0

lemma diagMat_apply_dg (a : Fin (min m n) → ℝ) (i : Fin (min m n)) :
    diagMat a (dg i) = a i := by
  simp only [diagMat, dg, PiLp.toLp_apply]
  split_ifs with hh
  · rfl
  · exact (hh ⟨trivial, i.isLt⟩).elim

lemma diagMat_apply_of_ne (a : Fin (min m n) → ℝ) (k : Fin m × Fin n)
    (hk : ∀ i, dg i ≠ k) : diagMat a k = 0 := by
  simp only [diagMat, PiLp.toLp_apply]
  split_ifs with h
  · exfalso
    apply hk ⟨k.1.val, h.2⟩
    apply Prod.ext <;> apply Fin.ext
    · rfl
    · exact h.1
  · rfl

lemma diagMat_add (a b : Fin (min m n) → ℝ) : diagMat (a + b) = diagMat a + diagMat b := by
  ext k
  simp only [diagMat, PiLp.add_apply, PiLp.toLp_apply, Pi.add_apply]
  split_ifs <;> simp

lemma diagMat_sub (a b : Fin (min m n) → ℝ) : diagMat (a - b) = diagMat a - diagMat b := by
  ext k
  simp only [diagMat, PiLp.sub_apply, PiLp.toLp_apply, Pi.sub_apply]
  split_ifs <;> simp

lemma diagMat_smul (c : ℝ) (a : Fin (min m n) → ℝ) : diagMat (c • a) = c • diagMat a := by
  ext k
  simp only [diagMat, PiLp.smul_apply, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

lemma inner_diagMat (a : Fin (min m n) → ℝ) (X : Space m n) :
    inner ℝ (diagMat a) X = ∑ i, a i * X (dg i) := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  have hsplit : (∑ k : Fin m × Fin n, X k * diagMat a k) =
      ∑ k ∈ Finset.univ.image (dg (m := m) (n := n)), X k * diagMat a k := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro k _ hk
    have hne : ∀ i, dg i ≠ k := by
      intro i hi
      exact hk (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    rw [diagMat_apply_of_ne a k hne, mul_zero]
  rw [hsplit, Finset.sum_image (fun i _ j _ h => dg_injective h)]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagMat_apply_dg]
  ring

lemma abs_apply_le_spectralNorm (X : Space m n) (k : Fin m × Fin n) :
    |X k| ≤ spectralNorm X := by
  have h1 := operatorEquiv_apply_basis X k.1 k.2
  have h2 : |operatorEquiv m n X (EuclideanSpace.basisFun (Fin n) ℝ k.2) k.1| ≤
      ‖operatorEquiv m n X (EuclideanSpace.basisFun (Fin n) ℝ k.2)‖ := by
    simpa [Real.norm_eq_abs] using
      PiLp.norm_apply_le (operatorEquiv m n X (EuclideanSpace.basisFun (Fin n) ℝ k.2)) k.1
  have h3 := (operatorEquiv m n X).le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ k.2)
  rw [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 k.2, mul_one] at h3
  rw [h1] at h2
  exact h2.trans h3

lemma nuclearNorm_diagMat_le (a : Fin (min m n) → ℝ) :
    nuclearNorm (diagMat a) ≤ ∑ i, |a i| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => abs_nonneg _)
  intro U
  change ‖inner ℝ (diagMat a) ((operatorEquiv m n).symm U)‖ ≤ _
  rw [inner_diagMat, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have h := abs_apply_le_spectralNorm ((operatorEquiv m n).symm U) (dg i)
  simpa [spectralNorm] using h

lemma spectralNorm_diagMat_le (a : Fin (min m n) → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    spectralNorm (diagMat a) ≤ 1 := by
  unfold spectralNorm
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply le_of_sq_le_sq _ (norm_nonneg v)
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have hrow (i : Fin m) : operatorEquiv m n (diagMat a) v i =
      if h : i.val < min m n then a ⟨i.val, h⟩ * v ⟨i.val, lt_of_lt_of_le h (min_le_right m n)⟩
      else 0 := by
    rw [operatorEquiv_apply_coordinate]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i.val, lt_of_lt_of_le h (min_le_right m n)⟩]
      · simp only [diagMat, PiLp.toLp_apply]
        split_ifs with hh
        · rfl
        · exfalso
          apply hh
          first | exact ⟨rfl, h⟩ | exact h | simp [h]
      · intro j _ hj
        simp only [diagMat, PiLp.toLp_apply]
        split_ifs with hh
        · exact absurd (Fin.ext hh.1.symm) hj
        · simp
      · simp
    · apply Finset.sum_eq_zero
      intro j _
      simp only [diagMat, PiLp.toLp_apply]
      split_ifs with hh
      · exact absurd hh.2 h
      · simp
  simp_rw [hrow]
  let e : Fin (min m n) → Fin n := fun i => ⟨i.val, lt_of_lt_of_le i.isLt (min_le_right m n)⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    simpa [e] using congrArg Fin.val hij
  calc (∑ i : Fin m, ‖if h : i.val < min m n then
          a ⟨i.val, h⟩ * v ⟨i.val, lt_of_lt_of_le h (min_le_right m n)⟩ else 0‖ ^ 2) =
        ∑ i : Fin (min m n), ‖a i * v (e i)‖ ^ 2 := by
          let f : Fin (min m n) → Fin m := fun i =>
            ⟨i.val, lt_of_lt_of_le i.isLt (min_le_left m n)⟩
          have hf : Function.Injective f := by
            intro i j hij
            apply Fin.ext
            simpa [f] using congrArg Fin.val hij
          rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))]
          · rw [Finset.sum_image (fun i _ j _ h => hf h)]
            apply Finset.sum_congr rfl
            intro i _
            simp [f, e, i.isLt]
          · intro i _ hi
            have : ¬ i.val < min m n := by
              intro h
              exact hi (Finset.mem_image.mpr ⟨⟨i.val, h⟩, Finset.mem_univ _, by
                apply Fin.ext; rfl⟩)
            simp [this]
    _ ≤ ∑ i : Fin (min m n), ‖v (e i)‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_mul, mul_pow]
          have h1 : ‖a i‖ ^ 2 ≤ 1 := by
            rw [Real.norm_eq_abs, sq_abs]
            nlinarith [ha i, abs_nonneg (a i), sq_abs (a i)]
          nlinarith [sq_nonneg ‖v (e i)‖]
    _ = ∑ j ∈ Finset.univ.image e, ‖v j‖ ^ 2 := by
          rw [Finset.sum_image (fun i _ j _ h => he h)]
    _ ≤ ∑ j, ‖v j‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun j _ _ => sq_nonneg _)

lemma nuclearNorm_diagMat (a : Fin (min m n) → ℝ) :
    nuclearNorm (diagMat a) = ∑ i, |a i| := by
  apply le_antisymm (nuclearNorm_diagMat_le a)
  let s : Fin (min m n) → ℝ := fun i => if 0 ≤ a i then 1 else -1
  have hs : ∀ i, |s i| ≤ 1 := by intro i; by_cases h : 0 ≤ a i <;> simp [s, h]
  have hpair := inner_le_nuclear_mul_spectral (diagMat a) (diagMat s)
  have hsp := spectralNorm_diagMat_le s hs
  rw [inner_diagMat] at hpair
  have hval : (∑ i, a i * diagMat s (dg i)) = ∑ i, |a i| := by
    apply Finset.sum_congr rfl
    intro i _
    rw [diagMat_apply_dg]
    by_cases h : 0 ≤ a i
    · simp [s, h, abs_of_nonneg h]
    · simp [s, h, abs_of_neg (lt_of_not_ge h)]
  rw [hval, abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)] at hpair
  have hn := nuclearNorm_nonneg (diagMat a)
  nlinarith

end LongTails.Proofs.DiagonalSpectral
