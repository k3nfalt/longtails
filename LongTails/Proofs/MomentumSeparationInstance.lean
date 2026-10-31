import LongTails.Proofs.MomentumSeparationCore
import LongTails.Proofs.SeparationLower
import LongTails.Proofs.NsgdLattice

namespace LongTails.Proofs.MomentumSeparationInstance

open MeasureTheory
open LongTails.Algorithms.MatrixPolar
open LongTails.Proofs.DiagonalSpectral LongTails.Proofs.SeparationInstance

variable {m n : ℕ}

def stiffEntry (p : Fin m × Fin n) : Prop := p.1.val = 0 ∧ (p.2.val = 0 ∨ min m n ≤ p.2.val)

instance (p : Fin m × Fin n) : Decidable (stiffEntry p) :=
  inferInstanceAs (Decidable (p.1.val = 0 ∧ (p.2.val = 0 ∨ min m n ≤ p.2.val)))

noncomputable def stiffVec (x0 X : Space m n) : Space m n :=
  WithLp.toLp 2 fun p => if stiffEntry p then X p - x0 p else 0

noncomputable def stiffPart (ℓ : ℝ) (x0 X : Space m n) : ℝ :=
  ∑ p : Fin m × Fin n, if stiffEntry p then ℓ / 2 * (X p - x0 p) ^ 2 else 0

noncomputable def objective (ℓ c : ℝ) (φ : FlatShape) (x0 X : Space m n) : ℝ :=
  stiffPart ℓ x0 X + SeparationInstance.objective 0 c φ x0 X

lemma hasGradientAt_stiffPart (ℓ : ℝ) (x0 X : Space m n) :
    HasGradientAt (stiffPart ℓ x0) (ℓ • stiffVec x0 X) X := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hcoord (p : Fin m × Fin n) : HasFDerivAt (fun Y : Space m n => Y p - x0 p)
      (EuclideanSpace.proj p : Space m n →L[ℝ] ℝ) X :=
    (EuclideanSpace.proj p : Space m n →L[ℝ] ℝ).hasFDerivAt.sub_const _
  have hterm (p : Fin m × Fin n) : HasFDerivAt (fun Y : Space m n =>
      if stiffEntry p then ℓ / 2 * (Y p - x0 p) ^ 2 else 0)
      ((if stiffEntry p then ℓ * (X p - x0 p) else 0) •
        (EuclideanSpace.proj p : Space m n →L[ℝ] ℝ)) X := by
    by_cases hs : stiffEntry p
    · simp only [hs, ↓reduceIte]
      have hq : HasDerivAt (fun u : ℝ => ℓ / 2 * u ^ 2) (ℓ * (X p - x0 p)) (X p - x0 p) := by
        convert HasDerivAt.const_mul (ℓ / 2) ((hasDerivAt_id (X p - x0 p)).pow 2) using 1
        all_goals (try funext u)
        all_goals (try simp)
        all_goals (try ring)
      exact HasDerivAt.comp_hasFDerivAt (h₂ := fun u => ℓ / 2 * u ^ 2) X hq (hcoord p)
    · simp only [hs, ↓reduceIte, zero_smul]
      exact hasFDerivAt_const _ _
  have hsum := HasFDerivAt.sum (u := Finset.univ) (fun p _ => hterm p)
  convert hsum using 1
  · funext Y
    simp [stiffPart]
  · ext Y
    rw [InnerProductSpace.toDual_apply_apply, PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial, stiffVec, PiLp.smul_apply,
      smul_eq_mul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro p _
    have hp : (EuclideanSpace.proj p : Space m n →L[ℝ] ℝ) Y = Y p := rfl
    rw [hp]
    split_ifs <;> ring

lemma hasGradientAt_objective (ℓ c : ℝ) (φ : FlatShape) (x0 X : Space m n) :
    HasGradientAt (objective ℓ c φ x0)
      (ℓ • stiffVec x0 X + diagMat (coefficients 0 c φ (offset x0 X))) X := by
  have h1 := (hasGradientAt_stiffPart ℓ x0 X).hasFDerivAt
  have h2 := (SeparationInstance.hasGradientAt_objective 0 c φ x0 X).hasFDerivAt
  rw [hasGradientAt_iff_hasFDerivAt, map_add]
  exact h1.add h2

lemma gradient_objective (ℓ c : ℝ) (φ : FlatShape) (x0 X : Space m n) :
    gradient (objective ℓ c φ x0) X =
      ℓ • stiffVec x0 X + diagMat (coefficients 0 c φ (offset x0 X)) :=
  (hasGradientAt_objective ℓ c φ x0 X).gradient

lemma sum_stiff_split' (hr : 0 < min m n) (A C : ℝ) :
    (∑ i : Fin (min m n), if stiff i then A else C) = A + (min m n - 1 : ℕ) * C := by
  have h := LongTails.Proofs.SeparationTrajectory.sum_stiff_split hr A C
  rw [← h]
  rfl

lemma spectralNorm_le_norm (X : Space m n) : spectralNorm X ≤ ‖X‖ := by
  unfold spectralNorm
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg X)
  intro v
  apply le_of_sq_le_sq _ (mul_nonneg (norm_nonneg X) (norm_nonneg v))
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  have hrow (i : Fin m) : (operatorEquiv m n X v i) ^ 2 ≤
      (∑ j, X (i, j) ^ 2) * ∑ j, v j ^ 2 := by
    rw [operatorEquiv_apply_coordinate]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ i, ‖operatorEquiv m n X v i‖ ^ 2 = ∑ i, (operatorEquiv m n X v i) ^ 2 := by
        simp [Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ i, (∑ j, X (i, j) ^ 2) * ∑ j, v j ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = (∑ p : Fin m × Fin n, ‖X p‖ ^ 2) * ∑ j, ‖v j‖ ^ 2 := by
        rw [← Finset.sum_mul, Fintype.sum_prod_type]
        simp [Real.norm_eq_abs, sq_abs]

lemma row_norm_eq (Z : Space m n) (i : Fin m) :
    ‖(operatorEquiv m n Z).adjoint (EuclideanSpace.basisFun (Fin m) ℝ i)‖ =
      Real.sqrt (∑ j, Z (i, j) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [LongTails.Proofs.SeparationModel.adjoint_basis_apply, Real.norm_eq_abs, sq_abs]

lemma row_norm_le_spectral (Z : Space m n) (i : Fin m) :
    Real.sqrt (∑ j, Z (i, j) ^ 2) ≤ spectralNorm Z := by
  rw [← row_norm_eq]
  calc _ ≤ ‖(operatorEquiv m n Z).adjoint‖ * ‖EuclideanSpace.basisFun (Fin m) ℝ i‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = spectralNorm Z := by
        rw [(EuclideanSpace.basisFun (Fin m) ℝ).orthonormal.1 i, mul_one]
        unfold spectralNorm
        exact LinearIsometryEquiv.norm_map ContinuousLinearMap.adjoint _

lemma nuclear_stiff_diff_le (x0 X Y : Space m n) (hm : 0 < m) :
    nuclearNorm (stiffVec x0 X - stiffVec x0 Y) ≤ spectralNorm (X - Y) := by
  refine (LongTails.Proofs.MatrixCovariance.nuclearNorm_le_rows
    (EuclideanSpace.basisFun (Fin m) ℝ) _).trans ?_
  simp_rw [row_norm_eq]
  rw [Finset.sum_eq_single (⟨0, hm⟩ : Fin m)]
  · refine le_trans ?_ (row_norm_le_spectral (X - Y) ⟨0, hm⟩)
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro j _
    simp only [stiffVec, PiLp.sub_apply]
    split_ifs <;> nlinarith [sq_nonneg (X (⟨0, hm⟩, j) - Y (⟨0, hm⟩, j))]
  · intro i _ hi
    have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
    have hz : ∑ j, (stiffVec x0 X - stiffVec x0 Y) (i, j) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [stiffVec, stiffEntry, hi']
    rw [hz, Real.sqrt_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma lipschitz_objective {ℓ c : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 ≤ c) (φ : FlatShape)
    (hr : 0 < min m n) (x0 X Y : Space m n) :
    nuclearNorm (gradient (objective ℓ c φ x0) X - gradient (objective ℓ c φ x0) Y) ≤
      (ℓ + (min m n - 1 : ℕ) * (c * φ.lip)) * spectralNorm (X - Y) := by
  have hm : 0 < m := lt_of_lt_of_le hr (min_le_left _ _)
  rw [gradient_objective, gradient_objective]
  have he : ℓ • stiffVec x0 X + diagMat (coefficients 0 c φ (offset x0 X)) -
      (ℓ • stiffVec x0 Y + diagMat (coefficients 0 c φ (offset x0 Y))) =
      ℓ • (stiffVec x0 X - stiffVec x0 Y) +
        (gradient (SeparationInstance.objective 0 c φ x0) X -
          gradient (SeparationInstance.objective 0 c φ x0) Y) := by
    rw [SeparationInstance.gradient_objective, SeparationInstance.gradient_objective, smul_sub]
    abel
  rw [he]
  refine (nuclearNorm_add_le _ _).trans ?_
  have h1 := (LongTails.Proofs.MomentumMuonRate.nuclearNorm_smul_le hℓ
    (stiffVec x0 X - stiffVec x0 Y)).trans
    (mul_le_mul_of_nonneg_left (nuclear_stiff_diff_le x0 X Y hm) hℓ)
  have h2 := SeparationInstance.lipschitz_objective (le_refl (0 : ℝ)) hc φ x0 X Y
  have hsum : (∑ i : Fin (min m n), if stiff i then (0 : ℝ) else c * φ.lip) =
      (min m n - 1 : ℕ) * (c * φ.lip) := by
    rw [sum_stiff_split' hr, zero_add]
  rw [hsum] at h2
  nlinarith

lemma nuclear_ge_stiff (ℓ c : ℝ) (φ : FlatShape) (x0 X : Space m n) :
    ℓ * ‖stiffVec x0 X‖ ≤ nuclearNorm (gradient (objective ℓ c φ x0) X) := by
  rw [gradient_objective]
  set v := stiffVec x0 X
  have hdiag : inner ℝ (diagMat (coefficients 0 c φ (offset x0 X))) v = 0 := by
    rw [inner_diagMat]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i.val = 0
    · simp [coefficients, stiff, hi]
    · have : v (dg i) = 0 := by
        simp only [v, stiffVec, PiLp.toLp_apply, dg, stiffEntry]
        simp [hi]
      rw [this, mul_zero]
  have hin : inner ℝ (ℓ • v + diagMat (coefficients 0 c φ (offset x0 X))) v = ℓ * ‖v‖ ^ 2 := by
    rw [inner_add_left, hdiag, add_zero, inner_smul_left, real_inner_self_eq_norm_sq]
    simp
  have hb := inner_le_nuclear_mul_spectral (ℓ • v + diagMat (coefficients 0 c φ (offset x0 X))) v
  rw [hin] at hb
  have hsp := spectralNorm_le_norm v
  have hn0 := nuclearNorm_nonneg (ℓ • v + diagMat (coefficients 0 c φ (offset x0 X)))
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact hn0
  · have h1 : ℓ * ‖v‖ ^ 2 ≤ nuclearNorm (ℓ • v + diagMat (coefficients 0 c φ (offset x0 X))) * ‖v‖ :=
      (le_abs_self _).trans (hb.trans (mul_le_mul_of_nonneg_left hsp hn0))
    nlinarith

lemma nuclear_ge_flat (ℓ c : ℝ) (φ : FlatShape) (x0 X : Space m n) :
    ∑ i, |coefficients 0 c φ (offset x0 X) i| ≤ nuclearNorm (gradient (objective ℓ c φ x0) X) := by
  rw [gradient_objective]
  set a := coefficients 0 c φ (offset x0 X)
  let sg : Fin (min m n) → ℝ := fun i => if i.val = 0 then 0 else if 0 ≤ a i then 1 else -1
  have hsg : ∀ i, |sg i| ≤ 1 := by
    intro i; simp only [sg]; split_ifs <;> norm_num
  have hsp := spectralNorm_diagMat_le sg hsg
  have h1 : inner ℝ (stiffVec x0 X) (diagMat sg) = 0 := by
    rw [real_inner_comm, inner_diagMat]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i.val = 0
    · simp [sg, hi]
    · have : stiffVec x0 X (dg i) = 0 := by
        simp only [stiffVec, PiLp.toLp_apply, dg, stiffEntry]
        simp [hi]
      rw [this, mul_zero]
  have h2 : inner ℝ (diagMat a) (diagMat sg) = ∑ i, |a i| := by
    rw [inner_diagMat]
    apply Finset.sum_congr rfl
    intro i _
    rw [diagMat_apply_dg]
    by_cases hi : i.val = 0
    · have ha : a i = 0 := by simp [a, coefficients, stiff, hi]
      simp [sg, hi, ha]
    · simp only [sg, hi, ↓reduceIte]
      split_ifs with hai
      · rw [abs_of_nonneg hai]; ring
      · rw [abs_of_neg (not_le.mp hai)]; ring
  have hin : inner ℝ (ℓ • stiffVec x0 X + diagMat a) (diagMat sg) = ∑ i, |a i| := by
    rw [inner_add_left, inner_smul_left, h1, h2]
    simp
  have hb := inner_le_nuclear_mul_spectral (ℓ • stiffVec x0 X + diagMat a) (diagMat sg)
  rw [hin] at hb
  have hn0 := nuclearNorm_nonneg (ℓ • stiffVec x0 X + diagMat a)
  calc ∑ i, |a i| ≤ abs (∑ i, |a i|) := le_abs_self _
    _ ≤ nuclearNorm (ℓ • stiffVec x0 X + diagMat a) * spectralNorm (diagMat sg) := hb
    _ ≤ nuclearNorm (ℓ • stiffVec x0 X + diagMat a) * 1 := mul_le_mul_of_nonneg_left hsp hn0
    _ = _ := mul_one _

lemma objective_lower {ℓ c w : ℝ} (hℓ : 0 ≤ ℓ) (hc : 0 ≤ c) (hw : 0 < w) (D : ℝ)
    (hpos : 0 < min m n) (x0 X : Space m n) :
    (min m n - 1 : ℕ) * (c * w) ≤ objective ℓ c (valleyShape hw D) x0 X := by
  have h1 : 0 ≤ stiffPart ℓ x0 X := Finset.sum_nonneg fun p _ => by
    split_ifs <;> positivity
  have h2 : (min m n - 1 : ℕ) * (c * w) ≤ SeparationInstance.objective 0 c (valleyShape hw D) x0 X := by
    unfold SeparationInstance.objective
    have hr : ∀ i : Fin (min m n), (if stiff i then (0 : ℝ) else c * w) ≤
        (if stiff i then 0 / 2 * offset x0 X i ^ 2 else c * (valleyShape hw D).value (offset x0 X i)) := by
      intro i
      split_ifs
      · simp
      · exact mul_le_mul_of_nonneg_left (LongTails.Proofs.SeparationLower.valley_ge_width hw.le D _) hc
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun i _ => hr i)
    rw [sum_stiff_split' hpos, zero_add]
  unfold objective
  linarith

lemma objective_start_le {ℓ c w : ℝ} (hc : 0 ≤ c) (hw : 0 < w) (D : ℝ) (hr : 0 < min m n)
    (x0 : Space m n) :
    objective ℓ c (valleyShape hw D) x0 x0 ≤ (min m n - 1 : ℕ) * (c * (w + |D|)) := by
  unfold objective stiffPart
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    ite_self, Finset.sum_const_zero, zero_add]
  rw [SeparationInstance.objective_start, sum_stiff_split' hr, zero_add]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hc
  have := LongTails.Proofs.NsgdLattice.valley_le w D 0 hw.le
  simpa [valleyShape, abs_sub_comm] using this

end LongTails.Proofs.MomentumSeparationInstance
