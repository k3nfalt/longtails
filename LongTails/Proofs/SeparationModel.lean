import LongTails.Proofs.SeparationInstance
import LongTails.Proofs.GaussianBlocks
import LongTails.Proofs.BatchedDirectionExecution
import LongTails.Setups.BatchedSpectralSmooth

namespace LongTails.Proofs.SeparationModel

open MeasureTheory ProbabilityTheory OracleTemplate
open LongTails.Algorithms.MatrixPolar LongTails.Proofs.DiagonalSpectral
open LongTails.Proofs.SeparationInstance LongTails.Proofs.GaussianBlocks
open LongTails.Proofs.BatchedDirectionExecution
open scoped NNReal

variable {m n : ℕ}

noncomputable def noiseVec (v : ℝ) : Fin (min m n) → ℝ := fun i => if stiff i then v else 0

noncomputable def sample (ℓ c s : ℝ) (φ : FlatShape) (x0 : Space m n) (X : Space m n) (ω : ℝ) :
    Space m n :=
  gradient (objective ℓ c φ x0) X + diagMat (noiseVec (s * ω))

lemma noiseVec_smul (v : ℝ) : noiseVec (m := m) (n := n) v = v • noiseVec 1 := by
  funext i
  simp [noiseVec]

lemma measurable_gradient_objective (ℓ c : ℝ) (φ : FlatShape) (x0 : Space m n) :
    Measurable (gradient (objective ℓ c φ x0)) :=
  MuonProcess.measurable_gradient _

lemma sample_eq (ℓ c s : ℝ) (φ : FlatShape) (x0 X : Space m n) (ω : ℝ) :
    sample ℓ c s φ x0 X ω = gradient (objective ℓ c φ x0) X +
      (s * ω) • diagMat (noiseVec (m := m) (n := n) 1) := by
  rw [sample, noiseVec_smul, diagMat_smul]

lemma measurable_sample (ℓ c s : ℝ) (φ : FlatShape) (x0 : Space m n) :
    Measurable (Function.uncurry (sample ℓ c s φ x0)) := by
  have h : Function.uncurry (sample ℓ c s φ x0) = fun z : Space m n × ℝ =>
      gradient (objective ℓ c φ x0) z.1 + (s * z.2) • diagMat (noiseVec (m := m) (n := n) 1) := by
    funext z
    exact sample_eq ℓ c s φ x0 z.1 z.2
  rw [h]
  exact ((measurable_gradient_objective ℓ c φ x0).comp measurable_fst).add
    ((measurable_const.mul measurable_snd).smul_const _)

lemma adjoint_basis_apply (X : Space m n) (i : Fin m) (j : Fin n) :
    (operatorEquiv m n X).adjoint (EuclideanSpace.basisFun (Fin m) ℝ i) j = X (i, j) := by
  have h := ContinuousLinearMap.adjoint_inner_right (operatorEquiv m n X)
    (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin m) ℝ i)
  rw [EuclideanSpace.basisFun_inner, EuclideanSpace.inner_basisFun_real] at h
  rw [h]
  exact operatorEquiv_apply_basis X i j

lemma norm_adjoint_noise (i : Fin m) :
    ‖(operatorEquiv m n (diagMat (noiseVec (m := m) (n := n) 1))).adjoint
      (EuclideanSpace.basisFun (Fin m) ℝ i)‖ ≤ if i.val = 0 then 1 else 0 := by
  rw [← Real.sqrt_sq (norm_nonneg _), EuclideanSpace.norm_sq_eq]
  simp_rw [adjoint_basis_apply]
  have hentry (j : Fin n) : diagMat (noiseVec (m := m) (n := n) 1) (i, j) =
      if i.val = 0 ∧ j.val = 0 then 1 else 0 := by
    simp only [diagMat, noiseVec, stiff, PiLp.toLp_apply]
    by_cases hij : i.val = j.val ∧ i.val < min m n
    · rw [dite_eq_left hij]
      by_cases h0 : i.val = 0
      · simp [h0, show j.val = 0 by omega]
      · simp [h0]
    · rw [dite_eq_right hij]
      by_cases h0 : i.val = 0 ∧ j.val = 0
      · exfalso
        apply hij
        constructor
        · omega
        · have : 0 < min m n := lt_of_le_of_lt (Nat.zero_le _) (by
            rcases Nat.eq_zero_or_pos (min m n) with h | h
            · exfalso
              have := j.isLt
              have := i.isLt
              simp only [Nat.min_eq_zero_iff] at h
              omega
            · exact h)
          omega
      · simp [h0]
  simp_rw [hentry]
  by_cases h0 : i.val = 0
  · simp only [h0, true_and, ↓reduceIte]
    calc Real.sqrt (∑ j : Fin n, ‖if j.val = 0 then (1 : ℝ) else 0‖ ^ 2) ≤ Real.sqrt 1 := by
          apply Real.sqrt_le_sqrt
          calc (∑ j : Fin n, ‖if j.val = 0 then (1 : ℝ) else 0‖ ^ 2) =
                ∑ j ∈ Finset.univ.filter (fun j : Fin n => j.val = 0), (1 : ℝ) := by
                  rw [Finset.sum_filter]
                  apply Finset.sum_congr rfl
                  intro j _
                  split_ifs <;> simp
            _ ≤ 1 := by
                  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
                  have : (Finset.univ.filter (fun j : Fin n => j.val = 0)).card ≤ 1 := by
                    apply Finset.card_le_one.mpr
                    intro a ha b hb
                    simp only [Finset.mem_filter] at ha hb
                    exact Fin.ext (ha.2.trans hb.2.symm)
                  exact_mod_cast this
      _ = 1 := Real.sqrt_one
  · simp [h0]

noncomputable def model (ℓ c s : ℝ) (φ : FlatShape) (x0 : Space m n) (hs : 0 ≤ s)
    (hmn : 0 < m) :
    LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel (objective ℓ c φ x0) s where
  Ω := ℝ
  law := (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)
  sample := sample ℓ c s φ x0
  jointly_measurable := measurable_sample ℓ c s φ x0
  integrable x := by
    change Integrable (fun ω => sample ℓ c s φ x0 x ω) (gaussianReal 0 1)
    simp_rw [sample_eq]
    exact (integrable_const _).add
      ((((memLp_id_gaussianReal 1).integrable le_rfl).const_mul s).smul_const _)
  unbiased x := by
    change (∫ ω, sample ℓ c s φ x0 x ω ∂(gaussianReal 0 1)) = _
    simp_rw [sample_eq]
    have h1 : Integrable (fun ω : ℝ => (s * ω) • diagMat (noiseVec (m := m) (n := n) 1))
        (gaussianReal 0 1) :=
      (((memLp_id_gaussianReal 1).integrable le_rfl).const_mul s).smul_const _
    rw [integral_add (integrable_const _) h1, integral_const, integral_smul_const,
      integral_const_mul]
    simp [integral_id_gaussianReal]
  row_profile := by
    refine ⟨EuclideanSpace.basisFun (Fin m) ℝ, fun i => if i.val = 0 then s else 0, ?_, ?_, ?_⟩
    · intro i
      dsimp only
      split_ifs <;> simp [hs]
    · rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.univ.filter (fun i : Fin m => i.val = 0)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨⟨0, hmn⟩, ?_⟩
        ext i
        simp [Fin.ext_iff]
      rw [hcard]
      simp
    · intro x i
      have hrow (ω : ℝ) : (operatorEquiv m n (sample ℓ c s φ x0 x ω -
          gradient (objective ℓ c φ x0) x)).adjoint (EuclideanSpace.basisFun (Fin m) ℝ i) =
          (s * ω) • (operatorEquiv m n (diagMat (noiseVec (m := m) (n := n) 1))).adjoint
            (EuclideanSpace.basisFun (Fin m) ℝ i) := by
        rw [sample_eq, add_sub_cancel_left, map_smul, map_smul]
        rfl
      simp_rw [hrow]
      set u := (operatorEquiv m n (diagMat (noiseVec (m := m) (n := n) 1))).adjoint
        (EuclideanSpace.basisFun (Fin m) ℝ i)
      have hu : ‖u‖ ≤ if i.val = 0 then 1 else 0 := norm_adjoint_noise (m := m) (n := n) i
      constructor
      · show MemLp (fun ω : ℝ => (s * ω) • u) 2 (gaussianReal 0 1)
        have h := (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) u).comp_memLp'
          ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).const_mul s)
        convert h using 1 <;> first | (funext ω; simp) | norm_num
      · have hsq : (∫ ω, ‖(s * ω) • u‖ ^ 2 ∂(gaussianReal 0 1 : Measure ℝ)) =
            s ^ 2 * ‖u‖ ^ 2 * ∫ ω, ω ^ 2 ∂(gaussianReal 0 1 : Measure ℝ) := by
          rw [← integral_const_mul]
          congr 1
          funext ω
          rw [norm_smul, Real.norm_eq_abs, mul_pow, abs_mul, mul_pow, sq_abs, sq_abs]
          ring
        have hvar : (∫ ω, ω ^ 2 ∂(gaussianReal 0 1 : Measure ℝ)) = 1 := by
          have hv := variance_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
          rw [variance_eq_integral (measurable_id.aemeasurable)] at hv
          simpa [integral_id_gaussianReal] using hv
        change (∫ ω, ‖(s * ω) • u‖ ^ 2 ∂(gaussianReal 0 1 : Measure ℝ)) ≤ _
        rw [hsq, hvar, mul_one]
        by_cases h0 : i.val = 0
        · simp only [h0, ↓reduceIte] at hu ⊢
          have h1 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
          nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg s)]
        · simp only [h0, ↓reduceIte] at hu ⊢
          have : ‖u‖ = 0 := le_antisymm hu (norm_nonneg u)
          simp [this]

def raise {f : Space m n → ℝ} {s s' : ℝ}
    (M : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s) (h : s ≤ s') :
    LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s' where
  Ω := M.Ω
  measurableΩ := M.measurableΩ
  law := M.law
  sample := M.sample
  jointly_measurable := M.jointly_measurable
  integrable := M.integrable
  unbiased := M.unbiased
  row_profile := by
    obtain ⟨b, σ, h0, hs, hrow⟩ := M.row_profile
    exact ⟨b, σ, h0, hs.trans h, hrow⟩

end LongTails.Proofs.SeparationModel
