import LongTails.Proofs.MatrixPolarGeometry
import LongTails.Proofs.MatrixOracleMoments

namespace LongTails.Proofs.MatrixCovariance

open MeasureTheory
open LongTails.Setups.MatrixGeometry LongTails.Algorithms.MatrixPolar

lemma nuclearNorm_le_rows {m n : ℕ} {I : Type*} [Fintype I]
    (b : OrthonormalBasis I ℝ (EuclideanSpace ℝ (Fin m))) (X : Space m n) :
    nuclearNorm X ≤ ∑ i, ‖(operatorEquiv m n X).adjoint (b i)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
    ((innerSL ℝ X).comp (operatorEquiv m n).symm.toContinuousLinearMap)
    (Finset.sum_nonneg (fun i _ => norm_nonneg _))
  intro U
  change ‖inner ℝ X ((operatorEquiv m n).symm U)‖ ≤ _
  rw [Real.norm_eq_abs, inner_eq_trace_pair]
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    MatrixOracleMoments.trace_pair_bound b (operatorEquiv m n X) U

lemma continuous_nuclearNorm (m n : ℕ) : Continuous (nuclearNorm (m := m) (n := n)) := by
  exact ((innerSL ℝ).continuous.clm_comp_const (operatorEquiv m n).symm.toContinuousLinearMap).norm

lemma row_profile_second_moment {Ω I : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {m n : ℕ} [Fintype I]
    (b : OrthonormalBasis I ℝ (EuclideanSpace ℝ (Fin m))) {N : Ω → Space m n}
    (hN : Measurable N) {σ : I → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (hrows : ∀ i, MemLp (fun ω => ‖(operatorEquiv m n (N ω)).adjoint (b i)‖) 2 P)
    (hsecond : ∀ i, (∫ ω, ‖(operatorEquiv m n (N ω)).adjoint (b i)‖ ^ 2 ∂P) ≤ σ i ^ 2) :
    MemLp (fun ω => nuclearNorm (N ω)) 2 P ∧
      (∫ ω, nuclearNorm (N ω) ^ 2 ∂P) ≤ (∑ i, σ i) ^ 2 := by
  exact MatrixOracleMoments.second_moment_of_sum_bound Finset.univ
    (fun i _ => hrows i) (fun i _ => hσ i) (fun i _ => hsecond i)
    ((continuous_nuclearNorm m n).measurable.comp hN).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by unfold nuclearNorm; positivity))
    (Filter.Eventually.of_forall (fun ω => nuclearNorm_le_rows b (N ω)))

lemma weighted_row_martingale_second_moment {Ω I : Type*}
    {m₀ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {m n : ℕ} [Fintype I]
    (b : OrthonormalBasis I ℝ (EuclideanSpace ℝ (Fin m)))
    {F : ℕ → MeasurableSpace Ω} (hF : ∀ t, F t ≤ m₀) (hmono : Monotone F)
    {N : ℕ → Ω → Space m n} (hN : ∀ t, Measurable (N t))
    {σ : I → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (hrows : ∀ t i, MemLp (fun ω => (operatorEquiv m n (N t ω)).adjoint (b i)) 2 P)
    (hadapt : ∀ t i, StronglyMeasurable[F (t + 1)]
      (fun ω => (operatorEquiv m n (N t ω)).adjoint (b i)))
    (hzero : ∀ t i, ∀ᵐ ω ∂P,
      P[fun ω => (operatorEquiv m n (N t ω)).adjoint (b i) | F t] ω = 0)
    (hsecond : ∀ t i,
      (∫ ω, ‖(operatorEquiv m n (N t ω)).adjoint (b i)‖ ^ 2 ∂P) ≤ σ i ^ 2)
    (w : ℕ → ℝ) (T : ℕ) :
    MemLp (fun ω => nuclearNorm (∑ t ∈ Finset.range T, w t • N t ω)) 2 P ∧
      (∫ ω, nuclearNorm (∑ t ∈ Finset.range T, w t • N t ω) ^ 2 ∂P) ≤
        (∑ t ∈ Finset.range T, w t ^ 2) * (∑ i, σ i) ^ 2 := by
  let V := ∑ t ∈ Finset.range T, w t ^ 2
  have hV : 0 ≤ V := Finset.sum_nonneg (fun t _ => sq_nonneg _)
  have hroweq (i : I) (ω : Ω) :
      (operatorEquiv m n (∑ t ∈ Finset.range T, w t • N t ω)).adjoint (b i) =
        ∑ t ∈ Finset.range T, w t • (operatorEquiv m n (N t ω)).adjoint (b i) := by
    simp
  have hr (i : I) : MemLp (fun ω =>
      (operatorEquiv m n (∑ t ∈ Finset.range T, w t • N t ω)).adjoint (b i)) 2 P := by
    simp_rw [hroweq]
    exact memLp_finsetSum _ (fun t _ => (hrows t i).const_smul (w t))
  have hb (i : I) : (∫ ω,
      ‖(operatorEquiv m n (∑ t ∈ Finset.range T, w t • N t ω)).adjoint (b i)‖ ^ 2 ∂P)
        ≤ (Real.sqrt V * σ i) ^ 2 := by
    simp_rw [hroweq]
    rw [MatrixOracleMoments.vector_martingale_sum_second_moment
      (EuclideanSpace.basisFun (Fin n) ℝ) hF hmono
      (fun t => hrows t i) (fun t => hadapt t i) (fun t => hzero t i)]
    calc
      _ ≤ ∑ t ∈ Finset.range T, w t ^ 2 * σ i ^ 2 :=
        Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hsecond t i) (sq_nonneg _))
      _ = (Real.sqrt V * σ i) ^ 2 := by rw [mul_pow, Real.sq_sqrt hV, Finset.sum_mul]
  have hh := row_profile_second_moment b
    (Finset.measurable_sum _ (fun t _ => (hN t).const_smul (w t)))
    (fun i => mul_nonneg (Real.sqrt_nonneg _) (hσ i))
    (fun i => (hr i).norm) hb
  simpa only [← Finset.mul_sum, mul_pow, Real.sq_sqrt hV, Pi.smul_apply] using hh

lemma conditional_weighted_row_second_moment {Ω I : Type*}
    {m₀ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} [Fintype I]
    (b : OrthonormalBasis I ℝ (EuclideanSpace ℝ (Fin m)))
    {F : ℕ → MeasurableSpace Ω} (hF : ∀ t, F t ≤ m₀) (hmono : Monotone F)
    {N : ℕ → Ω → Space m n} (hN : ∀ t, Measurable (N t))
    {σ : I → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (hrows : ∀ t i, MemLp (fun ω => (operatorEquiv m n (N t ω)).adjoint (b i)) 2 P)
    (hadapt : ∀ t i, StronglyMeasurable[F (t + 1)]
      (fun ω => (operatorEquiv m n (N t ω)).adjoint (b i)))
    (hzero : ∀ t i, ∀ᵐ ω ∂P,
      P[fun ω => (operatorEquiv m n (N t ω)).adjoint (b i) | F t] ω = 0)
    (hlocal : ∀ A, MeasurableSet[F 0] A → ∀ t i,
      (∫ ω in A, ‖(operatorEquiv m n (N t ω)).adjoint (b i)‖ ^ 2 ∂P)
        ≤ σ i ^ 2 * P.real A)
    (w : ℕ → ℝ) (T : ℕ) :
    ∀ᵐ ω ∂P, P[fun u => nuclearNorm (∑ t ∈ Finset.range T, w t • N t u) ^ 2 | F 0] ω
      ≤ (∑ t ∈ Finset.range T, w t ^ 2) * (∑ i, σ i) ^ 2 := by
  have hg := weighted_row_martingale_second_moment b hF hmono hN hσ hrows hadapt hzero
    (fun t i => by simpa using hlocal Set.univ MeasurableSet.univ t i) w T
  apply MatrixOracleMoments.conditional_le_of_local_integrals (hF 0) hg.1.integrable_sq
  intro A hA
  have hAt (t : ℕ) : MeasurableSet[F t] A := hmono (Nat.zero_le t) _ hA
  have hz (t : ℕ) (i : I) : ∀ᵐ ω ∂P.restrict A,
      (P.restrict A)[fun u => (operatorEquiv m n (N t u)).adjoint (b i) | F t] ω = 0 :=
    (condExp_restrict_ae_eq_restrict (hF t) (hAt t)
      ((hrows t i).integrable (by norm_num))).trans (ae_restrict_of_ae (hzero t i))
  have hs (t : ℕ) (i : I) :
      (∫ ω, ‖(operatorEquiv m n (N t ω)).adjoint (b i)‖ ^ 2 ∂P.restrict A)
        ≤ (Real.sqrt (P.real A) * σ i) ^ 2 := by
    simpa only [mul_pow, Real.sq_sqrt (measureReal_nonneg), mul_comm (P.real A)]
      using hlocal A hA t i
  have hh := weighted_row_martingale_second_moment (P := P.restrict A) b hF hmono hN
    (fun i => mul_nonneg (Real.sqrt_nonneg _) (hσ i))
    (fun t i => (hrows t i).mono_measure Measure.restrict_le_self) hadapt hz hs w T
  calc
    _ ≤ (∑ t ∈ Finset.range T, w t ^ 2) *
        (∑ i, Real.sqrt (P.real A) * σ i) ^ 2 := hh.2
    _ = ((∑ t ∈ Finset.range T, w t ^ 2) * (∑ i, σ i) ^ 2) * P.real A := by
      rw [← Finset.mul_sum, mul_pow, Real.sq_sqrt measureReal_nonneg]
      ring

lemma conditional_weighted_row_mean {Ω I : Type*}
    {m₀ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} [Fintype I]
    (b : OrthonormalBasis I ℝ (EuclideanSpace ℝ (Fin m)))
    {F : ℕ → MeasurableSpace Ω} (hF : ∀ t, F t ≤ m₀) (hmono : Monotone F)
    {N : ℕ → Ω → Space m n} (hN : ∀ t, Measurable (N t))
    {σ : I → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (hrows : ∀ t i, MemLp (fun ω => (operatorEquiv m n (N t ω)).adjoint (b i)) 2 P)
    (hadapt : ∀ t i, StronglyMeasurable[F (t + 1)]
      (fun ω => (operatorEquiv m n (N t ω)).adjoint (b i)))
    (hzero : ∀ t i, ∀ᵐ ω ∂P,
      P[fun ω => (operatorEquiv m n (N t ω)).adjoint (b i) | F t] ω = 0)
    (hsecond : ∀ t i, ∀ᵐ ω ∂P,
      P[fun u => ‖(operatorEquiv m n (N t u)).adjoint (b i)‖ ^ 2 | F t] ω ≤ σ i ^ 2)
    (w : ℕ → ℝ) (T : ℕ) :
    ∀ᵐ ω ∂P, P[fun u => nuclearNorm (∑ t ∈ Finset.range T, w t • N t u) | F 0] ω
      ≤ Real.sqrt (∑ t ∈ Finset.range T, w t ^ 2) * ∑ i, σ i := by
  have hlocal (A : Set Ω) (hA : MeasurableSet[F 0] A) (t : ℕ) (i : I) :
      (∫ ω in A, ‖(operatorEquiv m n (N t ω)).adjoint (b i)‖ ^ 2 ∂P)
        ≤ σ i ^ 2 * P.real A :=
    MatrixOracleMoments.local_integral_le_of_conditional_bound (hF t)
      (hrows t i).norm.integrable_sq (hsecond t i) (hmono (Nat.zero_le t) _ hA)
  have hg := weighted_row_martingale_second_moment b hF hmono hN hσ hrows hadapt hzero
    (fun t i => by simpa using hlocal Set.univ MeasurableSet.univ t i) w T
  have hc := conditional_weighted_row_second_moment b hF hmono hN hσ hrows hadapt hzero hlocal w T
  apply MatrixOracleMoments.conditional_mean_le_of_second_moment hg.1
    (mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun i _ => hσ i)))
  simpa only [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun t _ => sq_nonneg (w t)))] using hc

end LongTails.Proofs.MatrixCovariance
