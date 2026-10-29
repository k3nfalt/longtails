import LongTails.Proofs.CovarianceSoftCutOracle
import LongTails.Proofs.CovarianceSoftCutSelection
import LongTails.Proofs.HeavyTailedRayleighValidation

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutMom

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut
open LongTails.Proofs.CovarianceSoftCutOracle

lemma directionalMean_eq (q : Params) (n : ℕ) (u : Space q) (replies : Fin n → Space q) :
    directionalMean q n u replies = ⟪(1 / (n : ℝ)) • ∑ i, replies i, u⟫ := by
  simp only [directionalMean, real_inner_smul_left, sum_inner]

lemma directionalMean_failure (q : Params) (hd : 0 < q.d)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (x u : Space q) (hu : ‖u‖ ≤ 1) (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 < a)
    (hbatch : 8*q.σ^2 ≤ (q.d : ℝ)*n*a^2) :
    (Measure.pi fun _ : Fin n => p).real
      {ζ | a < |directionalMean q n u (fun i => g x (ζ i)) - ⟪v x, u⟫|} ≤ 1 / 4 := by
  let Q := Measure.pi fun _ : Fin n => p
  let error := fun ζ : Fin n → q.Ω => ⟪(1 / (n : ℝ)) • ∑ i, g x (ζ i) - v x, u⟫
  have hv := batch_directional_variance q p f v g hg x u n hn
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ζ : Fin n → q.Ω => sq_nonneg (error ζ))) hv.1 (a^2)
  have he (ζ : Fin n → q.Ω) : directionalMean q n u (fun i => g x (ζ i)) - ⟪v x, u⟫ = error ζ := by
    rw [directionalMean_eq]
    exact (inner_sub_left _ _ _).symm
  simp_rw [he]
  have hsub : {ζ : Fin n → q.Ω | a < |error ζ|} ⊆ {ζ | a^2 ≤ error ζ ^ 2} := by
    intro ζ hζ
    change a^2 ≤ error ζ^2
    have hh := sq_le_sq₀ ha.le (abs_nonneg (error ζ))
    simpa only [sq_abs] using hh.mpr hζ.le
  have hd' : 0 < (q.d : ℝ) := by exact_mod_cast hd
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hu2 : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hvar : q.σ^2*‖u‖^2 / (q.d*n) ≤ a^2/8 := by
    apply (div_le_iff₀ (by positivity : 0 < (q.d : ℝ)*n)).2
    have hσ := mul_le_mul_of_nonneg_left hu2 (sq_nonneg q.σ)
    nlinarith
  refine le_of_mul_le_mul_left ?_ (sq_pos_of_pos ha)
  calc
    a^2 * Q.real {ζ | a < |error ζ|} ≤ a^2 * Q.real {ζ | a^2 ≤ error ζ^2} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsub) (sq_nonneg a)
    _ ≤ ∫ ζ, error ζ^2 ∂Q := hm
    _ ≤ a^2/8 := hv.2.trans hvar
    _ ≤ a^2*(1/4) := by nlinarith [sq_nonneg a]

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma directionalMom_stream_failure (q : Params) (hd : 0 < q.d)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (x u : Space q) (hu : ‖u‖ ≤ 1) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (a : ℝ) (ha : 0 < a) (hbatch : 8*q.σ^2 ≤ (q.d : ℝ)*n*a^2) :
    (Measure.infinitePi fun _ : ℕ => p).real
      {ξ | a < |directionalMom q n m u (fun i => g x (ξ i)) - ⟪v x, u⟫|} ≤
        Real.exp (-(m : ℝ)/8) := by
  have hgm : Measurable (g x) := hg.measurable.comp (measurable_const.prodMk measurable_id)
  have hA : Measurable (fun ζ : Fin n → q.Ω => directionalMean q n u (fun i => g x (ζ i))) := by
    unfold directionalMean
    fun_prop
  exact HeavyTailedRayleighValidation.stream_median_probability p n m hm _ hA _ a
    (directionalMean_failure q hd p f v g hg x u hu n hn a ha hbatch)

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_directionalMomBlock (q : Params) (n m : ℕ) :
    Measurable (fun z : Space q × (Fin (n*m) → Space q) => directionalMomBlock q n m z.1 z.2) := by
  have hY : Measurable (fun z : Space q × (Fin (n*m) → Space q) =>
      fun j : Fin m => directionalMean q n z.1 (fun i => z.2 (groupIndex n m j i))) := by
    apply Measurable.of_eval
    intro j
    unfold directionalMean
    fun_prop
  exact (OracleTemplate.AdaptiveList.measurable_getD (m / 2) 0).comp
    (OracleTemplate.AdaptiveHeavyTailSimplex.measurable_mergeSort.comp
      ((OracleTemplate.AdaptiveList.measurable_ofFn m).comp hY))

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma directionalMom_block_failure (q : Params) (hd : 0 < q.d)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (x u : Space q) (hu : ‖u‖ ≤ 1) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (a : ℝ) (ha : 0 < a) (hbatch : 8*q.σ^2 ≤ (q.d : ℝ)*n*a^2) :
    (Measure.pi fun _ : Fin (n*m) => p).real
      {ζ | a < |directionalMomBlock q n m u (fun i => g x (ζ i)) - ⟪v x, u⟫|} ≤
        Real.exp (-(m : ℝ)/8) := by
  have hgm : Measurable (g x) := hg.measurable.comp (measurable_const.prodMk measurable_id)
  have hR : Measurable (fun ζ : Fin (n*m) → q.Ω => fun i : Fin (n*m) => g x (ζ i)) :=
    Measurable.of_eval (fun i => hgm.comp (measurable_pi_apply i))
  have hp : Measurable (fun ζ : Fin (n*m) → q.Ω => (u, fun i : Fin (n*m) => g x (ζ i))) :=
    measurable_const.prodMk hR
  have hM : Measurable (fun ζ : Fin (n*m) → q.Ω => directionalMomBlock q n m u (fun i => g x (ζ i))) := by
    simpa only [Function.comp_def] using (measurable_directionalMomBlock q n m).comp hp
  have hset : MeasurableSet {ζ : Fin (n*m) → q.Ω |
      a < |directionalMomBlock q n m u (fun i => g x (ζ i)) - ⟪v x, u⟫|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hM.sub_const _))
  have he := (OracleTemplate.StochasticGeneralized.prefix_preserving p (n*m)).measure_preimage
    hset.nullMeasurableSet
  have hb := directionalMom_stream_failure q hd p f v g hg x u hu n m hn hm a ha hbatch
  rw [measureReal_def, ← he]
  exact hb

end LongTails.Proofs.CovarianceSoftCutMom

