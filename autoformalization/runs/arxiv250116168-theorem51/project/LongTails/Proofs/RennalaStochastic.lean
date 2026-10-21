import LongTails.Algorithms.RennalaSgd
import LongTails.Proofs.GdConvex
import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.SgdConvex
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.GapStrongGrowthIteration
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.Rennala

variable {d : ℕ} {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]

lemma smooth_growth (f : Point d → ℝ) (L : ℝ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    (∀ x y, f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2) ∧
    (∀ x, |f x| ≤ |f 0| + ‖gradient f 0‖ * ‖x‖ + L / 2 * ‖x‖ ^ 2) ∧
    (∀ x, ‖gradient f x‖ ^ 2 ≤ 2 * ‖gradient f 0‖ ^ 2 + 2 * L ^ 2 * ‖x‖ ^ 2) := by
  set_option backward.isDefEq.respectTransparency false in
    exact (by
      refine ⟨Gradient.smooth_upper_bound hg hlip, ?_, ?_⟩
      · intro x
        have hn : ∀ y, HasGradientAt (fun z => -f z) (-gradient f y) y :=
        fun y => by
          rw [hasGradientAt_iff_hasFDerivAt]
          rw [map_neg]
          convert! (hg y).hasFDerivAt.neg using 1
        have hnlip : ∀ y z, ‖-gradient f y - -gradient f z‖ ≤ L * ‖y - z‖ := by
          intro y z
          have he : -gradient f y - -gradient f z = -(gradient f y - gradient f z) := by
            simp only [neg_sub_neg, neg_sub]
          rw [he, norm_neg]
          exact hlip y z
        have hu := Gradient.smooth_upper_bound hg hlip 0 x
        have hl := Gradient.smooth_upper_bound hn hnlip 0 x
        simp only [sub_zero, inner_neg_left] at hu hl
        have hi := real_inner_le_norm (gradient f 0) x
        have hni : -(inner ℝ (gradient f 0) x) ≤ ‖gradient f 0‖ * ‖x‖ := by
          simpa only [inner_neg_left, norm_neg] using real_inner_le_norm (-gradient f 0) x
        refine abs_le.mpr ⟨?_, ?_⟩
        · linarith [neg_le_abs (f 0)]
        · linarith [le_abs_self (f 0)]
      · intro x
        have hx := hlip x 0
        simp only [sub_zero] at hx
        have ht : ‖gradient f x‖ ≤ ‖gradient f x - gradient f 0‖ + ‖gradient f 0‖ := by
          simpa only [sub_add_cancel] using norm_add_le (gradient f x - gradient f 0) (gradient f 0)
        have hn : ‖gradient f x‖ ≤ ‖gradient f 0‖ + L * ‖x‖ := by linarith
        have hs := pow_le_pow_left₀ (norm_nonneg (gradient f x)) hn 2
        nlinarith [sq_nonneg (‖gradient f 0‖ - L * ‖x‖)]
    )


lemma batch_moments (f : Point d → ℝ) (g : Point d → Ω → Point d)
    (μ : ProbabilityMeasure Ω) (v : ℝ) (hv : 0 ≤ v)
    (ho : StochasticOracle Ω μ f g v) (S : ℕ) (hS : 0 < S) :
    let μS : ProbabilityMeasure (Fin S → Ω) :=
      ⟨Measure.pi (fun _ : Fin S => (μ : Measure Ω)), inferInstance⟩
    StochasticOracle (Fin S → Ω) μS f (batchEstimator S g) (v / (S : ℝ)) := by
  classical
  let ν : Measure (Fin S → Ω) := Measure.pi (fun _ : Fin S => (μ : Measure Ω))
  let : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  change LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point d) (Fin S → Ω) ν f
    (batchEstimator S g) (Real.sqrt (v / (S : ℝ)))
  have hl (i : Fin S) : HasLaw (fun seeds : Fin S → Ω => seeds i) (μ : Measure Ω) ν :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  have hgi (x : Point d) (i : Fin S) : Integrable (fun seeds : Fin S → Ω => g x (seeds i)) ν :=
    (hl i).integrable_comp (ho.integrable x)
  have hmean (x : Point d) (i : Fin S) :
      (∫ seeds, g x (seeds i) ∂ν) = gradient f x :=
    ((hl i).integral_comp (ho.integrable x).aestronglyMeasurable).trans (ho.unbiased x)
  have hvar (x : Point d) := RobustGradient.finite_mean_variance
    (ho.measurable.of_uncurry_left (x := x)) (ho.integrable x) (gradient f x)
    (ho.variance_integrable x) (ho.unbiased x) S hS
  have hSne : (S : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change Measurable (fun z : Point d × (Fin S → Ω) =>
      (1 / (S : ℝ)) • ∑ i, g z.1 (z.2 i))
    have hm (i : Fin S) : Measurable (fun z : Point d × (Fin S → Ω) => g z.1 (z.2 i)) :=
      ho.measurable.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
    exact (Finset.measurable_sum Finset.univ (fun i _ => hm i)).const_smul (1 / (S : ℝ))
  · intro x
    exact Integrable.smul (1 / (S : ℝ)) (integrable_finsetSum Finset.univ (fun i _ => hgi x i))
  · intro x
    change (∫ seeds, (1 / (S : ℝ)) • ∑ i, g x (seeds i) ∂ν) = gradient f x
    rw [integral_smul, integral_finsetSum _ (fun i _ => hgi x i)]
    simp_rw [hmean]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    rw [one_div_mul_cancel hSne, one_smul]
  · intro x
    exact (hvar x).1
  · intro x
    change (∫ seeds : Fin S → Ω,
      ‖(1 / (S : ℝ)) • ∑ i, g x (seeds i) - gradient f x‖ ^ 2 ∂ν) ≤
        (Real.sqrt (v / (S : ℝ))) ^ 2
    rw [Real.sq_sqrt (div_nonneg hv (Nat.cast_nonneg S)), (hvar x).2]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg S)
    simpa only [Real.sq_sqrt hv] using ho.variance x


lemma finite_moments (f : Point d → ℝ) (g : Point d → Ω → Point d)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω)
    (L v gamma : ℝ) (x0 : Point d) (S : ℕ) (hS : 0 < S)
    (hL : 0 < L) (hv : 0 ≤ v)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : StochasticOracle Ω μ f g v)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ)) (k : ℕ) :
    let x := fun ω => iterate g gamma S x0 (fun j => ξ j ω) k
    Measurable x ∧
    Integrable (fun ω => ‖x ω‖ ^ 2) (P : Measure Ξ) ∧
    Integrable (fun ω => f (x ω)) (P : Measure Ξ) ∧
    Integrable (fun ω => ‖gradient f (x ω)‖ ^ 2) (P : Measure Ξ) := by
  classical
  let ν : Measure (Fin S → Ω) := Measure.pi (fun _ : Fin S => (μ : Measure Ω))
  have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let μS : ProbabilityMeasure (Fin S → Ω) := ⟨ν, inferInstance⟩
  let A : Point d → (Fin S → Ω) → Point d := fun x b => x - gamma • batchEstimator S g x b
  have hsub (x y : Point d) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    have hn : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
    have hh := pow_le_pow_left₀ (norm_nonneg (x-y)) hn 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
  have hraw (x : Point d) : Integrable (fun a => ‖g x a‖ ^ 2) (μ : Measure Ω) ∧
      (∫ a, ‖g x a‖ ^ 2 ∂(μ : Measure Ω)) ≤ 2 * v + 2 * ‖gradient f x‖ ^ 2 := by
    have hb (a : Ω) : ‖g x a‖ ^ 2 ≤ 2 * ‖g x a - gradient f x‖ ^ 2 +
        2 * ‖gradient f x‖ ^ 2 := by
      simpa only [sub_neg_eq_add, sub_add_cancel, norm_neg] using
        hsub (g x a - gradient f x) (-gradient f x)
    have hi : Integrable (fun a => 2 * ‖g x a - gradient f x‖ ^ 2 +
        2 * ‖gradient f x‖ ^ 2) (μ : Measure Ω) :=
      ((ho.variance_integrable x).const_mul 2).add (integrable_const _)
    have hgi : Integrable (fun a => ‖g x a‖ ^ 2) (μ : Measure Ω) := by
      apply hi.mono' ((ho.measurable.of_uncurry_left (x := x)).norm.pow_const 2).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs, abs_sq] using hb a)
    refine ⟨hgi, ?_⟩
    have hh := integral_mono hgi hi hb
    rw [integral_add ((ho.variance_integrable x).const_mul 2) (integrable_const _), integral_const_mul] at hh
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    have hvx : (∫ a, ‖g x a - gradient f x‖ ^ 2 ∂(μ : Measure Ω)) ≤ v := by
      simpa only [Real.sq_sqrt hv] using ho.variance x
    linarith
  have hbatchm : Measurable (fun z : Point d × (Fin S → Ω) => batchEstimator S g z.1 z.2) := by
    exact (Finset.measurable_sum Finset.univ (fun i _ => ho.measurable.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))).const_smul (1 / (S : ℝ))
  have hA : Measurable (fun z : Point d × (Fin S → Ω) => A z.1 z.2) :=
    measurable_fst.sub (hbatchm.const_smul gamma)
  have hbatch (x : Point d) : Integrable (fun b => ‖batchEstimator S g x b‖ ^ 2) ν ∧
      (∫ b, ‖batchEstimator S g x b‖ ^ 2 ∂ν) ≤ 2 * v + 2 * ‖gradient f x‖ ^ 2 := by
    have hl (i : Fin S) : HasLaw (fun b : Fin S → Ω => b i) (μ : Measure Ω) ν :=
      ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
    have hgi (i : Fin S) : Integrable (fun b : Fin S → Ω => ‖g x (b i)‖ ^ 2) ν :=
      (hl i).integrable_comp (hraw x).1
    have hb (b : Fin S → Ω) : ‖batchEstimator S g x b‖ ^ 2 ≤
        (1 / (S : ℝ)) ^ 2 * ((S : ℝ) * ∑ i, ‖g x (b i)‖ ^ 2) := by
      have hn : ‖∑ i, g x (b i)‖ ≤ ∑ i, ‖g x (b i)‖ := norm_sum_le _ _
      have hp := pow_le_pow_left₀ (norm_nonneg (∑ i, g x (b i))) hn 2
      have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin S))
        (fun i => ‖g x (b i)‖) (fun _ => (1 : ℝ))
      simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hc
      change ‖(1 / (S : ℝ)) • ∑ i, g x (b i)‖ ^ 2 ≤ _
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      exact mul_le_mul_of_nonneg_left (hp.trans (by nlinarith [hc])) (sq_nonneg _)
    have hi : Integrable (fun b : Fin S → Ω =>
        (1 / (S : ℝ)) ^ 2 * ((S : ℝ) * ∑ i, ‖g x (b i)‖ ^ 2)) ν :=
      ((integrable_finsetSum Finset.univ (fun i _ => hgi i)).const_mul (S : ℝ)).const_mul _
    have hbi : Integrable (fun b => ‖batchEstimator S g x b‖ ^ 2) ν := by
      apply hi.mono' ((hbatchm.of_uncurry_left (x := x)).norm.pow_const 2).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun b => by simpa only [Real.norm_eq_abs, abs_sq] using hb b)
    refine ⟨hbi, ?_⟩
    have hh := integral_mono hbi hi hb
    rw [integral_const_mul, integral_const_mul, integral_finsetSum _ (fun i _ => hgi i)] at hh
    have he (i : Fin S) : (∫ b : Fin S → Ω, ‖g x (b i)‖ ^ 2 ∂ν) =
        ∫ a, ‖g x a‖ ^ 2 ∂(μ : Measure Ω) := (hl i).integral_comp (hraw x).1.aestronglyMeasurable
    simp_rw [he] at hh
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    have hs : (S : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hS
    have hc : (1 / (S : ℝ)) ^ 2 * ((S : ℝ) * ((S : ℝ) *
        (∫ a, ‖g x a‖ ^ 2 ∂(μ : Measure Ω)))) =
        ∫ a, ‖g x a‖ ^ 2 ∂(μ : Measure Ω) := by field_simp [hs]
    rw [hc] at hh
    exact hh.trans (hraw x).2
  have hstep (x : Point d) : Integrable (fun b => ‖A x b‖ ^ 2) ν ∧
      (∫ b, ‖A x b‖ ^ 2 ∂ν) ≤ (2 + 8 * gamma ^ 2 * L ^ 2) * ‖x‖ ^ 2 +
        (4 * gamma ^ 2 * v + 8 * gamma ^ 2 * ‖gradient f 0‖ ^ 2) := by
    have hb (b : Fin S → Ω) : ‖A x b‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * gamma ^ 2 * ‖batchEstimator S g x b‖ ^ 2 := by
      simpa only [A, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_assoc] using hsub x (gamma • batchEstimator S g x b)
    have hi : Integrable (fun b : Fin S → Ω => 2 * ‖x‖ ^ 2 + 2 * gamma ^ 2 * ‖batchEstimator S g x b‖ ^ 2) ν :=
      (integrable_const _).add ((hbatch x).1.const_mul _)
    have hai : Integrable (fun b => ‖A x b‖ ^ 2) ν := by
      apply hi.mono' ((hA.of_uncurry_left (x := x)).norm.pow_const 2).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun b => by simpa only [Real.norm_eq_abs, abs_sq] using hb b)
    refine ⟨hai, ?_⟩
    have hh := integral_mono hai hi hb
    rw [integral_add (integrable_const _) ((hbatch x).1.const_mul _)] at hh
    simp only [integral_const_mul] at hh
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    have hvx := mul_le_mul_of_nonneg_left (hbatch x).2 (by positivity : 0 ≤ 2 * gamma ^ 2)
    have hgx := mul_le_mul_of_nonneg_left ((smooth_growth f L hg hlip).2.2 x)
      (by positivity : 0 ≤ 4 * gamma ^ 2)
    nlinarith
  have hiter (m : ℕ) (seeds : ℕ → Ω) : iterate g gamma S x0 seeds m =
      ContinuizedSimilarQuasar.iterateSamples A m x0 (fun i j => seeds (i.val * S + j.val)) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [GapStrongGrowth.iterateSamples_succ_last]
      change iterate g gamma S x0 seeds m - gamma • batchEstimator S g
        (iterate g gamma S x0 seeds m) (fun i => seeds (m * S + i.val)) = _
      rw [ih]
      rfl
  have hcanon := StochasticGeneralized.infinitePi_iid (μ : Measure Ω)
  have hblocks := FiniteVariance.infinite_block_law (μ : Measure Ω)
    (Measure.infinitePi fun _ : ℕ => (μ : Measure Ω)) hcanon.independent hcanon.marginal S
  have hpres := ((StochasticGeneralized.prefix_preserving ν k).comp hblocks).comp hiid.stream_law
  have hmeas : Measurable (fun b => ContinuizedSimilarQuasar.iterateSamples A k x0 b) :=
    (GapStrongGrowth.iterateSamples_measurable hA k).comp (measurable_const.prodMk measurable_id)
  have hi := (GapStrongGrowth.iterateSamples_measurable_integral hA μS
    (fun x => ‖x‖ ^ 2) (by fun_prop) (fun _ => sq_nonneg _)
    (by positivity : 0 ≤ 2 + 8 * gamma ^ 2 * L ^ 2)
    hstep k x0).1
  have hx : Measurable (fun ω => iterate g gamma S x0 (fun j => ξ j ω) k) := by
    simp only [hiter]
    convert! hmeas.comp hpres.measurable using 1
  have hx2 : Integrable (fun ω => ‖iterate g gamma S x0 (fun j => ξ j ω) k‖ ^ 2) (P : Measure Ξ) := by
    simp only [hiter]
    convert! hpres.integrable_comp_of_integrable hi using 1
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).hasFDerivAt.continuousAt)
  have hgc : Continuous (gradient f) := (lipschitzWith_iff_norm_sub_le.mpr hlip :
    LipschitzWith ⟨L, hL.le⟩ (gradient f)).continuous
  have hxnorm : Integrable (fun ω => ‖iterate g gamma S x0 (fun j => ξ j ω) k‖) (P : Measure Ξ) := by
    exact (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
      ((memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mpr hx2)).norm
  refine ⟨hx, hx2, ?_, ?_⟩
  · apply (((integrable_const |f 0|).add (hxnorm.const_mul ‖gradient f 0‖)).add
      (hx2.const_mul (L / 2))).mono' (hfc.measurable.comp hx).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, Function.comp_def, Pi.add_apply] using (smooth_growth f L hg hlip).2.1
        (iterate g gamma S x0 (fun j => ξ j ω) k))
  · apply ((integrable_const (2 * ‖gradient f 0‖ ^ 2)).add
      (hx2.const_mul (2 * L ^ 2))).mono' ((hgc.measurable.comp hx).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, abs_sq, Function.comp_def, Pi.add_apply] using (smooth_growth f L hg hlip).2.2
        (iterate g gamma S x0 (fun j => ξ j ω) k))


lemma expected_descent (f : Point d → ℝ) (g : Point d → Ω → Point d)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω)
    (L v gamma lower : ℝ) (x0 : Point d)
    (hL : 0 < L) (hv : 0 ≤ v) (hgamma : 0 < gamma) (hgammaL : gamma ≤ 1 / L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (ho : StochasticOracle Ω μ f g v)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ)) (k : ℕ) :
    let x := fun j ω => iterate g gamma 1 x0 (fun i => ξ i ω) j
    (∫ ω, f (x (k + 1) ω) - lower ∂(P : Measure Ξ)) ≤
      (∫ ω, f (x k ω) - lower ∂(P : Measure Ξ)) -
        gamma / 2 * (∫ ω, ‖gradient f (x k ω)‖ ^ 2 ∂(P : Measure Ξ)) +
        L * gamma ^ 2 * v / 2 := by
  classical
  let advance : Point d → Ω → Point d := fun x a => x - gamma • g x a
  have ha : Measurable (fun z : Point d × Ω => advance z.1 z.2) :=
    measurable_fst.sub (ho.measurable.const_smul gamma)
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hg x).hasFDerivAt.continuousAt)
  have hgc : Continuous (gradient f) := (lipschitzWith_iff_norm_sub_le.mpr hlip :
    LipschitzWith ⟨L, hL.le⟩ (gradient f)).continuous
  let Q : ProbabilityMeasure (ℕ → Ω) := ⟨Measure.infinitePi (fun _ : ℕ => (μ : Measure Ω)), inferInstance⟩
  have hcanon := StochasticGeneralized.infinitePi_iid (μ : Measure Ω)
  have heval : MeasurePreserving (fun a : ℕ → Ω => a 0) (Q : Measure (ℕ → Ω)) (μ : Measure Ω) :=
    ⟨measurable_pi_apply 0, Measure.infinitePi_map_eval _ _⟩
  have hfixed (x : Point d) : Integrable (fun a => f (advance x a) - lower) (μ : Measure Ω) := by
    have hmi : Integrable (fun a : ℕ → Ω => f (iterate g gamma 1 x a 1)) (Q : Measure (ℕ → Ω)) :=
      (finite_moments f g μ Q (fun i a => a i) L v gamma x 1 (by norm_num) hL hv hg hlip ho hcanon 1).2.2.1
    have hm : Integrable (fun a : ℕ → Ω => f (iterate g gamma 1 x a 1) - lower) (Q : Measure (ℕ → Ω)) :=
      hmi.sub (integrable_const lower)
    apply (heval.integrable_comp ((hfc.measurable.comp (ha.of_uncurry_left (x := x))).sub_const lower).aestronglyMeasurable).mp
    dsimp only [iterate, batchEstimator] at hm
    simpa only [Function.comp_def, Pi.sub_apply, Fin.sum_univ_one, Nat.cast_one,
      div_one, one_smul, Nat.zero_mul, Fin.val_zero, Nat.zero_add, advance] using hm
  have hstep (x : Point d) : (∫ a, f (advance x a) - lower ∂(μ : Measure Ω)) ≤
      f x - lower - gamma / 2 * ‖gradient f x‖ ^ 2 + L * gamma ^ 2 * v / 2 := by
    have he (a : Ω) : ‖g x a‖ ^ 2 = ‖g x a - gradient f x‖ ^ 2 +
        2 * inner ℝ (gradient f x) (g x a) - ‖gradient f x‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_comm (g x a) (gradient f x)]
      ring
    have hinner : Integrable (fun a => inner ℝ (gradient f x) (g x a)) (μ : Measure Ω) :=
      (ho.integrable x).const_inner _
    have hg2 : Integrable (fun a => ‖g x a‖ ^ 2) (μ : Measure Ω) := by
      simp_rw [he]
      exact ((ho.variance_integrable x).add (hinner.const_mul 2)).sub (integrable_const _)
    have heg : (∫ a, ‖g x a‖ ^ 2 ∂(μ : Measure Ω)) =
        (∫ a, ‖g x a - gradient f x‖ ^ 2 ∂(μ : Measure Ω)) + ‖gradient f x‖ ^ 2 := by
      simp_rw [he]
      have hsum : Integrable (fun a => ‖g x a - gradient f x‖ ^ 2 +
          2 * inner ℝ (gradient f x) (g x a)) (μ : Measure Ω) :=
        (ho.variance_integrable x).add (hinner.const_mul 2)
      rw [integral_sub hsum (integrable_const _),
        integral_add (ho.variance_integrable x) (hinner.const_mul 2), integral_const_mul,
        integral_inner (ho.integrable x), ho.unbiased]
      simp only [real_inner_self_eq_norm_sq, integral_const, probReal_univ, one_smul]
      ring
    have hgb : (∫ a, ‖g x a‖ ^ 2 ∂(μ : Measure Ω)) ≤ v + ‖gradient f x‖ ^ 2 := by
      rw [heg]
      exact add_le_add (by simpa only [Real.sq_sqrt hv] using ho.variance x) (le_refl _)
    have hp (a : Ω) : f (advance x a) - lower ≤ f x - lower -
        gamma * inner ℝ (gradient f x) (g x a) + (L * gamma ^ 2 / 2) * ‖g x a‖ ^ 2 := by
      have hh := (smooth_growth f L hg hlip).1 x (advance x a)
      have hd : advance x a - x = -(gamma • g x a) := by dsimp [advance]; module
      rw [hd, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
        mul_pow, sq_abs] at hh
      nlinarith
    have hbi : Integrable (fun a => f x - lower - gamma * inner ℝ (gradient f x) (g x a) +
        (L * gamma ^ 2 / 2) * ‖g x a‖ ^ 2) (μ : Measure Ω) :=
      ((integrable_const _).sub (hinner.const_mul gamma)).add (hg2.const_mul _)
    have hh := integral_mono (hfixed x) hbi hp
    have hlinear : Integrable (fun a => f x - lower - gamma * inner ℝ (gradient f x) (g x a))
        (μ : Measure Ω) := (integrable_const _).sub (hinner.const_mul gamma)
    rw [integral_add hlinear (hg2.const_mul _),
      integral_sub (integrable_const _) (hinner.const_mul gamma)] at hh
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul,
      integral_inner (ho.integrable x), ho.unbiased, real_inner_self_eq_norm_sq] at hh
    have hvx := mul_le_mul_of_nonneg_left hgb (by positivity : 0 ≤ L * gamma ^ 2 / 2)
    have hgl : gamma * L ≤ 1 := (le_div_iff₀ hL).mp hgammaL
    have hc : L * gamma ^ 2 / 2 ≤ gamma / 2 := by nlinarith
    have hcx := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖gradient f x‖)
    nlinarith
  have hiter (m : ℕ) (seeds : ℕ → Ω) : iterate g gamma 1 x0 seeds m =
      ContinuizedSimilarQuasar.iterateSamples advance m x0 (fun i => seeds i.val) := by
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [GapStrongGrowth.iterateSamples_succ_last]
      dsimp only [iterate, batchEstimator]
      simp only [ Fin.sum_univ_one, Nat.cast_one, div_one, one_smul,
        Nat.mul_one, Fin.val_zero, Nat.add_zero, ih]
      rfl
  let X : (Fin k → Ω) → Point d := ContinuizedSimilarQuasar.iterateSamples advance k x0
  have hXm : Measurable X := (GapStrongGrowth.iterateSamples_measurable ha k).comp
    (measurable_const.prodMk measurable_id)
  let ρ : Measure (Fin k → Ω) := Measure.pi (fun _ : Fin k => (μ : Measure Ω))
  have : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have hp : MeasurePreserving (fun ω => (fun i : Fin k => ξ i ω)) (P : Measure Ξ) ρ :=
    (StochasticGeneralized.prefix_preserving (μ : Measure Ω) k).comp hiid.stream_law
  have hpair : MeasurePreserving (fun ω => ((fun i : Fin k => ξ i ω), ξ k ω))
      (P : Measure Ξ) (ρ.prod (μ : Measure Ω)) := by
    have ht := ((MeasurePreserving.id ρ).prod heval).comp (hiid.prefix_tail_law k)
    simpa only [Function.comp_def, Prod.map_apply, id_eq, Nat.add_zero] using ht
  have hx (ω : Ξ) : X (fun i => ξ i ω) = iterate g gamma 1 x0 (fun j => ξ j ω) k :=
    (hiter k (fun j => ξ j ω)).symm
  have hnext (ω : Ξ) : advance (X (fun i => ξ i ω)) (ξ k ω) =
      iterate g gamma 1 x0 (fun j => ξ j ω) (k+1) := by
    rw [hx]
    dsimp only [advance, iterate, batchEstimator]
    simp only [ Fin.sum_univ_one, Nat.cast_one, div_one,
      one_smul, Nat.mul_one, Fin.val_zero, Nat.add_zero]
  have hmk := finite_moments f g μ P ξ L v gamma x0 1 (by norm_num) hL hv hg hlip ho hiid k
  have hmk1 := finite_moments f g μ P ξ L v gamma x0 1 (by norm_num) hL hv hg hlip ho hiid (k+1)
  have hprei : Integrable (fun b => f (X b) - lower) ρ := by
    apply (hp.integrable_comp ((hfc.measurable.comp hXm).sub_const lower).aestronglyMeasurable).mp
    have hh : Integrable (fun ω => f (iterate g gamma 1 x0 (fun j => ξ j ω) k) - lower) (P : Measure Ξ) :=
      Integrable.sub hmk.2.2.1 (integrable_const lower)
    simpa only [Function.comp_def, hx] using hh
  have hgri : Integrable (fun b => ‖gradient f (X b)‖ ^ 2) ρ := by
    apply (hp.integrable_comp ((hgc.measurable.comp hXm).norm.pow_const 2).aestronglyMeasurable).mp
    simpa only [Function.comp_def, hx] using hmk.2.2.2
  let F : (Fin k → Ω) × Ω → ℝ := fun z => f (advance (X z.1) z.2) - lower
  have hFm : Measurable F := (hfc.measurable.comp
    (ha.comp ((hXm.comp measurable_fst).prodMk measurable_snd))).sub_const lower
  have hFi : Integrable F (ρ.prod (μ : Measure Ω)) := by
    apply (hpair.integrable_comp hFm.aestronglyMeasurable).mp
    have hh : Integrable (fun ω => f (iterate g gamma 1 x0 (fun j => ξ j ω) (k+1)) - lower) (P : Measure Ξ) :=
      Integrable.sub hmk1.2.2.1 (integrable_const lower)
    simpa only [Function.comp_def, F, hnext] using hh
  have hprelaw : HasLaw (fun ω => (fun i : Fin k => ξ i ω)) ρ (P : Measure Ξ) :=
    ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  have hpairlaw : HasLaw (fun ω => ((fun i : Fin k => ξ i ω), ξ k ω))
      (ρ.prod (μ : Measure Ω)) (P : Measure Ξ) := ⟨hpair.measurable.aemeasurable, hpair.map_eq⟩
  have heF : (∫ ω, f (iterate g gamma 1 x0 (fun j => ξ j ω) (k+1)) - lower ∂(P : Measure Ξ)) =
      ∫ z, F z ∂(ρ.prod (μ : Measure Ω)) := by
    simpa only [Function.comp_def, F, hnext] using hpairlaw.integral_comp hFi.aestronglyMeasurable
  have hepre : (∫ ω, f (iterate g gamma 1 x0 (fun j => ξ j ω) k) - lower ∂(P : Measure Ξ)) =
      ∫ b, f (X b) - lower ∂ρ := by
    simpa only [Function.comp_def, hx] using hprelaw.integral_comp hprei.aestronglyMeasurable
  have hegr : (∫ ω, ‖gradient f (iterate g gamma 1 x0 (fun j => ξ j ω) k)‖ ^ 2 ∂(P : Measure Ξ)) =
      ∫ b, ‖gradient f (X b)‖ ^ 2 ∂ρ := by
    simpa only [Function.comp_def, hx] using hprelaw.integral_comp hgri.aestronglyMeasurable
  change (∫ ω, f (iterate g gamma 1 x0 (fun j => ξ j ω) (k+1)) - lower ∂(P : Measure Ξ)) ≤ _
  rw [heF, hepre, hegr, integral_prod _ hFi]
  have hlinear : Integrable (fun b => f (X b) - lower - gamma / 2 * ‖gradient f (X b)‖ ^ 2) ρ :=
    hprei.sub (hgri.const_mul (gamma / 2))
  have hboundi : Integrable (fun b => f (X b) - lower - gamma / 2 * ‖gradient f (X b)‖ ^ 2 +
      L * gamma ^ 2 * v / 2) ρ := hlinear.add (integrable_const _)
  have hbound := integral_mono hFi.integral_prod_left hboundi
    (fun b => hstep (X b))
  simpa only [integral_add hlinear (integrable_const _),
    integral_sub hprei (hgri.const_mul (gamma / 2)), integral_const_mul,
    integral_const, probReal_univ, one_smul] using hbound


lemma classical_sgd (f : Point d → ℝ) (g : Point d → Ω → Point d)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω)
    (L v eps Delta lower : ℝ) (x0 : Point d)
    (hL : 0 < L) (hv : 0 ≤ v) (heps : 0 < eps)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hlower : ∀ x, lower ≤ f x) (hgap : f x0 - lower = Delta)
    (ho : StochasticOracle Ω μ f g v)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ)) :
    (∀ (gamma : ℝ), 0 < gamma → gamma ≤ 1 / L → ∀ (K : ℕ), 0 < K →
      (1 / (K : ℝ)) * ∑ k ∈ Finset.range K,
        (∫ ω, ‖gradient f (iterate g gamma 1 x0 (fun j => ξ j ω) k)‖ ^ 2 ∂(P : Measure Ξ)) ≤
          2 * Delta / (gamma * K) + L * gamma * v) ∧
    (let gamma := if v = 0 then 1 / L else min (1 / L) (eps / (2 * L * v))
     ∀ (K : ℕ), 0 < K → 4 * Delta * L / eps + 8 * Delta * L * v / eps ^ 2 ≤ (K : ℝ) →
       (1 / (K : ℝ)) * ∑ k ∈ Finset.range K,
         (∫ ω, ‖gradient f (iterate g gamma 1 x0 (fun j => ξ j ω) k)‖ ^ 2 ∂(P : Measure Ξ)) ≤ eps) := by
  classical
  have hDelta : 0 ≤ Delta := by rw [← hgap]; exact sub_nonneg.mpr (hlower x0)
  have hgeneral (gamma : ℝ) (hgamma : 0 < gamma) (hgammaL : gamma ≤ 1 / L)
      (K : ℕ) (hK : 0 < K) :
      (1 / (K : ℝ)) * ∑ k ∈ Finset.range K,
        (∫ ω, ‖gradient f (iterate g gamma 1 x0 (fun j => ξ j ω) k)‖ ^ 2 ∂(P : Measure Ξ)) ≤
          2 * Delta / (gamma * K) + L * gamma * v := by
    let F : ℕ → ℝ := fun k => ∫ ω, f (iterate g gamma 1 x0 (fun j => ξ j ω) k) - lower ∂(P : Measure Ξ)
    let G : ℕ → ℝ := fun k => ∫ ω, ‖gradient f (iterate g gamma 1 x0 (fun j => ξ j ω) k)‖ ^ 2 ∂(P : Measure Ξ)
    have hstep (k : ℕ) : F (k+1) ≤ F k - gamma / 2 * G k + L * gamma ^ 2 * v / 2 :=
      expected_descent f g μ P ξ L v gamma lower x0 hL hv hgamma hgammaL hg hlip ho hiid k
    have hzero : F 0 = Delta := by
      dsimp only [F, iterate]
      simp only [integral_const, probReal_univ, one_smul, hgap]
    have hnonneg (k : ℕ) : 0 ≤ F k := integral_nonneg (fun ω => sub_nonneg.mpr (hlower _))
    have hsum (m : ℕ) : gamma / 2 * ∑ k ∈ Finset.range m, G k ≤
        F 0 - F m + (m : ℝ) * (L * gamma ^ 2 * v / 2) := by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
        have hs := hstep m
        nlinarith
    have ht := hsum K
    rw [hzero] at ht
    have hd : (∑ k ∈ Finset.range K, G k) ≤
        (2 * Delta + L * gamma ^ 2 * v * K) / gamma := by
      apply (le_div_iff₀ hgamma).mpr
      nlinarith [hnonneg K]
    have hKr : (0 : ℝ) < K := by exact_mod_cast hK
    have hm := div_le_div_of_nonneg_right hd hKr.le
    convert hm using 1
    · dsimp [G]; ring
    · field_simp
  refine ⟨hgeneral, ?_⟩
  dsimp only
  intro K hK hb
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  by_cases hv0 : v = 0
  · simp only [hv0, ↓reduceIte] at *
    have hh := hgeneral (1/L) (one_div_pos.mpr hL) le_rfl K hK
    simp only [mul_zero, zero_div, add_zero] at hh hb
    apply hh.trans
    apply (div_le_iff₀ (mul_pos (one_div_pos.mpr hL) hKr)).mpr
    have hb' := (div_le_iff₀ heps).mp hb
    have he : eps * ((1 / L) * (K : ℝ)) * L = eps * K := by field_simp
    have hh2 : 2 * Delta * L ≤ eps * K := by nlinarith
    nlinarith
  · have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
    let gamma := min (1 / L) (eps / (2 * L * v))
    have hgamma : 0 < gamma := lt_min (one_div_pos.mpr hL) (div_pos heps (by positivity))
    have hgammaL : gamma ≤ 1 / L := min_le_left _ _
    have hnoise : L * gamma * v ≤ eps / 2 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 2 * L * v)).mp (min_le_right (1 / L) (eps / (2 * L * v)))
      change gamma * (2 * L * v) ≤ eps at hh
      nlinarith
    have hfirst : 2 * Delta / (gamma * K) ≤ eps / 2 := by
      apply (div_le_iff₀ (mul_pos hgamma hKr)).mpr
      by_cases hcase : 1 / L ≤ eps / (2 * L * v)
      · have hgamm : gamma = 1 / L := min_eq_left hcase
        have ha : 0 ≤ 8 * Delta * L * v / eps ^ 2 := by positivity
        have hb' : 4 * Delta * L ≤ (K : ℝ) * eps := (div_le_iff₀ heps).mp (by linarith [ha] : 4 * Delta * L / eps ≤ (K : ℝ))
        rw [hgamm]
        apply (mul_le_mul_iff_right₀ hL).mp
        have he : (eps / 2 * ((1 / L) * (K : ℝ))) * L = eps * K / 2 := by field_simp
        nlinarith [he]
      · have hgamm : gamma = eps / (2 * L * v) := min_eq_right (le_of_not_ge hcase)
        have ha : 0 ≤ 4 * Delta * L / eps := by positivity
        have hb' : 8 * Delta * L * v ≤ (K : ℝ) * eps ^ 2 :=
          (div_le_iff₀ (sq_pos_of_pos heps)).mp (by linarith [ha] : 8 * Delta * L * v / eps ^ 2 ≤ (K : ℝ))
        rw [hgamm]
        apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * L * v)).mp
        have he : (eps / 2 * ((eps / (2 * L * v)) * (K : ℝ))) * (2 * L * v) = eps ^ 2 * K / 2 := by field_simp
        nlinarith [he]
    have hh := hgeneral gamma hgamma hgammaL K hK
    simp only [hv0, ↓reduceIte]
    exact hh.trans (by linarith)


lemma iteration_accuracy (f : Point d → ℝ) (g : Point d → Ω → Point d)
    (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure Ξ) (ξ : ℕ → Ξ → Ω)
    (L v eps Delta lower : ℝ) (x0 : Point d)
    (hL : 0 < L) (hv : 0 ≤ v) (heps : 0 < eps)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hlower : ∀ x, lower ≤ f x) (hgap : f x0 - lower = Delta)
    (ho : StochasticOracle Ω μ f g v)
    (hiid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ (μ : Measure Ω) (P : Measure Ξ))
    (K : ℕ) (hK : 0 < K) (hbudget : 24 * Delta * L / eps ≤ (K : ℝ)) :
    (1 / (K : ℝ)) * ∑ k ∈ Finset.range K,
      (∫ ω, ‖gradient f (iterate g (stepSize L v eps) (batchSize v eps) x0
        (fun j => ξ j ω) k)‖ ^ 2 ∂(P : Measure Ξ)) ≤ eps := by
  classical
  let S := batchSize v eps
  have hS : 0 < S := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  let ν : Measure (Fin S → Ω) := Measure.pi (fun _ : Fin S => (μ : Measure Ω))
  have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let μS : ProbabilityMeasure (Fin S → Ω) := ⟨ν, inferInstance⟩
  let η : ℕ → Ξ → (Fin S → Ω) := fun k ω i => ξ (k * S + i.val) ω
  have hcanon := StochasticGeneralized.infinitePi_iid (μ : Measure Ω)
  have hblocks := FiniteVariance.infinite_block_law (μ : Measure Ω)
    (Measure.infinitePi fun _ : ℕ => (μ : Measure Ω)) hcanon.independent hcanon.marginal S
  have hp : MeasurePreserving (fun ω k => η k ω) (P : Measure Ξ)
      (Measure.infinitePi fun _ : ℕ => ν) := hblocks.comp hiid.stream_law
  have hm (k : ℕ) : Measurable (η k) := Measurable.of_eval (fun i => hiid.measurable _)
  have hmarg (k : ℕ) : (P : Measure Ξ).map (η k) = ν := by
    have heval : MeasurePreserving (fun b : ℕ → (Fin S → Ω) => b k)
        (Measure.infinitePi fun _ : ℕ => ν) ν :=
      ⟨measurable_pi_apply k, Measure.infinitePi_map_eval _ _⟩
    exact (heval.comp hp).map_eq
  have hη : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID η ν (P : Measure Ξ) := by
    refine ⟨hm, ?_, hmarg⟩
    apply (iIndepFun_iff_map_fun_eq_infinitePi_map hm).mpr
    simpa only [hmarg] using hp.map_eq
  have hoS : StochasticOracle (Fin S → Ω) μS f (batchEstimator S g) (v / (S : ℝ)) :=
    batch_moments f g μ v hv ho S hS
  have hvS : 0 ≤ v / (S : ℝ) := div_nonneg hv hSr.le
  have hSbound : v / (S : ℝ) ≤ eps := by
    have hh : v / eps ≤ (S : ℝ) := (Nat.le_ceil (v / eps)).trans (by
      exact_mod_cast (le_max_left ⌈v / eps⌉₊ 1))
    apply (div_le_iff₀ hSr).mpr
    have ht := (div_le_iff₀ heps).mp hh
    nlinarith
  have hDelta : 0 ≤ Delta := by rw [← hgap]; exact sub_nonneg.mpr (hlower x0)
  have hthreshold : 4 * Delta * L / eps + 8 * Delta * L * (v / (S : ℝ)) / eps ^ 2 ≤ (K : ℝ) := by
    have ht : 8 * Delta * L * (v / (S : ℝ)) / eps ^ 2 ≤ 8 * Delta * L / eps := by
      apply (div_le_iff₀ (sq_pos_of_pos heps)).mpr
      have hh := mul_le_mul_of_nonneg_left hSbound (by positivity : 0 ≤ 8 * Delta * L)
      have he : (8 * Delta * L / eps) * eps ^ 2 = 8 * Delta * L * eps := by field_simp
      nlinarith
    have hz : 0 ≤ Delta * L / eps := by positivity
    have hlin : 4 * Delta * L / eps + 8 * Delta * L / eps ≤ 24 * Delta * L / eps := by
      have h4 : 4 * Delta * L / eps = 4 * (Delta * L / eps) := by ring
      have h8 : 8 * Delta * L / eps = 8 * (Delta * L / eps) := by ring
      have h24 : 24 * Delta * L / eps = 24 * (Delta * L / eps) := by ring
      rw [h4, h8, h24]
      nlinarith
    exact (add_le_add (le_refl _) ht).trans (hlin.trans hbudget)
  have hgamma : (if v / (S : ℝ) = 0 then 1 / L else min (1 / L) (eps / (2 * L * (v / (S : ℝ))))) =
      stepSize L v eps := by
    dsimp only [stepSize]
    by_cases hv0 : v = 0
    · simp only [hv0, zero_div, ↓reduceIte]
    · have hnz : v / (S : ℝ) ≠ 0 := div_ne_zero hv0 (ne_of_gt hSr)
      simp only [hnz, hv0, ↓reduceIte]
      congr 1
      change eps / (2 * L * (v / (S : ℝ))) = eps * (S : ℝ) / (2 * L * v)
      field_simp
  have htraj (m : ℕ) (ω : Ξ) :
      iterate (batchEstimator S g) (stepSize L v eps) 1 x0 (fun j => η j ω) m =
        iterate g (stepSize L v eps) S x0 (fun j => ξ j ω) m := by
    induction m with
    | zero => rfl
    | succ m ih =>
      dsimp only [iterate, batchEstimator]
      simp only [ Fin.sum_univ_one, Nat.cast_one, div_one,
        one_smul, Nat.mul_one, Fin.val_zero, Nat.add_zero, ih]
      rfl
  have hh := (classical_sgd f (batchEstimator S g) μS P η L (v / (S : ℝ)) eps Delta lower x0
    hL hvS heps hg hlip hlower hgap hoS hη).2 K hK hthreshold
  rw [hgamma] at hh
  simpa only [htraj] using hh


end OracleTemplate.Rennala
