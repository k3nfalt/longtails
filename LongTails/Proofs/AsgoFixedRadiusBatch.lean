import LongTails.Proofs.AsgoFixedRadiusGeometry
import LongTails.Proofs.RipmConditional
import LongTails.Proofs.AdaptiveIID
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Integrable
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Matrix OracleTemplate.Muon
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace OracleTemplate.AsgoFixedRadius

open LongTails.Setups.AsgoFixedRadius

lemma prefix_batch_independent {Ξ Ω : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ξ) (P : ProbabilityMeasure Ω) (ξ : ℕ → Ω → Ξ)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ μ.toMeasure P.toMeasure) (M t : ℕ) :
    IndepFun (fun ω (i : Fin (t * M)) => ξ i ω)
      (fun ω (j : Fin M) => ξ (t * M + j) ω) P.toMeasure := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    have h := hξ.prefix_tail_independent (t * M)
    have hr : Measurable (fun s : ℕ → Ξ => fun j : Fin M => s j) :=
      Measurable.of_eval (fun j => measurable_pi_apply (j : ℕ))
    simpa only [Function.comp_def, id_eq] using h.comp measurable_id hr
  )

lemma batch_noise_memLp (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (hM : 1 ≤ p.M) (t : ℕ) (X : Ω → Mat p.m p.n)
    (hX : @Measurable Ω (Mat p.m p.n)
      (MeasurableSpace.comap (fun ω (i : Fin (t * p.M)) => ξ i ω) inferInstance)
      inferInstance X)
    (F : ℝ) (hF : 0 ≤ F) (hbound : ∀ᵐ ω ∂P.toMeasure, ‖X ω - Wstar‖ ≤ F) :
    MemLp (fun ω => Core.batchGradient p I.g (fun j => ξ j ω) t (X ω)) 2 P.toMeasure ∧
      MemLp (fun ω => Core.batchGradient p I.g (fun j => ξ j ω) t (X ω) - I.H (X ω)) 2 P.toMeasure := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    classical
    have hGram {m n : ℕ} {Ω' : Type} [MeasurableSpace Ω'] (μ : Measure Ω')
        (X : Ω' → Mat m n) (hX : MemLp X 2 μ) :
        Integrable (fun ω => Core.gram (X ω)) μ := by
      classical
      let J : Mat m n →L[ℝ] Matrix (Fin m) (Fin n) ℝ :=
        LinearMap.toContinuousLinearMap
          { toFun := toMatrix, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      let K : Mat m n →L[ℝ] Matrix (Fin n) (Fin m) ℝ :=
        LinearMap.toContinuousLinearMap
          { toFun := fun Y => (toMatrix Y)ᵀ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      have hj : MemLp (fun ω => J (X ω)) 2 μ := hX.of_le_mul
        (J.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun ω => J.le_opNorm (X ω)))
      have hk : MemLp (fun ω => K (X ω)) 2 μ := hX.of_le_mul
        (K.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun ω => K.le_opNorm (X ω)))
      have hp : MemLp (fun ω => J (X ω)*K (X ω)) 1 μ :=
        MemLp.of_bilin (fun (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) => A*B)
          1 hj hk (continuous_fst.matrix_mul continuous_snd)
          (Filter.Eventually.of_forall (fun ω => by
            simpa only [one_mul] using Matrix.l2_opNNNorm_mul (J (X ω)) (K (X ω))))
      exact memLp_one_iff_integrable.1 hp
    have hWeight {m n : ℕ} {Ω' : Type} [MeasurableSpace Ω'] (μ : Measure Ω')
        (X : Ω' → Mat m n) (K : Matrix (Fin m) (Fin m) ℝ)
        (hGram : Integrable (fun ω => Core.gram (X ω)) μ) :
        Integrable (fun ω => Core.weightedQuadratic K (X ω)) μ ∧
          (∫ ω, Core.weightedQuadratic K (X ω) ∂μ) =
            ((∫ ω, Core.gram (X ω) ∂μ) * K).trace := by
      classical
      let L : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] ℝ :=
        { toFun := fun A => (A*K).trace
          map_add' := by intro A B; rw [Matrix.add_mul,Matrix.trace_add]
          map_smul' := by intro c A; simp only [Matrix.smul_mul,Matrix.trace_smul,RingHom.id_apply] }
      let C := LinearMap.toContinuousLinearMap L
      have he (Y : Mat m n) : Core.weightedQuadratic K Y=C (Core.gram Y) := by
        change ((toMatrix Y)ᵀ*K*toMatrix Y).trace=(toMatrix Y*(toMatrix Y)ᵀ*K).trace
        rw [Matrix.trace_mul_cycle]
      simp_rw [he]
      exact ⟨C.integrable_comp hGram,C.integral_comp_comm hGram⟩
    have hpoint (x : Mat p.m p.n) :
        (∫ s, ‖I.g x s - I.H x‖ ^ 2 ∂I.law.toMeasure) ≤ (I.V * I.V).trace := by
      have hmeas : Measurable (fun s => I.g x s - I.H x) :=
        (hS.gradientMeasurable.comp (measurable_const.prodMk measurable_id)).sub measurable_const
      have hlp : MemLp (fun s => I.g x s - I.H x) 2 I.law.toMeasure :=
        (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).2 (hS.noiseSquareIntegrable x)
      have hi := hWeight I.law.toMeasure (fun s => I.g x s - I.H x) 1
        (hGram I.law.toMeasure _ hlp)
      have he (Y : Mat p.m p.n) : Core.weightedQuadratic 1 Y = ‖Y‖ ^ 2 := by
        change ((toMatrix Y)ᵀ * (1 : Matrix (Fin p.m) (Fin p.m) ℝ) * toMatrix Y).trace = _
        rw [Matrix.mul_one, ← inner_trace, real_inner_self_eq_norm_sq]
      simp only [he, Matrix.mul_one] at hi
      have hc := (hS.covariance x).trace_nonneg
      rw [Matrix.trace_sub] at hc
      rw [hi.2]
      exact sub_nonneg.mp hc
    let block : Ω → (Fin p.M → I.Sample) := fun ω j => ξ (t * p.M + j) ω
    have hblock : Measurable block :=
      Measurable.of_eval (fun j => hξ.measurable (t * p.M + j))
    have hpre : Measurable (fun ω (i : Fin (t * p.M)) => ξ i ω) :=
      Measurable.of_eval (fun i => hξ.measurable i)
    have hXm : Measurable X := hX.mono hpre.comap_le le_rfl
    have hbi := hξ.independent.precomp
      (g := fun j : Fin p.M => t * p.M + j.val)
      (by intro j k hjk; apply Fin.ext; exact Nat.add_left_cancel hjk)
    have hblaw : P.toMeasure.map block =
        Measure.pi (fun _ : Fin p.M => I.law.toMeasure) := by
      have hh := hbi.map_fun_eq_pi_map
        (fun j : Fin p.M => (hξ.measurable (t * p.M + j)).aemeasurable)
      simpa only [hξ.marginal] using hh
    have hpb := prefix_batch_independent I.law P ξ hξ p.M t
    have hxb : IndepFun X block P.toMeasure :=
      indep_of_indep_of_le hpb hX.comap_le le_rfl
    have hpairlaw : P.toMeasure.map (fun ω => (X ω, block ω)) =
        (P.toMeasure.map X).prod (Measure.pi (fun _ : Fin p.M => I.law.toMeasure)) := by
      rw [hxb.map_prod_eq_prod_map_map hXm.aemeasurable hblock.aemeasurable, hblaw]
    let q : Mat p.m p.n × I.Sample → ℝ :=
      fun y => ‖I.g y.1 y.2 - I.H y.1‖ ^ 2
    have hHm : Measurable (fun ω => I.H (X ω)) :=
      (gradient_continuous I Wstar hS).measurable.comp hXm
    have hqm : Measurable q :=
      (hS.gradientMeasurable.sub
        ((gradient_continuous I Wstar hS).measurable.comp measurable_fst)).norm.pow_const 2
    have hprodI : Integrable q
        ((P.toMeasure.map X).prod I.law.toMeasure) := by
      apply (integrable_prod_iff hqm.aestronglyMeasurable).2
      constructor
      · exact Filter.Eventually.of_forall hS.noiseSquareIntegrable
      · have havgm : StronglyMeasurable
            (fun x => ∫ s, ‖q (x, s)‖ ∂I.law.toMeasure) :=
          hqm.stronglyMeasurable.norm.integral_prod_right
        apply (integrable_const ((I.V * I.V).trace)).mono' havgm.aestronglyMeasurable
        filter_upwards [] with x
        have he : (∫ s, ‖q (x, s)‖ ∂I.law.toMeasure) =
            ∫ s, ‖I.g x s - I.H x‖ ^ 2 ∂I.law.toMeasure := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun s => Real.norm_of_nonneg (sq_nonneg _))
        rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)), he]
        exact hpoint x
    have hsingle (j : Fin p.M) :
        MemLp (fun ω => I.g (X ω) (ξ (t * p.M + j) ω) - I.H (X ω)) 2 P.toMeasure := by
      have hind := hxb.comp measurable_id (measurable_pi_apply j)
      have hjm := hξ.measurable (t * p.M + j)
      have hlaw : P.toMeasure.map (fun ω => (X ω, ξ (t * p.M + j) ω)) =
          (P.toMeasure.map X).prod I.law.toMeasure := by
        have hh := hind.map_prod_eq_prod_map_map hXm.aemeasurable hjm.aemeasurable
        simpa only [Function.comp_def, hξ.marginal] using hh
      have hpres : MeasurePreserving (fun ω => (X ω, ξ (t * p.M + j) ω))
          P.toMeasure ((P.toMeasure.map X).prod I.law.toMeasure) :=
        ⟨hXm.prodMk hjm, hlaw⟩
      have hi := hpres.integrable_comp_of_integrable hprodI
      have hm : Measurable (fun ω => I.g (X ω) (ξ (t * p.M + j) ω) - I.H (X ω)) :=
        (hS.gradientMeasurable.comp (hXm.prodMk hjm)).sub hHm
      apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
      exact hi
    have hH : MemLp (fun ω => I.H (X ω)) 2 P.toMeasure := by
      apply MemLp.of_bound hHm.aestronglyMeasurable ((spectralNorm (ofMatrix I.L) + 1) * (F + 1))
      filter_upwards [hbound] with ω hω
      have hh := (gradient_norm_bound I Wstar hS (X ω)).trans
        (mul_le_mul_of_nonneg_left hω (spectralNorm_nonneg _))
      nlinarith [spectralNorm_nonneg (ofMatrix I.L)]
    let N : Ω → Mat p.m p.n := fun ω =>
      (1 / (p.M : ℝ)) • ∑ j : Fin p.M, (I.g (X ω) (ξ (t * p.M + j) ω) - I.H (X ω))
    have hN : MemLp N 2 P.toMeasure :=
      (memLp_finsetSum Finset.univ (fun j _ => hsingle j)).const_smul (1 / (p.M : ℝ))
    have hMne : (p.M : ℝ) ≠ 0 := by exact_mod_cast (by omega : p.M ≠ 0)
    have hsplit (ω : Ω) :
        Core.batchGradient p I.g (fun j => ξ j ω) t (X ω) = N ω + I.H (X ω) := by
      change (1 / (p.M : ℝ)) • (∑ j ∈ Finset.range p.M, I.g (X ω) (ξ (t * p.M + j) ω)) =
        (1 / (p.M : ℝ)) •
          (∑ j : Fin p.M, (I.g (X ω) (ξ (t * p.M + j) ω) - I.H (X ω))) + I.H (X ω)
      rw [← Fin.sum_univ_eq_sum_range, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_sub,
        ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_smul, one_div_mul_cancel hMne, one_smul]
      module
    constructor
    · simp only [hsplit]
      convert! hN.add hH using 1
    · simpa only [hsplit, add_sub_cancel_right] using hN
  )

lemma batch_noise_condMean (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (hM : 1 ≤ p.M) (t : ℕ) (X : Ω → Mat p.m p.n)
    (hX : @Measurable Ω (Mat p.m p.n)
      (MeasurableSpace.comap (fun ω (i : Fin (t * p.M)) => ξ i ω) inferInstance)
      inferInstance X)
    (F : ℝ) (hF : 0 ≤ F) (hbound : ∀ᵐ ω ∂P.toMeasure, ‖X ω - Wstar‖ ≤ F) :
    MeasureTheory.condExp
      (MeasurableSpace.comap (fun ω (i : Fin (t * p.M)) => ξ i ω) inferInstance)
      P.toMeasure (fun ω => Core.batchGradient p I.g (fun j => ξ j ω) t (X ω) - I.H (X ω)) =ᵐ[P.toMeasure] fun _ => (0 : Mat p.m p.n) := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    classical
    let block : Ω → (Fin p.M → I.Sample) := fun ω j => ξ (t * p.M + j) ω
    have hblock : Measurable block :=
      Measurable.of_eval (fun j => hξ.measurable (t * p.M + j))
    have hpre : Measurable (fun ω (i : Fin (t * p.M)) => ξ i ω) :=
      Measurable.of_eval (fun i => hξ.measurable i)
    have hXm : Measurable X := hX.mono hpre.comap_le le_rfl
    have hbi := hξ.independent.precomp
      (g := fun j : Fin p.M => t * p.M + j.val)
      (by intro j k hjk; apply Fin.ext; exact Nat.add_left_cancel hjk)
    have hblaw : P.toMeasure.map block =
        Measure.pi (fun _ : Fin p.M => I.law.toMeasure) := by
      have hh := hbi.map_fun_eq_pi_map
        (fun j : Fin p.M => (hξ.measurable (t * p.M + j)).aemeasurable)
      simpa only [hξ.marginal] using hh
    have hpb := prefix_batch_independent I.law P ξ hξ p.M t
    have hxb : IndepFun X block P.toMeasure :=
      indep_of_indep_of_le hpb hX.comap_le le_rfl
    have hpairlaw : P.toMeasure.map (fun ω => (X ω, block ω)) =
        (P.toMeasure.map X).prod (Measure.pi (fun _ : Fin p.M => I.law.toMeasure)) := by
      rw [hxb.map_prod_eq_prod_map_map hXm.aemeasurable hblock.aemeasurable, hblaw]
    let nu : ProbabilityMeasure (Fin p.M → I.Sample) :=
      ⟨Measure.pi (fun _ : Fin p.M => I.law.toMeasure), inferInstance⟩
    let k : Mat p.m p.n → (Fin p.M → I.Sample) → Mat p.m p.n :=
      fun x s => (1 / (p.M : ℝ)) • (∑ j : Fin p.M, I.g x (s j)) - I.H x
    have hk : Measurable (Function.uncurry k) := by
      have hg : Measurable (fun q : Mat p.m p.n × (Fin p.M → I.Sample) =>
          ∑ j : Fin p.M, I.g q.1 (q.2 j)) :=
        Finset.measurable_fun_sum Finset.univ
          (fun j _ => hS.gradientMeasurable.comp
            (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)))
      exact (hg.const_smul (1 / (p.M : ℝ))).sub
        ((gradient_continuous I Wstar hS).measurable.comp measurable_fst)
    have hki (x : Mat p.m p.n) (j : Fin p.M) :
        Integrable (fun s : Fin p.M → I.Sample => I.g x (s j)) nu.toMeasure :=
      (measurePreserving_eval (fun _ : Fin p.M => I.law.toMeasure) j).integrable_comp_of_integrable
        (hS.gradientIntegrable x)
    have hmean (x : Mat p.m p.n) (j : Fin p.M) :
        (∫ s, I.g x (s j) ∂nu.toMeasure) = I.H x := by
      have hm : Measurable (I.g x) :=
        hS.gradientMeasurable.comp (measurable_const.prodMk measurable_id)
      have hh := integral_map_of_stronglyMeasurable
        (measurable_pi_apply j) hm.stronglyMeasurable
        (μ := nu.toMeasure)
      change (∫ y, I.g x y ∂(Measure.pi (fun _ : Fin p.M => I.law.toMeasure)).map (Function.eval j)) = _ at hh
      rw [(measurePreserving_eval (fun _ : Fin p.M => I.law.toMeasure) j).map_eq] at hh
      exact hh.symm.trans (hS.unbiased x)
    have hzero (x : Mat p.m p.n) : (∫ s, k x s ∂nu.toMeasure) = 0 := by
      have hsum : Integrable (fun s : Fin p.M → I.Sample => ∑ j : Fin p.M, I.g x (s j))
          nu.toMeasure := integrable_finsetSum Finset.univ (fun j _ => hki x j)
      change (∫ s, (1 / (p.M : ℝ)) • (∑ j : Fin p.M, I.g x (s j)) - I.H x ∂nu.toMeasure) = 0
      have hscaled : Integrable (fun s : Fin p.M → I.Sample =>
          (1 / (p.M : ℝ)) • ∑ j : Fin p.M, I.g x (s j)) nu.toMeasure := by
        convert! hsum.smul (1 / (p.M : ℝ)) using 1
      rw [integral_sub hscaled (integrable_const _),
        integral_smul, integral_finsetSum _ (fun j _ => hki x j)]
      simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        integral_const, probReal_univ, one_smul]
      rw [← Nat.cast_smul_eq_nsmul (R := ℝ), smul_smul,
        one_div_mul_cancel (by exact_mod_cast (by omega : p.M ≠ 0)), one_smul, sub_self]
    have hbatch (ω : Ω) : k (X ω) (block ω) =
        Core.batchGradient p I.g (fun j => ξ j ω) t (X ω) - I.H (X ω) := by
      change (1 / (p.M : ℝ)) • (∑ j : Fin p.M, I.g (X ω) (ξ (t * p.M + j) ω)) - I.H (X ω) = _
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => I.g (X ω) (ξ (t * p.M + j) ω))]
      rfl
    have hni := (batch_noise_memLp p I Wstar hS P ξ hξ hM t X hX F hF hbound).2
    have hI : Integrable (fun ω => k (X ω) (block ω)) P.toMeasure := by
      simpa only [hbatch] using hni.integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have havg : Integrable (fun ω => ∫ s, k (X ω) s ∂nu.toMeasure) P.toMeasure := by
      simpa only [hzero] using (integrable_const (0 : Mat p.m p.n) : Integrable _ P.toMeasure)
    have hc := LongTails.Proofs.RipmConditional.conditional_kernel P nu
      (MeasurableSpace.comap (fun ω (i : Fin (t * p.M)) => ξ i ω) inferInstance)
      hpre.comap_le block X k hblock hX hk hpb.symm hblaw hI havg
    simpa only [hbatch, hzero] using hc
  )

lemma batch_noise_covariance (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (hM : 1 ≤ p.M) (t : ℕ) (X : Ω → Mat p.m p.n)
    (hX : @Measurable Ω (Mat p.m p.n)
      (MeasurableSpace.comap (fun ω (i : Fin (t * p.M)) => ξ i ω) inferInstance)
      inferInstance X)
    (F : ℝ) (hF : 0 ≤ F) (hbound : ∀ᵐ ω ∂P.toMeasure, ‖X ω - Wstar‖ ≤ F) :
    Core.loewner (∫ ω, Core.gram (Core.batchGradient p I.g (fun j => ξ j ω) t (X ω) - I.H (X ω)) ∂P.toMeasure)
      ((1 / (p.M : ℝ)) • (I.V * I.V)) := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    classical
    let ν : ProbabilityMeasure (Fin p.M → I.Sample) :=
      ⟨Measure.pi (fun _ : Fin p.M => I.law.toMeasure), inferInstance⟩
    let c : ℝ := 1/(p.M : ℝ)
    have hM0 : (p.M : ℝ)≠0 := by exact_mod_cast (show p.M≠0 by omega)
    have hc : 0≤c := by dsimp only [c]; positivity
    let κ (U : Mat p.m p.n) (b : Fin p.M → I.Sample) :=
      c•∑ i : Fin p.M, (I.g U (b i)-I.H U)
    have hGramContinuous : Continuous (@Core.gram p.m p.n) := by
      let J : Mat p.m p.n →L[ℝ] Matrix (Fin p.m) (Fin p.n) ℝ :=
        LinearMap.toContinuousLinearMap
          { toFun := toMatrix, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      let K : Mat p.m p.n →L[ℝ] Matrix (Fin p.n) (Fin p.m) ℝ :=
        LinearMap.toContinuousLinearMap
          { toFun := fun Y => (toMatrix Y)ᵀ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      change Continuous (fun Y => J Y*K Y)
      exact J.continuous.matrix_mul K.continuous
    have hscale (a : ℝ) (Y : Mat p.m p.n) : Core.gram (a•Y)=a^2•Core.gram Y := by
      change (a•toMatrix Y)*(a•toMatrix Y)ᵀ=a^2•(toMatrix Y*(toMatrix Y)ᵀ)
      rw [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,pow_two]
    have hSum (Z : Fin p.M → (Fin p.M → I.Sample) → Mat p.m p.n)
        (hZ : ∀ i, MemLp (Z i) 2 ν.toMeasure) (hind : iIndepFun Z ν.toMeasure)
        (hmean : ∀ i, (∫ b, Z i b ∂ν.toMeasure)=0) :
        (∫ b, Core.gram (∑ i, Z i b) ∂ν.toMeasure)=
          ∑ i, ∫ b, Core.gram (Z i b) ∂ν.toMeasure := by
      classical
      have hc (i j : Fin p.M) :
          Integrable (fun ω => toMatrix (Z i ω)*(toMatrix (Z j ω))ᵀ) ν.toMeasure := by
        let X := Z i
        let Y := Z j
        let μ := ν.toMeasure
        have hX : MemLp X 2 μ := hZ i
        have hY : MemLp Y 2 μ := hZ j
        classical
        let J : Mat p.m p.n →L[ℝ] Matrix (Fin p.m) (Fin p.n) ℝ :=
          LinearMap.toContinuousLinearMap
            { toFun := toMatrix, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
        let K : Mat p.m p.n →L[ℝ] Matrix (Fin p.n) (Fin p.m) ℝ :=
          LinearMap.toContinuousLinearMap
            { toFun := fun Y => (toMatrix Y)ᵀ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
        have hj : MemLp (fun ω => J (X ω)) 2 μ := hX.of_le_mul
          (J.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)
          (Filter.Eventually.of_forall (fun ω => J.le_opNorm (X ω)))
        have hk : MemLp (fun ω => K (Y ω)) 2 μ := hY.of_le_mul
          (K.continuous.comp_aestronglyMeasurable hY.aestronglyMeasurable)
          (Filter.Eventually.of_forall (fun ω => K.le_opNorm (Y ω)))
        have hp : MemLp (fun ω => J (X ω)*K (Y ω)) 1 μ :=
          MemLp.of_bilin (fun (A : Matrix (Fin p.m) (Fin p.n) ℝ) (B : Matrix (Fin p.n) (Fin p.m) ℝ) => A*B)
            1 hj hk (continuous_fst.matrix_mul continuous_snd)
            (Filter.Eventually.of_forall (fun ω => by
              simpa only [one_mul] using Matrix.l2_opNNNorm_mul (J (X ω)) (K (Y ω))))
        exact memLp_one_iff_integrable.1 hp
      let B0 : Mat p.m p.n →ₗ[ℝ] Mat p.m p.n →ₗ[ℝ] Matrix (Fin p.m) (Fin p.m) ℝ :=
        { toFun := fun X =>
            { toFun := fun Y => toMatrix X*(toMatrix Y)ᵀ
              map_add' := by
                intro Y W
                change toMatrix X*(toMatrix Y+toMatrix W)ᵀ = _
                rw [Matrix.transpose_add,Matrix.mul_add]
              map_smul' := by
                intro c Y
                change toMatrix X*(c•toMatrix Y)ᵀ = c•(toMatrix X*(toMatrix Y)ᵀ)
                rw [Matrix.transpose_smul,Matrix.mul_smul] }
          map_add' := by
            intro X Y
            apply LinearMap.ext
            intro W
            change (toMatrix X+toMatrix Y)*(toMatrix W)ᵀ = _
            rw [Matrix.add_mul]
            rfl
          map_smul' := by
            intro c X
            apply LinearMap.ext
            intro Y
            change (c•toMatrix X)*(toMatrix Y)ᵀ = c•(toMatrix X*(toMatrix Y)ᵀ)
            rw [Matrix.smul_mul] }
      let B : Mat p.m p.n →L[ℝ] Mat p.m p.n →L[ℝ] Matrix (Fin p.m) (Fin p.m) ℝ :=
        LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp B0)
      have hcB (i j : Fin p.M) : Integrable (fun ω => B (Z i ω) (Z j ω)) ν.toMeasure := hc i j
      have he (i j : Fin p.M) : (∫ ω, B (Z i ω) (Z j ω) ∂ν.toMeasure)=
          if i=j then ∫ ω, Core.gram (Z i ω) ∂ν.toMeasure else 0 := by
        by_cases hij : i=j
        · subst j
          rw [ite_eq_left rfl]
          rfl
        · rw [ite_eq_right hij]
          have h := (hind.indepFun hij).integral_bilin
            ((hZ i).integrable (by norm_num)) ((hZ j).integrable (by norm_num)) B
          rw [hmean i,hmean j] at h
          simpa only [map_zero,_root_.zero_apply] using h
      have hfun : (fun ω => Core.gram (∑ i, Z i ω))=
          (fun ω => ∑ i, ∑ j, B (Z i ω) (Z j ω)) := by
        funext ω
        change B (∑ i, Z i ω) (∑ j, Z j ω)=_
        rw [map_sum]
        simp only [_root_.sum_apply,map_sum]
        rw [Finset.sum_comm]
      rw [hfun,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hcB i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hcB i j)]
      simp [he]
    have hfixed (U : Mat p.m p.n) :
        Core.loewner (∫ b, Core.gram (κ U b) ∂ν.toMeasure) (c•(I.V*I.V)) := by
      let noise : I.Sample → Mat p.m p.n := fun s => I.g U s-I.H U
      have hnoiseM : Measurable noise :=
        (hS.gradientMeasurable.comp (measurable_const.prodMk measurable_id)).sub measurable_const
      have hnoiseL : MemLp noise 2 I.law.toMeasure :=
        (memLp_two_iff_integrable_sq_norm hnoiseM.aestronglyMeasurable).2 (hS.noiseSquareIntegrable U)
      have hmean0 : (∫ s, noise s ∂I.law.toMeasure)=0 := by
        change (∫ s, I.g U s-I.H U ∂I.law.toMeasure)=0
        rw [integral_sub (hS.gradientIntegrable U) (integrable_const _),hS.unbiased U]
        simp
      let Z : Fin p.M → (Fin p.M → I.Sample) → Mat p.m p.n := fun i b => noise (b i)
      have hev (i : Fin p.M) : ν.toMeasure.map (Function.eval i)=I.law.toMeasure :=
        (measurePreserving_eval (fun _ : Fin p.M => I.law.toMeasure) i).map_eq
      have hZ (i : Fin p.M) : MemLp (Z i) 2 ν.toMeasure :=
        hnoiseL.comp_measurePreserving (measurePreserving_eval (fun _ : Fin p.M => I.law.toMeasure) i)
      have hind : iIndepFun Z ν.toMeasure := iIndepFun_pi (fun _ => hnoiseM.aemeasurable)
      have hmeans (i : Fin p.M) : (∫ b, Z i b ∂ν.toMeasure)=0 := by
        calc
          _ = ∫ s, noise s ∂ν.toMeasure.map (Function.eval i) :=
            (integral_map_of_stronglyMeasurable (measurable_pi_apply i) hnoiseM.stronglyMeasurable).symm
          _ = _ := by rw [hev,hmean0]
      let Q := ∫ s, Core.gram (noise s) ∂I.law.toMeasure
      have hdiag (i : Fin p.M) : (∫ b, Core.gram (Z i b) ∂ν.toMeasure)=Q := by
        calc
          _ = ∫ s, Core.gram (noise s) ∂ν.toMeasure.map (Function.eval i) :=
            (integral_map_of_stronglyMeasurable (measurable_pi_apply i)
              (hGramContinuous.measurable.comp hnoiseM).stronglyMeasurable).symm
          _ = _ := by rw [hev]
      have hs : c^2*(p.M : ℝ)=c := by dsimp only [c]; field_simp [hM0]
      have heq : (∫ b, Core.gram (κ U b) ∂ν.toMeasure)=c•Q := by
        change (∫ b, Core.gram (c•∑ i, Z i b) ∂ν.toMeasure)=c•Q
        simp_rw [hscale]
        rw [integral_smul,hSum Z hZ hind hmeans]
        simp only [hdiag,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
        rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,hs]
      rw [heq]
      change (c•(I.V*I.V)-c•Q).PosSemidef
      rw [← smul_sub]
      exact (hS.covariance U).smul hc
    let block : Ω → (Fin p.M → I.Sample) := fun ω j => ξ (t * p.M + j) ω
    have hblock : Measurable block :=
      Measurable.of_eval (fun j => hξ.measurable (t * p.M + j))
    have hpre : Measurable (fun ω (i : Fin (t * p.M)) => ξ i ω) :=
      Measurable.of_eval (fun i => hξ.measurable i)
    have hXm : Measurable X := hX.mono hpre.comap_le le_rfl
    have hbi := hξ.independent.precomp
      (g := fun j : Fin p.M => t * p.M + j.val)
      (by intro j k hjk; apply Fin.ext; exact Nat.add_left_cancel hjk)
    have hblaw : P.toMeasure.map block =
        Measure.pi (fun _ : Fin p.M => I.law.toMeasure) := by
      have hh := hbi.map_fun_eq_pi_map
        (fun j : Fin p.M => (hξ.measurable (t * p.M + j)).aemeasurable)
      simpa only [hξ.marginal] using hh
    have hpb := prefix_batch_independent I.law P ξ hξ p.M t
    have hxb : IndepFun X block P.toMeasure :=
      indep_of_indep_of_le hpb hX.comap_le le_rfl
    have hpairlaw : P.toMeasure.map (fun ω => (X ω, block ω)) =
        (P.toMeasure.map X).prod (Measure.pi (fun _ : Fin p.M => I.law.toMeasure)) := by
      rw [hxb.map_prod_eq_prod_map_map hXm.aemeasurable hblock.aemeasurable, hblaw]
    let N : Ω → Mat p.m p.n := fun ω => κ (X ω) (block ω)
    have hEq (ω : Ω) : Core.batchGradient p I.g (fun j => ξ j ω) t (X ω)-I.H (X ω)=N ω := by
      change c•(∑ j ∈ Finset.range p.M, I.g (X ω) (ξ (t*p.M+j) ω))-I.H (X ω)=
        c•∑ j : Fin p.M, (I.g (X ω) (ξ (t*p.M+j) ω)-I.H (X ω))
      rw [Finset.sum_sub_distrib,smul_sub]
      have hconst : c•(∑ _j : Fin p.M, I.H (X ω))=I.H (X ω) := by
        rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℝ,smul_smul]
        simp only [c,one_div,inv_mul_cancel₀ hM0,one_smul]
      rw [hconst,Fin.sum_univ_eq_sum_range (fun j => I.g (X ω) (ξ (t*p.M+j) ω)) p.M]
    have hN : MemLp N 2 P.toMeasure := by
      have hh := (batch_noise_memLp p I Wstar hS P ξ hξ hM t X hX F hF hbound).2
      convert hh using 1
      funext ω
      exact (hEq ω).symm
    have hGram : Integrable (fun ω => Core.gram (N ω)) P.toMeasure := by
      classical
      let J : Mat p.m p.n →L[ℝ] Matrix (Fin p.m) (Fin p.n) ℝ :=
        LinearMap.toContinuousLinearMap
          { toFun := toMatrix, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      let K : Mat p.m p.n →L[ℝ] Matrix (Fin p.n) (Fin p.m) ℝ :=
        LinearMap.toContinuousLinearMap
          { toFun := fun Y => (toMatrix Y)ᵀ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      have hj : MemLp (fun ω => J (N ω)) 2 P.toMeasure := hN.of_le_mul
        (J.continuous.comp_aestronglyMeasurable hN.aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun ω => J.le_opNorm (N ω)))
      have hk : MemLp (fun ω => K (N ω)) 2 P.toMeasure := hN.of_le_mul
        (K.continuous.comp_aestronglyMeasurable hN.aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun ω => K.le_opNorm (N ω)))
      have hp : MemLp (fun ω => J (N ω)*K (N ω)) 1 P.toMeasure :=
        MemLp.of_bilin (fun (A : Matrix (Fin p.m) (Fin p.n) ℝ) (B : Matrix (Fin p.n) (Fin p.m) ℝ) => A*B)
          1 hj hk (continuous_fst.matrix_mul continuous_snd)
          (Filter.Eventually.of_forall (fun ω => by
            simpa only [one_mul] using Matrix.l2_opNNNorm_mul (J (N ω)) (K (N ω))))
      exact memLp_one_iff_integrable.1 hp
    have hκ : Measurable (Function.uncurry κ) :=
      (Finset.measurable_fun_sum Finset.univ (fun j _ =>
        (hS.gradientMeasurable.comp (measurable_fst.prodMk
          ((measurable_pi_apply j).comp measurable_snd))).sub
            ((gradient_continuous I Wstar hS).measurable.comp measurable_fst))).const_smul c
    let K : Mat p.m p.n × (Fin p.M → I.Sample) → Matrix (Fin p.m) (Fin p.m) ℝ :=
      fun z => Core.gram (κ z.1 z.2)
    have hK : Measurable K := hGramContinuous.measurable.comp hκ
    have hIntMap : Integrable K (P.toMeasure.map (fun ω => (X ω,block ω))) :=
      (integrable_map_measure hK.aestronglyMeasurable (hXm.prodMk hblock).aemeasurable).2 hGram
    rw [hpairlaw] at hIntMap
    let PX : ProbabilityMeasure (Mat p.m p.n) := P.map X
    change Integrable K (PX.toMeasure.prod ν.toMeasure) at hIntMap
    have hi : (∫ ω, Core.gram (Core.batchGradient p I.g (fun j => ξ j ω) t (X ω)-I.H (X ω)) ∂P.toMeasure)=
        ∫ ω, Core.gram (N ω) ∂P.toMeasure :=
      integral_congr_ae (Filter.Eventually.of_forall (fun ω => congrArg Core.gram (hEq ω)))
    change ((1/(p.M : ℝ))•(I.V*I.V)-
      ∫ ω, Core.gram (Core.batchGradient p I.g (fun j => ξ j ω) t (X ω)-I.H (X ω)) ∂P.toMeasure).PosSemidef
    rw [hi]
    change (∫ ω, Core.gram (N ω) ∂P.toMeasure) ≤ c•(I.V*I.V)
    calc
      _ = ∫ z, K z ∂P.toMeasure.map (fun ω => (X ω,block ω)) :=
        (integral_map_of_stronglyMeasurable (hXm.prodMk hblock) hK.stronglyMeasurable).symm
      _ = ∫ z, K z ∂PX.toMeasure.prod ν.toMeasure  := by rw [hpairlaw]; rfl
      _ = ∫ U, ∫ b, K (U,b) ∂ν.toMeasure ∂PX.toMeasure := integral_prod K hIntMap
      _ ≤ ∫ _U, c•(I.V*I.V) ∂PX.toMeasure :=
        integral_mono hIntMap.integral_prod_left (integrable_const _) (fun U => hfixed U)
      _ = _ := by simp
  )

lemma batch_noise_weighted (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (hM : 1 ≤ p.M) (t : ℕ) (X : Ω → Mat p.m p.n)
    (hX : @Measurable Ω (Mat p.m p.n)
      (MeasurableSpace.comap (fun ω (i : Fin (t * p.M)) => ξ i ω) inferInstance)
      inferInstance X)
    (F : ℝ) (hF : 0 ≤ F) (hbound : ∀ᵐ ω ∂P.toMeasure, ‖X ω - Wstar‖ ≤ F) :
    (∫ ω, Core.weightedQuadratic I.V⁻¹ (Core.batchGradient p I.g (fun j => ξ j ω) t (X ω) - I.H (X ω)) ∂P.toMeasure) ≤
      I.V.trace / (p.M : ℝ) := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    classical
    let N : Ω → Mat p.m p.n := fun ω =>
      Core.batchGradient p I.g (fun j => ξ j ω) t (X ω)-I.H (X ω)
    have hN : MemLp N 2 P.toMeasure :=
      (batch_noise_memLp p I Wstar hS P ξ hξ hM t X hX F hF hbound).2
    have hGram : Integrable (fun ω => Core.gram (N ω)) P.toMeasure := by
      classical
      let J : Mat p.m p.n →L[ℝ] Matrix (Fin p.m) (Fin p.n) ℝ :=
        LinearMap.toContinuousLinearMap
          { toFun := toMatrix, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      let K : Mat p.m p.n →L[ℝ] Matrix (Fin p.n) (Fin p.m) ℝ :=
        LinearMap.toContinuousLinearMap
          { toFun := fun Y => (toMatrix Y)ᵀ, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
      have hj : MemLp (fun ω => J (N ω)) 2 P.toMeasure := hN.of_le_mul
        (J.continuous.comp_aestronglyMeasurable hN.aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun ω => J.le_opNorm (N ω)))
      have hk : MemLp (fun ω => K (N ω)) 2 P.toMeasure := hN.of_le_mul
        (K.continuous.comp_aestronglyMeasurable hN.aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun ω => K.le_opNorm (N ω)))
      have hp : MemLp (fun ω => J (N ω)*K (N ω)) 1 P.toMeasure :=
        MemLp.of_bilin (fun (A : Matrix (Fin p.m) (Fin p.n) ℝ) (B : Matrix (Fin p.n) (Fin p.m) ℝ) => A*B)
          1 hj hk (continuous_fst.matrix_mul continuous_snd)
          (Filter.Eventually.of_forall (fun ω => by
            simpa only [one_mul] using Matrix.l2_opNNNorm_mul (J (N ω)) (K (N ω))))
      exact memLp_one_iff_integrable.1 hp
    let K := I.V⁻¹
    have hIntegral : Integrable (fun ω => Core.weightedQuadratic K (N ω)) P.toMeasure ∧
        (∫ ω, Core.weightedQuadratic K (N ω) ∂P.toMeasure)=
          ((∫ ω, Core.gram (N ω) ∂P.toMeasure)*K).trace := by
      classical
      let L : Matrix (Fin p.m) (Fin p.m) ℝ →ₗ[ℝ] ℝ :=
        { toFun := fun A => (A*K).trace
          map_add' := by intro A B; rw [Matrix.add_mul,Matrix.trace_add]
          map_smul' := by intro c A; simp only [Matrix.smul_mul,Matrix.trace_smul,RingHom.id_apply] }
      let C := LinearMap.toContinuousLinearMap L
      have he (Y : Mat p.m p.n) : Core.weightedQuadratic K Y=C (Core.gram Y) := by
        change ((toMatrix Y)ᵀ*K*toMatrix Y).trace=(toMatrix Y*(toMatrix Y)ᵀ*K).trace
        rw [Matrix.trace_mul_cycle]
      simp_rw [he]
      exact ⟨C.integrable_comp hGram,C.integral_comp_comm hGram⟩
    have hCov : Core.loewner (∫ ω, Core.gram (N ω) ∂P.toMeasure)
        ((1/(p.M : ℝ))•(I.V*I.V)) :=
      batch_noise_covariance p I Wstar hS P ξ hξ hM t X hX F hF hbound
    have hInv := inverse_posDef I.V hS.variancePos
    have htr := trace_mul_nonneg
      ((1/(p.M : ℝ))•(I.V*I.V)-(∫ ω, Core.gram (N ω) ∂P.toMeasure))
      I.V⁻¹ hCov hInv.1.posSemidef
    rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul,
      Matrix.mul_assoc,hInv.2.1,Matrix.mul_one] at htr
    change (∫ ω, Core.weightedQuadratic K (N ω) ∂P.toMeasure) ≤ I.V.trace/(p.M : ℝ)
    rw [hIntegral.2]
    calc
      _ ≤ (1/(p.M : ℝ))*I.V.trace := sub_nonneg.mp htr
      _ = _ := by ring
  )

lemma batch_inner_zero (p : LongTails.Setups.AsgoFixedRadius.Public) (I : Core.Problem p.m p.n)
    (Wstar : Mat p.m p.n) (hS : Core.SourceAssumptions I Wstar)
    {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (ξ : ℕ → Ω → I.Sample)
    (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      ξ I.law.toMeasure P.toMeasure)
    (hM : 1 ≤ p.M) (t : ℕ) (X : Ω → Mat p.m p.n)
    (hX : @Measurable Ω (Mat p.m p.n)
      (MeasurableSpace.comap (fun ω (i : Fin (t * p.M)) => ξ i ω) inferInstance)
      inferInstance X)
    (F : ℝ) (hF : 0 ≤ F) (hbound : ∀ᵐ ω ∂P.toMeasure, ‖X ω - Wstar‖ ≤ F) :
    (∫ ω, inner ℝ (Core.batchGradient p I.g (fun j => ξ j ω) t (X ω) - I.H (X ω)) (X ω - Wstar) ∂P.toMeasure) = 0 := by
  open Matrix MeasureTheory ProbabilityTheory in
  open scoped BigOperators in
  (
    classical
    let block : Ω → (Fin p.M → I.Sample) := fun ω j => ξ (t * p.M + j) ω
    have hblock : Measurable block :=
      Measurable.of_eval (fun j => hξ.measurable (t * p.M + j))
    have hpre : Measurable (fun ω (i : Fin (t * p.M)) => ξ i ω) :=
      Measurable.of_eval (fun i => hξ.measurable i)
    have hXm : Measurable X := hX.mono hpre.comap_le le_rfl
    have hbi := hξ.independent.precomp
      (g := fun j : Fin p.M => t * p.M + j.val)
      (by intro j k hjk; apply Fin.ext; exact Nat.add_left_cancel hjk)
    have hblaw : P.toMeasure.map block =
        Measure.pi (fun _ : Fin p.M => I.law.toMeasure) := by
      have hh := hbi.map_fun_eq_pi_map
        (fun j : Fin p.M => (hξ.measurable (t * p.M + j)).aemeasurable)
      simpa only [hξ.marginal] using hh
    have hpb := prefix_batch_independent I.law P ξ hξ p.M t
    have hxb : IndepFun X block P.toMeasure :=
      indep_of_indep_of_le hpb hX.comap_le le_rfl
    have hpairlaw : P.toMeasure.map (fun ω => (X ω, block ω)) =
        (P.toMeasure.map X).prod (Measure.pi (fun _ : Fin p.M => I.law.toMeasure)) := by
      rw [hxb.map_prod_eq_prod_map_map hXm.aemeasurable hblock.aemeasurable, hblaw]
    let nu : ProbabilityMeasure (Fin p.M → I.Sample) :=
      ⟨Measure.pi (fun _ : Fin p.M => I.law.toMeasure), inferInstance⟩
    let k : Mat p.m p.n → (Fin p.M → I.Sample) → Mat p.m p.n :=
      fun x s => (1 / (p.M : ℝ)) • (∑ j : Fin p.M, I.g x (s j)) - I.H x
    have hk : Measurable (Function.uncurry k) := by
      have hg : Measurable (fun q : Mat p.m p.n × (Fin p.M → I.Sample) =>
          ∑ j : Fin p.M, I.g q.1 (q.2 j)) :=
        Finset.measurable_fun_sum Finset.univ
          (fun j _ => hS.gradientMeasurable.comp
            (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd)))
      exact (hg.const_smul (1 / (p.M : ℝ))).sub
        ((gradient_continuous I Wstar hS).measurable.comp measurable_fst)
    have hki (x : Mat p.m p.n) (j : Fin p.M) :
        Integrable (fun s : Fin p.M → I.Sample => I.g x (s j)) nu.toMeasure :=
      (measurePreserving_eval (fun _ : Fin p.M => I.law.toMeasure) j).integrable_comp_of_integrable
        (hS.gradientIntegrable x)
    have hmean (x : Mat p.m p.n) (j : Fin p.M) :
        (∫ s, I.g x (s j) ∂nu.toMeasure) = I.H x := by
      have hm : Measurable (I.g x) :=
        hS.gradientMeasurable.comp (measurable_const.prodMk measurable_id)
      have hh := integral_map_of_stronglyMeasurable
        (measurable_pi_apply j) hm.stronglyMeasurable
        (μ := nu.toMeasure)
      change (∫ y, I.g x y ∂(Measure.pi (fun _ : Fin p.M => I.law.toMeasure)).map (Function.eval j)) = _ at hh
      rw [(measurePreserving_eval (fun _ : Fin p.M => I.law.toMeasure) j).map_eq] at hh
      exact hh.symm.trans (hS.unbiased x)
    have hzero (x : Mat p.m p.n) : (∫ s, k x s ∂nu.toMeasure) = 0 := by
      have hsum : Integrable (fun s : Fin p.M → I.Sample => ∑ j : Fin p.M, I.g x (s j))
          nu.toMeasure := integrable_finsetSum Finset.univ (fun j _ => hki x j)
      change (∫ s, (1 / (p.M : ℝ)) • (∑ j : Fin p.M, I.g x (s j)) - I.H x ∂nu.toMeasure) = 0
      have hscaled : Integrable (fun s : Fin p.M → I.Sample =>
          (1 / (p.M : ℝ)) • ∑ j : Fin p.M, I.g x (s j)) nu.toMeasure := by
        convert! hsum.smul (1 / (p.M : ℝ)) using 1
      rw [integral_sub hscaled (integrable_const _),
        integral_smul, integral_finsetSum _ (fun j _ => hki x j)]
      simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        integral_const, probReal_univ, one_smul]
      rw [← Nat.cast_smul_eq_nsmul (R := ℝ), smul_smul,
        one_div_mul_cancel (by exact_mod_cast (by omega : p.M ≠ 0)), one_smul, sub_self]
    have hbatch (ω : Ω) : k (X ω) (block ω) =
        Core.batchGradient p I.g (fun j => ξ j ω) t (X ω) - I.H (X ω) := by
      change (1 / (p.M : ℝ)) • (∑ j : Fin p.M, I.g (X ω) (ξ (t * p.M + j) ω)) - I.H (X ω) = _
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => I.g (X ω) (ξ (t * p.M + j) ω))]
      rfl
    have hKI (x : Mat p.m p.n) : Integrable (k x) nu.toMeasure := by
      have hh := ((integrable_finsetSum Finset.univ (fun j _ => hki x j)).smul
        (1 / (p.M : ℝ))).sub' (integrable_const (I.H x))
      simpa only [k, Pi.smul_apply] using hh
    let ki : Mat p.m p.n → (Fin p.M → I.Sample) → ℝ :=
      fun x s => inner ℝ (k x s) (x - Wstar)
    have hkim : Measurable (Function.uncurry ki) :=
      hk.inner (measurable_fst.sub measurable_const)
    have hki0 (x : Mat p.m p.n) : (∫ s, ki x s ∂nu.toMeasure) = 0 := by
      calc
        _ = ∫ s, inner ℝ (x - Wstar) (k x s) ∂nu.toMeasure :=
          integral_congr_ae (Filter.Eventually.of_forall (fun s => real_inner_comm _ _))
        _ = inner ℝ (x - Wstar) (∫ s, k x s ∂nu.toMeasure) := integral_inner (𝕜 := ℝ) (hKI x) _
        _ = 0 := by rw [hzero, inner_zero_right]
    have hni := (batch_noise_memLp p I Wstar hS P ξ hξ hM t X hX F hF hbound).2
    have hdist : MemLp (fun ω => X ω - Wstar) 2 P.toMeasure :=
      MemLp.of_bound (hXm.sub measurable_const).aestronglyMeasurable F hbound
    have hII : Integrable
        (fun ω => inner ℝ (Core.batchGradient p I.g (fun j => ξ j ω) t (X ω) - I.H (X ω))
          (X ω - Wstar)) P.toMeasure := by
      apply (hni.norm.integrable_mul hdist.norm).mono'
        (hni.aestronglyMeasurable.inner hdist.aestronglyMeasurable)
      exact Filter.Eventually.of_forall (fun ω => norm_inner_le_norm _ _)
    have hjoint : Integrable (fun ω => ki (X ω) (block ω)) P.toMeasure := by
      simpa only [ki, hbatch] using hII
    have havg : Integrable (fun ω => ∫ s, ki (X ω) s ∂nu.toMeasure) P.toMeasure := by
      simpa only [hki0] using (integrable_const (0 : ℝ) : Integrable _ P.toMeasure)
    have hc := LongTails.Proofs.RipmConditional.conditional_kernel P nu
      (MeasurableSpace.comap (fun ω (i : Fin (t * p.M)) => ξ i ω) inferInstance)
      hpre.comap_le block X ki hblock hX hkim hpb.symm hblaw hjoint havg
    have hz : MeasureTheory.condExp
        (MeasurableSpace.comap (fun ω (i : Fin (t * p.M)) => ξ i ω) inferInstance)
        P.toMeasure (fun ω => ki (X ω) (block ω)) =ᵐ[P.toMeasure] fun _ => (0 : ℝ) := by
      simpa only [hki0] using hc
    have he : (∫ ω, ki (X ω) (block ω) ∂P.toMeasure) = 0 := by
      rw [← integral_condExp hpre.comap_le]
      exact (integral_congr_ae hz).trans (integral_zero _ _)
    simpa only [ki, hbatch] using he
  )

end OracleTemplate.AsgoFixedRadius
