import LongTails.Proofs.FullRangeEstimator

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.FullRangeOperator

open OracleTemplate.StochasticCohypomonotone OracleTemplate.LocalHiddenConvex
open LongTails.Algorithms.FullRangeMlmc
open LongTails.Setups.StochasticGeneralizedMonotone (IsStochasticOperator)
open LongTails.Proofs.FullRangeInner LongTails.Proofs.FullRangeEstimator
open LongTails.Proofs.FullRangeResolvent LongTails.Proofs.FullRangeClip
open LongTails.Proofs.BiasedAnchoring

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
variable {F : E → E} {G : E → Set E} {J : ℝ → E → E} {L ρ η : ℝ}

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma variance_le_second_moment {W : Type*} [MeasurableSpace W] (Q : Measure W)
    [IsProbabilityMeasure Q] (X : W → E) (hX : Integrable X Q) (c : E)
    (hX2 : Integrable (fun w => ‖X w - c‖ ^ 2) Q) :
    Integrable (fun w => ‖X w - ∫ v, X v ∂Q‖ ^ 2) Q ∧
    (∫ w, ‖X w - ∫ v, X v ∂Q‖ ^ 2 ∂Q) ≤ ∫ w, ‖X w - c‖ ^ 2 ∂Q ∧
    ‖(∫ v, X v ∂Q) - c‖ ^ 2 ≤ ∫ w, ‖X w - c‖ ^ 2 ∂Q := by
  set m := ∫ v, X v ∂Q with hm
  have hid (w : W) : ‖X w - c‖ ^ 2 =
      ‖X w - m‖ ^ 2 + 2 * ⟪m - c, X w - m⟫ + ‖m - c‖ ^ 2 := by
    have e : X w - c = (m - c) + (X w - m) := by abel
    rw [e, norm_add_sq_real]
    ring
  have hin : Integrable (fun w => ⟪m - c, X w - m⟫) Q :=
    ((innerSL ℝ (m - c)).integrable_comp (hX.sub (integrable_const m)))
  have hzero : (∫ w, ⟪m - c, X w - m⟫ ∂Q) = 0 := by
    have hsub : Integrable (fun w => X w - m) Q := hX.sub (integrable_const m)
    rw [integral_inner hsub, integral_sub hX (integrable_const m)]
    simp [← hm]
  have hval : Integrable (fun w => ‖X w - m‖ ^ 2) Q := by
    have : (fun w => ‖X w - m‖ ^ 2) = fun w => ‖X w - c‖ ^ 2 - (2 * ⟪m - c, X w - m⟫ + ‖m - c‖ ^ 2) := by
      funext w
      rw [hid w]
      ring
    rw [this]
    exact hX2.sub ((hin.const_mul 2).add (integrable_const _))
  have htot : (∫ w, ‖X w - c‖ ^ 2 ∂Q) = (∫ w, ‖X w - m‖ ^ 2 ∂Q) + ‖m - c‖ ^ 2 := by
    simp_rw [hid]
    rw [integral_add (f := fun w => ‖X w - m‖ ^ 2 + 2 * ⟪m - c, X w - m⟫)
        (g := fun _ => ‖m - c‖ ^ 2) (hval.add (hin.const_mul 2)) (integrable_const _),
      integral_add (f := fun w => ‖X w - m‖ ^ 2) (g := fun w => 2 * ⟪m - c, X w - m⟫)
        hval (hin.const_mul 2), integral_const_mul, hzero]
    simp
  have hv0 : 0 ≤ ∫ w, ‖X w - m‖ ^ 2 ∂Q := integral_nonneg fun _ => sq_nonneg _
  exact ⟨hval, by rw [htot]; nlinarith [sq_nonneg ‖m - c‖], by rw [htot]; linarith⟩

section Operator

variable (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) {σ γ0 : ℝ} {n0 top : ℕ}
  (p : ProbabilityMeasure Ω) (g : E → Ω → E)

noncomputable def clippedMap (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) (a : ℝ)
    (x0 : E) (r : ℝ) (x : E) : E :=
  fixedMap H hη hηL a (ballProj x0 r x)

noncomputable def callEstimate (J : ℝ → E → E) (g : E → Ω → E) (η γ0 a : ℝ) (n0 top : ℕ)
    (x0 : E) (r : ℝ) (x : E) (θ : Fin (top + 1) × (ℕ → Ω)) : E :=
  (1 - a) • ballProj x0 r x + a • estimator J g η γ0 n0 top (ballProj x0 r x) (θ.1 : ℕ) θ.2

include H hη in
omit [CompleteSpace E] in
lemma innerPath_joint_measurable (hγ0 : 0 < γ0) (hg : Measurable (Function.uncurry g)) (k : ℕ) :
    Measurable (fun w : E × (ℕ → Ω) => innerPath J g η γ0 n0 w.1 k w.2) := by
  induction k with
  | zero =>
      have : (fun w : E × (ℕ → Ω) => innerPath J g η γ0 n0 w.1 0 w.2) = Prod.fst := by
        funext w
        simp [innerPath, OracleTemplate.ContinuizedSimilarQuasar.iterateSamples]
      rw [this]
      exact measurable_fst
  | succ k ih =>
      simp_rw [innerPath_succ]
      have hγ : 0 < stepAt γ0 n0 k * η := by unfold stepAt; positivity
      have hc : Continuous (J (stepAt γ0 n0 k * η)) := (LipschitzWith.of_dist_le_mul (K := 1) (by
        intro a b
        simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using H.res_nonexp hγ a b)).continuous
      have hsample : Measurable (fun w : E × (ℕ → Ω) => w.2 k) :=
        (measurable_pi_apply k).comp measurable_snd
      have hgv : Measurable (fun w : E × (ℕ → Ω) =>
          g (innerPath J g η γ0 n0 w.1 k w.2) (w.2 k)) := hg.comp (ih.prodMk hsample)
      unfold innerStep
      exact hc.measurable.comp (ih.sub (((ih.sub measurable_fst).add
        (hgv.const_smul η)).const_smul _))

include H hη in
omit [CompleteSpace E] in
lemma callEstimate_measurable (hγ0 : 0 < γ0) (hg : Measurable (Function.uncurry g)) (a : ℝ)
    (x0 : E) {r : ℝ} (hr : 0 ≤ r) :
    Measurable (Function.uncurry (callEstimate (top := top) J g η γ0 a n0 x0 r)) := by
  have hP : Measurable (ballProj x0 r : E → E) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (by
      intro a b
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
        ballProj_nonexpansive x0 a b hr)).continuous.measurable
  have hpath (k : ℕ) : Measurable (fun w : E × (Fin (top + 1) × (ℕ → Ω)) =>
      innerPath J g η γ0 n0 (ballProj x0 r w.1) k w.2.2) :=
    (innerPath_joint_measurable H hη (n0 := n0) g hγ0 hg k).comp
      ((hP.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd))
  have hslice (l : Fin (top + 1)) : Measurable (fun w : E × (ℕ → Ω) =>
      estimator J g η γ0 n0 top (ballProj x0 r w.1) (l : ℕ) w.2) := by
    have hp2 (k : ℕ) : Measurable (fun w : E × (ℕ → Ω) =>
        innerPath J g η γ0 n0 (ballProj x0 r w.1) k w.2) :=
      (innerPath_joint_measurable H hη (n0 := n0) g hγ0 hg k).comp
        ((hP.comp measurable_fst).prodMk measurable_snd)
    unfold estimator
    by_cases hl : (l : ℕ) = 0
    · simpa [hl] using hp2 n0
    · simp only [hl, ite_false]
      exact (hp2 _).add (((hp2 _).sub (hp2 _)).const_smul _)
  have hall : Measurable (fun w : Fin (top + 1) × (E × (ℕ → Ω)) =>
      estimator J g η γ0 n0 top (ballProj x0 r w.2.1) (w.1 : ℕ) w.2.2) :=
    measurable_from_prod_countable_right hslice
  have hcomb : Measurable (fun w : E × (Fin (top + 1) × (ℕ → Ω)) =>
      estimator J g η γ0 n0 top (ballProj x0 r w.1) (w.2.1 : ℕ) w.2.2) :=
    hall.comp (show Measurable (fun w : E × (Fin (top + 1) × (ℕ → Ω)) =>
      (w.2.1, (w.1, w.2.2))) from by fun_prop)
  unfold Function.uncurry callEstimate
  exact ((hP.comp measurable_fst).const_smul _).add (hcomb.const_smul _)

include H hη hηL in
theorem callEstimate_biased (hγ0 : 0 < γ0) (hγ0s : γ0 * (1 + η * L) ^ 2 ≤ 1 - η * L) (hn0 : 0 < n0)
    (hκ : Real.exp (-(γ0 * (1 - η * L) * n0 / 2)) ≤ 1 / 16)
    (hg : IsStochasticOperator (p : Measure Ω) F g σ)
    {a : ℝ} (ha : 0 < a) (_ha1 : a ≤ 1) (haη : a * η ≤ 2 * (η - ρ))
    (x0 xstar : E) {r : ℝ} (hr : 0 < r) (hstar : -F xstar ∈ G xstar) (hx : ‖xstar - x0‖ ≤ r / 2)
    {sT βT : ℝ} (hβT : 0 ≤ βT)
    (hsT : (2 : ℝ) ^ (top + 5) * (Real.exp (-(γ0 * (1 - η * L) * n0)) * (9 * r ^ 2)) +
      a ^ 2 * ((24 * top + 4) * (γ0 * (η ^ 2 * σ ^ 2) / (1 - η * L))) ≤ sT ^ 2)
    (hbT : Real.exp (-(γ0 * (1 - η * L) * n0)) * (9 * r ^ 2) +
      a ^ 2 * (2 * (γ0 * (η ^ 2 * σ ^ 2) / (1 - η * L)) / (2 : ℝ) ^ top) ≤ βT ^ 2) :
    IsBiasedOperator ((levelLaw top).prod (Measure.infinitePi fun _ : ℕ => (p : Measure Ω)))
      (clippedMap H hη hηL a x0 r) (callEstimate J g η γ0 a n0 top x0 r) sT βT := by
  let Q := (levelLaw top).prod (Measure.infinitePi fun _ : ℕ => (p : Measure Ω))
  have hL := H.L_pos
  have hμ : 0 < 1 - η * L := by linarith
  have hκ0 : 0 ≤ Real.exp (-(γ0 * (1 - η * L) * n0)) := (Real.exp_pos _).le
  have hc0 : 0 ≤ γ0 * (η ^ 2 * σ ^ 2) / (1 - η * L) := by positivity
  have hdata (x : E) := estimator_mean (top := top) (n0 := n0) H hη hηL p g (ballProj x0 r x)
    hγ0 hγ0s hg
  have hsec (x : E) := estimator_second (top := top) (n0 := n0) H hη hηL p g (ballProj x0 r x)
    hγ0 hγ0s hn0 hκ hg
  have hD (x : E) : a ^ 2 * ‖ballProj x0 r x - resH H hη hηL (ballProj x0 r x)‖ ^ 2 ≤ 9 * r ^ 2 := by
    set y := ballProj x0 r x
    have hsub := sub_fixedMap H hη hηL a y
    have hnon := fixedMap_nonexpansive H hη hηL ha.le haη y xstar
    rw [fixedMap_of_zero H hη hηL a hstar] at hnon
    have hyb : ‖y - x0‖ ≤ r := by
      have := ballProj_mem x0 x hr.le
      rwa [Metric.mem_closedBall, dist_eq_norm] at this
    have hyx : ‖y - xstar‖ ≤ 3 * r / 2 := by
      have := norm_sub_le_norm_sub_add_norm_sub y x0 xstar
      rw [norm_sub_rev x0 xstar] at this
      linarith
    have hres : ‖y - fixedMap H hη hηL a y‖ ≤ 3 * r := by
      have := norm_sub_le_norm_sub_add_norm_sub y xstar (fixedMap H hη hηL a y)
      rw [norm_sub_rev xstar] at this
      linarith
    rw [hsub, norm_smul, Real.norm_of_nonneg ha.le] at hres
    have := (sq_le_sq₀ (by positivity) (by positivity)).mpr hres
    nlinarith
  have hm (x : E) : Measurable (fun θ : Fin (top + 1) × (ℕ → Ω) =>
      callEstimate J g η γ0 a n0 top x0 r x θ) :=
    (callEstimate_measurable H hη g hγ0 hg.measurable a x0 hr.le).comp measurable_prodMk_left
  have hcall (x : E) (θ : Fin (top + 1) × (ℕ → Ω)) :
      callEstimate J g η γ0 a n0 top x0 r x θ - clippedMap H hη hηL a x0 r x =
        a • (estimator J g η γ0 n0 top (ballProj x0 r x) (θ.1 : ℕ) θ.2 -
          resH H hη hηL (ballProj x0 r x)) := by
    simp only [callEstimate, clippedMap, fixedMap, smul_sub]
    abel
  have hi (x : E) : Integrable (callEstimate J g η γ0 a n0 top x0 r x) Q :=
    (integrable_const _).add ((hdata x).1.smul a)
  have hsq (x : E) (θ : Fin (top + 1) × (ℕ → Ω)) :
      ‖callEstimate J g η γ0 a n0 top x0 r x θ - clippedMap H hη hηL a x0 r x‖ ^ 2 =
        a ^ 2 * ‖estimator J g η γ0 n0 top (ballProj x0 r x) (θ.1 : ℕ) θ.2 -
          resH H hη hηL (ballProj x0 r x)‖ ^ 2 := by
    rw [hcall, norm_smul, Real.norm_of_nonneg ha.le, mul_pow]
  have hX2 (x : E) : Integrable (fun θ =>
      ‖callEstimate J g η γ0 a n0 top x0 r x θ - clippedMap H hη hηL a x0 r x‖ ^ 2) Q := by
    simp_rw [hsq]
    exact (hsec x).1.const_mul _
  have hbound (x : E) : (∫ θ, ‖callEstimate J g η γ0 a n0 top x0 r x θ - clippedMap H hη hηL a x0 r x‖ ^ 2 ∂Q) ≤
      (2 : ℝ) ^ (top + 5) * (Real.exp (-(γ0 * (1 - η * L) * n0)) * (9 * r ^ 2)) +
        a ^ 2 * ((24 * top + 4) * (γ0 * (η ^ 2 * σ ^ 2) / (1 - η * L))) := by
    simp_rw [hsq]
    rw [integral_const_mul]
    have h1 := mul_le_mul_of_nonneg_left (hsec x).2 (sq_nonneg a)
    refine h1.trans ?_
    have h2 := mul_le_mul_of_nonneg_left (hD x)
      (show 0 ≤ (2 : ℝ) ^ (top + 5) * Real.exp (-(γ0 * (1 - η * L) * n0)) by positivity)
    nlinarith
  have hvar (x : E) := variance_le_second_moment Q (callEstimate J g η γ0 a n0 top x0 r x) (hi x)
    (clippedMap H hη hηL a x0 r x) (hX2 x)
  refine ⟨callEstimate_measurable H hη g hγ0 hg.measurable a x0 hr.le, hi,
    fun x => (hvar x).1, fun x => (hvar x).2.1.trans ((hbound x).trans hsT), fun x => ?_⟩
  have hmeanC : (∫ θ, callEstimate J g η γ0 a n0 top x0 r x θ ∂Q) - clippedMap H hη hηL a x0 r x =
      a • ((∫ ξ, innerPath J g η γ0 n0 (ballProj x0 r x) (levelTime n0 top) ξ
        ∂Measure.infinitePi fun _ : ℕ => (p : Measure Ω)) - resH H hη hηL (ballProj x0 r x)) := by
    have : (∫ θ, callEstimate J g η γ0 a n0 top x0 r x θ ∂Q) =
        (1 - a) • ballProj x0 r x + a • ∫ θ : Fin (top + 1) × (ℕ → Ω),
          estimator J g η γ0 n0 top (ballProj x0 r x) (θ.1 : ℕ) θ.2 ∂Q := by
      unfold callEstimate
      have hY : Integrable (fun θ : Fin (top + 1) × (ℕ → Ω) =>
          a • estimator J g η γ0 n0 top (ballProj x0 r x) (θ.1 : ℕ) θ.2) Q := (hdata x).1.smul a
      rw [integral_add (f := fun _ => (1 - a) • ballProj x0 r x)
        (g := fun θ : Fin (top + 1) × (ℕ → Ω) =>
          a • estimator J g η γ0 n0 top (ballProj x0 r x) (θ.1 : ℕ) θ.2)
        (integrable_const _) hY]
      congr 1
      · simp
      · exact integral_smul _ _
    rw [this, (hdata x).2]
    simp only [clippedMap, fixedMap, smul_sub]
    abel
  rw [hmeanC, norm_smul, Real.norm_of_nonneg ha.le]
  set u := resH H hη hηL (ballProj x0 r x)
  let μ := Measure.infinitePi fun _ : ℕ => (p : Measure Ω)
  have hZi := innerPath_integrable (n0 := n0) H hη hηL p g (ballProj x0 r x) hγ0 hγ0s hg
    (levelTime n0 top)
  have hZ2 := path_integrable H hη hηL (n0 := n0) p g (ballProj x0 r x) hγ0 hγ0s hg (levelTime n0 top)
  have hbias := (variance_le_second_moment μ _ hZi u hZ2).2.2
  have hlev := level_moment H hη hηL p g (ballProj x0 r x) hγ0 hγ0s hn0 hκ hg top
  unfold mse at hlev
  have hsqb : (a * ‖(∫ ξ, innerPath J g η γ0 n0 (ballProj x0 r x) (levelTime n0 top) ξ ∂μ) - u‖) ^ 2 ≤ βT ^ 2 := by
    rw [mul_pow]
    have h1 := mul_le_mul_of_nonneg_left (hbias.trans hlev) (sq_nonneg a)
    refine h1.trans (le_trans ?_ hbT)
    have h2 := mul_le_mul_of_nonneg_left (hD x) hκ0
    nlinarith
  exact (abs_le_of_sq_le_sq' hsqb hβT).2

end Operator

end LongTails.Proofs.FullRangeOperator
