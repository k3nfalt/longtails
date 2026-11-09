import LongTails.Proofs.FullRangeInner
import LongTails.Proofs.FullRangeClip
import LongTails.Proofs.BiasedAnchoring
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.FullRangeEstimator

open OracleTemplate.StochasticCohypomonotone
open LongTails.Algorithms.FullRangeMlmc
open LongTails.Setups.StochasticGeneralizedMonotone (IsStochasticOperator)
open LongTails.Proofs.FullRangeInner

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
variable {F : E → E} {G : E → Set E} {J : ℝ → E → E} {L ρ η : ℝ}

section Level

variable (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) {σ γ0 : ℝ} {n0 : ℕ}
  (p : ProbabilityMeasure Ω) (g : E → Ω → E) (x : E)

noncomputable def mse (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) (γ0 : ℝ) (n0 : ℕ)
    (p : ProbabilityMeasure Ω) (g : E → Ω → E) (x : E) (k : ℕ) : ℝ :=
  ∫ ξ, ‖innerPath J g η γ0 n0 x k ξ - resH H hη hηL x‖ ^ 2
    ∂Measure.infinitePi fun _ : ℕ => (p : Measure Ω)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma mse_nonneg (γ0 : ℝ) (n0 k : ℕ) : 0 ≤ mse H hη hηL γ0 n0 p g x k :=
  integral_nonneg fun _ => sq_nonneg _

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma mse_zero (γ0 : ℝ) (n0 : ℕ) :
    mse H hη hηL γ0 n0 p g x 0 = ‖x - resH H hη hηL x‖ ^ 2 := by
  unfold mse
  have : (fun ξ : ℕ → Ω => ‖innerPath J g η γ0 n0 x 0 ξ - resH H hη hηL x‖ ^ 2) =
      fun _ => ‖x - resH H hη hηL x‖ ^ 2 := by
    funext ξ
    simp [innerPath, OracleTemplate.ContinuizedSimilarQuasar.iterateSamples]
  rw [this]
  simp

lemma level_moment (hγ0 : 0 < γ0) (hγ0s : γ0 * (1 + η * L) ^ 2 ≤ 1 - η * L) (hn0 : 0 < n0)
    (hκ : Real.exp (-(γ0 * (1 - η * L) * n0 / 2)) ≤ 1 / 16)
    (hg : IsStochasticOperator (p : Measure Ω) F g σ) (l : ℕ) :
    mse H hη hηL γ0 n0 p g x (levelTime n0 l) ≤
      Real.exp (-(γ0 * (1 - η * L) * n0)) * ‖x - resH H hη hηL x‖ ^ 2 +
        2 * (γ0 * (η ^ 2 * σ ^ 2) / (1 - η * L)) / (2 : ℝ) ^ l := by
  have hL := H.L_pos
  set μ := 1 - η * L with hμd
  have hμ : 0 < μ := by rw [hμd]; linarith
  have hμ1 : μ ≤ 1 := by rw [hμd]; nlinarith [mul_pos hη hL]
  have hℓ : 1 ≤ (1 + η * L) ^ 2 := by nlinarith [mul_pos hη hL]
  have hγle : γ0 ≤ μ := by nlinarith
  set C := η ^ 2 * σ ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  set c := γ0 * C / μ with hc
  have hc0 : 0 ≤ c := by positivity
  set D := ‖x - resH H hη hηL x‖ ^ 2 with hD
  have hD0 : 0 ≤ D := sq_nonneg _
  let u := mse H hη hηL γ0 n0 p g x
  have hrec (k : ℕ) := (path_succ_bound H hη hηL (n0 := n0) p g x hγ0 hγ0s hg k
    (path_integrable H hη hηL (n0 := n0) p g x hγ0 hγ0s hg k)).2
  have hepoch (γ : ℝ) (e s m : ℕ) (hγv : γ = γ0 / (2 : ℝ) ^ e)
      (hrange : ∀ i < m, epochOf n0 (s + i) = e) :
      u (s + m) ≤ (1 - γ * μ) ^ m * u s + γ * C / μ := by
    have hγ : 0 < γ := by rw [hγv]; positivity
    have hγle2 : γ ≤ γ0 := by
      rw [hγv]
      exact div_le_self hγ0.le (one_le_pow₀ (by norm_num))
    have ha : 0 < γ * μ := by positivity
    have ha1 : γ * μ ≤ 1 := by nlinarith
    have hb : 0 ≤ γ ^ 2 * C := by positivity
    have := geometric_recursion (u := u) ha ha1 hb s m (fun i hi => by
      have h := hrec (s + i)
      have hst : stepAt γ0 n0 (s + i) = γ := by
        unfold stepAt
        rw [hrange i hi, hγv]
      rw [hst] at h
      simpa only [u, mse, mul_assoc] using h)
    have he : γ ^ 2 * C / (γ * μ) = γ * C / μ := by
      field_simp
    rwa [he] at this
  induction l with
  | zero =>
      have h0 := hepoch γ0 0 0 n0 (by simp) (fun i hi => by
        simpa using epochOf_of_lt n0 i hn0 hi)
      have hu0 : u 0 = D := mse_zero H hη hηL p g x γ0 n0
      simp only [zero_add] at h0
      rw [hu0] at h0
      have hpow := pow_le_exp_mul (a := γ0 * μ) (by nlinarith) n0
      have hpow2 : (1 - γ0 * μ) ^ n0 ≤ Real.exp (-(γ0 * μ * n0)) := hpow
      have hmul := mul_le_mul_of_nonneg_right hpow2 hD0
      have ht : levelTime n0 0 = n0 := by simp [levelTime]
      change u (levelTime n0 0) ≤ _
      rw [ht]
      simp only [pow_zero, div_one]
      linarith
  | succ l ih =>
      set s := levelTime n0 l with hs
      have hsv : s = n0 * 2 ^ l := rfl
      have hnext : levelTime n0 (l + 1) = s + s := by
        simp only [levelTime, hsv, pow_succ]
        ring
      have hγv : γ0 / (2 : ℝ) ^ (l + 1) = γ0 / (2 : ℝ) ^ (l + 1) := rfl
      have h1 := hepoch (γ0 / (2 : ℝ) ^ (l + 1)) (l + 1) s s rfl (fun i hi => by
        apply epochOf_of_range n0 l (s + i) hn0
        · rw [← hsv]; omega
        · have : n0 * 2 ^ (l + 1) = s + s := by rw [hsv, pow_succ]; ring
          omega)
      have hexp : (1 - γ0 / (2 : ℝ) ^ (l + 1) * μ) ^ s ≤ 1 / 16 := by
        have ha1 : γ0 / (2 : ℝ) ^ (l + 1) * μ ≤ 1 := by
          have : γ0 / (2 : ℝ) ^ (l + 1) ≤ γ0 := div_le_self hγ0.le (one_le_pow₀ (by norm_num))
          nlinarith
        have h2 := pow_le_exp_mul ha1 s
        have h3 : γ0 / (2 : ℝ) ^ (l + 1) * μ * (s : ℝ) = γ0 * μ * n0 / 2 := by
          simp only [hsv]
          push_cast
          field_simp
          ring
        rw [h3] at h2
        exact h2.trans hκ
      have hus : 0 ≤ u s := mse_nonneg H hη hηL p g x γ0 n0 s
      have h4 := mul_le_mul_of_nonneg_right hexp hus
      have hval : γ0 / (2 : ℝ) ^ (l + 1) * C / μ = c / (2 : ℝ) ^ (l + 1) := by
        rw [hc]
        field_simp
      change u (levelTime n0 (l + 1)) ≤ _
      rw [hnext]
      rw [hval] at h1
      have hih : u s ≤ Real.exp (-(γ0 * μ * n0)) * D + 2 * c / (2 : ℝ) ^ l := ih
      have hκ0 : 0 ≤ Real.exp (-(γ0 * μ * n0)) * D := by positivity
      have hp : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
      have hsplit : c / (2 : ℝ) ^ (l + 1) = (c / (2 : ℝ) ^ l) / 2 := by
        rw [pow_succ]
        field_simp
      have hsplit2 : 2 * c / (2 : ℝ) ^ (l + 1) = c / (2 : ℝ) ^ l := by
        rw [pow_succ]
        field_simp
      have hsplit3 : 2 * c / (2 : ℝ) ^ l = 2 * (c / (2 : ℝ) ^ l) := by ring
      have hcp : 0 ≤ c / (2 : ℝ) ^ l := by positivity
      rw [hsplit2]
      rw [hsplit] at h1
      rw [hsplit3] at hih
      nlinarith

end Level


noncomputable def levelLaw (top : ℕ) : Measure (Fin (top + 1)) :=
  ∑ l : Fin (top + 1), ENNReal.ofReal (levelWeight top l) • Measure.dirac l

lemma levelWeight_pos (top l : ℕ) : 0 < levelWeight top l := by
  unfold levelWeight
  split_ifs <;> positivity

lemma tail_weight_sum (m : ℕ) :
    ∑ l ∈ Finset.range m, (1 : ℝ) / (2 : ℝ) ^ (l + 1) = 1 - 1 / (2 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      field_simp
      ring

lemma levelWeight_sum (top : ℕ) : ∑ l : Fin (top + 1), levelWeight top l = 1 := by
  rw [Fin.sum_univ_succ]
  have h0 : levelWeight top ((0 : Fin (top + 1)) : ℕ) = 1 / (2 : ℝ) ^ top := by simp [levelWeight]
  have hs : ∀ i : Fin top, levelWeight top (i.succ : Fin (top + 1)) = 1 / (2 : ℝ) ^ ((i : ℕ) + 1) := by
    intro i
    simp [levelWeight]
  simp only [hs, h0]
  rw [Fin.sum_univ_eq_sum_range (fun l => (1 : ℝ) / (2 : ℝ) ^ (l + 1)) top, tail_weight_sum]
  ring

instance levelLaw_prob (top : ℕ) : IsProbabilityMeasure (levelLaw top) := by
  constructor
  simp only [levelLaw, Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  have h := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (f := fun l : Fin (top + 1) => levelWeight top (l : ℕ)) (fun l _ => (levelWeight_pos top l).le)
  rw [← h, levelWeight_sum]
  simp

lemma integral_levelLaw {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (top : ℕ)
    (f : Fin (top + 1) → V) :
    ∫ l, f l ∂levelLaw top = ∑ l : Fin (top + 1), levelWeight top (l : ℕ) • f l := by
  unfold levelLaw
  rw [integral_finsetSum_measure (fun l _ =>
    (Integrable.of_finite (μ := Measure.dirac l)).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (levelWeight_pos top l).le]

lemma theta_integral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] (top : ℕ)
    (μ : Measure (ℕ → Ω)) [IsProbabilityMeasure μ] (h : Fin (top + 1) → (ℕ → Ω) → V)
    (hm : ∀ l, Measurable (h l)) (hi : ∀ l, Integrable (h l) μ) :
    Integrable (fun w : Fin (top + 1) × (ℕ → Ω) => h w.1 w.2) ((levelLaw top).prod μ) ∧
    (∫ w, h w.1 w.2 ∂(levelLaw top).prod μ) =
      ∑ l : Fin (top + 1), levelWeight top (l : ℕ) • ∫ ξ, h l ξ ∂μ := by
  have hmeas : Measurable (fun w : Fin (top + 1) × (ℕ → Ω) => h w.1 w.2) :=
    measurable_from_prod_countable_right hm
  have hint : Integrable (fun w : Fin (top + 1) × (ℕ → Ω) => h w.1 w.2) ((levelLaw top).prod μ) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    exact ⟨Filter.Eventually.of_forall hi, Integrable.of_finite⟩
  refine ⟨hint, ?_⟩
  rw [integral_prod _ hint, integral_levelLaw]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma estimator_mean_pointwise (top : ℕ) (Z : ℕ → E) :
    ∑ l : Fin (top + 1), levelWeight top (l : ℕ) •
        (if (l : ℕ) = 0 then Z 0 else Z 0 + (levelWeight top (l : ℕ))⁻¹ • (Z l - Z ((l : ℕ) - 1))) =
      Z top := by
  rw [Fin.sum_univ_succ]
  have hs : ∀ i : Fin top, levelWeight top ((i.succ : Fin (top + 1)) : ℕ) •
      (if ((i.succ : Fin (top + 1)) : ℕ) = 0 then Z 0 else
        Z 0 + (levelWeight top ((i.succ : Fin (top + 1)) : ℕ))⁻¹ •
          (Z (i.succ : Fin (top + 1)) - Z (((i.succ : Fin (top + 1)) : ℕ) - 1))) =
      (1 / (2 : ℝ) ^ ((i : ℕ) + 1)) • Z 0 + (Z ((i : ℕ) + 1) - Z (i : ℕ)) := by
    intro i
    have hw : levelWeight top ((i.succ : Fin (top + 1)) : ℕ) = 1 / (2 : ℝ) ^ ((i : ℕ) + 1) := by
      simp [levelWeight]
    have hne : (1 / (2 : ℝ) ^ ((i : ℕ) + 1)) ≠ 0 := by positivity
    simp only [Fin.val_succ, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel] at *
    rw [hw, smul_add, smul_smul, mul_inv_cancel₀ hne, one_smul]
  simp only [hs, Finset.sum_add_distrib, ← Finset.sum_smul]
  have h0 : levelWeight top ((0 : Fin (top + 1)) : ℕ) = 1 / (2 : ℝ) ^ top := by simp [levelWeight]
  have hsum1 : ∑ i : Fin top, (1 : ℝ) / (2 : ℝ) ^ ((i : ℕ) + 1) = 1 - 1 / (2 : ℝ) ^ top := by
    rw [Fin.sum_univ_eq_sum_range (fun l => (1 : ℝ) / (2 : ℝ) ^ (l + 1)) top, tail_weight_sum]
  have hsum2 : ∑ i : Fin top, (Z ((i : ℕ) + 1) - Z (i : ℕ)) = Z top - Z 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun l => Z (l + 1) - Z l) top, Finset.sum_range_sub]
  rw [hsum1, hsum2, h0]
  simp only [Fin.val_zero, ite_true]
  rw [sub_smul, one_smul]
  abel

section Moments

variable (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) {σ γ0 : ℝ} {n0 top : ℕ}
  (p : ProbabilityMeasure Ω) (g : E → Ω → E) (x : E)

include H hη in
omit [CompleteSpace E] in
lemma innerPath_measurable (hγ0 : 0 < γ0) (hg : Measurable (Function.uncurry g)) (k : ℕ) :
    Measurable (innerPath J g η γ0 n0 x k) := by
  unfold innerPath
  have h := (OracleTemplate.GapStrongGrowth.iterateSamples_measurable
    (innerStep_measurable H g x hη hγ0 (n0 := n0) hg) k).snd
  exact h.comp (show Measurable (fun ξ : ℕ → Ω => (((0 : ℕ), x), (fun i : Fin k => ξ i))) from
    by fun_prop)

include H hη hηL in
lemma innerPath_integrable (hγ0 : 0 < γ0) (hγ0s : γ0 * (1 + η * L) ^ 2 ≤ 1 - η * L)
    (hg : IsStochasticOperator (p : Measure Ω) F g σ) (k : ℕ) :
    Integrable (innerPath J g η γ0 n0 x k) (Measure.infinitePi fun _ : ℕ => (p : Measure Ω)) := by
  have hm := innerPath_measurable (n0 := n0) H hη g x hγ0 hg.measurable k
  have hsq := path_integrable H hη hηL (n0 := n0) p g x hγ0 hγ0s hg k
  set u := resH H hη hηL x
  have hbound : Integrable (fun ξ => ‖innerPath J g η γ0 n0 x k ξ - u‖ ^ 2 + (1 + ‖u‖))
      (Measure.infinitePi fun _ : ℕ => (p : Measure Ω)) := hsq.add (integrable_const _)
  refine hbound.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  have h1 := norm_sub_norm_le (innerPath J g η γ0 n0 x k ξ) u
  nlinarith [sq_nonneg (‖innerPath J g η γ0 n0 x k ξ - u‖ - 1),
    norm_nonneg (innerPath J g η γ0 n0 x k ξ - u)]

omit [CompleteSpace E] in
include H hη in
lemma estimator_level_measurable (hγ0 : 0 < γ0) (hg : Measurable (Function.uncurry g)) (l : ℕ) :
    Measurable (estimator J g η γ0 n0 top x l) := by
  unfold estimator
  by_cases hl : l = 0
  · simpa [hl] using innerPath_measurable (n0 := n0) H hη g x hγ0 hg n0
  · simp only [hl, ite_false]
    exact (innerPath_measurable H hη g x hγ0 hg _).add
      (((innerPath_measurable H hη g x hγ0 hg _).sub
        (innerPath_measurable H hη g x hγ0 hg _)).const_smul _)

include H hη hηL in
lemma estimator_level_integrable (hγ0 : 0 < γ0) (hγ0s : γ0 * (1 + η * L) ^ 2 ≤ 1 - η * L)
    (hg : IsStochasticOperator (p : Measure Ω) F g σ) (l : ℕ) :
    Integrable (estimator J g η γ0 n0 top x l)
      (Measure.infinitePi fun _ : ℕ => (p : Measure Ω)) := by
  unfold estimator
  by_cases hl : l = 0
  · simpa [hl] using innerPath_integrable (n0 := n0) H hη hηL p g x hγ0 hγ0s hg n0
  · simp only [hl, ite_false]
    exact (innerPath_integrable H hη hηL p g x hγ0 hγ0s hg _).add
      (((innerPath_integrable H hη hηL p g x hγ0 hγ0s hg _).sub
        (innerPath_integrable H hη hηL p g x hγ0 hγ0s hg _)).smul _)

include H hη hηL in
lemma estimator_mean (hγ0 : 0 < γ0) (hγ0s : γ0 * (1 + η * L) ^ 2 ≤ 1 - η * L)
    (hg : IsStochasticOperator (p : Measure Ω) F g σ) :
    Integrable (fun w : Fin (top + 1) × (ℕ → Ω) => estimator J g η γ0 n0 top x w.1 w.2)
      ((levelLaw top).prod (Measure.infinitePi fun _ : ℕ => (p : Measure Ω))) ∧
    (∫ w : Fin (top + 1) × (ℕ → Ω), estimator J g η γ0 n0 top x w.1 w.2
      ∂(levelLaw top).prod (Measure.infinitePi fun _ : ℕ => (p : Measure Ω))) =
      ∫ ξ, innerPath J g η γ0 n0 x (levelTime n0 top) ξ
        ∂Measure.infinitePi fun _ : ℕ => (p : Measure Ω) := by
  let μ := Measure.infinitePi fun _ : ℕ => (p : Measure Ω)
  have hm (l : Fin (top + 1)) := estimator_level_measurable (n0 := n0) (top := top) H hη g x hγ0
    hg.measurable (l : ℕ)
  have hi (l : Fin (top + 1)) := estimator_level_integrable (n0 := n0) (top := top) H hη hηL p g x
    hγ0 hγ0s hg (l : ℕ)
  have h := theta_integral top μ (fun l : Fin (top + 1) => estimator J g η γ0 n0 top x (l : ℕ)) hm hi
  refine ⟨h.1, h.2.trans ?_⟩
  have hsw : ∑ l : Fin (top + 1), levelWeight top (l : ℕ) •
      ∫ ξ, estimator J g η γ0 n0 top x (l : ℕ) ξ ∂μ =
      ∫ ξ, ∑ l : Fin (top + 1), levelWeight top (l : ℕ) • estimator J g η γ0 n0 top x (l : ℕ) ξ ∂μ := by
    have hsum := integral_finsetSum (μ := μ) (Finset.univ : Finset (Fin (top + 1)))
      (f := fun (l : Fin (top + 1)) ξ => levelWeight top (l : ℕ) • estimator J g η γ0 n0 top x (l : ℕ) ξ)
      (fun l _ => (hi l).smul (levelWeight top (l : ℕ)))
    rw [hsum]
    exact Finset.sum_congr rfl fun l _ => (integral_smul _ _).symm
  rw [hsw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have := estimator_mean_pointwise top (fun k => innerPath J g η γ0 n0 x (levelTime n0 k) ξ)
  simp only [levelTime, pow_zero, mul_one] at this
  simpa only [estimator, levelTime] using this

lemma two_power_sum (m : ℕ) :
    ∑ l ∈ Finset.range m, (2 : ℝ) ^ (l + 1) = 2 ^ (m + 1) - 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ (2 : ℝ) (m + 1)]
      ring

include H hη hηL in
lemma estimator_second (hγ0 : 0 < γ0) (hγ0s : γ0 * (1 + η * L) ^ 2 ≤ 1 - η * L) (hn0 : 0 < n0)
    (hκ : Real.exp (-(γ0 * (1 - η * L) * n0 / 2)) ≤ 1 / 16)
    (hg : IsStochasticOperator (p : Measure Ω) F g σ) :
    Integrable (fun w : Fin (top + 1) × (ℕ → Ω) =>
        ‖estimator J g η γ0 n0 top x w.1 w.2 - resH H hη hηL x‖ ^ 2)
      ((levelLaw top).prod (Measure.infinitePi fun _ : ℕ => (p : Measure Ω))) ∧
    (∫ w : Fin (top + 1) × (ℕ → Ω), ‖estimator J g η γ0 n0 top x w.1 w.2 - resH H hη hηL x‖ ^ 2
      ∂(levelLaw top).prod (Measure.infinitePi fun _ : ℕ => (p : Measure Ω))) ≤
      (2 : ℝ) ^ (top + 5) * (Real.exp (-(γ0 * (1 - η * L) * n0)) * ‖x - resH H hη hηL x‖ ^ 2) +
        (24 * top + 4) * (γ0 * (η ^ 2 * σ ^ 2) / (1 - η * L)) := by
  set u := resH H hη hηL x with hu
  let μ := Measure.infinitePi fun _ : ℕ => (p : Measure Ω)
  set B := Real.exp (-(γ0 * (1 - η * L) * n0)) * ‖x - u‖ ^ 2 with hB
  set c := γ0 * (η ^ 2 * σ ^ 2) / (1 - η * L) with hc
  have hL := H.L_pos
  have hμ : 0 < 1 - η * L := by linarith
  have hB0 : 0 ≤ B := by positivity
  have hc0 : 0 ≤ c := by positivity
  let Z : ℕ → (ℕ → Ω) → E := fun k => innerPath J g η γ0 n0 x (levelTime n0 k)
  let M : ℕ → ℝ := fun k => ∫ ξ, ‖Z k ξ - u‖ ^ 2 ∂μ
  have hMb (k : ℕ) : M k ≤ B + 2 * c / (2 : ℝ) ^ k :=
    level_moment H hη hηL p g x hγ0 hγ0s hn0 hκ hg k
  have hZi (k : ℕ) : Integrable (fun ξ => ‖Z k ξ - u‖ ^ 2) μ :=
    path_integrable H hη hηL p g x hγ0 hγ0s hg _
  have hZm (k : ℕ) : Measurable (Z k) := innerPath_measurable H hη g x hγ0 hg.measurable _
  have hZ0 : ∀ ξ, innerPath J g η γ0 n0 x n0 ξ = Z 0 ξ := by
    intro ξ
    simp [Z, levelTime]
  have hYm (l : ℕ) : Measurable (fun ξ => ‖estimator J g η γ0 n0 top x l ξ - u‖ ^ 2) :=
    ((estimator_level_measurable (n0 := n0) (top := top) H hη g x hγ0 hg.measurable l).sub
      measurable_const).norm.pow_const 2
  have hpt (l : ℕ) (hl : l ≠ 0) (ξ : ℕ → Ω) :
      ‖estimator J g η γ0 n0 top x l ξ - u‖ ^ 2 ≤
        2 * ‖Z 0 ξ - u‖ ^ 2 + 4 * ((levelWeight top l)⁻¹) ^ 2 *
          (‖Z l ξ - u‖ ^ 2 + ‖Z (l - 1) ξ - u‖ ^ 2) := by
    have hw := levelWeight_pos top l
    have e : estimator J g η γ0 n0 top x l ξ - u =
        (Z 0 ξ - u) + (levelWeight top l)⁻¹ • ((Z l ξ - u) - (Z (l - 1) ξ - u)) := by
      simp only [estimator, hl, ite_false, hZ0]
      simp only [Z]
      module
    rw [e]
    have h1 := norm_add_le (Z 0 ξ - u) ((levelWeight top l)⁻¹ • ((Z l ξ - u) - (Z (l - 1) ξ - u)))
    rw [norm_smul, Real.norm_of_nonneg (by positivity)] at h1
    have h2 := norm_sub_le (Z l ξ - u) (Z (l - 1) ξ - u)
    set a := ‖Z 0 ξ - u‖
    set b := ‖Z l ξ - u‖
    set d := ‖Z (l - 1) ξ - u‖
    set W := (levelWeight top l)⁻¹
    have hW : 0 ≤ W := by positivity
    set e' := ‖(Z 0 ξ - u) + W • ((Z l ξ - u) - (Z (l - 1) ξ - u))‖
    have ha := norm_nonneg (Z 0 ξ - u)
    have hb := norm_nonneg (Z l ξ - u)
    have hd := norm_nonneg (Z (l - 1) ξ - u)
    have h3 : e' ≤ a + W * (b + d) := h1.trans (by
      have := mul_le_mul_of_nonneg_left h2 hW
      linarith)
    have h4 : e' ^ 2 ≤ (a + W * (b + d)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h3
    have h5 : (a + W * (b + d)) ^ 2 ≤ 2 * a ^ 2 + 2 * (W * (b + d)) ^ 2 := by
      nlinarith [sq_nonneg (a - W * (b + d))]
    have h6 : (b + d) ^ 2 ≤ 2 * (b ^ 2 + d ^ 2) := by nlinarith [sq_nonneg (b - d)]
    have h7 : 2 * (W * (b + d)) ^ 2 ≤ 4 * W ^ 2 * (b ^ 2 + d ^ 2) := by
      have := mul_le_mul_of_nonneg_left h6 (show 0 ≤ 2 * W ^ 2 by positivity)
      nlinarith
    linarith
  have hYi (l : ℕ) : Integrable (fun ξ => ‖estimator J g η γ0 n0 top x l ξ - u‖ ^ 2) μ := by
    by_cases hl : l = 0
    · simpa [estimator, hl, hZ0] using hZi 0
    · exact (((hZi 0).const_mul 2).add (((hZi l).add (hZi (l - 1))).const_mul _)).mono'
        (hYm l).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact hpt l hl ξ)
  have hYb (l : ℕ) (hl : l ≠ 0) :
      (∫ ξ, ‖estimator J g η γ0 n0 top x l ξ - u‖ ^ 2 ∂μ) ≤
        2 * M 0 + 4 * ((levelWeight top l)⁻¹) ^ 2 * (M l + M (l - 1)) := by
    have hR : Integrable (fun ξ => 2 * ‖Z 0 ξ - u‖ ^ 2 + 4 * ((levelWeight top l)⁻¹) ^ 2 *
        (‖Z l ξ - u‖ ^ 2 + ‖Z (l - 1) ξ - u‖ ^ 2)) μ :=
      ((hZi 0).const_mul 2).add (((hZi l).add (hZi (l - 1))).const_mul _)
    refine (integral_mono (hYi l) hR (hpt l hl)).trans (le_of_eq ?_)
    have hsumi : Integrable (fun ξ => ‖Z l ξ - u‖ ^ 2 + ‖Z (l - 1) ξ - u‖ ^ 2) μ :=
      (hZi l).add (hZi (l - 1))
    rw [integral_add (f := fun ξ => 2 * ‖Z 0 ξ - u‖ ^ 2)
      (g := fun ξ => 4 * ((levelWeight top l)⁻¹) ^ 2 * (‖Z l ξ - u‖ ^ 2 + ‖Z (l - 1) ξ - u‖ ^ 2))
      ((hZi 0).const_mul 2) (hsumi.const_mul _),
      integral_const_mul, integral_const_mul,
      integral_add (f := fun ξ => ‖Z l ξ - u‖ ^ 2) (g := fun ξ => ‖Z (l - 1) ξ - u‖ ^ 2)
        (hZi l) (hZi (l - 1))]
  have hth := theta_integral top μ
    (fun l : Fin (top + 1) => fun ξ => ‖estimator J g η γ0 n0 top x (l : ℕ) ξ - u‖ ^ 2)
    (fun l => hYm l) (fun l => hYi l)
  refine ⟨hth.1, ?_⟩
  rw [hth.2, Fin.sum_univ_succ]
  simp only [smul_eq_mul]
  have hzero : levelWeight top ((0 : Fin (top + 1)) : ℕ) *
      ∫ ξ, ‖estimator J g η γ0 n0 top x ((0 : Fin (top + 1)) : ℕ) ξ - u‖ ^ 2 ∂μ =
      (1 / (2 : ℝ) ^ top) * M 0 := by
    have hw : levelWeight top ((0 : Fin (top + 1)) : ℕ) = 1 / (2 : ℝ) ^ top := by simp [levelWeight]
    rw [hw]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp [estimator, hZ0]
  have hstep (i : Fin top) : levelWeight top ((i.succ : Fin (top + 1)) : ℕ) *
      ∫ ξ, ‖estimator J g η γ0 n0 top x ((i.succ : Fin (top + 1)) : ℕ) ξ - u‖ ^ 2 ∂μ ≤
      (1 / (2 : ℝ) ^ ((i : ℕ) + 1)) * (2 * M 0) + (2 : ℝ) ^ ((i : ℕ) + 1) * (8 * B) + 24 * c := by
    have hw : levelWeight top ((i.succ : Fin (top + 1)) : ℕ) = 1 / (2 : ℝ) ^ ((i : ℕ) + 1) := by
      simp [levelWeight]
    have hb := hYb ((i : ℕ) + 1) (Nat.succ_ne_zero _)
    have hval : ((i.succ : Fin (top + 1)) : ℕ) = (i : ℕ) + 1 := by simp
    rw [hw, hval]
    set t := (2 : ℝ) ^ ((i : ℕ) + 1) with ht
    have htp : 0 < t := by positivity
    have hwi : (levelWeight top ((i : ℕ) + 1))⁻¹ = t := by
      simp [levelWeight, ht]
    rw [hwi] at hb
    have hM1 := hMb ((i : ℕ) + 1)
    have hM2 := hMb (i : ℕ)
    have ht2 : (2 : ℝ) ^ (i : ℕ) = t / 2 := by rw [ht, pow_succ]; field_simp
    rw [ht2] at hM2
    have hmul := mul_le_mul_of_nonneg_left hb (show 0 ≤ 1 / t by positivity)
    refine hmul.trans ?_
    have e1 : 1 / t * (2 * M 0 + 4 * t ^ 2 * (M ((i : ℕ) + 1) + M ((i : ℕ) + 1 - 1))) =
        1 / t * (2 * M 0) + 4 * t * (M ((i : ℕ) + 1) + M (i : ℕ)) := by
      simp only [Nat.add_sub_cancel]
      field_simp
    rw [e1]
    have hsum : M ((i : ℕ) + 1) + M (i : ℕ) ≤ 2 * B + 6 * c / t := by
      have e2 : 2 * c / (t / 2) = 4 * c / t := by field_simp; ring
      rw [e2] at hM2
      have e3 : 2 * B + 6 * c / t = (B + 2 * c / t) + (B + 4 * c / t) := by ring
      rw [e3]
      exact add_le_add hM1 hM2
    have hfin := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 4 * t by positivity)
    have e4 : 4 * t * (2 * B + 6 * c / t) = t * (8 * B) + 24 * c := by
      field_simp
      ring
    linarith
  have hsumB : ∑ i : Fin top, levelWeight top ((i.succ : Fin (top + 1)) : ℕ) *
      ∫ ξ, ‖estimator J g η γ0 n0 top x ((i.succ : Fin (top + 1)) : ℕ) ξ - u‖ ^ 2 ∂μ ≤
      (1 - 1 / (2 : ℝ) ^ top) * (2 * M 0) + ((2 : ℝ) ^ (top + 1) - 2) * (8 * B) + top * (24 * c) := by
    refine (Finset.sum_le_sum fun i _ => hstep i).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      Fin.sum_univ_eq_sum_range (fun l => (1 : ℝ) / (2 : ℝ) ^ (l + 1)) top,
      Fin.sum_univ_eq_sum_range (fun l => (2 : ℝ) ^ (l + 1)) top, tail_weight_sum, two_power_sum]
    simp
  rw [hzero]
  have hM0 := hMb 0
  simp only [pow_zero, div_one] at hM0
  have hM0nn : 0 ≤ M 0 := integral_nonneg fun _ => sq_nonneg _
  have hq : (0 : ℝ) < 1 / (2 : ℝ) ^ top := by positivity
  have hq1 : 1 / (2 : ℝ) ^ top ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hpow : (2 : ℝ) ^ (top + 5) = 16 * (2 : ℝ) ^ (top + 1) := by ring
  have hp1 : (2 : ℝ) ≤ (2 : ℝ) ^ (top + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [hpow]
  nlinarith [mul_nonneg hq.le hM0nn, mul_nonneg (sub_nonneg.mpr hq1) hM0nn,
    mul_nonneg (sub_nonneg.mpr hp1) hB0, mul_nonneg (Nat.cast_nonneg top : (0 : ℝ) ≤ top) hc0]

end Moments

end LongTails.Proofs.FullRangeEstimator
