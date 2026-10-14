import LongTails.Proofs.AcceleratedMarkovExpectation
import LongTails.Proofs.AcceleratedMarkovExecution
import LongTails.Proofs.AcceleratedMarkovRates

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace OracleTemplate.HeavyTailedMarkovGradient

open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω]

lemma clippedRun_energy_expectation (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (π : ProbabilityMeasure Ω) (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω))
    {f : E → ℝ} {g : E → Ω → E} (hG : Measurable (Function.uncurry g))
    (hGi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ y, g x y ∂(π : Measure Ω) = gradient f x)
    {L D R C p σ δ : ℝ} (hL : 0 < L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R)
    (hC : 0 < C) (hLC : 4 * L * R ≤ C) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmi : ∀ x, Integrable (fun y => ‖g x y - gradient f x‖ ^ p) (π : Measure Ω))
    (hmoment : ∀ x, (∫ y, ‖g x y - gradient f x‖ ^ p ∂(π : Measure Ω)) ≤ σ ^ p)
    (m : ℕ) (hd : Integrable (mixingDistance κ π m) (π : Measure Ω))
    (hmix : (∫ y, mixingDistance κ π m y ∂(π : Measure Ω)) ≤ δ)
    (x0 u : E) (hm : IsMinOn f univ u) (hu : ‖u - x0‖ ≤ R) (K : ℕ) :
    (∫ ξ, StochasticGradient.acceleratedEnergy f D u K (clippedRun g D R C m x0 ξ K).2
      ∂(pathLaw κ π : Measure (ℕ → Ω))) ≤
      D / 2 * R ^ 2 + StochasticGradient.acceleratedWeight K *
        (2 * R * (σ ^ p / (C / 2) ^ (p - 1)) + 12 * R * C * δ) +
      (∑ k ∈ Finset.range K, (((k : ℝ) + 1) / 2) ^ p) *
        ((2 * R) ^ (2 - p) / (D / 4) ^ (p - 1) * σ ^ p) := by
  let P : Measure (ℕ → Ω) := pathLaw κ π
  have hEi (k : ℕ) : Integrable (fun ξ => StochasticGradient.acceleratedEnergy f D u k
      (clippedRun g D R C m x0 ξ k).2) P :=
    integrable_energy_ball (measurable_clippedRun hG D R C m x0 k) hL hD.le hR hg hlip hm hu
      (fun ξ => clippedRun_ball g D C hR m x0 ξ k) k
  have hErr (k : ℕ) : Integrable (clippedRunError f g D R C p m x0 u k) P :=
    integrable_clippedRunError hG hL hD hR hC.le hLC hg hlip m x0 u hm hu k
  induction K with
  | zero =>
    simp only [clippedRun, StochasticGradient.acceleratedEnergy, StochasticGradient.acceleratedWeight,
      Nat.cast_zero, zero_mul, zero_div, zero_add, Finset.range_zero, Finset.sum_empty,
      add_zero, integral_const, probReal_univ, one_smul]
    have hh : ‖x0 - u‖ ^ 2 ≤ R ^ 2 := by
      rw [norm_sub_rev]
      exact (sq_le_sq₀ (norm_nonneg _) hR).mpr hu
    exact mul_le_mul_of_nonneg_left hh (by positivity)
  | succ K ih =>
    have hstep := integral_mono (hEi (K + 1)) ((hEi K).add (hErr K))
      (clippedRun_energy_step g hL hD hLD hR hp hp2 hc hg hlip m x0 u hu K)
    simp only [Pi.add_apply] at hstep
    rw [integral_add (hEi K) (hErr K)] at hstep
    have herr := integral_clippedRunError κ π hπ hG hGi hmean hL hD hR hC hLC hp hg hlip hmi hmoment
      m hd hmix x0 u hm hu K
    have hw : StochasticGradient.acceleratedWeight (K + 1) =
        StochasticGradient.acceleratedWeight K + ((K : ℝ) + 1) / 2 := by
      simp only [StochasticGradient.acceleratedWeight, Nat.cast_add, Nat.cast_one]
      ring
    rw [hw, Finset.sum_range_succ]
    change (∫ ξ, StochasticGradient.acceleratedEnergy f D u (K + 1) (clippedRun g D R C m x0 ξ (K + 1)).2 ∂P) ≤ _
    nlinarith only [hstep, ih, herr]

lemma clippedRun_expected_gap (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (π : ProbabilityMeasure Ω) (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω))
    {f : E → ℝ} {g : E → Ω → E} (hG : Measurable (Function.uncurry g))
    (hGi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ y, g x y ∂(π : Measure Ω) = gradient f x)
    {L D R C p σ δ : ℝ} (hL : 0 < L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R)
    (hC : 0 < C) (hLC : 4 * L * R ≤ C) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmi : ∀ x, Integrable (fun y => ‖g x y - gradient f x‖ ^ p) (π : Measure Ω))
    (hmoment : ∀ x, (∫ y, ‖g x y - gradient f x‖ ^ p ∂(π : Measure Ω)) ≤ σ ^ p)
    (m : ℕ) (hd : Integrable (mixingDistance κ π m) (π : Measure Ω))
    (hmix : (∫ y, mixingDistance κ π m y ∂(π : Measure Ω)) ≤ δ)
    (x0 u : E) (hm : IsMinOn f univ u) (hu : ‖u - x0‖ ≤ R) (K : ℕ) (hK : 0 < K) :

    Integrable (fun ξ => f (clippedRun g D R C m x0 ξ K).2.1 - f u)
      (pathLaw κ π : Measure (ℕ → Ω)) ∧
    (∫ ξ, f (clippedRun g D R C m x0 ξ K).2.1 - f u ∂(pathLaw κ π : Measure (ℕ → Ω))) ≤
      (D / 2 * R ^ 2 + (∑ k ∈ Finset.range K, (((k : ℝ) + 1) / 2) ^ p) *
        ((2 * R) ^ (2 - p) / (D / 4) ^ (p - 1) * σ ^ p)) / StochasticGradient.acceleratedWeight K +
      (2 * R * (σ ^ p / (C / 2) ^ (p - 1)) + 12 * R * C * δ) := by
  let P : Measure (ℕ → Ω) := pathLaw κ π
  have hs := measurable_clippedRun hG D R C m x0 K
  have hf : Measurable f :=
    (continuous_iff_continuousAt.mpr (fun x => (hg x).differentiableAt.continuousAt)).measurable
  have hFi : Integrable (fun ξ => f (clippedRun g D R C m x0 ξ K).2.1 - f u) P := by
    apply Integrable.of_bound ((hf.comp hs.fst).sub_const (f u)).aestronglyMeasurable (2 * L * R ^ 2)
    apply Filter.Eventually.of_forall
    intro ξ
    have hh := smooth_gap_ball hL hR hg hlip hm hu (clippedRun_ball g D C hR m x0 ξ K).1
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_nonneg hh.1] using hh.2
  refine ⟨hFi, ?_⟩
  have hEi : Integrable (fun ξ => StochasticGradient.acceleratedEnergy f D u K
      (clippedRun g D R C m x0 ξ K).2) P :=
    integrable_energy_ball hs hL hD.le hR hg hlip hm hu (fun ξ => clippedRun_ball g D C hR m x0 ξ K) K
  have hw : 0 < StochasticGradient.acceleratedWeight K := by
    unfold StochasticGradient.acceleratedWeight
    have : (0 : ℝ) < K := Nat.cast_pos.mpr hK
    positivity
  have hlo := integral_mono (hFi.const_mul (StochasticGradient.acceleratedWeight K)) hEi
    (fun ξ => le_add_of_nonneg_right (by positivity : 0 ≤ D / 2 * ‖(clippedRun g D R C m x0 ξ K).2.2 - u‖ ^ 2))
  rw [integral_const_mul] at hlo
  have hb := clippedRun_energy_expectation κ π hπ hG hGi hmean hL hD hLD hR hC hLC hp hp2 hc hg hlip
    hmi hmoment m hd hmix x0 u hm hu K
  have hh := hlo.trans hb
  apply (mul_le_mul_iff_right₀ hw).mp
  calc
    _ ≤ _ := hh
    _ = _ := by field_simp; ring

lemma clippedRun_rate (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (π : ProbabilityMeasure Ω) (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω))
    {f : E → ℝ} {g : E → Ω → E} (hG : Measurable (Function.uncurry g))
    (hGi : ∀ x, Integrable (g x) (π : Measure Ω))
    (hmean : ∀ x, ∫ y, g x y ∂(π : Measure Ω) = gradient f x)
    {L D R C p σ δ : ℝ} (hL : 0 < L) (hD : 0 < D) (hLD : 2 * L ≤ D) (hR : 0 ≤ R)
    (hσ : 0 ≤ σ) (hC : 0 < C) (hLC : 4 * L * R ≤ C) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hmi : ∀ x, Integrable (fun y => ‖g x y - gradient f x‖ ^ p) (π : Measure Ω))
    (hmoment : ∀ x, (∫ y, ‖g x y - gradient f x‖ ^ p ∂(π : Measure Ω)) ≤ σ ^ p)
    (m : ℕ) (hd : Integrable (mixingDistance κ π m) (π : Measure Ω))
    (hmix : (∫ y, mixingDistance κ π m y ∂(π : Measure Ω)) ≤ δ)
    (x0 u : E) (hm : IsMinOn f univ u) (hu : ‖u - x0‖ ≤ R) (K : ℕ) (hK : 0 < K) :

    Integrable (fun ξ => f (clippedRun g D R C m x0 ξ K).2.1 - f u)
      (pathLaw κ π : Measure (ℕ → Ω)) ∧
    (∫ ξ, f (clippedRun g D R C m x0 ξ K).2.1 - f u ∂(pathLaw κ π : Measure (ℕ → Ω))) ≤
      2 * D * R ^ 2 / (K : ℝ) ^ 2 +
      4 * σ ^ p * R ^ (2 - p) * (K : ℝ) ^ (p - 1) / D ^ (p - 1) +
      (2 * R * (σ ^ p / (C / 2) ^ (p - 1)) + 12 * R * C * δ) := by
  have hh := clippedRun_expected_gap κ π hπ hG hGi hmean hL hD hLD hR hC hLC hp hp2 hc hg hlip
    hmi hmoment m hd hmix x0 u hm hu K hK
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact accelerated_finite_sum_bound hD hR hσ (by linarith) K hK

end OracleTemplate.HeavyTailedMarkovGradient
