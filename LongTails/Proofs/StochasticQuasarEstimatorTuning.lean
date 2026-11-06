import LongTails.Proofs.StochasticQuasarMlmcCost
import LongTails.Proofs.StochasticQuasarMlmcExecution

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.StochasticQuasar

lemma estimator_radius_pos {L v : ℝ} (hL : 0 < L) (hv : 0 < v) (β : ℝ) :
    0 < estimatorRadius L v β := by
  unfold estimatorRadius
  positivity

lemma estimator_radius_sq (L v β : ℝ) :
    estimatorRadius L v β ^ 2 = v ^ 2 / (40 * L ^ 2 * (estimatorDepth v β + 1 : ℝ)) := by
  unfold estimatorRadius
  rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 10 * (estimatorDepth v β + 1 : ℝ))]
  congr 1
  ring

lemma estimator_depth_power_lower (v β : ℝ) :
    v / β ≤ (2 : ℝ) ^ (estimatorDepth v β + 1) := by
  have hn := Nat.le_pow_clog (by decide : 1 < 2) ⌈1 + v / β⌉₊
  have hc : 1 + v / β ≤ (2 : ℝ) ^ estimatorDepth v β := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast hn
  have hp : (2 : ℝ) ^ estimatorDepth v β ≤ (2 : ℝ) ^ (estimatorDepth v β + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
  linarith

lemma estimator_depth_power_upper {v β : ℝ} (hv : 0 < v) (hβ : 0 < β) :
    (2 : ℝ) ^ (estimatorDepth v β + 1) ≤ 4 * (1 + v / β) := by
  have hh := inner_stage_power_lt (by norm_num : (0 : ℝ) < 1)
    (show 1 < 1 + v / β by have hh := div_pos hv hβ; linarith)
  have hp : (2 : ℝ) ^ estimatorDepth v β < 2 * (1 + v / β) := by
    simpa only [innerStageCount, estimatorDepth, div_one] using hh
  rw [pow_succ]
  nlinarith

lemma estimator_depth_four_bound {v β : ℝ} (hv : 0 < v) (hβ : 0 < β) :
    (4 : ℝ) ^ (estimatorDepth v β + 1) ≤ 32 * (1 + v ^ 2 / β ^ 2) := by
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (2 : ℝ) ^ (estimatorDepth v β + 1))
    (estimator_depth_power_upper hv hβ) 2
  have he : ((2 : ℝ) ^ (estimatorDepth v β + 1)) ^ 2 = (4 : ℝ) ^ (estimatorDepth v β + 1) := by
    rw [← pow_mul, Nat.mul_comm (estimatorDepth v β + 1) 2, pow_mul]
    norm_num
  rw [he] at hh
  have hs : (1 + v / β) ^ 2 ≤ 2 * (1 + (v / β) ^ 2) := by nlinarith [sq_nonneg (1 - v / β)]
  rw [div_pow] at hs
  nlinarith

lemma estimator_bias_tuning {L v β : ℝ} (hL : 0 < L) (hv : 0 < v) (hβ : 0 < β) :
    2 * L * mlmcRadius (estimatorRadius L v β) (estimatorDepth v β + 1) ≤ β := by
  have hs : 1 ≤ Real.sqrt (10 * (estimatorDepth v β + 1 : ℝ)) := by
    have he := Real.sq_sqrt (by positivity : 0 ≤ 10 * (estimatorDepth v β + 1 : ℝ))
    have hn := Real.sqrt_nonneg (10 * (estimatorDepth v β + 1 : ℝ))
    have hm : (0 : ℝ) ≤ estimatorDepth v β := by positivity
    nlinarith
  have he : 2 * L * estimatorRadius L v β =
      v / Real.sqrt (10 * (estimatorDepth v β + 1 : ℝ)) := by
    unfold estimatorRadius
    field_simp
  have hb : 2 * L * estimatorRadius L v β ≤ v := by
    rw [he]
    exact div_le_self hv.le hs
  calc
    _ = (2 * L * estimatorRadius L v β) / (2 : ℝ) ^ (estimatorDepth v β + 1) := by
      unfold mlmcRadius
      ring
    _ ≤ v / (2 : ℝ) ^ (estimatorDepth v β + 1) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ ≤ β := by
      apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (estimatorDepth v β + 1))).mpr
      have hh := (div_le_iff₀ hβ).mp (estimator_depth_power_lower v β)
      simpa only [mul_comm] using hh

lemma estimator_second_tuning {L : ℝ} (hL : 0 < L) (v β : ℝ) :
    4 * L ^ 2 * (10 * (estimatorDepth v β + 1 : ℝ) * estimatorRadius L v β ^ 2) = v ^ 2 := by
  rw [estimator_radius_sq]
  have hm : (estimatorDepth v β + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma estimator_inverse_radius {L v : ℝ} (hL : 0 < L) (hv : 0 < v) (β : ℝ) :
    1 / (L ^ 2 * estimatorRadius L v β ^ 2) =
      40 * (estimatorDepth v β + 1 : ℝ) / v ^ 2 := by
  rw [estimator_radius_sq]
  have hm : (estimatorDepth v β + 1 : ℝ) ≠ 0 := by positivity
  field_simp

lemma tuned_estimator_expected_calls {L v : ℝ} (hL : 0 < L) (hv : 0 < v)
    (β σ D : ℝ) :
    (∫ j : Fin (estimatorDepth v β + 1),
      (mlmcCalls L σ D (estimatorRadius L v β) j.val : ℝ)
      ∂(mlmcLevelLaw (estimatorDepth v β) : Measure _)) ≤
      12 * innerStageCount D (estimatorRadius L v β) + 16 +
        3840 * (estimatorDepth v β + 1 : ℝ) ^ 2 * σ ^ 2 / v ^ 2 := by
  have hh := mlmc_expected_calls hL (estimator_radius_pos hL hv β) σ D (estimatorDepth v β)
  have he : 96 * (estimatorDepth v β + 1 : ℝ) * σ ^ 2 /
      (L ^ 2 * estimatorRadius L v β ^ 2) =
      3840 * (estimatorDepth v β + 1 : ℝ) ^ 2 * σ ^ 2 / v ^ 2 := by
    calc
      _ = (96 * (estimatorDepth v β + 1 : ℝ) * σ ^ 2) *
          (1 / (L ^ 2 * estimatorRadius L v β ^ 2)) := by ring
      _ = _ := by rw [estimator_inverse_radius hL hv β]; ring
  rwa [he] at hh

lemma tuned_estimator_max_calls {L v β : ℝ} (hL : 0 < L) (hv : 0 < v) (hβ : 0 < β)
    (σ D : ℝ) (j : Fin (estimatorDepth v β + 1)) :
    (mlmcCalls L σ D (estimatorRadius L v β) j.val : ℝ) ≤
      12 * innerStageCount D (estimatorRadius L v β) + 8 * (estimatorDepth v β + 1 : ℝ) +
        40960 * (estimatorDepth v β + 1 : ℝ) * σ ^ 2 * (1 / v ^ 2 + 1 / β ^ 2) := by
  have hh := mlmc_max_calls hL (estimator_radius_pos hL hv β) σ D (estimatorDepth v β) j
  have he : 32 * σ ^ 2 / (L ^ 2 * estimatorRadius L v β ^ 2) =
      1280 * (estimatorDepth v β + 1 : ℝ) * σ ^ 2 / v ^ 2 := by
    calc
      _ = 32 * σ ^ 2 * (1 / (L ^ 2 * estimatorRadius L v β ^ 2)) := by ring
      _ = _ := by rw [estimator_inverse_radius hL hv β]; ring
  rw [he] at hh
  have hb := mul_le_mul_of_nonneg_left (estimator_depth_four_bound hv hβ)
    (by positivity : 0 ≤ 1280 * (estimatorDepth v β + 1 : ℝ) * σ ^ 2 / v ^ 2)
  have ha : (1280 * (estimatorDepth v β + 1 : ℝ) * σ ^ 2 / v ^ 2) *
      (32 * (1 + v ^ 2 / β ^ 2)) =
      40960 * (estimatorDepth v β + 1 : ℝ) * σ ^ 2 * (1 / v ^ 2 + 1 / β ^ 2) := by
    field_simp
    ring
  rw [ha] at hb
  linarith

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma tuned_envelope_plan_moments {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} {f : E → ℝ} {G : E → E} {g : E → Ω → E}
    {x0 c : E} {L σ D v β : ℝ} (hP : ConstrainedMonotone.Proj Q P)
    (hL : 0 < L) (hD0 : 0 < D) (hv : 0 < v) (hβ : 0 < β) (hx0 : x0 ∈ Q)
    (hQ : IsCompact Q) (hcv : Convex ℝ Q)
    (hD : ∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ D)
    (hG : ∀ x ∈ Q, HasGradientAt f (G x) x)
    (hlip : ∀ x ∈ Q, ∀ y ∈ Q, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ x ∈ Q, Integrable (g x) μ)
    (hmean : ∀ x ∈ Q, (∫ ω, g x ω ∂μ) = G x)
    (hg2 : ∀ x ∈ Q, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) μ)
    (hvar : ∀ x ∈ Q, (∫ ω, ‖g x ω - G x‖ ^ 2 ∂μ) ≤ σ ^ 2) :
    let ν := (mlmcLevelLaw (estimatorDepth v β) : Measure _).prod
      (Measure.infinitePi fun _ : ℕ => μ)
    let Z := fun w : Fin (estimatorDepth v β + 1) × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (tunedEnvelopePlan L σ D v β c x0 w.1) 0
    let target := (2 * L) • (c - constrainedProx Q f L c)
    Integrable Z ν ∧ ‖(∫ w, Z w ∂ν) - target‖ ≤ β ∧
      Integrable (fun w => ‖Z w - target‖ ^ 2) ν ∧
      (∫ w, ‖Z w - target‖ ^ 2 ∂ν) ≤ v ^ 2 := by
  have hh := prox_mlmc_plan_moments (c := c) hP hL hD0 (estimator_radius_pos hL hv β)
    hx0 hQ hcv hD hG hlip hgm hgi hmean hg2 hvar (estimatorDepth v β)
  have hs := scaled_estimator_moments (c := c) hL.le hh.1 hh.2.2.1 hh.2.2.2.2 hh.2.2.2.1
  dsimp only
  simp_rw [tunedEnvelopePlan, sampled_envelope_estimate]
  exact ⟨hs.1, hs.2.1.trans (estimator_bias_tuning hL hv hβ), hs.2.2.1,
    hs.2.2.2.trans_eq (estimator_second_tuning hL v β)⟩

end OracleTemplate.StochasticQuasar
