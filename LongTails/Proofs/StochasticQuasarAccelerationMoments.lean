import LongTails.Proofs.StochasticQuasarAccelerationExecution
import LongTails.Proofs.StochasticQuasarEstimatorTuning
import LongTails.Proofs.StochasticQuasarProcess

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticQuasar

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma sampled_acceleration_barrier_drift {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} {f : E → ℝ} {G : E → E} {g : E → Ω → E}
    {x0 x z u : E} {L σ D v β A η c q B H γ : ℝ} {p : ℕ}
    (hP : ConstrainedMonotone.Proj Q P) (hL : 0 < L) (hD0 : 0 < D)
    (hv : 0 < v) (hβ : 0 < β) (hx0 : x0 ∈ Q) (hu : u ∈ Q) (hz : z ∈ Q)
    (hQ : IsCompact Q) (hcv : Convex ℝ Q)
    (hD : ∀ y ∈ Q, ∀ w ∈ Q, ‖y - w‖ ≤ D)
    (hG : ∀ y ∈ Q, HasGradientAt f (G y) y)
    (hlip : ∀ y ∈ Q, ∀ w ∈ Q, ‖G y - G w‖ ≤ L * ‖y - w‖)
    (hmin : IsMinOn f Q u) (hγ : γ ≤ 1)
    (hquasar : ∀ y ∈ Q, γ * (f y - f u) ≤ ⟪G y, y - u⟫)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ y ∈ Q, Integrable (g y) μ)
    (hmean : ∀ y ∈ Q, (∫ ω, g y ω ∂μ) = G y)
    (hg2 : ∀ y ∈ Q, Integrable (fun ω => ‖g y ω - G y‖ ^ 2) μ)
    (hvar : ∀ y ∈ Q, (∫ ω, ‖g y ω - G y‖ ^ 2 ∂μ) ≤ σ ^ 2)
    (hA : 0 < A) (hη : 0 < η) (hc0 : 0 ≤ c) (hq : 0 ≤ q)
    (hB : 0 < B) (hH : 0 < H) (hp : 2 ≤ p)
    (hLη : (2 * L) * η = q) (hc : c ^ 2 ≤ A * η * q)
    (hsmall : 144 * (p : ℝ) * q ≤ 1) (hqcap : q ≤ 1 / 16)
    (hbalance : (p : ℝ) * (A * η) * H ^ 2 = B) :
    let ν := (mlmcLevelLaw (estimatorDepth v β) : Measure (Fin (estimatorDepth v β + 1))).prod
      (Measure.infinitePi fun _ : ℕ => μ)
    let M := constrainedEnvelope Q f L
    let Gm := fun y => (2 * L) • (y - constrainedProx Q f L y)
    let out := fun w : Fin (estimatorDepth v β + 1) × (ℕ → Ω) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
        (accelerationJumpPlan L σ D v β η c H x z x0 w.1) 0
    Integrable (fun w => shiftedEnergyBarrier M u A B p (out w).1 (out w).2) ν ∧
      shiftedEnergyBarrierDrift M Gm u A B γ c p x z +
        (∫ w, shiftedEnergyBarrier M u A B p (out w).1 (out w).2 ∂ν) -
          shiftedEnergyBarrier M u A B p x z ≤
        (2 * (p : ℝ) * (A * η * v ^ 2 + 3 * Real.sqrt (q * (A * η) * B) * β) / B) *
          shiftedEnergyBarrier M u A B p x z := by
  let ν := (mlmcLevelLaw (estimatorDepth v β) : Measure (Fin (estimatorDepth v β + 1))).prod
    (Measure.infinitePi fun _ : ℕ => μ)
  let Z := fun w : Fin (estimatorDepth v β + 1) × (ℕ → Ω) =>
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
      (tunedEnvelopePlan L σ D v β x x0 w.1) 0
  have hPm : Measurable P := (hP.lipschitz).continuous.measurable
  have hZm : Measurable Z :=
    (measurable_envelope_estimate_joint hPm hgm L σ D (estimatorRadius L v β)
      (estimatorDepth v β) 0).comp ((measurable_const (a := (x, x0))).prodMk measurable_id)
  have he := tuned_envelope_plan_moments (c := x) hP hL hD0 hv hβ hx0 hQ hcv hD hG hlip
    hgm hgi hmean hg2 hvar
  have hMu : constrainedEnvelope Q f L u = f u := by
    have hh := constrainedEnvelope_bounds hL.le hQ hG hu hmin u
    have hupp : constrainedEnvelope Q f L u ≤ f u := by simpa using hh.2
    exact le_antisymm hupp hh.1
  have hMm (y : E) : constrainedEnvelope Q f L u ≤ constrainedEnvelope Q f L y := by
    rw [hMu]
    exact (constrainedEnvelope_bounds hL.le hQ hG hu hmin y).1
  have hMq : γ * (constrainedEnvelope Q f L x - constrainedEnvelope Q f L u) ≤
      ⟪(2 * L) • (x - constrainedProx Q f L x), x - u⟫ := by
    rw [hMu]
    exact constrainedEnvelope_quasar hL.le hγ hQ hcv hG hu hquasar x
  have hh := shifted_barrier_jump_drift (μ := ν) (Z := Z) hP hu hz hA hη hc0
    (by positivity : 0 < 2 * L) hq hB hH hp hLη hc hsmall hqcap hbalance
    (constrainedEnvelope_hasGradient hL hQ ⟨u, hu⟩ hcv hG hlip)
    (constrainedEnvelope_gradient_lipschitz hL hQ ⟨u, hu⟩ hcv hG hlip)
    hMm hMq hZm he.1 he.2.2.1 he.2.1 he.2.2.2
  dsimp only
  simp only [sampled_acceleration_jump]
  exact hh

lemma sampled_acceleration_holding {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Set E} {P : E → E} {f : E → ℝ} {G : E → E} {g : E → Ω → E}
    {x0 x z u : E} {L σ D v β η q B γ ρ s T : ℝ} {p : ℕ} {A c H : ℝ → ℝ}
    (hP : ConstrainedMonotone.Proj Q P) (hL : 0 < L) (hD0 : 0 < D)
    (hv : 0 < v) (hβ : 0 < β) (hx0 : x0 ∈ Q) (hu : u ∈ Q) (hz : z ∈ Q)
    (hQ : IsCompact Q) (hcv : Convex ℝ Q)
    (hD : ∀ y ∈ Q, ∀ w ∈ Q, ‖y - w‖ ≤ D)
    (hG : ∀ y ∈ Q, HasGradientAt f (G y) y)
    (hlip : ∀ y ∈ Q, ∀ w ∈ Q, ‖G y - G w‖ ≤ L * ‖y - w‖)
    (hmin : IsMinOn f Q u) (hγ0 : 0 < γ) (hγ : γ ≤ 1)
    (hquasar : ∀ y ∈ Q, γ * (f y - f u) ≤ ⟪G y, y - u⟫)
    (hgm : Measurable (Function.uncurry g)) (hgi : ∀ y ∈ Q, Integrable (g y) μ)
    (hmean : ∀ y ∈ Q, (∫ ω, g y ω ∂μ) = G y)
    (hg2 : ∀ y ∈ Q, Integrable (fun ω => ‖g y ω - G y‖ ^ 2) μ)
    (hvar : ∀ y ∈ Q, (∫ ω, ‖g y ω - G y‖ ^ 2 ∂μ) ≤ σ ^ 2)
    (hη : 0 < η) (hq : 0 ≤ q) (hB : 0 < B) (hp : 2 ≤ p) (hρ : 0 ≤ ρ) (hs : 0 ≤ s)
    (hAc : Continuous A) (hcc : Continuous c) (hHm : Measurable H)
    (hA : ∀ t, 0 < A t) (hc0 : ∀ t, 0 ≤ c t) (hH : ∀ t, 0 < H t)
    (hAder : ∀ t, HasDerivAt A (γ * c t) t) (hcend : ∀ t, T ≤ t → c t = 0)
    (hLη : (2 * L) * η = q) (hc : ∀ t, c t ^ 2 ≤ A t * η * q)
    (hsmall : 144 * (p : ℝ) * q ≤ 1) (hqcap : q ≤ 1 / 16)
    (hbalance : ∀ t, (p : ℝ) * (A t * η) * H t ^ 2 = B)
    (hρbound : ∀ t, 2 * (p : ℝ) *
      (A t * η * v ^ 2 + 3 * Real.sqrt (q * (A t * η) * B) * β) / B ≤ ρ) :
    let ν := (mlmcLevelLaw (estimatorDepth v β) : Measure (Fin (estimatorDepth v β + 1))).prod
      (Measure.infinitePi fun _ : ℕ => μ)
    let M := constrainedEnvelope Q f L
    let out := fun w : ℝ × (Fin (estimatorDepth v β + 1) × (ℕ → Ω)) =>
      QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2.2
        (accelerationAdvancePlan A c H γ L σ D v β η x0 (w.1, w.2.1) (s, x, z)) 0
    (∫ w, Real.exp (-(ρ * (out w).1)) *
      shiftedEnergyBarrier M u (A (out w).1) B p (out w).2.1 (out w).2.2
      ∂(RelativeQuasar.holdingLaw : Measure ℝ).prod ν) ≤
        Real.exp (-(ρ * s)) * shiftedEnergyBarrier M u (A s) B p x z := by
  let ν := (mlmcLevelLaw (estimatorDepth v β) : Measure (Fin (estimatorDepth v β + 1))).prod
    (Measure.infinitePi fun _ : ℕ => μ)
  let M := constrainedEnvelope Q f L
  let Gm := fun y => (2 * L) • (y - constrainedProx Q f L y)
  let Y := fun t => accelerationFlow A γ s (s + t) x z
  let jump := fun t (w : Fin (estimatorDepth v β + 1) × (ℕ → Ω)) =>
    QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) w.2
      (accelerationJumpPlan L σ D v β η (c (s + t)) (H (s + t)) (Y t) z x0 w.1) 0
  let F := fun w : ℝ × (Fin (estimatorDepth v β + 1) × (ℕ → Ω)) =>
    shiftedEnergyBarrier M u (A (s + w.1)) B p (jump w.1 w.2).1 (jump w.1 w.2).2
  have hMG (y : E) : HasGradientAt M (Gm y) y :=
    constrainedEnvelope_hasGradient hL hQ ⟨u, hu⟩ hcv hG hlip y
  have hMc : Continuous M := continuous_iff_continuousAt.mpr fun y => (hMG y).hasFDerivAt.continuousAt
  have hGmc : Continuous Gm := by
    apply (LipschitzWith.of_dist_le_mul (K := (2 * L).toNNReal) fun y w => ?_).continuous
    rw [Real.coe_toNNReal _ (by positivity : 0 ≤ 2 * L), dist_eq_norm, dist_eq_norm]
    exact constrainedEnvelope_gradient_lipschitz hL hQ ⟨u, hu⟩ hcv hG hlip y w
  have hMu : M u = f u := by
    have hh := constrainedEnvelope_bounds hL.le hQ hG hu hmin u
    have hupp : M u ≤ f u := by simpa [M] using hh.2
    exact le_antisymm hupp hh.1
  have hMm (y : E) : M u ≤ M y := by
    rw [hMu]
    exact (constrainedEnvelope_bounds hL.le hQ hG hu hmin y).1
  have hYc : Continuous Y := (continuous_acceleration_flow hAc hA hγ0.le).comp
    (show Continuous (fun t : ℝ => ((s, s + t), x, z)) by fun_prop)
  have ht : Measurable (fun w : ℝ × (Fin (estimatorDepth v β + 1) × (ℕ → Ω)) => s + w.1) :=
    measurable_const.add measurable_fst
  have hjump : Measurable (fun w : ℝ × (Fin (estimatorDepth v β + 1) × (ℕ → Ω)) => jump w.1 w.2) :=
    measurable_acceleration_jump_parameters hP.lipschitz.continuous.measurable hgm L σ D v β x0 0
      (hYc.measurable.comp measurable_fst) (measurable_const (a := z)) (measurable_const (a := η))
      (hcc.measurable.comp ht) (hHm.comp ht) measurable_snd.fst measurable_snd.snd
  have hF : Measurable F := by
    dsimp only [F, shiftedEnergyBarrier, GradientOnlyQuasar.weightedEnergy]
    apply GradientOnlyQuasar.continuous_barrier.measurable.comp
    fun_prop
  have hFb (w : ℝ × (Fin (estimatorDepth v β + 1) × (ℕ → Ω))) : 0 ≤ F w ∧ F w ≤ 1 :=
    ⟨shifted_barrier_nonneg (hA (s + w.1)).le hB.le hMm, shifted_barrier_le_one _ _ _ _ _ _ _⟩
  have hgen (t : ℝ) (_ht : 0 ≤ t) :
      shiftedEnergyBarrierDrift M Gm u (A (s + t)) B γ (c (s + t)) p (Y t) z +
        (∫ ω, F (t, ω) ∂ν) - shiftedEnergyBarrier M u (A (s + t)) B p (Y t) z ≤
          ρ * shiftedEnergyBarrier M u (A (s + t)) B p (Y t) z := by
    have hh := sampled_acceleration_barrier_drift (x := Y t) (μ := μ) hP hL hD0 hv hβ hx0 hu hz
      hQ hcv hD hG hlip hmin hγ hquasar hgm hgi hmean hg2 hvar (hA (s + t)) hη (hc0 (s + t))
      hq hB (hH (s + t)) hp hLη (hc (s + t)) hsmall hqcap (hbalance (s + t))
    exact hh.2.trans (mul_le_mul_of_nonneg_right (hρbound (s + t))
      (shifted_barrier_nonneg (hA (s + t)).le hB.le hMm))
  have hh := shifted_barrier_random_holding (μ := ν) hγ0 hB hρ hs hAc hcc hA hAder hcend
    hMG hGmc x z u hMm hF hFb hgen
  dsimp only
  simp only [sampled_acceleration_advance]
  exact hh

end OracleTemplate.StochasticQuasar
