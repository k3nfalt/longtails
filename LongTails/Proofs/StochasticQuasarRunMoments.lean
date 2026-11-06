import LongTails.Proofs.StochasticQuasarAccelerationMoments
import LongTails.Proofs.StochasticQuasarIteration

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.StochasticQuasar

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma sampled_acceleration_run_barrier {μ : Measure Ω} [IsProbabilityMeasure μ]
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
      (A t * η * v ^ 2 + 3 * Real.sqrt (q * (A t * η) * B) * β) / B ≤ ρ) (k : ℕ) :
    let seedLaw := (RelativeQuasar.holdingLaw : Measure ℝ).prod
      (mlmcLevelLaw (estimatorDepth v β) : Measure (Fin (estimatorDepth v β + 1)))
    let M := constrainedEnvelope Q f L
    let calls := fun a : ℝ × Fin (estimatorDepth v β + 1) => accelerationJumpCalls L σ D v β a.2.val
    let advance := fun state a ξ => QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
      (accelerationAdvancePlan A c H γ L σ D v β η x0 a state) 0
    (∫⁻ seeds : Fin k → ℝ × Fin (estimatorDepth v β + 1), ∫⁻ ξ,
      ENNReal.ofReal (compensatedEnergyBarrier M u A B ρ p (seededStreamRun calls advance k (s, x, z) seeds ξ))
      ∂Measure.infinitePi (fun _ : ℕ => μ) ∂Measure.pi (fun _ : Fin k => seedLaw)) ≤
        ENNReal.ofReal (compensatedEnergyBarrier M u A B ρ p (s, x, z)) := by
  let seedLaw := (RelativeQuasar.holdingLaw : Measure ℝ).prod
    (mlmcLevelLaw (estimatorDepth v β) : Measure (Fin (estimatorDepth v β + 1)))
  let ν := Measure.infinitePi fun _ : ℕ => μ
  let M := constrainedEnvelope Q f L
  let calls := fun a : ℝ × Fin (estimatorDepth v β + 1) => accelerationJumpCalls L σ D v β a.2.val
  let advance := fun state a ξ => QueryPlan.sampledEval (ProjectedClippedExtragradient.channelReply P g) ξ
    (accelerationAdvancePlan A c H γ L σ D v β η x0 a state) 0
  let V := fun state => ENNReal.ofReal (compensatedEnergyBarrier M u A B ρ p state)
  let good := fun state : ℝ × E × E => 0 ≤ state.1 ∧ state.2.2 ∈ Q
  have hMc : Continuous M := continuous_iff_continuousAt.mpr fun y =>
    (constrainedEnvelope_hasGradient hL hQ ⟨u, hu⟩ hcv hG hlip y).hasFDerivAt.continuousAt
  have hMu : M u = f u := by
    have hh := constrainedEnvelope_bounds hL.le hQ hG hu hmin u
    have hupp : M u ≤ f u := by simpa [M] using hh.2
    exact le_antisymm hupp hh.1
  have hMm (y : E) : M u ≤ M y := by
    rw [hMu]
    exact (constrainedEnvelope_bounds hL.le hQ hG hu hmin y).1
  have hVm : Measurable (compensatedEnergyBarrier M u A B ρ p) :=
    (continuous_compensated_barrier hMc hAc u B ρ p).measurable
  have hV : Measurable V := ENNReal.measurable_ofReal.comp hVm
  have hcalls : Measurable calls :=
    (measurable_of_finite (fun j : Fin (estimatorDepth v β + 1) => accelerationJumpCalls L σ D v β j.val)).comp
      measurable_snd
  have ha : Measurable (fun w : (ℝ × E × E) × ((ℝ × Fin (estimatorDepth v β + 1)) × (ℕ → Ω)) =>
      advance w.1 w.2.1 w.2.2) :=
    measurable_acceleration_advance_parameters hP.lipschitz.continuous.measurable hgm
      hAc hA hγ0.le hcc.measurable hHm L σ D v β η x0 0
      measurable_fst measurable_snd.fst measurable_snd.snd
  have hdep (state : ℝ × E × E) (a : ℝ × Fin (estimatorDepth v β + 1)) (ξ ζ : ℕ → Ω)
      (he : ∀ j, j < calls a → ξ j = ζ j) : advance state a ξ = advance state a ζ := by
    apply StochasticCohypomonotone.sampledEval_congr
    intro j hj
    simpa only [Nat.zero_add] using he j hj
  have hkeep (state : ℝ × E × E) (hg : good state) (a : ℝ × Fin (estimatorDepth v β + 1))
      (ξ : ℕ → Ω) : good (advance state a ξ) := by
    dsimp only [good, advance]
    rw [sampled_acceleration_advance]
    refine ⟨add_nonneg hg.1 (le_max_left _ _), ?_⟩
    exact sampled_acceleration_auxiliary_mem hP.mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hstep (state : ℝ × E × E) (hg : good state) :
      (∫⁻ a, ∫⁻ ξ, V (advance state a ξ) ∂ν ∂seedLaw) ≤ V state := by
    let W := fun w : ℝ × (Fin (estimatorDepth v β + 1) × (ℕ → Ω)) =>
      compensatedEnergyBarrier M u A B ρ p (advance state (w.1, w.2.1) w.2.2)
    have hW : Measurable W := hVm.comp (ha.comp
      (measurable_const.prodMk ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)))
    have hWb (w : ℝ × (Fin (estimatorDepth v β + 1) × (ℕ → Ω))) : 0 ≤ W w ∧ W w ≤ 1 :=
      ⟨compensated_barrier_nonneg (fun t => (hA t).le) hB.le hMm _,
        compensated_barrier_le_one (fun t => (hA t).le) hB.le hMm hρ _ (hkeep state hg _ _).1⟩
    have he := reassociated_lintegral_ofReal
      (μa := (RelativeQuasar.holdingLaw : Measure ℝ))
      (μb := (mlmcLevelLaw (estimatorDepth v β) : Measure (Fin (estimatorDepth v β + 1))))
      (μc := ν) hW hWb
    have hh := sampled_acceleration_holding (x := state.2.1) (z := state.2.2) (s := state.1)
      hP hL hD0 hv hβ hx0 hu hg.2 hQ hcv hD hG hlip hmin hγ0 hγ hquasar hgm hgi hmean hg2 hvar
      hη hq hB hp hρ hg.1 hAc hcc hHm hA hc0 hH hAder hcend hLη hc hsmall hqcap hbalance hρbound
    exact he.trans_le (ENNReal.ofReal_le_ofReal hh)
  exact seeded_stream_run_lintegral hcalls ha hdep hV hkeep hstep k (s, x, z) ⟨hs, hz⟩

end OracleTemplate.StochasticQuasar
