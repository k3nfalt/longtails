import LongTails.Proofs.InertialMonotoneSampling

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.InertialMonotone

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def energy (F : E → E) (hc : Continuous F)
    (hm : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫) (μ : ℝ) (hμ : 0 < μ) (state : E × E) : ℝ :=
  let p := ClippedExtragradient.regularizedZero F hc hm μ hμ state.1
  μ ^ 2 * ‖state.2 - p‖ ^ 2 + ‖F p‖ ^ 2

lemma energy_nonneg (F : E → E) (hc : Continuous F)
    (hm : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫) (μ : ℝ) (hμ : 0 < μ) (state : E × E) :
    0 ≤ energy F hc hm μ hμ state := by
  unfold energy
  positivity

lemma energy_continuous (F : E → E) (hc : Continuous F)
    (hm : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫) (μ : ℝ) (hμ : 0 < μ) :
    Continuous (energy F hc hm μ hμ) := by
  have hr := ClippedExtragradient.regularizedZero_continuous F hc hm μ hμ
  change Continuous (fun state : E × E =>
    μ ^ 2 * ‖state.2 - ClippedExtragradient.regularizedZero F hc hm μ hμ state.1‖ ^ 2 +
      ‖F (ClippedExtragradient.regularizedZero F hc hm μ hμ state.1)‖ ^ 2)
  fun_prop

lemma energy_initial (F : E → E) (hc : Continuous F)
    (hm : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫) (μ : ℝ) (hμ : 0 < μ)
    (x xs : E) {R : ℝ} (hxs : F xs = 0) (hx : ‖x - xs‖ ≤ R) :
    energy F hc hm μ hμ (x, x) ≤ 2 * μ ^ 2 * R ^ 2 :=
  initial_energy hμ hm x _ xs (ClippedExtragradient.regularizedZero_spec F hc hm μ hμ x) hxs hx

lemma energy_residual (F : E → E) (hc : Continuous F)
    (hm : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫) (μ : ℝ) (hμ : 0 < μ)
    {L : ℝ} (hL : 0 ≤ L) (hLμ : L ≤ μ)
    (hlip : ∀ a b, ‖F a - F b‖ ≤ L * ‖a - b‖) (state : E × E) :
    ‖F state.2‖ ^ 2 ≤ 2 * energy F hc hm μ hμ state :=
  residual_energy hL hLμ hlip state.2 _

lemma batch_energy_step [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : E → E} (hc : Continuous F) (hm : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫)
    {g : E → Ω → E} {σ L μ η r : ℝ}
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator P F g σ)
    (hlip : ∀ a b, ‖F a - F b‖ ≤ L * ‖a - b‖)
    (hμ : 0 < μ) (hr : 0 < r) (hrmax : r ≤ 1 / 16) (hη : η = 2 * r / μ)
    (hcap : 2 * η * μ + 2 * η ^ 2 * (L + μ) ^ 2 ≤ 1)
    (state : E × E) {b : ℕ} (hb : 0 < b) :
    let Q := Measure.pi (fun _ : Fin b => P)
    let hnext : 0 < μ * (1 + r / 2) := by positivity
    let f := fun ω : (Fin b → Ω) × (Fin b → Ω) =>
      energy F hc hm (μ * (1 + r / 2)) hnext
        (transported r state.1 (batchTrial g μ η b state ω.1 ω.2))
    Integrable f (Q.prod Q) ∧ (∫ ω, f ω ∂Q.prod Q) ≤
      energy F hc hm μ hμ state + 14 * r ^ 2 * (σ ^ 2 / b) := by
  intro Q hnext f
  let p := ClippedExtragradient.regularizedZero F hc hm μ hμ state.1
  let w := fun ω : (Fin b → Ω) × (Fin b → Ω) => batchTrial g μ η b state ω.1 ω.2
  let q := fun ω => ClippedExtragradient.regularizedZero F hc hm (μ * (1 + r / 2)) hnext
    (transported r state.1 (w ω)).1
  have hw : Measurable w := (batchTrial_measurable hg.measurable μ η b).comp
    (measurable_const.prodMk measurable_id)
  have hq : Measurable q := by
    have hh := (ClippedExtragradient.regularizedZero_continuous F hc hm
      (μ * (1 + r / 2)) hnext).measurable
    apply hh.comp
    dsimp [transported]
    fun_prop
  have hp : F p = μ • (state.1 - p) := by
    have hh := ClippedExtragradient.regularized_root_value
      (ClippedExtragradient.regularizedZero_spec F hc hm μ hμ state.1)
    change F p = _ at hh
    rw [hh]
    module
  have hroot (ω) : F (q ω) = (μ * (1 + r / 2)) •
      (state.1 + (3 * r / (2 * (2 + r))) • (w ω - state.1) - q ω) := by
    have hh := ClippedExtragradient.regularized_root_value
      (ClippedExtragradient.regularizedZero_spec F hc hm (μ * (1 + r / 2)) hnext
        (transported r state.1 (w ω)).1)
    change F (q ω) = -((μ * (1 + r / 2)) •
      (q ω - (transported r state.1 (w ω)).1)) at hh
    rw [hh]
    simp only [transported]
    module
  have hs := batch_trial_contraction hc hμ.le (show 0 ≤ η by rw [hη]; positivity)
    hcap hm hlip hg state.1 state.2 p
    (ClippedExtragradient.regularizedZero_spec F hc hm μ hμ state.1) hb
  have ht := integral_potential_step (P := Q.prod Q) hc.measurable hr hrmax hμ
    (show 0 ≤ σ ^ 2 / (b : ℝ) by positivity) hη hm state.1 state.2 p hp hw hq hs.1 hs.2 hroot
  simpa only [f, energy, transported, p, q, w, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs] using ht

end OracleTemplate.InertialMonotone
