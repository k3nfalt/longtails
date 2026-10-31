import LongTails.Proofs.SmoothBanachProcess
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.QuadraticNoiseMoments

open MeasureTheory

set_option maxHeartbeats 2000000

namespace LongTails.Proofs.SmoothBanachSampling

open LongTails.Setups.StochasticSmoothBanachFixedPoint
open LongTails.Algorithms.SmoothBanachAnchoring
open SmoothBanachProcess SmoothBanachTuning
open OracleTemplate.ContinuizedSimilarQuasar (iterateSamples)

lemma prefix_next_preserving {Ω : Type*} [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (n : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => ((fun i : Fin n => ξ i), ξ n))
      (Measure.infinitePi fun _ : ℕ => p) ((Measure.pi fun _ : Fin n => p).prod p) := by
  have he : MeasurePreserving (fun ξ : ℕ → Ω => ξ 0) (Measure.infinitePi fun _ : ℕ => p) p :=
    ⟨measurable_pi_apply 0, Measure.infinitePi_map_eval _ _⟩
  have hp := (MeasurePreserving.id (Measure.pi fun _ : Fin n => p)).prod he
  simpa [Function.comp_def, OracleTemplate.StochasticGeneralized.splitStream] using
    hp.comp (OracleTemplate.StochasticGeneralized.splitStream_preserving p n)

lemma stream_energy_bound (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (hC : 0 ≤ q.C) (hε : 0 < q.ε)
    (J : q.E → q.E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + q.C * ‖y‖ ^ 2)
    (p : ProbabilityMeasure q.Ω) (g : q.E → q.Ω → q.E)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator
      (p : Measure q.Ω) T g q.σ)
    (xstar : q.E) (hstar : T xstar = xstar) (hR : ‖q.x0 - xstar‖ ≤ q.R) (n : ℕ) :
    Integrable (fun ξ => energy q T hT (epochState q g n ξ))
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω)) ∧
    (∫ ξ, energy q T hT (epochState q g n ξ)
      ∂Measure.infinitePi (fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω))) ≤
      q.ε ^ 2 / 64 := by
  have hi := epoch_energy_bound q T hT hC hε J hsmooth p g hg xstar hstar hR n
  have hp := OracleTemplate.StochasticGeneralized.prefix_preserving
    (Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω)) n
  refine ⟨hp.integrable_comp_of_integrable hi.1, ?_⟩
  have hm : Measurable (fun ξ => energy q T hT (iterateSamples (epochAdvance q g) n
      (0, strength q 0 • q.x0, q.x0) ξ)) :=
    (energy_measurable q T hT).comp ((OracleTemplate.GapStrongGrowth.iterateSamples_measurable
      (epochAdvance_measurable q g hg.measurable) n).comp measurable_prodMk_left)
  have he := integral_map (μ := Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω)) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm.trans_le hi.2

noncomputable def epochError (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (g : q.E → q.Ω → q.E)
    (n : ℕ) (ξ : ℕ → Fin (innerSteps q) → q.Ω) : ℝ :=
  let s := epochState q g n ξ
  energy q T hT (s.1, s.2.1, (epochAdvance q g s (ξ n)).2.2)

lemma epoch_error_bound (q : Params) (T : q.E → q.E)
    (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖) (hC : 0 ≤ q.C) (hε : 0 < q.ε)
    (J : q.E → q.E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + q.C * ‖y‖ ^ 2)
    (p : ProbabilityMeasure q.Ω) (g : q.E → q.Ω → q.E)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator
      (p : Measure q.Ω) T g q.σ)
    (xstar : q.E) (hstar : T xstar = xstar) (hR : ‖q.x0 - xstar‖ ≤ q.R) (n : ℕ) :
    Integrable (epochError q T hT g n)
      (Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω)) ∧
    (∫ ξ, epochError q T hT g n ξ
      ∂Measure.infinitePi (fun _ : ℕ => Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω))) ≤
      q.ε ^ 2 / (256 * (levels q + 1 : ℝ) ^ 2) := by
  let B := Fin (innerSteps q) → q.Ω
  let Q : Measure B := Measure.pi fun _ : Fin (innerSteps q) => (p : Measure q.Ω)
  let state := fun ξ : Fin n → B => iterateSamples (epochAdvance q g) n
    (0, strength q 0 • q.x0, q.x0) ξ
  let F : (Fin n → B) × B → ℝ := fun w =>
    energy q T hT ((state w.1).1, (state w.1).2.1,
      (epochAdvance q g (state w.1) w.2).2.2)
  let G : (Fin n → B) → ℝ := fun ξ =>
    energy q T hT (state ξ) / (64 * (levels q + 1 : ℝ) ^ 2) + q.C * relaxation q * q.σ ^ 2
  have hstate : Measurable state :=
    (OracleTemplate.GapStrongGrowth.iterateSamples_measurable
      (epochAdvance_measurable q g hg.measurable) n).comp measurable_prodMk_left
  have hnew := (epochAdvance_measurable q g hg.measurable).comp
    ((hstate.comp measurable_fst).prodMk measurable_snd)
  have hF : Measurable F := (energy_measurable q T hT).comp
    ((hstate.comp measurable_fst).fst.prodMk
      ((hstate.comp measurable_fst).snd.fst.prodMk hnew.snd.snd))
  have hi := epoch_energy_bound q T hT hC hε J hsmooth p g hg xstar hstar hR n
  have hG : Integrable G (Measure.pi fun _ : Fin n => Q) :=
    (hi.1.div_const _).add (integrable_const _)
  have hfiber (ξ : Fin n → B) := epoch_output_moment q T hT hC J hsmooth p g hg (state ξ)
  have hp := OracleTemplate.StochasticConvexQuadratic.nonnegative_product_control hF
    (fun w => energy_nonneg q T hT _) (fun ξ => (hfiber ξ).1) hG (fun ξ => (hfiber ξ).2)
  have hpres := prefix_next_preserving Q n
  refine ⟨hpres.integrable_comp_of_integrable hp.1, ?_⟩
  have hchange : (∫ ξ, epochError q T hT g n ξ ∂Measure.infinitePi (fun _ : ℕ => Q)) =
      ∫ w, F w ∂(Measure.pi fun _ : Fin n => Q).prod Q := by
    have he := integral_map (μ := Measure.infinitePi fun _ : ℕ => Q) hpres.measurable.aemeasurable hF.aestronglyMeasurable
    rw [hpres.map_eq] at he
    exact he.symm
  rw [hchange]
  apply hp.2.trans
  dsimp only [G]
  rw [integral_add (hi.1.div_const _) (integrable_const _), integral_div]
  simp only [integral_const, probReal_univ, one_smul]
  have hden : 0 < 64 * (levels q + 1 : ℝ) ^ 2 := by positivity
  have hv := div_le_div_of_nonneg_right hi.2 hden.le
  have hn := normalized_noise_floor q hC hε
  calc
    _ ≤ (q.ε ^ 2 / 64) / (64 * (levels q + 1 : ℝ) ^ 2) +
        q.ε ^ 2 / (1024 * (levels q + 1 : ℝ) ^ 2) := add_le_add hv hn
    _ ≤ _ := by
      have hS : (levels q + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      nlinarith [sq_nonneg q.ε]

end LongTails.Proofs.SmoothBanachSampling
