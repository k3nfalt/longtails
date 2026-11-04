import LongTails.Proofs.UscgSharpConfigured
import LongTails.Proofs.UscgSharpExecution

namespace LongTails.Proofs.UscgSharpGuarantee

open MeasureTheory
open LongTails.Setups.UscgHighProbability
open LongTails.Setups.UscgConstant (Space IsBallLMO Problem dualNorm)
open LongTails.Algorithms.UscgSharpConfidence
open OracleTemplate.NormBallLMO
open UscgSharpTuning UscgSharpSchedule

noncomputable def canonicalOutput {Ω : Type} (q : Public)
    (g : Space q.d → Ω → Space q.d) (lmo : Space q.d → Space q.d) (ξ : ℕ → Ω) :
    ℕ × (ℕ → Space q.d) :=
  (horizon q, fun k => if k < horizon q then
    (path (fun x m => x + chosenStep q • lmo m) (correctedWeight (chosenMemory q)) q.x₁ g ξ k).1
    else q.x₁)

lemma canonical_measurable {Ω : Type} [MeasurableSpace Ω] (q : Public)
    {g : Space q.d → Ω → Space q.d} {lmo : Space q.d → Space q.d}
    (hg : Measurable (Function.uncurry g)) (hlmo : IsBallLMO q.N 1 lmo) :
    Measurable (canonicalOutput q g lmo) := by
  have hstep : Measurable (fun z : Space q.d × Space q.d => z.1 + chosenStep q • lmo z.2) :=
    measurable_fst.add ((hlmo.measurable.comp measurable_snd).const_smul (chosenStep q))
  apply measurable_const.prodMk
  apply Measurable.of_eval
  intro k
  by_cases hk : k < horizon q
  · simpa only [hk, ↓reduceIte] using
      (measurable_path hstep (correctedWeight (chosenMemory q)) q.x₁ hg k).fst
  · simp only [hk, ↓reduceIte]
    exact measurable_const

lemma average_canonical {Ω : Type} (q : Public) (f : Space q.d → ℝ)
    (g : Space q.d → Ω → Space q.d) (lmo : Space q.d → Space q.d) (ξ : ℕ → Ω) :
    averageStationarity q f (canonicalOutput q g lmo ξ) =
      (∑ t ∈ Finset.range (horizon q), dualNorm q.N (gradient f
        (path (fun x m => x + chosenStep q • lmo m)
          (correctedWeight (chosenMemory q)) q.x₁ g ξ t).1)) / (horizon q : ℝ) := by
  unfold averageStationarity canonicalOutput
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  simp [Finset.mem_range.mp ht]

lemma average_measurable {Ω : Type} [MeasurableSpace Ω] {q : Public}
    {f : Space q.d → ℝ} {g : Space q.d → Ω → Space q.d} {lmo : Space q.d → Space q.d}
    (hg : Measurable (Function.uncurry g)) (hlmo : IsBallLMO q.N 1 lmo)
    (hR : 0 ≤ q.R) (hRb : ∀ x, q.N x ≤ 1 → ‖x‖ ≤ q.R) :
    Measurable (fun ξ => averageStationarity q f (canonicalOutput q g lmo ξ)) := by
  have hout := canonical_measurable q hg hlmo
  have hgrad := measurable_gradient_space f
  have hdual := (continuous_dualNorm hRb hR).measurable
  change Measurable (fun ξ => (∑ t ∈ Finset.range (horizon q),
    dualNorm q.N (gradient f ((canonicalOutput q g lmo ξ).2 t))) / (horizon q : ℝ))
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro t _
  exact (hdual.comp hgrad).comp ((measurable_pi_apply t).comp hout.snd)

lemma canonical_tail {Ω : Type} [MeasurableSpace Ω] {q : Params}
    (hq : spec.valid q) {f : Space q.d → ℝ} {g : Space q.d → Ω → Space q.d}
    {lmo : Space q.d → Space q.d} {p : Measure Ω} [IsProbabilityMeasure p]
    (hlmo : IsBallLMO q.N 1 lmo)
    (H : Problem q.N q.L q.L₂ q.σ q.Δ q.x₁ f g p) :
    (Measure.infinitePi fun _ : ℕ => p).real
      {ξ | q.ε < averageStationarity q.toPublic f (canonicalOutput q.toPublic g lmo ξ)} ≤ q.δ := by
  rcases hq with ⟨hdef, hR, hRb, hζ, hζb, hL, hL2, hσ, hΔ, he, hδ, hδ1⟩
  have hδone : q.δ ≤ 1 := by linarith
  by_cases hh : 2 * q.L * q.Δ ≤ q.ε ^ 2
  · obtain ⟨fmin, hfmin, hgap⟩ := H.lower
    have hself := UscgSharpGeometry.gradient_self_bound hRb hdef hL H.differentiable
      H.lipschitz hfmin hlmo q.x₁
    have hg : dualNorm q.N (gradient f q.x₁) ≤ q.ε := by
      have hgap' := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * q.L by positivity)
      nlinarith
    have hval : ∀ ξ, averageStationarity q.toPublic f (canonicalOutput q.toPublic g lmo ξ) =
        dualNorm q.N (gradient f q.x₁) := by
      intro ξ
      rw [average_canonical]
      simp [horizon, hh, path]
    have hempty : {ξ | q.ε < averageStationarity q.toPublic f (canonicalOutput q.toPublic g lmo ξ)} = ∅ := by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rw [hval]
      exact not_lt_of_ge hg
    rw [hempty]
    simpa using hδ.le
  · have hT : (0 : ℝ) < horizon q.toPublic := by
      exact_mod_cast horizon_pos q.toPublic hL.le hΔ hδ hδone
    have hiid := OracleTemplate.StochasticGeneralized.infinitePi_iid p
    have hp := UscgSharpConfigured.hard_path_tail q.toPublic H hiid hRb hdef hL hζ he hδ hδone hζb hlmo hh
    convert hp using 2
    ext ξ
    simp only [Set.mem_ofPred_eq]
    rw [average_canonical, lt_div_iff₀ hT]
    simp only [chosenStep, chosenMemory, ite_eq_right hh]

lemma execute_canonical {Ω : Type} [MeasurableSpace Ω] (q : Public)
    (g : Space q.d → Ω → Space q.d) (lmo : Space q.d → Space q.d)
    (P : ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω) :
    OracleTemplate.execute (UscgSharpExecution.canonicalOracle q g lmo P) (configured q)
      (fun _ => horizon q) () ξ = canonicalOutput q g lmo (fun k => ξ (2 * k)) := by
  unfold configured algorithm
  rw [UscgSharpExecution.execute_machine]
  rfl

lemma configured_allowed (q : Public) (hL : 0 ≤ q.L) (hΔ : 0 ≤ q.Δ)
    (he : 0 < q.ε) (hδ : 0 < q.δ) (hδ1 : q.δ ≤ 1) :
    spec.allowedAlgorithm q (configured q) := by
  unfold configured
  by_cases hh : 2 * q.L * q.Δ ≤ q.ε ^ 2
  · simp only [chosenMemory, chosenStep, ite_eq_left hh]
    exact algorithm_allowed q (by norm_num) (by norm_num) (by norm_num)
  · simp only [chosenMemory, chosenStep, ite_eq_right hh]
    have hΔp : 0 < q.Δ := by nlinarith [lt_of_not_ge hh, sq_pos_of_pos he]
    have hT : (0 : ℝ) < horizon q := by exact_mod_cast horizon_pos q hL hΔ hδ hδ1
    exact algorithm_allowed q (memory_pos_lt_one q).1 (memory_pos_lt_one q).2 (by positivity)

end LongTails.Proofs.UscgSharpGuarantee
