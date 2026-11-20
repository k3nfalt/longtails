import LongTails.Proofs.SublevelPLBlocks
import LongTails.Proofs.RobustPilotConfidence

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.HighProbabilityTest

open OracleTemplate RobustGradient SublevelRobustGradient

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p]

omit [CompleteSpace E] in
lemma measurable_aggregate {k r : ℕ} (hk : 0 < k) (B : ℝ) {V : Ω → E} (hV : Measurable V) :
    Measurable (fun v : Fin (k * r) → Ω =>
      SublevelRobustGradient.aggregate (m := k) (b := r) hk B (fun j => V (v j))) := by
  unfold SublevelRobustGradient.aggregate
  refine (measurable_robustCenter hk B).comp ?_
  refine Measurable.of_eval fun i => ?_
  unfold blockMean
  exact (Finset.measurable_sum _ fun l _ => hV.comp (measurable_pi_apply _)).const_smul _

lemma test_inaccurate {V : Ω → E} (hV : Measurable V) (hVi : Integrable V p) (u : E)
    (hvi : Integrable (fun ω => ‖V ω - u‖ ^ 2) p) (hmean : (∫ ω, V ω ∂p) = u)
    {σ α : ℝ} (hvar : (∫ ω, ‖V ω - u‖ ^ 2 ∂p) ≤ σ ^ 2) (hα : 0 < α)
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r) (hrα : 144 * σ ^ 2 ≤ r * α ^ 2) :
    (Measure.pi fun _ : Fin (k * r) => p)
      {v | α < ‖SublevelRobustGradient.aggregate (m := k) (b := r) hk (2 * α)
        (fun j => V (v j)) - u‖} ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  classical
  let A : Set (Fin r → Ω) := {ζ | 2 * α / 6 < ‖(1 / (r : ℝ)) • ∑ l : Fin r, V (ζ l) - u‖}
  have hAm : MeasurableSet A := by
    refine measurableSet_lt measurable_const ?_
    exact (((Finset.measurable_sum _ fun l _ => hV.comp (measurable_pi_apply l)).const_smul _).sub_const
      u).norm
  have hpA : (Measure.pi fun _ : Fin r => p).real A ≤ 1 / 16 :=
    subbatch_failure p hV hVi u hvi hmean hvar r hr (B := 2 * α) (by positivity) (by nlinarith)
  have hmaj := majority_failure_probability (P := Measure.pi fun _ : Fin r => p) hAm hpA k
  have hpres := reindex_preserving p k r
  have hsub : {v : Fin (k * r) → Ω | α < ‖SublevelRobustGradient.aggregate (m := k) (b := r) hk
      (2 * α) (fun j => V (v j)) - u‖} ⊆
      reindex k r ⁻¹' {ζ | k ≤ 2 * (Finset.univ.filter (fun i => ζ i ∈ A)).card} := by
    intro v hv
    simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hv ⊢
    by_contra hcon
    push Not at hcon
    have hgood : k < 2 * (Finset.univ.filter (fun i =>
        ‖blockMean k r (fun j => V (v j)) i - u‖ ≤ 2 * α / 6)).card := by
      have hpart := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin k))) (fun i => reindex k r v i ∈ A)
      have hneg : (Finset.univ.filter (fun i => ¬ reindex k r v i ∈ A)) =
          Finset.univ.filter (fun i => ‖blockMean k r (fun j => V (v j)) i - u‖ ≤ 2 * α / 6) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, A, Set.mem_ofPred_eq, not_lt]
        rw [blockMean_eq]
        rfl
      rw [hneg, Finset.card_univ, Fintype.card_fin] at hpart
      omega
    have hacc := robustCenter_accuracy hk (B := 2 * α) (blockMean k r (fun j => V (v j))) u hgood
    have : ‖SublevelRobustGradient.aggregate (m := k) (b := r) hk (2 * α) (fun j => V (v j)) - u‖ ≤
        α := by
      unfold SublevelRobustGradient.aggregate
      linarith
    linarith
  calc (Measure.pi fun _ : Fin (k * r) => p) {v | α < ‖SublevelRobustGradient.aggregate (m := k)
        (b := r) hk (2 * α) (fun j => V (v j)) - u‖} ≤
      (Measure.pi fun _ : Fin (k * r) => p)
        (reindex k r ⁻¹' {ζ | k ≤ 2 * (Finset.univ.filter (fun i => ζ i ∈ A)).card}) :=
        measure_mono hsub
    _ = (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin r => p)
        {ζ | k ≤ 2 * (Finset.univ.filter (fun i => ζ i ∈ A)).card} := by
        have hcard : Measurable (fun ζ : Fin k → (Fin r → Ω) =>
            (Finset.univ.filter (fun i => ζ i ∈ A)).card) := by
          simp only [Finset.card_filter]
          exact Finset.measurable_sum _ fun i _ =>
            Measurable.ite (hAm.preimage (measurable_pi_apply i)) measurable_const measurable_const
        have hset : MeasurableSet {ζ : Fin k → (Fin r → Ω) |
            k ≤ 2 * (Finset.univ.filter (fun i => ζ i ∈ A)).card} :=
          hcard (MeasurableSet.of_discrete (s := {n : ℕ | k ≤ 2 * n}))
        exact hpres.measure_preimage hset.nullMeasurableSet
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := hmaj

end LongTails.Proofs.HighProbabilityTest
