import LongTails.Proofs.ProjectedClippedProcess
import LongTails.Proofs.ProjectedClippedExecution
import LongTails.Proofs.ClippedExtragradientProcess

open MeasureTheory

namespace OracleTemplate.ProjectedClippedExtragradient

open ConstrainedMonotone
open StochasticGeneralized (accumulated blockTrace)

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [MeasurableSpace Ω]

lemma execution_success {X : Set E} {proj F : E → E} (hP : Proj X proj) (hX : Convex ℝ X)
    (t : Tuning) (hF : GeneralizedMonotone.Hyp F t.L0 t.L1)
    (hR : 0 < t.R) (hε : 0 < t.ε) (hδ : 0 < t.δ) {x0 xstar : E} (hx0 : x0 ∈ X)
    (hstar : xstar ∈ X) (hnstar : Normal X xstar (-F xstar)) (hG : ‖F xstar‖ ≤ t.G)
    (hd : ‖x0 - xstar‖ ≤ t.R) {g : E → Ω → E}
    (p : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → Ω) => ξ k) (p : Measure Ω) (P : Measure _))
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator (p : Measure Ω) F g t.σ)
    (K : ℕ) (hK : runCalls t 0 (stageCount t) ≤ K) :
    let O : Oracle E E 2 := { Seed := fun _ => Ω, law := P, answer := fun _ q ω => channelReply proj g q ω }
    Measurable (fun seed : Unit × (ℕ → Ω) => output t x0 O (fun _ => K) seed.2) ∧
      ((Measure.dirac ()).prod (P : Measure _)) {seed : Unit × (ℕ → Ω) |
        ¬(output t x0 O (fun _ => K) seed.2 ∈ X ∧
          ∃ η, Normal X (output t x0 O (fun _ => K) seed.2) η ∧
            ‖F (output t x0 O (fun _ => K) seed.2) + η‖ ≤ t.ε)} ≤
        ENNReal.ofReal t.δ := by
  dsimp only [output]
  simp_rw [execute_trace P proj g t x0 K hK]
  have hc : Measurable (phaseCost (E := E) t) :=
    (measurable_of_countable (fun s : ℕ => if s < stageCount t then stageCalls t s else finalCalls t)).comp measurable_fst
  have hn := measurable_phaseNext hP.lipschitz.continuous.measurable hg.measurable t
  have ht : Measurable (fun ξ : ℕ → Ω =>
      blockTrace (phaseCost t) (phaseNext proj t g) (0, x0, x0) ξ (stageCount t + 1)) :=
    (ClippedExtragradient.measurable_blockTrace hc hn (stageCount t + 1)).comp
    (measurable_const.prodMk (measurable_id : Measurable (id : (ℕ → Ω) → _)))
  refine ⟨ht.fst.snd.snd.comp measurable_snd, ?_⟩
  let A : Set (ℕ → Ω) := {ξ | 1 ≤ accumulated (phaseCost t) (phaseNext proj t g)
    (phaseFailure hP t hF hR hε hx0 xstar g) (stageCount t + 1) (0, x0, x0) ξ}
  have hA : MeasurableSet A := measurableSet_le measurable_const
    ((StochasticGeneralized.accumulated_measurable hc hn
      (measurable_phaseFailure hP t hF hR hε hx0 xstar hg.measurable) (stageCount t + 1)).comp
        (measurable_const.prodMk measurable_id))
  let out := fun ξ : ℕ → Ω =>
    (blockTrace (phaseCost t) (phaseNext proj t g) (0, x0, x0) ξ (stageCount t + 1)).1.2.2
  have hsub : {seed : Unit × (ℕ → Ω) | ¬(out seed.2 ∈ X ∧ ∃ η, Normal X (out seed.2) η ∧ ‖F (out seed.2) + η‖ ≤ t.ε)} ⊆
      Prod.snd ⁻¹' A := by
    intro seed hbad
    by_contra hh
    have hh : accumulated (phaseCost t) (phaseNext proj t g)
        (phaseFailure hP t hF hR hε hx0 xstar g) (stageCount t + 1) (0, x0, x0) seed.2 < 1 :=
      lt_of_not_ge hh
    exact hbad (phaseTrace_correct hP hX t hF hR hε hx0 hstar hnstar hG hd g seed.2 hh)
  apply (measure_mono hsub).trans
  rw [measurePreserving_snd.measure_preimage hA.nullMeasurableSet]
  have hPlaw : (P : Measure _) = Measure.infinitePi (fun _ : ℕ => (p : Measure Ω)) := by
    have hh := hIID.stream_law.map_eq
    change Measure.map id (P : Measure (ℕ → Ω)) = _ at hh
    simpa only [Measure.map_id] using hh
  rw [hPlaw]
  exact accumulated_phase_failure hP hX t hF hR hε hδ hx0 hstar hnstar hG hg (0, x0, x0)

end OracleTemplate.ProjectedClippedExtragradient
