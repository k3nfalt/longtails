import LongTails.Proofs.ClippedExtragradientStageConfidence
import LongTails.Proofs.ClippedExtragradientBlocks

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.ClippedExtragradient

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace E] in
lemma measurable_blockOutput_joint {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (s : ℕ) :
    Measurable (fun w : (E × E) × (Fin (stageCalls t s) → Ω) =>
      blockOutput t s w.1.1 w.1.2 g w.2) :=
  (measurable_confidenceOutput_joint hg t s).comp
    (measurable_fst.prodMk ((measurable_splitStage t s).comp measurable_snd))

lemma blockOutput_confidence {g : E → Ω → E} {F : E → E} (t : Tuning)
    (h0 : 0 ≤ t.L0) (h1 : 0 ≤ t.L1) (hR : 0 < t.R) (hε : 0 < t.ε)
    (hc : Continuous F) (hmono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫)
    (hlip : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (t.L0 + t.L1 * M) * ‖x - y‖)
    (hg : LongTails.Setups.StochasticGeneralizedMonotone.IsStochasticOperator P F g t.σ)
    (s : ℕ) {anchor center p : E}
    (hp : HolderMonotone.reg F (regularization t s) anchor p = 0)
    (hF : ‖F p‖ ≤ t.ε) (hcroot : ‖p - center‖ ≤ radius t s) :
    (Measure.pi fun _ : Fin (stageCalls t s) => P)
      {samples | radius t s / 2 < ‖blockOutput t s anchor center g samples - p‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ repetitions t) := by
  have hm : Measurable (confidenceOutput t s anchor center g) := by
    change Measurable ((fun w : (E × E) × StageSamples t s Ω =>
      confidenceOutput t s w.1.1 w.1.2 g w.2) ∘ (fun samples => ((anchor, center), samples)))
    exact (measurable_confidenceOutput_joint hg.measurable t s).comp measurable_prodMk_left
  have hset : MeasurableSet {samples : StageSamples t s Ω |
      radius t s / 2 < ‖confidenceOutput t s anchor center g samples - p‖} :=
    measurableSet_lt measurable_const ((hm.sub measurable_const).norm)
  have he := (splitStage_preserving P t s).measure_preimage hset.nullMeasurableSet
  change (Measure.pi fun _ : Fin (stageCalls t s) => P) (splitStage t s ⁻¹' {samples | radius t s / 2 <
    ‖confidenceOutput t s anchor center g samples - p‖}) ≤ _
  rw [he]
  exact stage_confidence t h0 h1 hR hε hc hmono hlip hg s hp hF hcroot

omit [CompleteSpace E] in
lemma measurable_blockReply {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (n : ℕ) :
    Measurable (Function.uncurry (blockReply t g n)) := by
  exact measurable_guarded_block (stageCalls t)
    (fun s (a : E × E) => blockOutput t s a.1 a.2 g) Prod.snd measurable_snd
    (fun s => measurable_blockOutput_joint hg t s) n

omit [CompleteSpace E] in
lemma measurable_stageNext {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) (t : Tuning) (n : ℕ) :
    Measurable (Function.uncurry (stageNext t g n)) := by
  have hn := measurable_blockReply hg t n
  exact (by fun_prop : Measurable (fun w : StageState E × (Fin n → Ω) => w.1.1 + 1)).prodMk
    ((((measurable_fst.comp (measurable_snd.comp measurable_fst)).add hn).const_smul (1 / 2 : ℝ)).prodMk hn)

end OracleTemplate.ClippedExtragradient
