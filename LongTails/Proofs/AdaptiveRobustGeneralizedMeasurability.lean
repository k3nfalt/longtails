import LongTails.Algorithms.AdaptiveRobustGeneralizedAccelerated
import LongTails.Proofs.StochasticGeneralizedMeasurability
import LongTails.Proofs.RobustEstimatorMoments

open MeasureTheory

namespace OracleTemplate.AdaptiveRobustGeneralized

open RobustGradient

@[fun_prop] lemma measurable_radius (p : Params) : Measurable (radius p) := by
  unfold radius
  fun_prop

@[fun_prop] lemma measurable_pilotSize (p : Params) : Measurable (pilotSize p) := by
  unfold pilotSize
  fun_prop

@[fun_prop] lemma measurable_ratio (p : Params) : Measurable (ratio p) := by
  unfold ratio
  fun_prop

@[fun_prop] lemma measurable_pilotGroups (p : Params) : Measurable (pilotGroups p) := by
  unfold pilotGroups
  fun_prop

@[fun_prop] lemma measurable_correctionSize (p : Params) : Measurable (correctionSize p) := by
  unfold correctionSize
  fun_prop

@[fun_prop] lemma measurable_estimatorCost (p : Params) : Measurable (estimatorCost p) := by
  unfold estimatorCost
  fun_prop

lemma measurable_meanBlock {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (offset size : ℕ) :
    Measurable (meanBlock (E := E) offset size) := by
  unfold meanBlock
  fun_prop

lemma measurable_meanBlock_all {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] :
    Measurable (fun w : (ℕ × ℕ) × (ℕ → E) => meanBlock w.1.1 w.1.2 w.2) :=
  measurable_from_prod_countable_right (fun i => measurable_meanBlock i.1 i.2)

@[fun_prop] lemma measurable_pilotReply (p : Params) :
    Measurable (fun w : ℝ × (ℕ → p.E) => pilotReply p w.1 w.2) := by
  have hr : Measurable (fun w : ℝ × (ℕ → p.E) => pilotSize p w.1) :=
    (measurable_pilotSize p).comp measurable_fst
  have hG : Measurable (fun w : ℕ × (ℝ × (ℕ → p.E)) =>
      pilotCenter (radius p w.2.1) (fun i : Fin w.1 =>
        meanBlock (i*pilotSize p w.2.1) (pilotSize p w.2.1) w.2.2)) := by
    apply measurable_from_prod_countable_right
    intro k
    have hv : Measurable (fun w : ℝ × (ℕ → p.E) => fun i : Fin k =>
        meanBlock (i*pilotSize p w.1) (pilotSize p w.1) w.2) := by
      apply Measurable.of_eval
      intro i
      have hmap : Measurable (fun w : ℝ × (ℕ → p.E) =>
          (((i : ℕ)*pilotSize p w.1, pilotSize p w.1), w.2)) :=
        ((hr.const_mul (i : ℕ)).prodMk hr).prodMk measurable_snd
      have hh := (measurable_meanBlock_all (E := p.E)).comp hmap
      simpa only [Function.comp_def] using hh
    exact (measurable_pilotCenter k).comp
      (((measurable_radius p).comp measurable_fst).prodMk hv)
  exact hG.comp (((measurable_pilotGroups p).comp measurable_fst).prodMk measurable_id)

@[fun_prop] lemma measurable_correctionReply (p : Params) :
    Measurable (fun w : ℝ × (ℕ → p.E) => correctionReply p w.1 w.2) := by
  have hr : Measurable (fun w : ℝ × (ℕ → p.E) => pilotSize p w.1) :=
    (measurable_pilotSize p).comp measurable_fst
  have hk : Measurable (fun w : ℝ × (ℕ → p.E) => pilotGroups p w.1) :=
    (measurable_pilotGroups p).comp measurable_fst
  have hm : Measurable (fun w : ℝ × (ℕ → p.E) => correctionSize p w.1) :=
    (measurable_correctionSize p).comp measurable_fst
  have hmap : Measurable (fun w : ℝ × (ℕ → p.E) =>
      ((pilotGroups p w.1*pilotSize p w.1, correctionSize p w.1), w.2)) :=
    ((hk.mul hr).prodMk hm).prodMk measurable_snd
  have hh := (measurable_meanBlock_all (E := p.E)).comp hmap
  simpa only [Function.comp_def, correctionReply] using hh

@[fun_prop] lemma measurable_estimate (p : Params) :
    Measurable (fun w : ℝ × (ℕ → p.E) => estimate p w.1 w.2) :=
  measurable_centeredClip_joint.comp (((measurable_radius p).comp measurable_fst).prodMk
    ((measurable_pilotReply p).prodMk (measurable_correctionReply p)))

lemma measurable_sampleReplies (p : Params) {oracle : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (fun w : p.E × (Fin n → p.Ω) => sampleReplies oracle w.1 w.2) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i < n
  · simp only [sampleReplies, hi, ↓reduceDIte]
    exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply (⟨i, hi⟩ : Fin n)).comp measurable_snd))
  · simp only [sampleReplies, hi, ↓reduceDIte]
    exact measurable_const

lemma measurable_sampleEstimate (p : Params) {oracle : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (fun w : ℝ × p.E × (Fin n → p.Ω) => sampleEstimate p w.1 oracle w.2.1 w.2.2) :=
  (measurable_estimate p).comp
    (measurable_fst.prodMk ((measurable_sampleReplies p hg n).comp measurable_snd))

end OracleTemplate.AdaptiveRobustGeneralized
