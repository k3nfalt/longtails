import LongTails.Proofs.AdaptiveRobustGeneralizedMeasurability
import LongTails.Proofs.AdaptiveRobustGeneralizedTuning
import LongTails.Proofs.RobustSampleBlocks
import LongTails.Proofs.AdaptivePilotConfidence

open MeasureTheory

namespace OracleTemplate.AdaptiveRobustGeneralized

open RobustGradient

noncomputable def estimatorSplit (p : Params) (a : ℝ)
    (ξ : Fin (estimatorCost p a) → p.Ω) :
    (Fin (pilotGroups p a) → Fin (pilotSize p a) → p.Ω) × (Fin (correctionSize p a) → p.Ω) :=
  ((fun i j => ξ ⟨i*pilotSize p a+j, by
    have hi := Nat.mul_le_mul_right (pilotSize p a) (Nat.succ_le_of_lt i.isLt)
    simp only [Nat.succ_mul] at hi
    have hj := j.isLt
    unfold estimatorCost
    omega⟩),
   (fun j => ξ ⟨pilotGroups p a*pilotSize p a+j, by
    have hj := j.isLt
    unfold estimatorCost
    omega⟩))

lemma estimatorSplit_preserving (p : Params) (a : ℝ) (μ : Measure p.Ω)
    [IsProbabilityMeasure μ] :
    MeasurePreserving (estimatorSplit p a) (Measure.pi fun _ : Fin (estimatorCost p a) => μ)
      ((Measure.pi fun _ : Fin (pilotGroups p a) => Measure.pi fun _ : Fin (pilotSize p a) => μ).prod
        (Measure.pi fun _ : Fin (correctionSize p a) => μ)) :=
  grouped_split_preserving μ (pilotGroups p a) (pilotSize p a) (correctionSize p a)

lemma pilotReply_samples (p : Params) (a : ℝ) (oracle : p.E → p.Ω → p.E) (x : p.E)
    (ξ : Fin (estimatorCost p a) → p.Ω) :
    pilotReply p a (sampleReplies oracle x ξ) =
      pilotCenter (radius p a) (fun i => (1/(pilotSize p a : ℝ)) •
        ∑ j, oracle x ((estimatorSplit p a ξ).1 i j)) := by
  unfold pilotReply meanBlock
  congr 1
  funext i
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hi := Nat.mul_le_mul_right (pilotSize p a) (Nat.succ_le_of_lt i.isLt)
  simp only [Nat.succ_mul] at hi
  have hj := j.isLt
  have hb : i*pilotSize p a+j < estimatorCost p a := by unfold estimatorCost; omega
  simp only [sampleReplies, hb, ↓reduceDIte, estimatorSplit]

lemma correctionReply_samples (p : Params) (a : ℝ) (oracle : p.E → p.Ω → p.E) (x : p.E)
    (ξ : Fin (estimatorCost p a) → p.Ω) :
    correctionReply p a (sampleReplies oracle x ξ) =
      (1/(correctionSize p a : ℝ)) • ∑ j, oracle x ((estimatorSplit p a ξ).2 j) := by
  unfold correctionReply meanBlock
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hj := j.isLt
  have hb : pilotGroups p a*pilotSize p a+j < estimatorCost p a := by unfold estimatorCost; omega
  simp only [sampleReplies, hb, ↓reduceDIte, estimatorSplit]

noncomputable def guardedReply (p : Params) (f : p.E → ℝ) (a : ℝ)
    (oracle : p.E → p.Ω → p.E) (x : p.E) {n : ℕ} (ξ : Fin n → p.Ω) : p.E :=
  gradient f x+guardedError (radius p a) (gradient f x)
    (pilotReply p a (sampleReplies oracle x ξ)) (correctionReply p a (sampleReplies oracle x ξ))

lemma guardedReply_error (p : Params) (f : p.E → ℝ) (a : ℝ)
    (oracle : p.E → p.Ω → p.E) (x : p.E) {n : ℕ} (ξ : Fin n → p.Ω) :
    guardedReply p f a oracle x ξ-gradient f x =
      guardedError (radius p a) (gradient f x)
        (pilotReply p a (sampleReplies oracle x ξ)) (correctionReply p a (sampleReplies oracle x ξ)) := by
  unfold guardedReply
  abel

lemma guardedReply_eq (p : Params) (f : p.E → ℝ) (a : ℝ)
    (oracle : p.E → p.Ω → p.E) (x : p.E) {n : ℕ} (ξ : Fin n → p.Ω)
    (h : ‖gradient f x-pilotReply p a (sampleReplies oracle x ξ)‖ ≤ radius p a/2) :
    guardedReply p f a oracle x ξ = sampleEstimate p a oracle x ξ := by
  rw [guardedReply, guardedError_eq h]
  change gradient f x+(sampleEstimate p a oracle x ξ-gradient f x) = _
  abel

lemma guardedReply_bound (p : Params) (f : p.E → ℝ) (a : ℝ)
    (oracle : p.E → p.Ω → p.E) (x : p.E) {n : ℕ} (ξ : Fin n → p.Ω)
    (hB : 0 ≤ radius p a) :
    ‖guardedReply p f a oracle x ξ-gradient f x‖ ≤ 3*radius p a/2 := by
  rw [guardedReply_error]
  exact guardedError_bound hB _ _ _

lemma measurable_guardedReply (p : Params) {f : p.E → ℝ}
    (hgrad : Measurable (gradient f)) {oracle : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry oracle)) (n : ℕ) :
    Measurable (fun w : ℝ × p.E × (Fin n → p.Ω) => guardedReply p f w.1 oracle w.2.1 w.2.2) := by
  have hx : Measurable (fun w : ℝ × p.E × (Fin n → p.Ω) => gradient f w.2.1) :=
    hgrad.comp measurable_snd.fst
  have hs : Measurable (fun w : ℝ × p.E × (Fin n → p.Ω) =>
      (w.1, sampleReplies oracle w.2.1 w.2.2)) :=
    measurable_fst.prodMk ((measurable_sampleReplies p hg n).comp measurable_snd)
  exact hx.add (measurable_guardedError.comp
    (((measurable_radius p).comp measurable_fst).prodMk
      (hx.prodMk (((measurable_pilotReply p).comp hs).prodMk
        ((measurable_correctionReply p).comp hs)))))

lemma guardedReply_moments (p : Params) (μ : Measure p.Ω) [IsProbabilityMeasure μ]
    {f : p.E → ℝ} {oracle : p.E → p.Ω → p.E}
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (a : ℝ) (hB : 0 < radius p a) (x : p.E) :
    Integrable (fun ξ : Fin (estimatorCost p a) → p.Ω =>
      guardedReply p f a oracle x ξ-gradient f x) (Measure.pi fun _ => μ) ∧
    Integrable (fun ξ : Fin (estimatorCost p a) → p.Ω =>
      ‖guardedReply p f a oracle x ξ-gradient f x‖^2) (Measure.pi fun _ => μ) ∧
    (∫ ξ : Fin (estimatorCost p a) → p.Ω, ‖guardedReply p f a oracle x ξ-gradient f x‖^2
      ∂Measure.pi (fun _ => μ)) ≤ p.σ^2/(correctionSize p a : ℝ) ∧
    ‖∫ ξ : Fin (estimatorCost p a) → p.Ω, guardedReply p f a oracle x ξ-gradient f x
      ∂Measure.pi (fun _ => μ)‖ ≤ 2*(p.σ^2/(correctionSize p a : ℝ))/radius p a := by
  let C : (Fin (pilotGroups p a) → Fin (pilotSize p a) → p.Ω) → p.E :=
    fun ξ => pilotCenter (radius p a) (fun i => (1/(pilotSize p a : ℝ)) • ∑ j, oracle x (ξ i j))
  let V : (Fin (correctionSize p a) → p.Ω) → p.E :=
    fun ξ => (1/(correctionSize p a : ℝ)) • ∑ j, oracle x (ξ j)
  have hox : Measurable (oracle x) := hg.measurable.comp measurable_prodMk_left
  have hC : Measurable C := (measurable_pilotCenter (pilotGroups p a)).comp
    (measurable_const.prodMk (by fun_prop))
  have hV : Measurable V := by dsimp [V]; fun_prop
  have hm : 0 < correctionSize p a := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hmean := LightTail.finite_mean_integral (hg.integrable x) (correctionSize p a) hm
  have hvar := finite_mean_variance hox (hg.integrable x) (gradient f x)
    (hg.variance_integrable x) (hg.unbiased x) (correctionSize p a) hm
  have hv : (∫ ξ, ‖V ξ-gradient f x‖^2 ∂Measure.pi (fun _ : Fin (correctionSize p a) => μ)) ≤
      p.σ^2/(correctionSize p a : ℝ) := by
    rw [show (∫ ξ, ‖V ξ-gradient f x‖^2 ∂Measure.pi (fun _ : Fin (correctionSize p a) => μ)) =
      (∫ ω, ‖oracle x ω-gradient f x‖^2 ∂μ)/(correctionSize p a : ℝ) from hvar.2]
    exact div_le_div_of_nonneg_right (hg.variance x) (by positivity)
  have h := random_center_moments
    (P := Measure.pi fun _ : Fin (pilotGroups p a) => Measure.pi fun _ : Fin (pilotSize p a) => μ)
    hC hV hmean.1 (hmean.2.trans (hg.unbiased x)) hB hvar.1 hv
  let Y := fun w : (Fin (pilotGroups p a) → Fin (pilotSize p a) → p.Ω) ×
      (Fin (correctionSize p a) → p.Ω) => guardedError (radius p a) (gradient f x) (C w.1) (V w.2)
  have he (ξ : Fin (estimatorCost p a) → p.Ω) :
      guardedReply p f a oracle x ξ-gradient f x = Y (estimatorSplit p a ξ) := by
    rw [guardedReply_error, pilotReply_samples, correctionReply_samples]
  have hs := estimatorSplit_preserving p a μ
  have hl : ProbabilityTheory.HasLaw (estimatorSplit p a)
      ((Measure.pi fun _ : Fin (pilotGroups p a) => Measure.pi fun _ : Fin (pilotSize p a) => μ).prod
        (Measure.pi fun _ : Fin (correctionSize p a) => μ))
      (Measure.pi fun _ : Fin (estimatorCost p a) => μ) := ⟨hs.measurable.aemeasurable, hs.map_eq⟩
  simp_rw [he]
  refine ⟨hs.integrable_comp_of_integrable h.1, hs.integrable_comp_of_integrable h.2.1, ?_, ?_⟩
  · change (∫ ξ, ((fun w => ‖Y w‖^2) ∘ estimatorSplit p a) ξ ∂Measure.pi (fun _ => μ)) ≤ _
    exact (hl.integral_comp h.2.1.aestronglyMeasurable).trans_le h.2.2.1
  · have hi := hl.integral_comp h.1.aestronglyMeasurable
    change (∫ ξ, Y (estimatorSplit p a ξ) ∂Measure.pi (fun _ => μ)) = _ at hi
    rw [hi]
    exact h.2.2.2

lemma pilotReply_failure_probability (p : Params) (μ : Measure p.Ω) [IsProbabilityMeasure μ]
    {f : p.E → ℝ} {oracle : p.E → p.Ω → p.E}
    (hg : LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient p.E p.Ω μ f oracle p.σ)
    (a : ℝ) (hB : 0 < radius p a) (x : p.E) :
    (Measure.pi fun _ : Fin (estimatorCost p a) => μ)
      {ξ | radius p a/2 < ‖gradient f x-pilotReply p a (sampleReplies oracle x ξ)‖} ≤
      ENNReal.ofReal ((2*Real.sqrt (ratio p a/16))^(pilotGroups p a)) := by
  let C : (Fin (pilotGroups p a) → Fin (pilotSize p a) → p.Ω) → p.E :=
    fun ξ => pilotCenter (radius p a) (fun i => (1/(pilotSize p a : ℝ)) • ∑ j, oracle x (ξ i j))
  have hox : Measurable (oracle x) := hg.measurable.comp measurable_prodMk_left
  have hC : Measurable C := (measurable_pilotCenter (pilotGroups p a)).comp
    (measurable_const.prodMk (by fun_prop))
  have hr : 0 < pilotSize p a := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hθ : 0 < ratio p a/16 := by have h := ratio_pos p a; positivity
  have hθ1 : ratio p a/16 ≤ 1 := by have h := ratio_le_one p a; linarith
  have h := pilot_means_failure_probability_le hox (hg.integrable x) (gradient f x)
    (hg.unbiased x) (hg.variance_integrable x) (hg.variance x) hB hθ hθ1
    (pilotGroups p a) (pilotSize p a) hr (pilot_variance p hB)
  have hm := (measurePreserving_fst
    (μ := Measure.pi fun _ : Fin (pilotGroups p a) => Measure.pi fun _ : Fin (pilotSize p a) => μ)
    (ν := Measure.pi fun _ : Fin (correctionSize p a) => μ)).comp (estimatorSplit_preserving p a μ)
  have hset : MeasurableSet {w | radius p a/2 < ‖C w-gradient f x‖} :=
    measurableSet_lt measurable_const (hC.sub measurable_const).norm
  have he := hm.measure_preimage hset.nullMeasurableSet
  rw [← he] at h
  simpa only [Set.preimage_ofPred_eq, Function.comp_apply, pilotReply_samples,
    C, norm_sub_rev] using h

end OracleTemplate.AdaptiveRobustGeneralized
