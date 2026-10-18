import LongTails.Proofs.MixedNoiseExecution
import LongTails.Proofs.MixedNoiseMoments

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace OracleTemplate.MixedNoise

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ω : Type} [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma batchState_memLp (p : Measure Ω) [IsProbabilityMeasure p]
    (cfg : Config) (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (G : E → E) {L : ℝ≥0} (hG : LipschitzWith L G) (r σ : ℝ)
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p)
    (hbound : ∀ x, ∫ ω, ‖g x ω - G x‖ ^ 2 ∂p ≤ r * ‖G x‖ ^ 2 + σ ^ 2)
    (x0 : E) (seed : RepresentativeSeed cfg) (j : ℕ) :
    (∀ k, MemLp (fun ξ => (batchState cfg g x0 seed ξ j).xs k) 2
      (Measure.infinitePi fun _ : ℕ => p)) ∧
    (∀ l, MemLp (fun ξ => (batchState cfg g x0 seed ξ j).estimates l) 2
      (Measure.infinitePi fun _ : ℕ => p)) := by
  classical
  induction j with
  | zero => exact ⟨fun _ => memLp_const _, fun _ => memLp_const _⟩
  | succ j ih =>
    have hmeas := batchState_measurable cfg g hg x0 seed j
    have hpoint (side : Bool) :
        let X := fun ξ => if side then (taskPoints cfg (batchState cfg g x0 seed ξ j)).1
          else (taskPoints cfg (batchState cfg g x0 seed ξ j)).2
        Measurable X ∧ MemLp X 2 (Measure.infinitePi fun _ : ℕ => p) := by
      dsimp only
      cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, taskPoints,
        batchState_index, batchState_seed]
      all_goals split_ifs <;> exact ⟨hmeas.1 _, ih.1 _⟩
    have horacle (side : Bool) (n : ℕ) :
        MemLp (fun ξ => g (if side then (taskPoints cfg (batchState cfg g x0 seed ξ j)).1
          else (taskPoints cfg (batchState cfg g x0 seed ξ j)).2)
          (ξ (sampleOffset cfg j + n))) 2 (Measure.infinitePi fun _ : ℕ => p) := by
      apply fresh_oracle_memLp p (sampleOffset cfg j + n) _ (hpoint side).1
        _ g hg G hG.continuous.measurable
        (lipschitz_comp_memLp hG (hpoint side).2) r σ hnoise hbound
      intro ξ ξ' he
      rw [batchState_dep cfg g x0 seed j ξ ξ' (fun i hi => he i (by omega))]
    have hc (n : ℕ) : MemLp (fun ξ =>
        batchContribution cfg g (batchState cfg g x0 seed ξ j)
          (ξ (sampleOffset cfg j + n))) 2 (Measure.infinitePi fun _ : ℕ => p) := by
      simp only [batchContribution, batchState_index]
      split_ifs
      · simpa only [↓reduceIte] using horacle true n
      · convert (horacle true n).sub (horacle false n) using 1
        funext ξ
        simp only [Bool.false_eq_true, ↓reduceIte, Pi.sub_apply]
    have ha : MemLp (fun ξ => batchAccumulator cfg g (batchState cfg g x0 seed ξ j)
        ξ (sampleOffset cfg j) (cfg.tasks[j]!).size) 2 (Measure.infinitePi fun _ : ℕ => p) :=
      memLp_finsetSum _ fun n _ => hc n
    have he (l : ℕ) : MemLp (fun ξ => (batchState cfg g x0 seed ξ (j + 1)).estimates l)
        2 (Measure.infinitePi fun _ : ℕ => p) := by
      simp only [batchState, representativeCommit, batchState_index, Function.update_apply]
      split_ifs
      · exact ha.const_smul _
      · exact ih.2 l
    refine ⟨fun k => ?_, he⟩
    have hv := memLp_finsetSum (Finset.range (cfg.m + 1)) (fun l _ => he l)
    have hx := (ih.1 (cfg.tasks[j]!).t).sub (hv.const_smul cfg.η)
    simp only [batchState, representativeCommit, batchState_index] at hx ⊢
    split_ifs
    · simp only [Function.update_apply]
      split_ifs
      · convert hx using 1
        funext ξ
        simp only [Pi.sub_apply, Pi.smul_apply, Function.update_apply]
      · exact ih.1 k
    · exact ih.1 k

omit [CompleteSpace E] in
lemma batchPoints_memLp (p : Measure Ω) [IsProbabilityMeasure p]
    (cfg : Config) (g : E → Ω → E) (hg : Measurable (Function.uncurry g))
    (G : E → E) {L : ℝ≥0} (hG : LipschitzWith L G) (r σ : ℝ)
    (hnoise : ∀ x, Integrable (fun ω => ‖g x ω - G x‖ ^ 2) p)
    (hbound : ∀ x, ∫ ω, ‖g x ω - G x‖ ^ 2 ∂p ≤ r * ‖G x‖ ^ 2 + σ ^ 2)
    (x0 : E) (seed : RepresentativeSeed cfg) (j : ℕ) :
    MemLp (fun ξ => (taskPoints cfg (batchState cfg g x0 seed ξ j)).1) 2
      (Measure.infinitePi fun _ : ℕ => p) ∧
    MemLp (fun ξ => (taskPoints cfg (batchState cfg g x0 seed ξ j)).2) 2
      (Measure.infinitePi fun _ : ℕ => p) := by
  have h := (batchState_memLp p cfg g hg G hG r σ hnoise hbound x0 seed j).1
  simp only [taskPoints, batchState_index, batchState_seed]
  split_ifs <;> exact ⟨h _, h _⟩

omit [CompleteSpace E] in
lemma batchPoints_measurable (cfg : Config) (g : E → Ω → E)
    (hg : Measurable (Function.uncurry g)) (x0 : E) (seed : RepresentativeSeed cfg) (j : ℕ) :
    Measurable (fun ξ => taskPoints cfg (batchState cfg g x0 seed ξ j)) := by
  have h := (batchState_measurable cfg g hg x0 seed j).1
  simp only [taskPoints, batchState_index, batchState_seed]
  split_ifs <;> exact (h _).prodMk (h _)

end OracleTemplate.MixedNoise
