import LongTails.Proofs.SpikedSoftCutEvents
import LongTails.Proofs.SpikedSoftCutSeededExecution
import LongTails.Proofs.CovarianceSoftCutFreshness

open MeasureTheory

namespace LongTails.Proofs.SpikedSoftCutOuterProbability

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCutMethod
open SpikedSoftCutEpochProcess
open SpikedSoftCutFreshness
open SpikedSoftCutEvents
open OracleTemplate.StochasticGeneralized

abbrev BlockState (q : Params) := ℕ × OuterState q

def blockCost (q : Params) (c : Config) (s : BlockState q) : ℕ := epochCost c s.1

noncomputable def blockNext (q : Params) (c : Config) (g : Space q → q.Ω → Space q)
    (z : q.Ω) (n : ℕ) (s : BlockState q) (b : Fin n → q.Ω) : BlockState q :=
  (s.1+1, nextState q c s.1 s.2 (epochReplies q c s.1 s.2 g (SoftCutPredictableBatches.prefixStream z n b)))

noncomputable def blockIncrement (q : Params) (c : Config) (ν ρ : ℝ) (r : ℕ → ℝ)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q) (z : q.Ω)
    (n : ℕ) (s : BlockState q) (b : Fin n → q.Ω) : ℝ :=
  badIndicator q c ν ρ (r s.1) s.1 s.2 g v z n b

lemma measurable_blockCost (q : Params) (c : Config) : Measurable (blockCost q c) :=
  (measurable_of_countable (epochCost c)).comp measurable_fst

lemma measurable_blockNext (q : Params) (c : Config) (hR : 0 < q.R)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) (z : q.Ω) (n : ℕ) :
    Measurable (Function.uncurry (blockNext q c g z n)) := by
  let f := fun k : ℕ => fun w : OuterState q × (Fin n → q.Ω) =>
    (k+1, nextState q c k w.1 (epochReplies q c k w.1 g (SoftCutPredictableBatches.prefixStream z n w.2)))
  have hf (k : ℕ) : Measurable (f k) := by
    have hm : Measurable (fun w : OuterState q × (Fin n → q.Ω) =>
        (w.1,SoftCutPredictableBatches.prefixStream z n w.2)) :=
      measurable_fst.prodMk ((SoftCutPredictableBatches.measurable_prefixStream z n).comp measurable_snd)
    have hh := (measurable_seeded_nextState q c hR g hg k).comp hm
    have hc : Measurable (fun _ : OuterState q × (Fin n → q.Ω) => k+1) := measurable_const
    convert! hc.prodMk hh using 1
  have hp : Measurable (fun w : (OuterState q × (Fin n → q.Ω)) × ℕ => f w.2 w.1) :=
    measurable_from_prod_countable_left hf
  have harg : Measurable (fun x : BlockState q × (Fin n → q.Ω) => ((x.1.2,x.2),x.1.1)) :=
    (measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst
  have hh := hp.comp harg
  convert! hh using 1

lemma measurable_blockIncrement (q : Params) (c : Config) (hR : 0 < q.R)
    (ν ρ : ℝ) (r : ℕ → ℝ) (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) (z : q.Ω) (n : ℕ) :
    Measurable (Function.uncurry (blockIncrement q c ν ρ r g v z n)) := by
  let f := fun k : ℕ => fun w : OuterState q × (Fin n → q.Ω) => badIndicator q c ν ρ (r k) k w.1 g v z n w.2
  have hf (k : ℕ) : Measurable (f k) := measurable_badIndicator q c hR ν ρ (r k) k g v hg hv z n
  have hp : Measurable (fun w : (OuterState q × (Fin n → q.Ω)) × ℕ => f w.2 w.1) :=
    measurable_from_prod_countable_left hf
  have harg : Measurable (fun x : BlockState q × (Fin n → q.Ω) => ((x.1.2,x.2),x.1.1)) :=
    (measurable_fst.snd.prodMk measurable_snd).prodMk measurable_fst.fst
  have hh := hp.comp harg
  convert! hh using 1

lemma blockNext_full (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (g : Space q → q.Ω → Space q) (z : q.Ω) (s : BlockState q) (ξ : ℕ → q.Ω) :
    blockNext q c g z (blockCost q c s) s (fun i => ξ i) =
      (s.1+1, nextState q c s.1 s.2 (epochReplies q c s.1 s.2 g ξ)) := by
  have hp : ∀ i, i < epochCost c s.1 →
      SoftCutPredictableBatches.prefixStream z (epochCost c s.1) (fun j => ξ j) i = ξ i := by
    intro i hi
    simp only [SoftCutPredictableBatches.prefixStream, hi, dite_true]
  have he := epochReplies_seed_prefix q c s.1 s.2 g _ ξ hp
  have hh := SpikedSoftCutMethodExecution.nextState_prefix q c hT hn s.1 s.2 _ _ he
  exact congrArg (fun state : OuterState q => (s.1+1,state)) hh

lemma accumulated_bad_mean {Ξ : Type*} [MeasurableSpace Ξ]
    (q : Params) (c : Config) (hR : 0 < q.R) (hT : 0 < c.T) (hb : 0 < c.b) (hn : 0 < c.n)
    (ν ρ δ : ℝ) (r : ℕ → ℝ) (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (hg : Measurable (Function.uncurry g)) (hv : Measurable v) (z : q.Ω)
    (p : Measure q.Ω) [IsProbabilityMeasure p] (P : Measure Ξ)
    (ξ : ℕ → Ξ → q.Ω) (hξ : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P)
    (hprob : ∀ k state, (Measure.infinitePi fun _ : ℕ => p).real
      {seeds | badEpoch q c ν ρ (r k) k state g v seeds} ≤ δ) (steps : ℕ) (s : BlockState q) :
    Integrable (fun ω => accumulated (blockCost q c) (blockNext q c g z)
      (blockIncrement q c ν ρ r g v z) steps s (fun i => ξ i ω)) P ∧
    (∫ ω, accumulated (blockCost q c) (blockNext q c g z)
      (blockIncrement q c ν ρ r g v z) steps s (fun i => ξ i ω) ∂P) ≤ steps*δ := by
  apply CovarianceSoftCutFreshness.accumulated_mean_iid p P ξ hξ
    (measurable_blockCost q c) (measurable_blockNext q c hR g hg z)
    (measurable_blockIncrement q c hR ν ρ r g v hg hv z)
  · intro n state b
    exact (badIndicator_bounds q c ν ρ (r state.1) state.1 state.2 g v z n b).1
  · intro state
    exact badIndicator_integrable q c hR ν ρ (r state.1) state.1 state.2 g v hg hv z _ p
  · intro state
    exact badIndicator_mean q c hR hT hb hn ν ρ (r state.1) δ state.1 state.2 g v hg hv z p (hprob _ _)

lemma blockIncrement_full (q : Params) (c : Config) (hT : 0 < c.T) (hb : 0 < c.b) (hn : 0 < c.n)
    (ν ρ : ℝ) (r : ℕ → ℝ) (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (z : q.Ω) (s : BlockState q) (ξ : ℕ → q.Ω) :
    blockIncrement q c ν ρ r g v z (blockCost q c s) s (fun i => ξ i) =
      @ite ℝ (badEpoch q c ν ρ (r s.1) s.1 s.2 g v ξ) (Classical.propDecidable _) 1 0 := by
  have hh := badEpoch_seed_prefix q c hT hb hn ν ρ (r s.1) s.1 s.2 g v
    (SoftCutPredictableBatches.prefixStream z (epochCost c s.1) (fun i => ξ i)) ξ
    (fun i hi => by simp only [SoftCutPredictableBatches.prefixStream, hi, dite_true])
  unfold blockIncrement badIndicator blockCost
  rw [hh]

lemma accumulated_bad_nonneg (q : Params) (c : Config) (ν ρ : ℝ) (r : ℕ → ℝ)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q) (z : q.Ω)
    (steps : ℕ) (s : BlockState q) (ξ : ℕ → q.Ω) :
    0 ≤ accumulated (blockCost q c) (blockNext q c g z) (blockIncrement q c ν ρ r g v z) steps s ξ := by
  have hi : ∀ n (s : BlockState q) b, 0 ≤ blockIncrement q c ν ρ r g v z n s b :=
    fun n s b => (badIndicator_bounds q c ν ρ (r s.1) s.1 s.2 g v z n b).1
  exact CovarianceSoftCutFreshness.accumulated_nonneg (blockCost q c) (blockNext q c g z)
    (blockIncrement q c ν ρ r g v z) hi steps s ξ

lemma accumulated_small_preserves (q : Params) (c : Config) (hT : 0 < c.T) (hb : 0 < c.b) (hn : 0 < c.n)
    (ν ρ : ℝ) (r : ℕ → ℝ) (g : Space q → q.Ω → Space q) (v : Space q → Space q) (z : q.Ω)
    (Inv : ℕ → OuterState q → Prop)
    (hstep : ∀ k state ξ, Inv k state → ¬badEpoch q c ν ρ (r k) k state g v ξ →
      Inv (k+1) (nextState q c k state (epochReplies q c k state g ξ)))
    (steps k : ℕ) (state : OuterState q) (ξ : ℕ → q.Ω) (hInv : Inv k state)
    (hsmall : accumulated (blockCost q c) (blockNext q c g z)
      (blockIncrement q c ν ρ r g v z) steps (k,state) ξ < 1) :
    Inv (k+steps) (SpikedSoftCutSeededExecution.terminalState q c g k steps state ξ) := by
  classical
  induction steps generalizing k state ξ with
  | zero => simpa only [Nat.add_zero, SpikedSoftCutSeededExecution.terminalState] using hInv
  | succ steps ih =>
    let next := nextState q c k state (epochReplies q c k state g ξ)
    let tailSeeds := fun i => ξ (epochCost c k+i)
    have he : accumulated (blockCost q c) (blockNext q c g z)
        (blockIncrement q c ν ρ r g v z) (steps+1) (k,state) ξ =
        (if badEpoch q c ν ρ (r k) k state g v ξ then 1 else 0) +
          accumulated (blockCost q c) (blockNext q c g z)
            (blockIncrement q c ν ρ r g v z) steps (k+1,next) tailSeeds := by
      rw [accumulated, blockIncrement_full q c hT hb hn, blockNext_full q c hT hn]
      rfl
    rw [he] at hsmall
    have hnon := accumulated_bad_nonneg q c ν ρ r g v z steps (k+1,next) tailSeeds
    have hgood : ¬badEpoch q c ν ρ (r k) k state g v ξ := by
      intro hbad
      rw [ite_eq_left hbad] at hsmall
      linarith
    have htail : accumulated (blockCost q c) (blockNext q c g z)
        (blockIncrement q c ν ρ r g v z) steps (k+1,next) tailSeeds < 1 := by
      simpa only [ite_eq_right hgood, zero_add] using hsmall
    have hh := ih (k+1) next tailSeeds (hstep k state ξ hInv hgood) htail
    simpa only [SpikedSoftCutSeededExecution.terminalState, Nat.add_assoc, Nat.add_comm 1 steps,
      next, tailSeeds] using hh

lemma measurable_terminalState (q : Params) (c : Config) (hR : 0 < q.R)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) (steps k : ℕ) :
    Measurable (fun x : OuterState q × (ℕ → q.Ω) =>
      SpikedSoftCutSeededExecution.terminalState q c g k steps x.1 x.2) := by
  induction steps generalizing k with
  | zero => exact measurable_fst
  | succ steps ih =>
    have hn := measurable_seeded_nextState q c hR g hg k
    have ht : Measurable (fun x : OuterState q × (ℕ → q.Ω) => fun i => x.2 (epochCost c k+i)) :=
      Measurable.of_eval (fun i => (measurable_pi_apply (epochCost c k+i)).comp measurable_snd)
    have hh := (ih (k+1)).comp (hn.prodMk ht)
    convert! hh using 1

lemma measurable_seeded_output (q : Params) (c : Config) (hR : 0 < q.R)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) (steps k : ℕ) (state : OuterState q) :
    Measurable (fun ξ : ℕ → q.Ω => saved q (SpikedSoftCutSeededExecution.terminalState q c g k steps state ξ)) := by
  have hm := (measurable_terminalState q c hR g hg steps k).comp
    (show Measurable (fun ξ : ℕ → q.Ω => (state,ξ)) from measurable_prodMk_left)
  exact hm.snd.snd.fst

lemma event_probability_of_small_success {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P] (E : Set Ξ) (hE : MeasurableSet E)
    (B : Ξ → ℝ) (hBi : Integrable B P) (hB : ∀ ω, 0 ≤ B ω)
    (hgood : ∀ ω, B ω < 1 → ω ∉ E) : P.real E ≤ ∫ ω, B ω ∂P := by
  have hi : Integrable (E.indicator (fun _ => (1 : ℝ))) P := (integrable_const _).indicator hE
  have hh := integral_mono hi hBi (show ∀ ω, E.indicator (fun _ => (1 : ℝ)) ω ≤ B ω from by
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      exact le_of_not_gt (fun hb => hgood ω hb hω)
    · rw [Set.indicator_of_notMem hω]
      exact hB ω)
  simpa only [integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one] using hh

end LongTails.Proofs.SpikedSoftCutOuterProbability
