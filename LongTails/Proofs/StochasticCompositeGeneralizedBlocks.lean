import LongTails.Proofs.StochasticCompositeGeneralizedExecution
import LongTails.Proofs.ClippedExtragradientProcess
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.FairExecution
import LongTails.Proofs.AcceleratedMarkovExecution

open MeasureTheory

namespace OracleTemplate.StochasticCompositeGeneralized
open LongTails.Setups.StochasticCompositeGeneralizedSmooth
open StochasticGradient (advance)
open FairVarianceReduction (prefixValues prefixValues_zero prefixValues_update)

lemma rawAdvance_add (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (n m call : ℕ) (s : State p.E) :
    rawAdvance p I g ξ (n + m) call s =
      rawAdvance p I g ξ m (call + n) (rawAdvance p I g ξ n call s) :=
  HeavyTailedMarkovGradient.advance_add _ _ _ _ _

lemma rawAdvance_first_pilot_prefix (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (s : State p.E) (call j : ℕ) (hj : j < pilotSize p s.iteration) :
    rawAdvance p I g ξ j call { s with stage := 0, received := 0, replies := fun _ => 0 } =
      { s with
        stage := 0, received := j, replies := prefixValues (fun i => g s.x (ξ (call + i))) j } := by
  induction j with
  | zero => simp [rawAdvance, advance, prefixValues_zero]
  | succ j ih =>
    rw [rawAdvance_add, ih (by omega)]
    simp only [rawAdvance, advance, algorithm, oracleReply, update]
    simp only [Nat.reduceEqDiff, ite_true, ite_false, hj]
    rw [prefixValues_update]


noncomputable def finiteAdvance (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    {n : ℕ} (ξ : Fin n → p.Ω) (m call : ℕ) (s : State p.E) : State p.E :=
  advance (fun k s => update p s (if hk : k < n then canonicalReply p I g s (ξ ⟨k, hk⟩) else 0))
    m call s

lemma finiteAdvance_restrict (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (n m call : ℕ) (h : call + m ≤ n) (s : State p.E) :
    finiteAdvance p I g (fun i : Fin n => ξ i) m call s = canonicalAdvance p I g ξ m call s := by
  induction m generalizing call s with
  | zero => rfl
  | succ m ih =>
    have hk : call < n := by omega
    simp only [finiteAdvance, canonicalAdvance, advance, dite_eq_left hk]
    exact ih (call + 1) (by omega) _

lemma finiteAdvance_wellFormed (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    {n : ℕ} (ξ : Fin n → p.Ω) (m call : ℕ) {s : State p.E} (hs : WellFormed s) :
    WellFormed (finiteAdvance p I g ξ m call s) := by
  induction m generalizing call s with
  | zero => exact hs
  | succ m ih =>
    exact ih (call + 1) (update_wellFormed p hL0 hL1 hR hσ hs _)

lemma measurable_finiteAdvance (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry g))
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0)) (n m call : ℕ) :
    Measurable (fun w : State p.E × (Fin n → p.Ω) => finiteAdvance p I g w.2 m call w.1) := by
  induction m generalizing call with
  | zero => exact measurable_fst
  | succ m ih =>
    have hr : Measurable (fun w : State p.E × (Fin n → p.Ω) =>
        if hk : call < n then canonicalReply p I g w.1 (w.2 ⟨call, hk⟩) else 0) := by
      by_cases hk : call < n
      · simp only [dite_eq_left hk]
        exact (measurable_canonicalReply p I hg hprox).comp
          (measurable_fst.prodMk ((measurable_pi_apply (⟨call, hk⟩ : Fin n)).comp measurable_snd))
      · simp only [dite_eq_right hk]
        exact measurable_const
    have hu : Measurable (fun w : State p.E × (Fin n → p.Ω) =>
        update p w.1 (if hk : call < n then canonicalReply p I g w.1 (w.2 ⟨call, hk⟩) else 0)) :=
      (measurable_update p).comp (measurable_fst.prodMk hr)
    exact (ih (call + 1)).comp (hu.prodMk measurable_snd)

noncomputable def phaseCost (p : Public.{0}) (s : State p.E) : ℕ :=
  if s.stage = 0 ∨ s.stage = 1 then pilotSize p s.iteration
  else if s.stage = 2 then batchSize p s.iteration (stepWeight p s) else 1

noncomputable def phaseNext (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (n : ℕ) (s : State p.E) (ξ : Fin n → p.Ω) : State p.E :=
  finiteAdvance p I g ξ n 0 s

def PhaseEntry {E : Type*} [Zero E] (s : State E) : Prop :=
  (s.stage = 0 ∨ s.stage = 1 → s.received = 0 ∧ s.replies = fun _ => 0) ∧
    (s.stage = 2 → s.received = 0 ∧ s.total = 0)

lemma measurable_phaseCost (p : Public.{0}) : Measurable (phaseCost p) := by
  have hs (k : ℕ) : MeasurableSet {s : State p.E | s.stage = k} :=
    measurableSet_eq_fun measurable_state_stage measurable_const
  have hb := (measurable_batchSize p).comp
    ((measurable_state_iteration (E := p.E)).prodMk (measurable_stepWeight p))
  simp only [Function.comp_def] at hb
  unfold phaseCost
  apply Measurable.ite ((hs 0).union (hs 1))
  · exact (measurable_pilotSize p).comp measurable_state_iteration
  · exact Measurable.ite (hs 2) hb measurable_const

lemma measurable_phaseNext (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry g))
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0)) (n : ℕ) :
    Measurable (Function.uncurry (phaseNext p I g n)) :=
  measurable_finiteAdvance p I hg hprox n n 0

lemma phaseNext_eq_rawAdvance (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (ξ : ℕ → p.Ω) (n : ℕ) {s : State p.E} (hs : WellFormed s) :
    phaseNext p I g n s (fun i => ξ i) = rawAdvance p I g ξ n 0 s := by
  unfold phaseNext
  rw [finiteAdvance_restrict p I g ξ n n 0 (by omega),
    canonicalAdvance_eq p I g hL0 hL1 hR hσ ξ n 0 hs]


lemma pilotSize_pos (p : Public.{0}) (k : ℕ) : 0 < pilotSize p k :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

lemma batchSize_pos (p : Public.{0}) (k : ℕ) (a : ℝ) : 0 < batchSize p k a :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

lemma samplePilot_prefixValues (p : Public.{0}) (k : ℕ) (v : ℕ → p.E) (n : ℕ)
    (hn : pilotSize p k ≤ n) : samplePilot p k (prefixValues v n) = samplePilot p k v := by
  unfold samplePilot
  congr 1
  funext i
  exact ite_eq_left (lt_of_lt_of_le i.isLt hn)

lemma rawAdvance_first_pilot (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (s : State p.E) (call : ℕ) :
    rawAdvance p I g ξ (pilotSize p s.iteration) call
      { s with stage := 0, received := 0, replies := fun _ => 0 } =
      { s with
        stage := 1, M := p.L0 + p.L1 *
          (‖samplePilot p s.iteration (fun i => g s.x (ξ (call + i)))‖ + 96 * p.σ),
        received := 0, replies := fun _ => 0 } := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (pilotSize_pos p s.iteration).ne'
  rw [hj, Nat.succ_eq_add_one, rawAdvance_add, rawAdvance_first_pilot_prefix p I g ξ s call j (by omega)]
  simp only [rawAdvance, advance, algorithm, oracleReply, update]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, show ¬j + 1 < pilotSize p s.iteration by omega]
  rw [prefixValues_update, samplePilot_prefixValues p s.iteration _ (j + 1) (by omega)]

lemma rawAdvance_second_pilot_prefix (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (s : State p.E) (call j : ℕ) (hj : j < pilotSize p s.iteration) :
    rawAdvance p I g ξ j call { s with stage := 1, received := 0, replies := fun _ => 0 } =
      { s with
        stage := 1, received := j,
        replies := prefixValues (fun i => g (queryPoint p s) (ξ (call + i))) j } := by
  induction j with
  | zero => simp [rawAdvance, advance, prefixValues_zero]
  | succ j ih =>
    rw [rawAdvance_add, ih (by omega)]
    simp only [rawAdvance, advance, algorithm, oracleReply, update]
    simp only [Nat.reduceEqDiff, ite_true, ite_false, hj, true_or]
    dsimp only [queryPoint, stepWeight]
    rw [prefixValues_update]

lemma rawAdvance_second_pilot (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (s : State p.E) (call : ℕ) :
    rawAdvance p I g ξ (pilotSize p s.iteration) call
      { s with stage := 1, received := 0, replies := fun _ => 0 } =
      { s with
        stage := 2, center := samplePilot p s.iteration
          (fun i => g (queryPoint p s) (ξ (call + i))),
        total := 0, received := 0, replies := fun _ => 0 } := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (pilotSize_pos p s.iteration).ne'
  rw [hj, Nat.succ_eq_add_one, rawAdvance_add,
    rawAdvance_second_pilot_prefix p I g ξ s call j (by omega)]
  simp only [rawAdvance, advance, algorithm, oracleReply, update]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, true_or,
    show ¬j + 1 < pilotSize p s.iteration by omega]
  dsimp only [queryPoint, stepWeight]
  rw [prefixValues_update, samplePilot_prefixValues p s.iteration _ (j + 1) (by omega)]

lemma initialState_phaseEntry (p : Public.{0}) : PhaseEntry (initialState p) := by
  simp [PhaseEntry, initialState]

lemma rawAdvance_evaluation_prefix (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (s : State p.E) (call j : ℕ)
    (hj : j < batchSize p s.iteration (stepWeight p s)) :
    rawAdvance p I g ξ j call { s with stage := 2, received := 0, total := 0 } =
      { s with
        stage := 2, received := j,
        total := ∑ i ∈ Finset.range j, RobustGradient.centeredClip
          (clipRadius p s.iteration) s.center (g (queryPoint p s) (ξ (call + i))) } := by
  induction j with
  | zero => simp [rawAdvance, advance]
  | succ j ih =>
    rw [rawAdvance_add, ih (by omega)]
    simp only [rawAdvance, advance, algorithm, oracleReply, update]
    dsimp only [queryPoint, stepWeight] at *
    simp only [Nat.reduceEqDiff, ite_true, ite_false, false_or, hj, Finset.sum_range_succ]

lemma rawAdvance_evaluation (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (s : State p.E) (call : ℕ) :
    rawAdvance p I g ξ (batchSize p s.iteration (stepWeight p s)) call
      { s with stage := 2, received := 0, total := 0 } =
      { s with
        stage := 3, received := batchSize p s.iteration (stepWeight p s) - 1,
        total := ∑ i ∈ Finset.range (batchSize p s.iteration (stepWeight p s)),
          RobustGradient.centeredClip (clipRadius p s.iteration) s.center
            (g (queryPoint p s) (ξ (call + i))) } := by
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero
    (batchSize_pos p s.iteration (stepWeight p s)).ne'
  rw [hj, Nat.succ_eq_add_one, rawAdvance_add,
    rawAdvance_evaluation_prefix p I g ξ s call j (by omega)]
  simp only [rawAdvance, advance, algorithm, oracleReply, update]
  dsimp only [queryPoint, stepWeight] at *
  simp only [Nat.reduceEqDiff, ite_true, ite_false, false_or,
    show ¬j + 1 < batchSize p s.iteration
      (CompositeGeneralized.weight p.L1 (2 * p.R) s.A s.M) by omega,
    Finset.sum_range_succ, Nat.add_sub_cancel]

lemma update_proximal_phaseEntry (p : Public.{0}) (s : State p.E) (v : p.E)
    (hs : s.stage = 3) : PhaseEntry (update p s v) := by
  simp [update, hs, PhaseEntry]

lemma rawAdvance_frozen (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (s : State p.E) (hs : 4 ≤ s.stage) (n call : ℕ) :
    rawAdvance p I g ξ n call s = s := by
  induction n generalizing call with
  | zero => rfl
  | succ n ih =>
    have h : ∀ v, update p s v = s := by
      intro v
      simp [update, show s.stage ≠ 0 by omega, show s.stage ≠ 1 by omega,
        show s.stage ≠ 2 by omega, show s.stage ≠ 3 by omega]
    simp only [rawAdvance, advance, h]
    exact ih (call + 1)

lemma rawAdvance_shift (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (offset n call : ℕ) (s : State p.E) :
    rawAdvance p I g (fun k => ξ (offset + k)) n call s =
      rawAdvance p I g ξ n (offset + call) s := by
  induction n generalizing call s with
  | zero => rfl
  | succ n ih =>
    simp only [rawAdvance, advance]
    simpa only [rawAdvance, Nat.add_assoc] using ih (call + 1) _

lemma blockTrace_eq_rawAdvance (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (ξ : ℕ → p.Ω) (s : State p.E) (hs : WellFormed s) (n : ℕ) :
    (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).1 =
      rawAdvance p I g ξ
        (StochasticGeneralized.blockCalls (phaseCost p) (phaseNext p I g) s ξ n) 0 s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [StochasticGeneralized.blockTrace_succ, StochasticGeneralized.blockCalls_succ]
    dsimp only [StochasticGeneralized.blockAdvance]
    have ht : (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).2 =
        fun k => ξ (StochasticGeneralized.blockCalls (phaseCost p) (phaseNext p I g) s ξ n + k) :=
      funext (StochasticGeneralized.blockTrace_tail _ _ _ _ n)
    rw [ht]
    have hw : WellFormed
        (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).1 := by
      rw [ih]
      exact rawAdvance_wellFormed p I g hL0 hL1 hR hσ ξ _ 0 hs
    rw [phaseNext_eq_rawAdvance p I g hL0 hL1 hR hσ
      (fun k => ξ (StochasticGeneralized.blockCalls (phaseCost p) (phaseNext p I g) s ξ n + k))
      (phaseCost p (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).1) hw]
    rw [rawAdvance_shift, ih, rawAdvance_add]
    simp only [Nat.zero_add, Nat.add_zero]

lemma rawAdvance_phaseEntry (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (s : State p.E) (hs : PhaseEntry s) (call : ℕ) :
    PhaseEntry (rawAdvance p I g ξ (phaseCost p s) call s) := by
  by_cases h0 : s.stage = 0
  · have he : { s with stage := 0, received := 0, replies := fun _ => 0 } = s := by
      obtain ⟨hr, hv⟩ := hs.1 (Or.inl h0)
      cases s
      simp_all
    have hh := rawAdvance_first_pilot p I g ξ s call
    rw [he] at hh
    simp only [phaseCost, h0, true_or, ite_true]
    rw [hh]
    simp [PhaseEntry]
  by_cases h1 : s.stage = 1
  · have he : { s with stage := 1, received := 0, replies := fun _ => 0 } = s := by
      obtain ⟨hr, hv⟩ := hs.1 (Or.inr h1)
      cases s
      simp_all
    have hh := rawAdvance_second_pilot p I g ξ s call
    rw [he] at hh
    simp only [phaseCost, h1, or_true, ite_true]
    rw [hh]
    simp [PhaseEntry]
  by_cases h2 : s.stage = 2
  · have he : { s with stage := 2, received := 0, total := 0 } = s := by
      obtain ⟨hr, hv⟩ := hs.2 h2
      cases s
      simp_all
    have hh := rawAdvance_evaluation p I g ξ s call
    rw [he] at hh
    simp only [phaseCost, h2, Nat.reduceEqDiff, false_or, ite_false, ite_true]
    rw [hh]
    simp [PhaseEntry]
  by_cases h3 : s.stage = 3
  · simp only [phaseCost, h0, h1, h2, false_or, ite_false]
    change PhaseEntry (update p s _)
    exact update_proximal_phaseEntry p s _ h3
  · have hstage : 4 ≤ s.stage := by omega
    simp only [phaseCost, h0, h1, h2, false_or, ite_false]
    rw [rawAdvance_frozen p I g ξ s hstage]
    exact hs


lemma blockTrace_wellFormed (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (ξ : ℕ → p.Ω) (s : State p.E) (hs : WellFormed s) (n : ℕ) :
    WellFormed (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).1 := by
  rw [blockTrace_eq_rawAdvance p I g hL0 hL1 hR hσ ξ s hs n]
  exact rawAdvance_wellFormed p I g hL0 hL1 hR hσ ξ _ 0 hs

lemma blockTrace_phaseEntry (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (ξ : ℕ → p.Ω) (s : State p.E) (hs : WellFormed s) (he : PhaseEntry s) (n : ℕ) :
    PhaseEntry (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).1 := by
  induction n with
  | zero => exact he
  | succ n ih =>
    rw [StochasticGeneralized.blockTrace_succ]
    dsimp only [StochasticGeneralized.blockAdvance]
    rw [phaseNext_eq_rawAdvance p I g hL0 hL1 hR hσ
      (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).2
      (phaseCost p (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).1)
      (blockTrace_wellFormed p I g hL0 hL1 hR hσ ξ s hs n)]
    exact rawAdvance_phaseEntry p I g _ _ ih 0

lemma measurable_phaseTrace (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry g))
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0)) (n : ℕ) :
    Measurable (fun w : State p.E × (ℕ → p.Ω) =>
      StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) w.1 w.2 n) :=
  ClippedExtragradient.measurable_blockTrace (measurable_phaseCost p)
    (measurable_phaseNext p I hg hprox) n

lemma phaseNext_evaluation (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (s : State p.E) (hs : WellFormed s) (hstage : s.stage = 2)
    (hreceived : s.received = 0) (htotal : s.total = 0)
    (ξ : Fin (batchSize p s.iteration (stepWeight p s)) → p.Ω) :
    phaseNext p I g (batchSize p s.iteration (stepWeight p s)) s ξ =
      { s with
        stage := 3, received := batchSize p s.iteration (stepWeight p s) - 1,
        total := ∑ i, RobustGradient.centeredClip (clipRadius p s.iteration) s.center
          (g (queryPoint p s) (ξ i)) } := by
  let m := batchSize p s.iteration (stepWeight p s)
  let ξ' : ℕ → p.Ω := fun k => if hk : k < m then ξ ⟨k, hk⟩
    else ξ ⟨0, batchSize_pos p s.iteration (stepWeight p s)⟩
  have hpref : (fun i : Fin m => ξ' i) = ξ := by
    funext i
    simp only [ξ', dite_eq_left i.isLt]
    rfl
  rw [← hpref, phaseNext_eq_rawAdvance p I g hL0 hL1 hR hσ ξ' m hs]
  have he : { s with stage := 2, received := 0, total := 0 } = s := by
    cases s
    simp_all
  have hh := rawAdvance_evaluation p I g ξ' s 0
  rw [he] at hh
  rw [hh]
  congr 1
  simp only [Nat.zero_add]
  exact (Fin.sum_univ_eq_sum_range _ m).symm


end OracleTemplate.StochasticCompositeGeneralized
