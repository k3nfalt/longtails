import LongTails.Proofs.StochasticCompositeGeneralizedBlocks
import LongTails.Proofs.StochasticCompositeGeneralizedStep

open Set MeasureTheory
open scoped RealInnerProductSpace
namespace OracleTemplate.StochasticCompositeGeneralized
open LongTails.Setups.StochasticCompositeGeneralizedSmooth
open CompositeGeneralized

noncomputable def statePotential (p : Public) (I : Instance p) (xs : p.E) (s : State p.E) : ℝ :=
  s.A * (I.f s.x + I.ψ s.x - (I.f xs + I.ψ xs)) + ‖s.z - xs‖ ^ 2 / 2

noncomputable def evaluationError (p : Public) (I : Instance p) (s : State p.E) : p.E :=
  (1 / (batchSize p s.iteration (stepWeight p s) : ℝ)) • s.total - I.grad (queryPoint p s)

lemma initial_potential (p : Public) (I : Instance p) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (xs : p.E) (hd : ‖p.x0 - xs‖ ≤ p.R)
    (hg : I.f p.x0 + I.ψ p.x0 - (I.f xs + I.ψ xs) ≤ p.Δ) :
    statePotential p I xs (initialState p) ≤ 3 * p.R ^ 2 / 4 := by
  have hA : 0 < p.R ^ 2 / (4 * p.Δ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hg hA.le
  have he : p.R ^ 2 / (4 * p.Δ) * p.Δ = p.R ^ 2 / 4 := by field_simp
  rw [he] at hh
  have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  dsimp only [statePotential, initialState]
  linarith

lemma initial_invariant (p : Public) (I : Instance p) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (xs : p.E) (hx : p.x0 ∈ I.Q) (hd : ‖p.x0 - xs‖ ≤ p.R)
    (hg : I.f p.x0 + I.ψ p.x0 - (I.f xs + I.ψ xs) ≤ p.Δ) :
    Inv I.f I.ψ I.Q xs (2 * p.R)
      ((initialState p).A, (initialState p).x, (initialState p).z) := by
  have hp := initial_potential p I hR hΔ xs hd hg
  dsimp only [statePotential, initialState] at hp ⊢
  refine ⟨by positivity, hx, hx, ?_, ?_, ?_⟩ <;> nlinarith

lemma rawAdvance_prox (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (s : State p.E) (hs : s.stage = 3) (call : ℕ) :
    rawAdvance p I g ξ 1 call s = update p s
      (I.prox (stepWeight p s) s.z (I.grad (queryPoint p s) + evaluationError p I s)) := by
  have he : I.grad (queryPoint p s) + evaluationError p I s =
      (1 / (batchSize p s.iteration (stepWeight p s) : ℝ)) • s.total := by
    unfold evaluationError
    abel
  simp [rawAdvance, StochasticGradient.advance, algorithm, oracleReply, hs, he]

lemma proximal_potential_step (p : Public) (I : Instance p)
    (h : Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1) (hR : 0 < p.R)
    (xs : p.E) (hxs : xs ∈ I.Q) (hmin : IsMinOn (fun u => I.f u + I.ψ u) I.Q xs)
    (s : State p.E) (hstage : s.stage = 3)
    (hs : Inv I.f I.ψ I.Q xs (2 * p.R) (s.A, s.x, s.z))
    (hM : p.L0 + p.L1 * ‖I.grad s.x‖ ≤ s.M)
    (herr : stepWeight p s * ‖evaluationError p I s‖ ≤ 2 * p.R) :
    let t := update p s
      (I.prox (stepWeight p s) s.z (I.grad (queryPoint p s) + evaluationError p I s))
    t.x ∈ I.Q ∧ t.z ∈ I.Q ∧
      statePotential p I xs t ≤ statePotential p I xs s +
        stepWeight p s * ⟪evaluationError p I s, xs - s.z⟫ +
          (stepWeight p s) ^ 2 * ‖evaluationError p I s‖ ^ 2 := by
  have hM0 : 0 < s.M := lt_of_lt_of_le (by
    have hh := mul_nonneg h.hL1 (norm_nonneg (I.grad s.x))
    linarith [h.hL0]) hM
  have hw := weight_spec h.hL1 (by positivity : 0 < 2 * p.R) hs.1 hM0
  have hp := inexact_controlled_step h (by positivity : 0 < 2 * p.R) hxs hmin hs
    hw.1 hw.2.1 hw.2.2 hM herr
  dsimp only [queryPoint, stepWeight] at hp ⊢
  simp only [update, hstage, Nat.reduceEqDiff, ite_false, ite_true]
  exact ⟨hp.2.1, hp.1, hp.2.2⟩

lemma stepWeight_le_A (p : Public) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R)
    {s : State p.E} (hA : 0 < s.A) : stepWeight p s ≤ s.A := by
  have hd : 1 ≤ 1 + 32 * p.L1 * (2 * p.R) := by
    have hh : 0 ≤ 32 * p.L1 * (2 * p.R) := by positivity
    linarith
  exact (min_le_right _ _).trans ((div_le_iff₀ (by positivity)).mpr (by nlinarith))

lemma update_weight_bound (p : Public) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R)
    {s : State p.E} (hA : 0 < s.A)
    (hbound : s.A ≤ 8 * p.R ^ 2 / p.ε)
    (hactive : s.stage ≤ 3 → s.A < 4 * p.R ^ 2 / p.ε) (v : p.E) :
    (update p s v).A ≤ 8 * p.R ^ 2 / p.ε ∧
      ((update p s v).stage ≤ 3 → (update p s v).A < 4 * p.R ^ 2 / p.ε) := by
  have ha := stepWeight_le_A p hL1 hR hA
  by_cases h3 : s.stage = 3
  · have hh := hactive (by omega)
    simp only [update, h3, Nat.reduceEqDiff, ite_false, ite_true]
    constructor
    · rw [show 8 * p.R ^ 2 / p.ε = 2 * (4 * p.R ^ 2 / p.ε) by ring]
      linarith
    · split_ifs with ht
      · omega
      · intro _
        exact lt_of_not_ge ht
  · have he : (update p s v).A = s.A := by
      unfold update
      split_ifs <;> simp_all
    refine ⟨by rw [he]; exact hbound, ?_⟩
    intro ht
    rw [he]
    by_cases hs : s.stage ≤ 3
    · exact hactive hs
    · have hu : update p s v = s := by
        simp [update, show s.stage ≠ 0 by omega, show s.stage ≠ 1 by omega,
          show s.stage ≠ 2 by omega, h3]
      rw [hu] at ht
      omega

lemma measurable_statePotential (p : Public) (I : Instance p)
    (hf : Measurable I.f) (hψ : Measurable I.ψ) (xs : p.E) :
    Measurable (statePotential p I xs) := by
  unfold statePotential
  fun_prop

lemma measurable_evaluationError (p : Public) (I : Instance p)
    (hg : Measurable I.grad) : Measurable (evaluationError p I) := by
  have hm := (measurable_batchSize p).comp
    ((measurable_state_iteration (E := p.E)).prodMk (measurable_stepWeight p))
  simp only [Function.comp_def] at hm
  unfold evaluationError
  exact ((measurable_const.div ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hm)).smul measurable_state_total).sub
    (hg.comp (measurable_queryPoint p))

noncomputable def chargedWeight (p : Public) (s : State p.E) : ℝ :=
  if s.stage = 2 ∧ batchSize p s.iteration (stepWeight p s) ≤ s.received + 1
  then stepWeight p s else 0

noncomputable def weightLedger (p : Public) (s : State p.E) : ℝ :=
  s.A + if s.stage = 3 then stepWeight p s else 0

lemma update_weightLedger (p : Public) (s : State p.E) (v : p.E) :
    weightLedger p (update p s v) = weightLedger p s + chargedWeight p s := by
  unfold update weightLedger chargedWeight
  split_ifs <;> simp_all [stepWeight]
  all_goals first | omega | (split_ifs at * <;> simp_all)

lemma rawAdvance_one (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (call : ℕ) (s : State p.E) :
    rawAdvance p I g ξ 1 call s =
      update p s (oracleReply p I g ((algorithm p).query s).2 (ξ call)) := rfl

lemma rawAdvance_weightLedger (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (n call : ℕ) (s : State p.E) :
    weightLedger p (rawAdvance p I g ξ n call s) = weightLedger p s +
      ∑ j ∈ Finset.range n, chargedWeight p (rawAdvance p I g ξ j call s) := by
  induction n with
  | zero => simp [rawAdvance, StochasticGradient.advance]
  | succ n ih =>
    rw [rawAdvance_add, rawAdvance_one, update_weightLedger, ih, Finset.sum_range_succ]
    ring

lemma rawAdvance_weight_bound (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (ξ : ℕ → p.Ω) (n call : ℕ) {s : State p.E} (hs : WellFormed s)
    (hb : s.A ≤ 8 * p.R ^ 2 / p.ε)
    (ha : s.stage ≤ 3 → s.A < 4 * p.R ^ 2 / p.ε) :
    (rawAdvance p I g ξ n call s).A ≤ 8 * p.R ^ 2 / p.ε ∧
      ((rawAdvance p I g ξ n call s).stage ≤ 3 →
        (rawAdvance p I g ξ n call s).A < 4 * p.R ^ 2 / p.ε) := by
  induction n generalizing call s with
  | zero => exact ⟨hb, ha⟩
  | succ n ih =>
    have h := update_weight_bound p hL1 hR hs.1 hb ha
      (oracleReply p I g ((algorithm p).query s).2 (ξ call))
    exact ih (call + 1) (update_wellFormed p hL0 hL1 hR hσ hs _) h.1 h.2

lemma weightLedger_bound (p : Public) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R)
    {s : State p.E} (hA : 0 < s.A) (hb : s.A ≤ 8 * p.R ^ 2 / p.ε)
    (ha : s.stage ≤ 3 → s.A < 4 * p.R ^ 2 / p.ε) :
    weightLedger p s ≤ 8 * p.R ^ 2 / p.ε := by
  unfold weightLedger
  split_ifs with h3
  · have hh := ha (by omega)
    have hw := stepWeight_le_A p hL1 hR hA
    rw [show 8 * p.R ^ 2 / p.ε = 2 * (4 * p.R ^ 2 / p.ε) by ring]
    linarith
  · simpa using hb

lemma initial_active_weight_bound (p : Public) (hR : 0 < p.R) (hε : 0 < p.ε)
    (hεΔ : p.ε < p.Δ) :
    (initialState p).A < 4 * p.R ^ 2 / p.ε := by
  have hΔ : 0 < p.Δ := hε.trans hεΔ
  dsimp only [initialState]
  apply (div_lt_div_iff₀ (by positivity : 0 < 4 * p.Δ) hε).mpr
  have hh := mul_lt_mul_of_pos_left hεΔ (sq_pos_of_pos hR)
  have hp : 0 < p.R ^ 2 * p.Δ := by positivity
  nlinarith

lemma chargedWeight_nonneg (p : Public) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R)
    {s : State p.E} (hs : WellFormed s) : 0 ≤ chargedWeight p s := by
  unfold chargedWeight
  split_ifs with ht
  · exact (CompositeGeneralized.weight_spec hL1 (by positivity : 0 < 2 * p.R)
      hs.1 (hs.2 (Or.inr (Or.inl ht.1)))).1.le
  · exact le_rfl

lemma rawAdvance_chargedWeight_sum_bound (p : Public.{0}) (I : Instance p)
    (g : p.E → p.Ω → p.E) (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1)
    (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε) (hεΔ : p.ε < p.Δ)
    (ξ : ℕ → p.Ω) (n : ℕ) :
    (∑ j ∈ Finset.range n, chargedWeight p
      (rawAdvance p I g ξ j 0 (initialState p))) ≤ 8 * p.R ^ 2 / p.ε := by
  have hw := initialState_wellFormed p hR (hε.trans hεΔ)
  have ha := initial_active_weight_bound p hR hε hεΔ
  have hb : (initialState p).A ≤ 8 * p.R ^ 2 / p.ε := by
    rw [show 8 * p.R ^ 2 / p.ε = 2 * (4 * p.R ^ 2 / p.ε) by ring]
    have ht : 0 < 4 * p.R ^ 2 / p.ε := by positivity
    linarith
  have hrun := rawAdvance_weight_bound p I g hL0 hL1 hR hσ ξ n 0 hw hb (fun _ => ha)
  have hledger := weightLedger_bound p hL1 hR
    (rawAdvance_wellFormed p I g hL0 hL1 hR hσ ξ n 0 hw).1 hrun.1 hrun.2
  rw [rawAdvance_weightLedger] at hledger
  have hstart : 0 ≤ weightLedger p (initialState p) := by
    have he : (initialState p).stage ≠ 3 := by
      dsimp only [initialState]
      split_ifs <;> norm_num
    rw [weightLedger, ite_eq_right he, add_zero]
    exact hw.1.le
  linarith

lemma rawAdvance_chargedWeight_sum_bound_all (p : Public.{0}) (I : Instance p)
    (g : p.E → p.Ω → p.E) (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1)
    (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (hε : 0 < p.ε)
    (ξ : ℕ → p.Ω) (n : ℕ) :
    (∑ j ∈ Finset.range n, chargedWeight p
      (rawAdvance p I g ξ j 0 (initialState p))) ≤ 8 * p.R ^ 2 / p.ε := by
  by_cases hΔ : p.Δ ≤ p.ε
  · have hf (j : ℕ) := rawAdvance_frozen p I g ξ (initialState p)
      (by simp [initialState, hΔ]) j 0
    simp_rw [hf]
    simp only [chargedWeight, initialState, hΔ, ite_true, Nat.reduceEqDiff,
      false_and, ite_false, Finset.sum_const_zero]
    positivity
  · exact rawAdvance_chargedWeight_sum_bound p I g hL0 hL1 hR hσ hε
      (lt_of_not_ge hΔ) ξ n

lemma rawAdvance_selected_weight_bound (p : Public.{0}) (I : Instance p)
    (g : p.E → p.Ω → p.E) (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1)
    (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (ξ : ℕ → p.Ω) (n : ℕ) (active : ℕ → Prop) [DecidablePred active] :
    (∑ j ∈ Finset.range n, if active j then chargedWeight p
      (rawAdvance p I g ξ j 0 (initialState p)) else 0) ≤ 8 * p.R ^ 2 / p.ε := by
  apply le_trans (Finset.sum_le_sum ?_)
    (rawAdvance_chargedWeight_sum_bound_all p I g hL0 hL1 hR hσ hε ξ n)
  intro j _
  split_ifs
  · exact le_rfl
  · exact chargedWeight_nonneg p hL1 hR
      (rawAdvance_wellFormed p I g hL0 hL1 hR hσ ξ j 0 (initialState_wellFormed p hR hΔ))


noncomputable def phaseWeight (p : Public) (s : State p.E) : ℝ :=
  if s.stage = 2 then stepWeight p s else 0

lemma rawAdvance_phase_weightLedger (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (s : State p.E) (hs : PhaseEntry s) (call : ℕ) :
    weightLedger p (rawAdvance p I g ξ (phaseCost p s) call s) =
      weightLedger p s + phaseWeight p s := by
  by_cases h0 : s.stage = 0
  · have he : { s with stage := 0, received := 0, replies := fun _ => 0 } = s := by
      obtain ⟨hr, hv⟩ := hs.1 (Or.inl h0)
      cases s
      simp_all
    have hh := rawAdvance_first_pilot p I g ξ s call
    rw [he] at hh
    simp only [phaseCost, h0, true_or, ite_true]
    rw [hh]
    simp [weightLedger, phaseWeight, h0]
  by_cases h1 : s.stage = 1
  · have he : { s with stage := 1, received := 0, replies := fun _ => 0 } = s := by
      obtain ⟨hr, hv⟩ := hs.1 (Or.inr h1)
      cases s
      simp_all
    have hh := rawAdvance_second_pilot p I g ξ s call
    rw [he] at hh
    simp only [phaseCost, h1, or_true, ite_true]
    rw [hh]
    simp [weightLedger, phaseWeight, h1]
  by_cases h2 : s.stage = 2
  · have he : { s with stage := 2, received := 0, total := 0 } = s := by
      obtain ⟨hr, hv⟩ := hs.2 h2
      cases s
      simp_all
    have hh := rawAdvance_evaluation p I g ξ s call
    rw [he] at hh
    simp only [phaseCost, h2, Nat.reduceEqDiff, false_or, ite_false, ite_true]
    rw [hh]
    simp [weightLedger, phaseWeight, h2, stepWeight]
  by_cases h3 : s.stage = 3
  · simp only [phaseCost, h0, h1, h2, false_or, ite_false]
    rw [rawAdvance_one, update_weightLedger]
    simp [chargedWeight, phaseWeight, h3]
  · have hstage : 4 ≤ s.stage := by omega
    simp only [phaseCost, h0, h1, h2, false_or, ite_false]
    rw [rawAdvance_frozen p I g ξ s hstage]
    simp [phaseWeight, h2]


lemma blockTrace_weightLedger (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (ξ : ℕ → p.Ω) (s : State p.E) (hs : WellFormed s) (he : PhaseEntry s) (n : ℕ) :
    weightLedger p (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).1 =
      weightLedger p s + ∑ j ∈ Finset.range n, phaseWeight p
        (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ j).1 := by
  induction n with
  | zero => simp [StochasticGeneralized.blockTrace_zero]
  | succ n ih =>
    rw [StochasticGeneralized.blockTrace_succ]
    dsimp only [StochasticGeneralized.blockAdvance]
    rw [phaseNext_eq_rawAdvance p I g hL0 hL1 hR hσ
      (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).2
      (phaseCost p (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n).1)
      (blockTrace_wellFormed p I g hL0 hL1 hR hσ ξ s hs n)]
    rw [rawAdvance_phase_weightLedger p I g _ _
      (blockTrace_phaseEntry p I g hL0 hL1 hR hσ ξ s hs he n) 0]
    rw [ih, Finset.sum_range_succ]
    ring


lemma accumulated_phaseWeight_bound (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (ξ : ℕ → p.Ω) (n : ℕ) :
    StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
      (fun _ s _ => phaseWeight p s) n (initialState p) ξ ≤ 8 * p.R ^ 2 / p.ε := by
  have hw := initialState_wellFormed p hR hΔ
  have he := blockTrace_weightLedger p I g hL0 hL1 hR hσ ξ (initialState p)
    hw (initialState_phaseEntry p) n
  have hr := blockTrace_eq_rawAdvance p I g hL0 hL1 hR hσ ξ (initialState p) hw n
  rw [StochasticGeneralized.accumulated_eq_sum]
  by_cases hf : p.Δ ≤ p.ε
  · have hstate : (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g)
        (initialState p) ξ n).1 = initialState p := by
      rw [hr]
      exact rawAdvance_frozen p I g ξ (initialState p) (by simp [initialState, hf]) _ 0
    rw [hstate] at he
    have hz : (∑ j ∈ Finset.range n, phaseWeight p
        (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ j).1) = 0 := by
      linarith
    rw [hz]
    positivity
  · have ha := initial_active_weight_bound p hR hε (lt_of_not_ge hf)
    have hb : (initialState p).A ≤ 8 * p.R ^ 2 / p.ε := by
      rw [show 8 * p.R ^ 2 / p.ε = 2 * (4 * p.R ^ 2 / p.ε) by ring]
      have ht : 0 < 4 * p.R ^ 2 / p.ε := by positivity
      linarith
    have hrun := rawAdvance_weight_bound p I g hL0 hL1 hR hσ ξ
      (StochasticGeneralized.blockCalls (phaseCost p) (phaseNext p I g) (initialState p) ξ n)
      0 hw hb (fun _ => ha)
    have hwb := weightLedger_bound p hL1 hR
      (rawAdvance_wellFormed p I g hL0 hL1 hR hσ ξ
        (StochasticGeneralized.blockCalls (phaseCost p) (phaseNext p I g) (initialState p) ξ n) 0 hw).1
      hrun.1 hrun.2
    rw [← hr, he] at hwb
    have hstart : 0 ≤ weightLedger p (initialState p) := by
      have hne : (initialState p).stage ≠ 3 := by
        simp [initialState, hf]
      rw [weightLedger, ite_eq_right hne, add_zero]
      exact hw.1.le
    linarith

lemma phaseWeight_nonneg (p : Public) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R)
    {s : State p.E} (hs : WellFormed s) : 0 ≤ phaseWeight p s := by
  unfold phaseWeight
  split_ifs with ht
  · exact (CompositeGeneralized.weight_spec hL1 (by positivity : 0 < 2 * p.R)
      hs.1 (hs.2 (Or.inr (Or.inl ht)))).1.le
  · exact le_rfl


end OracleTemplate.StochasticCompositeGeneralized
