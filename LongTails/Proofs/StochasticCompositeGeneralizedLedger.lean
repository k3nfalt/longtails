import LongTails.Proofs.StochasticCompositeGeneralizedEvents

open MeasureTheory
open scoped RealInnerProductSpace
namespace OracleTemplate.StochasticCompositeGeneralized
open LongTails.Setups.StochasticCompositeGeneralizedSmooth

noncomputable def predictedPotential (p : Public) (I : Instance p) (xs : p.E) (s : State p.E) : ℝ :=
  statePotential p I xs s + if s.stage = 3 then
    stepWeight p s * ⟪evaluationError p I s, xs - s.z⟫ +
      stepWeight p s ^ 2 * ‖evaluationError p I s‖ ^ 2 else 0

lemma predictedPotential_of_not_pending (p : Public) (I : Instance p) (xs : p.E)
    (s : State p.E) (hs : s.stage ≠ 3) : predictedPotential p I xs s = statePotential p I xs s := by
  simp [predictedPotential, hs]

lemma phaseNext_prox (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (s : State p.E) (hs : WellFormed s)
    (hstage : s.stage = 3) (ξ : Fin 1 → p.Ω) :
    phaseNext p I g 1 s ξ = update p s
      (I.prox (stepWeight p s) s.z (I.grad (queryPoint p s) + evaluationError p I s)) := by
  have he : I.grad (queryPoint p s) + evaluationError p I s =
      (1 / (batchSize p s.iteration (stepWeight p s) : ℝ)) • s.total := by
    unfold evaluationError
    abel
  simp only [phaseNext, finiteAdvance, StochasticGradient.advance, Nat.zero_lt_one,
    dite_true, canonicalReply_eq p I g hL1 hR hs]
  simp [algorithm, oracleReply, hstage, he]

lemma phaseNext_predicted_evaluation (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (xs : p.E) (s : State p.E) (hs : WellFormed s) (he : PhaseEntry s) (hstage : s.stage = 2)
    (ξ : Fin (phaseCost p s) → p.Ω) :
    predictedPotential p I xs (phaseNext p I g (phaseCost p s) s ξ) =
      predictedPotential p I xs s + stepWeight p s * ⟪finiteError p I g (phaseCost p s) s ξ, xs - s.z⟫ +
        stepWeight p s ^ 2 * ‖finiteError p I g (phaseCost p s) s ξ‖ ^ 2 := by
  have hcost : phaseCost p s = batchSize p s.iteration (stepWeight p s) := by simp [phaseCost, hstage]
  have ht := phaseNext_evaluation p I g hL0 hL1 hR hσ s hs hstage (he.2 hstage).1 (he.2 hstage).2
  rw [← hcost] at ht
  have hE := phaseNext_evaluation_error p I g hL0 hL1 hR hσ s hs hstage
    (he.2 hstage).1 (he.2 hstage).2
  rw [← hcost] at hE
  have hE' := hE ξ
  rw [ht ξ] at hE'
  rw [ht ξ, predictedPotential_of_not_pending p I xs s (by omega)]
  simp only [predictedPotential, ite_true]
  rw [hE']
  change statePotential p I xs s +
    (stepWeight p s * ⟪finiteError p I g (phaseCost p s) s ξ, xs - s.z⟫ +
      stepWeight p s ^ 2 * ‖finiteError p I g (phaseCost p s) s ξ‖ ^ 2) = _
  ring

lemma phaseNext_predicted_prox (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (h : CompositeGeneralized.Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1) (hR : 0 < p.R)
    (xs : p.E) (hxs : xs ∈ I.Q) (hmin : IsMinOn (fun u => I.f u + I.ψ u) I.Q xs)
    (s : State p.E) (hw : WellFormed s) (hstage : s.stage = 3)
    (hs : CompositeGeneralized.Inv I.f I.ψ I.Q xs (2 * p.R) (s.A, s.x, s.z))
    (hM : p.L0 + p.L1 * ‖I.grad s.x‖ ≤ s.M)
    (herr : stepWeight p s * ‖evaluationError p I s‖ ≤ 2 * p.R) (ξ : Fin 1 → p.Ω) :
    predictedPotential p I xs (phaseNext p I g 1 s ξ) ≤ predictedPotential p I xs s := by
  rw [phaseNext_prox p I g h.hL1 hR s hw hstage ξ]
  have ht := proximal_potential_step p I h hR xs hxs hmin s hstage hs hM herr
  have hn : (update p s (I.prox (stepWeight p s) s.z
      (I.grad (queryPoint p s) + evaluationError p I s))).stage ≠ 3 := by
    simp only [update, hstage, Nat.reduceEqDiff, ite_false, ite_true]
    split_ifs <;> decide
  rw [predictedPotential_of_not_pending p I xs _ hn]
  simp only [predictedPotential, hstage, ite_true]
  dsimp only at ht
  linarith [ht.2.2]


def PhaseControl (p : Public) (I : Instance p) (xs : p.E) (s : State p.E) : Prop :=
  CompositeGeneralized.Inv I.f I.ψ I.Q xs (2 * p.R) (s.A, s.x, s.z) ∧
  (s.stage = 1 ∨ s.stage = 2 ∨ s.stage = 3 →
    p.L0 + p.L1 * ‖I.grad s.x‖ ≤ s.M ∧
      s.M ≤ p.L0 + p.L1 * ‖I.grad s.x‖ + 192 * p.L1 * p.σ) ∧
  (s.stage = 2 ∨ s.stage = 3 → ‖I.grad (queryPoint p s) - s.center‖ ≤ 96 * p.σ) ∧
  (s.stage = 3 → stepWeight p s * ‖evaluationError p I s‖ ≤ 2 * p.R)

lemma initial_phaseControl (p : Public) (I : Instance p) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (xs : p.E) (hx : p.x0 ∈ I.Q) (hd : ‖p.x0 - xs‖ ≤ p.R)
    (hg : I.f p.x0 + I.ψ p.x0 - (I.f xs + I.ψ xs) ≤ p.Δ) :
    PhaseControl p I xs (initialState p) := by
  refine ⟨initial_invariant p I hR hΔ xs hx hd hg, ?_, ?_, ?_⟩
  all_goals by_cases hf : p.Δ ≤ p.ε <;> simp [initialState, hf]

lemma phaseControl_first_pilot (p : Public) (I : Instance p) (hL1 : 0 ≤ p.L1)
    (xs : p.E) (s : State p.E) (hs : PhaseControl p I xs s)
    (v : p.E) (hv : ‖v - I.grad s.x‖ ≤ 96 * p.σ) :
    PhaseControl p I xs { s with
      stage := 1, M := p.L0 + p.L1 * (‖v‖ + 96 * p.σ), received := 0, replies := fun _ => 0} := by
  refine ⟨hs.1, ?_, ?_, ?_⟩
  · intro hh
    exact first_pilot_curvature_bounds p I s hL1 v hv
  · intro hh
    norm_num at hh
  · intro hh
    norm_num at hh

lemma phaseControl_second_pilot (p : Public) (I : Instance p)
    (xs : p.E) (s : State p.E) (hs : PhaseControl p I xs s) (hstage : s.stage = 1)
    (v : p.E) (hv : ‖v - I.grad (queryPoint p s)‖ ≤ 96 * p.σ) :
    PhaseControl p I xs { s with
      stage := 2, center := v, total := 0, received := 0, replies := fun _ => 0} := by
  refine ⟨hs.1, ?_, ?_, ?_⟩
  · intro hh
    exact hs.2.1 (Or.inl hstage)
  · intro hh
    change ‖I.grad (queryPoint p s) - v‖ ≤ _
    rw [norm_sub_rev]
    exact hv
  · intro hh
    norm_num at hh

lemma phaseControl_evaluation (p : Public) (I : Instance p)
    (xs : p.E) (s : State p.E) (hs : PhaseControl p I xs s) (hstage : s.stage = 2)
    (total : p.E) (received : ℕ)
    (herr : stepWeight p s * ‖evaluationError p I { s with
      stage := 3, total := total, received := received}‖ ≤ 2 * p.R) :
    PhaseControl p I xs {s with stage := 3, total := total, received := received} := by
  refine ⟨hs.1, ?_, ?_, ?_⟩
  · intro hh
    exact hs.2.1 (Or.inr (Or.inl hstage))
  · intro hh
    exact hs.2.2.1 (Or.inl hstage)
  · intro hh
    exact herr

lemma phaseControl_inactive (p : Public) (I : Instance p) (xs : p.E) (s : State p.E)
    (hs : CompositeGeneralized.Inv I.f I.ψ I.Q xs (2 * p.R) (s.A, s.x, s.z))
    (hstage : s.stage = 0 ∨ 4 ≤ s.stage) : PhaseControl p I xs s := by
  refine ⟨hs, ?_, ?_, ?_⟩ <;> intro hh <;> omega

lemma PhaseControl.evaluationReady (p : Public) (I : Instance p) (hL0 : 0 < p.L0)
    (hL1 : 0 ≤ p.L1) (xs : p.E) {s : State p.E} (hs : PhaseControl p I xs s)
    (hstage : s.stage = 2) (hA : s.A < 4 * p.R ^ 2 / p.ε) : EvaluationReady p I s := by
  refine ⟨hs.1.1, ?_, hA, hs.2.2.1 (Or.inl hstage)⟩
  have hM := (hs.2.1 (Or.inr (Or.inl hstage))).1
  have hn := mul_nonneg hL1 (norm_nonneg (I.grad s.x))
  linarith


lemma phaseControl_prox (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (h : CompositeGeneralized.Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1) (hR : 0 < p.R)
    (xs : p.E) (hxs : xs ∈ I.Q) (hmin : IsMinOn (fun u => I.f u + I.ψ u) I.Q xs)
    (s : State p.E) (hw : WellFormed s) (hs : PhaseControl p I xs s) (hstage : s.stage = 3)
    (hpot : predictedPotential p I xs s ≤ p.R ^ 2) (ξ : Fin 1 → p.Ω) :
    PhaseControl p I xs (phaseNext p I g 1 s ξ) := by
  have ha := stepWeight_pos p h.hL1 hR hw (Or.inr (Or.inr hstage))
  let v := I.prox (stepWeight p s) s.z (I.grad (queryPoint p s) + evaluationError p I s)
  have hp : v ∈ I.Q := (h.proxSpec _ ha _ _).1
  have ht := proximal_potential_step p I h hR xs hxs hmin s hstage hs.1
    (hs.2.1 (Or.inr (Or.inr hstage))).1 (hs.2.2.2 hstage)
  have hP : statePotential p I xs (update p s v) ≤ (2 * p.R) ^ 2 := by
    have hh : statePotential p I xs (update p s v) ≤ predictedPotential p I xs s := by
      dsimp only at ht
      simp only [predictedPotential, hstage, ite_true]
      linarith [ht.2.2]
    exact hh.trans (hpot.trans (by nlinarith [sq_nonneg p.R]))
  have henergy : (s.A + stepWeight p s) *
      (I.f (CompositeGeneralized.mixPoint s.A (stepWeight p s) s.x v) +
        I.ψ (CompositeGeneralized.mixPoint s.A (stepWeight p s) s.x v) - (I.f xs + I.ψ xs)) +
      ‖v - xs‖ ^ 2 / 2 ≤ (2 * p.R) ^ 2 := by
    simpa only [statePotential, update, hstage, Nat.reduceEqDiff, ite_false, ite_true] using hP
  have hInv := CompositeGeneralized.inexact_step_invariant h.setConvex
    (by positivity : 0 < 2 * p.R) hmin hs.1 ha hp henergy
  rw [phaseNext_prox p I g h.hL1 hR s hw hstage ξ]
  apply phaseControl_inactive
  · simpa only [update, hstage, Nat.reduceEqDiff, ite_false, ite_true] using hInv
  · simp only [update, hstage, Nat.reduceEqDiff, ite_false, ite_true]
    split_ifs <;> omega


lemma phaseNext_frozen (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (s : State p.E) (hs : 4 ≤ s.stage) (ξ : Fin 1 → p.Ω) : phaseNext p I g 1 s ξ = s := by
  have h0 : s.stage ≠ 0 := by omega
  have h1 : s.stage ≠ 1 := by omega
  have h2 : s.stage ≠ 2 := by omega
  have h3 : s.stage ≠ 3 := by omega
  simp [phaseNext, finiteAdvance, StochasticGradient.advance, update, h0, h1, h2, h3]

lemma phaseNext_predicted_pilot (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (xs : p.E) (s : State p.E) (hs : WellFormed s) (he : PhaseEntry s) (hstage : s.stage ≤ 1)
    (ξ : Fin (phaseCost p s) → p.Ω) :
    predictedPotential p I xs (phaseNext p I g (phaseCost p s) s ξ) = predictedPotential p I xs s := by
  have hcost : phaseCost p s = pilotSize p s.iteration := by
    have hh : s.stage = 0 ∨ s.stage = 1 := by omega
    simp [phaseCost, hh]
  by_cases h0 : s.stage = 0
  · have ht := phaseNext_first_pilot p I g hL0 hL1 hR hσ s hs h0
      (he.1 (Or.inl h0)).1 (he.1 (Or.inl h0)).2
    rw [← hcost] at ht
    rw [ht ξ]
    simp [predictedPotential, statePotential, h0]
  · have h1 : s.stage = 1 := by omega
    have ht := phaseNext_second_pilot p I g hL0 hL1 hR hσ s hs h1
      (he.1 (Or.inr h1)).1 (he.1 (Or.inr h1)).2
    rw [← hcost] at ht
    rw [ht ξ]
    simp [predictedPotential, statePotential, h1]

lemma phaseNext_evaluation_ledger (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (hgrad : ∀ x, HasGradientAt I.f (I.grad x) x)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (xs : p.E) (s : State p.E) (hs : WellFormed s) (he : PhaseEntry s) (hstage : s.stage = 2)
    (hr : EvaluationReady p I s) (hd : ‖xs - s.z‖ ≤ 4 * p.R) (S : ℝ) (hS : S < p.R ^ 2 / 10)
    (ξ : Fin (phaseCost p s) → p.Ω) (hf : phaseFailure p I g (phaseCost p s) s ξ = 0) :
    predictedPotential p I xs (phaseNext p I g (phaseCost p s) s ξ) ≤
      predictedPotential p I xs s + phaseSigned p I μ g xs (phaseCost p s) (s, S) ξ +
        phaseEnergy p I g (phaseCost p s) s ξ +
          (p.ε / (262144 * confidence p 0)) * phaseWeight p s := by
  have ha := stepWeight_pos p hL1 hR hs (Or.inr (Or.inl hstage))
  have hn : 0 < phaseCost p s := by
    simpa only [phaseCost, hstage, Nat.reduceEqDiff, or_self, ite_false, ite_true] using batchSize_pos p s.iteration (stepWeight p s)
  have hsign : phaseSigned p I μ g xs (phaseCost p s) (s, S) ξ =
      finiteSignedError p I μ g xs (phaseCost p s) s ξ := by
    simp [phaseSigned, SignedReady, hstage, hr, hd, hS]
  have hQ := phaseEnergy_eq_square p I g hL1 hR hδ hδ1 s hs hstage hr ξ hf
  have hb := weighted_oracleBias_bound p I μ ho hgrad hR hσ hα hα2 hε hδ hδ1 xs s ha.le hd
  have hb' := (le_abs_self (stepWeight p s * ⟪xs - s.z, oracleBias p I μ g s⟫)).trans hb
  rw [phaseNext_predicted_evaluation p I g hL0 hL1 hR hσ xs s hs he hstage ξ,
    finite_error_signed_split p I μ g hσ xs s hr _ hn ξ, hsign, hQ]
  simp only [phaseWeight, hstage, ite_true]
  calc
    _ ≤ predictedPotential p I xs s + finiteSignedError p I μ g xs (phaseCost p s) s ξ +
        stepWeight p s ^ 2 * ‖finiteError p I g (phaseCost p s) s ξ‖ ^ 2 +
          p.ε * stepWeight p s / (262144 * confidence p 0) := by linarith
    _ = _ := by ring



lemma phaseControl_next (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (h : CompositeGeneralized.Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1) (hR : 0 < p.R)
    (hσ : 0 ≤ p.σ) (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (xs : p.E) (hxs : xs ∈ I.Q) (hmin : IsMinOn (fun u => I.f u + I.ψ u) I.Q xs)
    (s : State p.E) (hw : WellFormed s) (he : PhaseEntry s) (hs : PhaseControl p I xs s)
    (hA : s.stage = 2 → s.A < 4 * p.R ^ 2 / p.ε)
    (hpot : predictedPotential p I xs s ≤ p.R ^ 2)
    (ξ : Fin (phaseCost p s) → p.Ω) (hf : phaseFailure p I g (phaseCost p s) s ξ = 0) :
    PhaseControl p I xs (phaseNext p I g (phaseCost p s) s ξ) := by
  by_cases h0 : s.stage = 0
  · have hcost : phaseCost p s = pilotSize p s.iteration := by simp [phaseCost, h0]
    have ht := phaseNext_first_pilot p I g h.hL0 h.hL1 hR hσ s hw h0
      (he.1 (Or.inl h0)).1 (he.1 (Or.inl h0)).2
    rw [← hcost] at ht
    rw [ht ξ]
    apply phaseControl_first_pilot p I h.hL1 xs s hs
    have hv := phaseFailure_pilot_accuracy p I g s (by omega) ξ hf
    simpa only [pilotPoint, h0, ite_true] using hv
  by_cases h1 : s.stage = 1
  · have hcost : phaseCost p s = pilotSize p s.iteration := by simp [phaseCost, h1]
    have ht := phaseNext_second_pilot p I g h.hL0 h.hL1 hR hσ s hw h1
      (he.1 (Or.inr h1)).1 (he.1 (Or.inr h1)).2
    rw [← hcost] at ht
    rw [ht ξ]
    apply phaseControl_second_pilot p I xs s hs h1
    have hv := phaseFailure_pilot_accuracy p I g s (by omega) ξ hf
    simpa only [pilotPoint, h0, ite_false] using hv
  by_cases h2 : s.stage = 2
  · have hcost : phaseCost p s = batchSize p s.iteration (stepWeight p s) := by simp [phaseCost, h2]
    have hr := hs.evaluationReady p I h.hL0 h.hL1 xs h2 (hA h2)
    have hl := confidence_lower p hδ hδ1 s.iteration
    have hroot : 1 ≤ Real.sqrt (confidence p s.iteration) := Real.one_le_sqrt.mpr hl
    have hbound : p.R / (32 * Real.sqrt (confidence p s.iteration)) ≤ 2 * p.R := by
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    have herr := (evaluation_accuracy_weighted p I g h.hL1 hR hδ hδ1 s hw h2 hr ξ hf).trans hbound
    have ht := phaseNext_evaluation p I g h.hL0 h.hL1 hR hσ s hw h2 (he.2 h2).1 (he.2 h2).2
    have hE := phaseNext_evaluation_error p I g h.hL0 h.hL1 hR hσ s hw h2 (he.2 h2).1 (he.2 h2).2
    rw [← hcost] at ht hE
    have hE' := hE ξ
    rw [ht ξ] at hE'
    rw [ht ξ]
    apply phaseControl_evaluation p I xs s hs h2
    rw [hE']
    exact herr
  by_cases h3 : s.stage = 3
  · have hcost : phaseCost p s = 1 := by simp [phaseCost, h0, h1, h2]
    have ht := phaseControl_prox p I g h hR xs hxs hmin s hw hs h3 hpot
    rw [← hcost] at ht
    exact ht ξ
  · have hcost : phaseCost p s = 1 := by simp [phaseCost, h0, h1, h2]
    have ht := phaseNext_frozen p I g s (by omega)
    rw [← hcost] at ht
    rw [ht ξ]
    exact hs


lemma phaseNext_ledger (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (h : CompositeGeneralized.Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1) (hR : 0 < p.R)
    (hσ : 0 ≤ p.σ) (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (xs : p.E) (hxs : xs ∈ I.Q) (hmin : IsMinOn (fun u => I.f u + I.ψ u) I.Q xs)
    (s : State p.E) (hw : WellFormed s) (he : PhaseEntry s) (hs : PhaseControl p I xs s)
    (hA : s.stage = 2 → s.A < 4 * p.R ^ 2 / p.ε)
    (S : ℝ) (hS : S < p.R ^ 2 / 10)
    (ξ : Fin (phaseCost p s) → p.Ω) (hf : phaseFailure p I g (phaseCost p s) s ξ = 0) :
    predictedPotential p I xs (phaseNext p I g (phaseCost p s) s ξ) ≤
      predictedPotential p I xs s + phaseSigned p I μ g xs (phaseCost p s) (s, S) ξ +
        phaseEnergy p I g (phaseCost p s) s ξ +
          (p.ε / (262144 * confidence p 0)) * phaseWeight p s := by
  by_cases h2 : s.stage = 2
  · have hr := hs.evaluationReady p I h.hL0 h.hL1 xs h2 (hA h2)
    have hd : ‖xs - s.z‖ ≤ 4 * p.R := by
      rw [norm_sub_rev]
      linarith [hs.1.2.2.2.2.2]
    exact phaseNext_evaluation_ledger p I μ ho h.grad h.hL0 h.hL1 hR hσ hα hα2 hε hδ hδ1
      xs s hw he h2 hr hd S hS ξ hf
  · have hv : phaseSigned p I μ g xs (phaseCost p s) (s, S) ξ = 0 ∧
        phaseEnergy p I g (phaseCost p s) s ξ = 0 ∧ phaseWeight p s = 0 := by
      simp [phaseSigned, SignedReady, phaseEnergy, phaseWeight, h2]
    simp only [hv.1, hv.2.1, hv.2.2, mul_zero, add_zero]
    by_cases hp : s.stage ≤ 1
    · exact le_of_eq (phaseNext_predicted_pilot p I g h.hL0 h.hL1 hR hσ xs s hw he hp ξ)
    · have h0 : s.stage ≠ 0 := by omega
      have h1 : s.stage ≠ 1 := by omega
      have hcost : phaseCost p s = 1 := by simp [phaseCost, h0, h1, h2]
      by_cases h3 : s.stage = 3
      · have ht := phaseNext_predicted_prox p I g h hR xs hxs hmin s hw h3 hs.1
          (hs.2.1 (Or.inr (Or.inr h3))).1 (hs.2.2.2 h3)
        rw [← hcost] at ht
        exact ht ξ
      · have ht := phaseNext_frozen p I g s (by omega)
        rw [← hcost] at ht
        rw [ht ξ]


lemma blockTrace_active_weight_bound (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (ξ : ℕ → p.Ω) (n : ℕ) :
    (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ n).1.stage ≤ 3 →
      (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ n).1.A <
        4 * p.R ^ 2 / p.ε := by
  intro ht
  have hw := initialState_wellFormed p hR hΔ
  have hr := blockTrace_eq_rawAdvance p I g hL0 hL1 hR hσ ξ (initialState p) hw n
  by_cases hf : p.Δ ≤ p.ε
  · have hstate : (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g)
        (initialState p) ξ n).1 = initialState p := by
      rw [hr]
      exact rawAdvance_frozen p I g ξ (initialState p) (by simp [initialState, hf]) _ 0
    rw [hstate] at ht
    simp [initialState, hf] at ht
  · have ha := initial_active_weight_bound p hR hε (lt_of_not_ge hf)
    have hb : (initialState p).A ≤ 8 * p.R ^ 2 / p.ε := by
      rw [show 8 * p.R ^ 2 / p.ε = 2 * (4 * p.R ^ 2 / p.ε) by ring]
      have hp : 0 < 4 * p.R ^ 2 / p.ε := by positivity
      linarith
    have hrun := rawAdvance_weight_bound p I g hL0 hL1 hR hσ ξ
      (StochasticGeneralized.blockCalls (phaseCost p) (phaseNext p I g) (initialState p) ξ n)
      0 hw hb (fun _ => ha)
    rw [← hr] at hrun
    exact hrun.2 ht

lemma signedTrace_succ_value (p : Public.{0}) (I : Instance p) (μ : Measure p.Ω)
    (g : p.E → p.Ω → p.E) (xs : p.E) (s : State p.E) (r : ℝ) (ξ : ℕ → p.Ω) (n : ℕ) :
    let w := StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n
    let S := (StochasticGeneralized.blockTrace (fun w : State p.E × ℝ => phaseCost p w.1)
      (phaseSignedNext p I μ g xs) (s, r) ξ n).1.2
    (StochasticGeneralized.blockTrace (fun w : State p.E × ℝ => phaseCost p w.1)
      (phaseSignedNext p I μ g xs) (s, r) ξ (n + 1)).1.2 =
      S + phaseSigned p I μ g xs (phaseCost p w.1) (w.1, S) (fun i => w.2 i) := by
  dsimp only
  rw [← signedTrace_projection p I μ g xs s r ξ n]
  rw [StochasticGeneralized.blockTrace_succ]
  rfl


lemma phase_accumulated_succ (p : Public.{0}) (I : Instance p) (g : p.E → p.Ω → p.E)
    (inc : (n : ℕ) → State p.E → (Fin n → p.Ω) → ℝ)
    (s : State p.E) (ξ : ℕ → p.Ω) (n : ℕ) :
    let w := StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) s ξ n
    StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g) inc (n + 1) s ξ =
      StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g) inc n s ξ +
        inc (phaseCost p w.1) w.1 (fun i => w.2 i) := by
  simp only [StochasticGeneralized.accumulated_eq_sum, Finset.sum_range_succ]

lemma goodEvents_phaseControl_ledger (p : Public.{0}) (I : Instance p) {g : p.E → p.Ω → p.E}
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (ho : IsMomentOracle p I μ g)
    (h : CompositeGeneralized.Hyp I.f I.ψ I.grad I.Q I.prox p.L0 p.L1) (hR : 0 < p.R)
    (hσ : 0 ≤ p.σ) (hα : 1 < p.α) (hα2 : p.α ≤ 2) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    (xs : p.E) (hxs : xs ∈ I.Q) (hmin : IsMinOn (fun u => I.f u + I.ψ u) I.Q xs)
    (hx : p.x0 ∈ I.Q) (hd : ‖p.x0 - xs‖ ≤ p.R)
    (hgap : I.f p.x0 + I.ψ p.x0 - (I.f xs + I.ψ xs) ≤ p.Δ)
    (ξ : ℕ → p.Ω) (n : ℕ) (hg : GoodEvents p I μ g xs n ξ) (j : ℕ) (hj : j ≤ n) :
    let s := (StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ j).1
    let S := (StochasticGeneralized.blockTrace (fun w : State p.E × ℝ => phaseCost p w.1)
      (phaseSignedNext p I μ g xs) (initialState p, 0) ξ j).1.2
    PhaseControl p I xs s ∧ predictedPotential p I xs s ≤ 3 * p.R ^ 2 / 4 + S +
      StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
        (phaseEnergy p I g) j (initialState p) ξ +
      (p.ε / (262144 * confidence p 0)) *
        StochasticGeneralized.accumulated (phaseCost p) (phaseNext p I g)
          (fun _ s _ => phaseWeight p s) j (initialState p) ξ := by
  dsimp only
  revert hj
  induction j with
  | zero =>
    intro hj
    simp only [StochasticGeneralized.blockTrace_zero, StochasticGeneralized.accumulated,
      mul_zero, add_zero]
    refine ⟨initial_phaseControl p I hR hΔ xs hx hd hgap, ?_⟩
    rw [predictedPotential_of_not_pending p I xs _ (by
      by_cases hf : p.Δ ≤ p.ε <;> simp [initialState, hf])]
    exact initial_potential p I hR hΔ xs hd hgap
  | succ j ih =>
    intro hj
    have hi := ih (by omega)
    let w := StochasticGeneralized.blockTrace (phaseCost p) (phaseNext p I g) (initialState p) ξ j
    let S := (StochasticGeneralized.blockTrace (fun w : State p.E × ℝ => phaseCost p w.1)
      (phaseSignedNext p I μ g xs) (initialState p, 0) ξ j).1.2
    have hw : WellFormed w.1 := blockTrace_wellFormed p I g h.hL0 h.hL1 hR hσ ξ
      (initialState p) (initialState_wellFormed p hR hΔ) j
    have he : PhaseEntry w.1 := blockTrace_phaseEntry p I g h.hL0 h.hL1 hR hσ ξ
      (initialState p) (initialState_wellFormed p hR hΔ) (initialState_phaseEntry p) j
    have hf := hg.failure_zero p I μ g xs n ξ (by omega : j < n)
    have hS : S < p.R ^ 2 / 10 := hg.signed_prefix_lt p I μ g xs n ξ (by omega)
    have hQ := hg.energy_prefix_lt p I μ g xs hδ hδ1 n ξ (by omega : j ≤ n)
    have hb := accumulated_biasAllowance_bound p I g h.hL0 h.hL1 hR hσ hΔ hε hδ hδ1 ξ j
    have hpot : predictedPotential p I xs w.1 ≤ p.R ^ 2 := by
      have ht := potential_allowance_bound (R := p.R) (confidence_lower p hδ hδ1 0)
      dsimp only [S] at hS
      exact hi.2.trans (by linarith)
    have hA : w.1.stage = 2 → w.1.A < 4 * p.R ^ 2 / p.ε := by
      intro h2
      exact blockTrace_active_weight_bound p I g h.hL0 h.hL1 hR hσ hΔ hε ξ j (by
        change w.1.stage ≤ 3
        omega)
    have hc := phaseControl_next p I g h hR hσ hδ hδ1 xs hxs hmin w.1 hw he hi.1 hA hpot
      (fun i => w.2 i) hf
    have hl := phaseNext_ledger p I μ ho h hR hσ hα hα2 hε hδ hδ1 xs hxs hmin
      w.1 hw he hi.1 hA S hS (fun i => w.2 i) hf
    constructor
    · simpa only [StochasticGeneralized.blockTrace_succ, StochasticGeneralized.blockAdvance] using hc
    · rw [StochasticGeneralized.blockTrace_succ, signedTrace_succ_value,
        phase_accumulated_succ, phase_accumulated_succ]
      dsimp only [StochasticGeneralized.blockAdvance]
      have hh := hi.2
      change predictedPotential p I xs w.1 ≤ _ at hh
      nlinarith [hl]


end OracleTemplate.StochasticCompositeGeneralized
