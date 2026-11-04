import LongTails.Proofs.HystereticHessianMeasurable

open MeasureTheory
open scoped LongTails.Proofs.HystereticHessianMeasurable

namespace LongTails.Proofs.HystereticHessianExpectation

open LongTails.Setups.GeneralizedAffineHessianVector
open LongTails.Algorithms.HystereticHessianTransport
open HystereticHessianMoments HystereticHessianPhases HystereticHessianBlocks
open HystereticHessianAnchorBlocks HystereticHessianMeasurable HeavyTailedProductProcess
open OracleTemplate.StochasticGeneralized

lemma potential_nonneg (p : Params) (c : Config) (g : Space p → Space p)
    (s : AnchoredState p c) : 0 ≤ potential p c g s := by
  unfold potential
  split_ifs <;> positivity

lemma stream_block_potential (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p)
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    {M : ℝ} (hM : 0 < M) (hthreshold : c.guardThreshold = 3 * M / 2)
    (hi : ∀ x, Integrable (fun z : ℝ × Ω => answer (x, none) z.2) P)
    (hmean : ∀ x, (∫ z, answer (x, none) z.2 ∂P) = g x)
    (hpi : ∀ x, Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) P)
    (hb : ∀ x, (∫ z : ℝ × Ω, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.pilotBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (hgroups : (1 / 2 : ℝ) ^ (c.groups + 1) ≤ 1 / 16)
    (s : AnchoredTimedState p c) (hs : BlockValid p c g M s) :
    let F := fun ξ : ℕ → ℝ × Ω =>
      potential p c g (anchoredPath p c answer s.1 ξ (anchoredTimedCost p c s))
    Integrable F (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, F ξ ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ potential p c g s.1 + 4 * M ^ 2 := by
  let F := fun ξ : ℕ → ℝ × Ω =>
    potential p c g (anchoredPath p c answer s.1 ξ (anchoredTimedCost p c s))
  change Integrable F _ ∧ (∫ ξ, F ξ ∂_) ≤ _
  have hc : CounterValid p c s.1.value := hs.1.1
  have hf : PhaseFits p c s.1.value := hs.1.2.1
  have hfr : Fresh p c s.1.value := hs.1.2.2.1
  have hconst (he : ∀ ξ, F ξ = potential p c g s.1) :
      Integrable F (Measure.infinitePi fun _ : ℕ => P) ∧
        (∫ ξ, F ξ ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ potential p c g s.1 + 4 * M ^ 2 := by
    rw [show F = (fun _ => potential p c g s.1) from funext he]
    refine ⟨integrable_const _, ?_⟩
    simp only [integral_const, probReal_univ, one_smul]
    exact le_add_of_nonneg_right (by positivity)
  by_cases ht : s.2 < trialCalls c
  · have hcost : anchoredTimedCost p c s = phaseCalls p c s.1.value := by
      simp [anchoredTimedCost, timedCost, forgetAnchor, ht]
    by_cases hactive : s.1.value.active = true
    · cases hphase : s.1.value.phase with
      | padding =>
        apply hconst
        intro ξ
        simp only [F, hcost, phaseCalls, hactive, ite_true, hphase]
        exact padding_potential p c g s.1.value s.1.anchor answer ξ (Or.inr hphase) hf.1
      | transport i sum =>
        have hh : i = 0 ∧ sum = 0 := by simpa only [hphase] using hfr hactive
        rcases hh with ⟨rfl, rfl⟩
        have hfit := phaseCalls_strict_fit p c s.1.value hc hf hactive (by simp [hphase])
        simp only [phaseCalls, hactive, ite_true, hphase, Nat.sub_zero] at hfit
        apply hconst
        intro ξ
        simp only [F, hcost, phaseCalls, hactive, ite_true, hphase, Nat.sub_zero]
        have hh := transport_potential p c g s.1.value s.1.anchor answer ξ hactive hfit
        rwa [← hphase] at hh
      | gradient refresh j i sum values =>
        have hh : j.val = 0 ∧ i = 0 ∧ sum = 0 ∧ values = fun _ => 0 := by
          simpa only [hphase] using hfr hactive
        have hj : j = 0 := Fin.ext hh.1
        subst j
        rcases hh with ⟨_, rfl, rfl, rfl⟩
        have hfit := phaseCalls_strict_fit p c s.1.value hc hf hactive (by simp [hphase])
        simp only [phaseCalls, hactive, ite_true, hphase, Fin.val_zero, batchRemaining_initial] at hfit
        cases refresh with
        | true =>
          apply hconst
          intro ξ
          simp only [F, hcost, phaseCalls, hactive, ite_true, hphase, Fin.val_zero, batchRemaining_initial]
          have hh := refresh_potential p c g s.1.value s.1.anchor answer ξ hactive hfit
          rwa [← hphase] at hh
        | false =>
          have hX : Measurable (fun z : ℝ × Ω => answer (s.1.value.point, none) z.2) :=
            ha.comp (measurable_const.prodMk measurable_snd)
          have hh := fresh_pilot_potential p c (Measure.infinitePi fun _ : ℕ => P)
            (infinitePi_iid P) g s.1 (fun z : ℝ × Ω => answer (s.1.value.point, none) z.2)
            hX hactive hp hp2 hσ hα hM hthreshold (hi _) (hmean _) (hpi _) (hb _)
            hsize hgroups (hs.2.2.2 hactive)
          dsimp only at hh
          simp_rw [finishPilot_potential p c g s.1.value s.1.anchor _ hactive] at hh
          have he (ξ : ℕ → ℝ × Ω) : F ξ =
              let v := OracleTemplate.MultiplicativeRobustEstimator.medoid
                (fun j : Fin (c.groups + 1) => ((c.pilotBatch + 1 : ℕ) : ℝ)⁻¹ •
                  ∑ l ∈ Finset.range (c.pilotBatch + 1),
                    answer (s.1.value.point, none) (ξ (j.val * (c.pilotBatch + 1) + l)).2)
              if c.guardThreshold < ‖v‖ then 0 else ‖g s.1.value.point‖ ^ 2 := by
            simp only [F, hcost, phaseCalls, hactive, ite_true, hphase, Bool.false_eq_true,
              ite_false, Fin.val_zero, batchRemaining_initial]
            have he := pilot_potential p c g s.1.value s.1.anchor answer ξ hactive hfit
            rwa [← hphase] at he
          refine ⟨?_, ?_⟩
          · convert hh.1 using 1
            funext ξ
            exact he ξ
          · have hbound : (∫ ξ, F ξ ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
                potential p c g s.1 / 2 + 4 * M ^ 2 := by simpa only [he] using hh.2
            linarith [potential_nonneg p c g s.1]
    · have haf : s.1.value.active = false := Bool.eq_false_iff.mpr hactive
      apply hconst
      intro ξ
      simp only [F, hcost, phaseCalls, haf, Bool.false_eq_true, ite_false]
      exact padding_potential p c g s.1.value s.1.anchor answer ξ (Or.inl haf) hf.1
  · apply hconst
    intro ξ
    simp [F, anchoredTimedCost, timedCost, forgetAnchor, ht, anchoredPath, trajectory]

lemma finite_block_potential (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω]
    (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g)
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    {M : ℝ} (hM : 0 < M) (hthreshold : c.guardThreshold = 3 * M / 2)
    (hi : ∀ x, Integrable (fun z : ℝ × Ω => answer (x, none) z.2) P)
    (hmean : ∀ x, (∫ z, answer (x, none) z.2 ∂P) = g x)
    (hpi : ∀ x, Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) P)
    (hb : ∀ x, (∫ z : ℝ × Ω, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.pilotBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (hgroups : (1 / 2 : ℝ) ^ (c.groups + 1) ≤ 1 / 16)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ s : State p c,
      ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M)
    (s : BlockState p c g M) :
    let n := anchoredTimedCost p c s.val
    let F := fun ξ : Fin n → ℝ × Ω =>
      potential p c g (blockNext p c answer g M hcoarse hfine n s ξ).val.1
    Integrable F (Measure.pi fun _ : Fin n => P) ∧
      (∫ ξ, F ξ ∂Measure.pi (fun _ : Fin n => P)) ≤ potential p c g s.val.1 + 4 * M ^ 2 := by
  let n := anchoredTimedCost p c s.val
  let F := fun ξ : Fin n → ℝ × Ω =>
    potential p c g (blockNext p c answer g M hcoarse hfine n s ξ).val.1
  change Integrable F _ ∧ (∫ ξ, F ξ ∂_) ≤ _
  have hnext := (measurable_blockNext p c answer ha g M hcoarse hfine n).comp
    (measurable_prodMk_left (x := s))
  have hF : Measurable F := (measurable_potential p c g hg).comp
    (measurable_fst.comp (measurable_subtype_coe.comp hnext))
  have hpre := prefix_preserving P n
  have hh := stream_block_potential p c P answer ha g hp hp2 hσ hα hM hthreshold
    hi hmean hpi hb hsize hgroups s.val s.property
  have he (ξ : ℕ → ℝ × Ω) : F (fun i => ξ i) =
      potential p c g (anchoredPath p c answer s.val.1 ξ n) := by
    dsimp only [F, n]
    rw [blockNext_at_cost, finiteRun_eq_trajectory, anchored_timed_trajectory]
  have hfi : Integrable (fun ξ : ℕ → ℝ × Ω => F (fun i => ξ i))
      (Measure.infinitePi fun _ : ℕ => P) := by
    simpa only [he] using hh.1
  refine ⟨(hpre.integrable_comp hF.aestronglyMeasurable).mp hfi, ?_⟩
  rw [← hpre.map_eq, integral_map hpre.measurable.aemeasurable hF.aestronglyMeasurable]
  simpa only [he] using hh.2

lemma trial_anchor_moment (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω]
    (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g)
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    {M : ℝ} (hM : 0 < M) (hthreshold : c.guardThreshold = 3 * M / 2)
    (hi : ∀ x, Integrable (fun z : ℝ × Ω => answer (x, none) z.2) P)
    (hmean : ∀ x, (∫ z, answer (x, none) z.2 ∂P) = g x)
    (hpi : ∀ x, Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) P)
    (hb : ∀ x, (∫ z : ℝ × Ω, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.pilotBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (hgroups : (1 / 2 : ℝ) ^ (c.groups + 1) ≤ 1 / 16)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ s : State p c,
      ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M)
    : Integrable (fun ξ : ℕ → ℝ × Ω =>
        potential p c g (anchoredPath p c answer ⟨initial p c, p.x0⟩ ξ (trialCalls c)))
        (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ : ℕ → ℝ × Ω,
        potential p c g (anchoredPath p c answer ⟨initial p c, p.x0⟩ ξ (trialCalls c))
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ ‖g p.x0‖ ^ 2 + (blockCap c : ℝ) * (4 * M ^ 2) := by
  let cost := fun s : BlockState p c g M => anchoredTimedCost p c s.val
  let next := blockNext p c answer g M hcoarse hfine
  let V := fun s : BlockState p c g M => potential p c g s.val.1
  let initialState : BlockState p c g M :=
    ⟨(⟨initial p c, p.x0⟩, 0), initial_block_valid p c g M⟩
  have hc : Measurable cost := (measurable_anchoredTimedCost p c).comp measurable_subtype_coe
  have hn : ∀ n, Measurable (Function.uncurry (next n)) :=
    measurable_blockNext p c answer ha g M hcoarse hfine
  have hV : Measurable V := (measurable_potential p c g hg).comp
    (measurable_fst.comp measurable_subtype_coe)
  have hm := fun s => finite_block_potential p c P answer ha g hg hp hp2 hσ hα hM hthreshold
    hi hmean hpi hb hsize hgroups hcoarse hfine s
  have hh := adaptive_potential_drift P hc hn hV (fun s => potential_nonneg p c g s.val.1)
    (fun s => (hm s).1) (fun s => (hm s).2) (blockCap c) initialState
  have he (ξ : ℕ → ℝ × Ω) : V (blockTrace cost next initialState ξ (blockCap c)).1 =
      potential p c g (anchoredPath p c answer ⟨initial p c, p.x0⟩ ξ (trialCalls c)) := by
    have he := valid_block_trace_projection p c answer g M hcoarse hfine initialState ξ (blockCap c)
    have hv := congrArg (fun t => potential p c g t.1.1) he
    dsimp only at hv
    rw [anchored_timed_trace_output] at hv
    exact hv
  have hinit : V initialState = ‖g p.x0‖ ^ 2 := rfl
  simpa only [he, hinit] using hh

lemma trial_output_second_moment (p : Params) (c : Config) {Ω : Type} [MeasurableSpace Ω] [Nonempty Ω]
    (P : Measure (ℝ × Ω)) [IsProbabilityMeasure P]
    (answer : (Space p × Option (Space p)) → Ω → Space p)
    (ha : Measurable (Function.uncurry answer)) (g : Space p → Space p) (hg : Measurable g)
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (hσ : 0 ≤ p.σg) (hα : 0 ≤ p.αg)
    {M : ℝ} (hM : 0 < M) (hthreshold : c.guardThreshold = 3 * M / 2)
    (hi : ∀ x, Integrable (fun z : ℝ × Ω => answer (x, none) z.2) P)
    (hmean : ∀ x, (∫ z, answer (x, none) z.2 ∂P) = g x)
    (hpi : ∀ x, Integrable (fun z : ℝ × Ω => ‖answer (x, none) z.2 - g x‖ ^ p.p) P)
    (hb : ∀ x, (∫ z : ℝ × Ω, ‖answer (x, none) z.2 - g x‖ ^ p.p ∂P) ≤
      p.σg ^ p.p + p.αg ^ p.p * ‖g x‖ ^ p.p)
    (hsize : 6 * (p.σg / M + p.αg) ^ p.p /
      ((c.pilotBatch + 1 : ℕ) : ℝ) ^ (p.p - 1) ≤ (1 / 24576 : ℝ) ^ p.p)
    (hgroups : (1 / 2 : ℝ) ^ (c.groups + 1) ≤ 1 / 16)
    (hcoarse : ∀ x v, ‖g (x + coarseDisplacement p c v)‖ ≤ 2 * max ‖g x‖ M)
    (hfine : ∀ s : State p c,
      ‖g (s.point + fineDisplacement p c s)‖ ≤ 2 * max ‖g s.point‖ M)
    : Integrable (fun ξ : ℕ → ℝ × Ω =>
        ‖g (output p c (path p c answer (initial p c) ξ (trialCalls c)))‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ : ℕ → ℝ × Ω, ‖g (output p c (path p c answer (initial p c) ξ (trialCalls c)))‖ ^ 2
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
          2 * ‖g p.x0‖ ^ 2 + (blockCap c : ℝ) * (4 * M ^ 2) := by
  have hh := trial_anchor_moment p c P answer ha g hg hp hp2 hσ hα hM hthreshold
    hi hmean hpi hb hsize hgroups hcoarse hfine
  have hsample : Measurable (fun ξ : ℕ → ℝ × Ω => fun i : Fin (trialCalls c) => ξ i) :=
    Measurable.of_eval (fun i => measurable_pi_apply (i : ℕ))
  have hrun := (finiteRun_measurable (anchoredTimedAdvance p c answer)
    (measurable_anchoredTimedAdvance p c answer ha) (trialCalls c)).comp
    ((measurable_const (a := ((⟨initial p c, p.x0⟩, 0) : AnchoredTimedState p c))).prodMk hsample)
  have hpath : Measurable (fun ξ : ℕ → ℝ × Ω => path p c answer (initial p c) ξ (trialCalls c)) := by
    have hv := (measurable_value p c).comp (measurable_fst.comp hrun)
    convert hv using 1
    funext ξ
    simp only [Function.comp_def, Function.uncurry_def, finiteRun_eq_trajectory, anchored_timed_trajectory, anchoredPath_projection]
  have hout : Measurable (fun ξ : ℕ → ℝ × Ω =>
      output p c (path p c answer (initial p c) ξ (trialCalls c))) := by
    unfold output
    exact Measurable.ite (measurableSet_eq_fun ((measurable_success p c).comp hpath) measurable_const)
      ((measurable_point p c).comp hpath) measurable_const
  have hsq := ((hg.comp hout).norm).pow_const 2
  have hdom := hh.1.add (integrable_const (‖g p.x0‖ ^ 2))
  have hio : Integrable (fun ξ : ℕ → ℝ × Ω =>
      ‖g (output p c (path p c answer (initial p c) ξ (trialCalls c)))‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => P) := by
    apply hdom.mono' hsq.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact path_output_energy_bound p c answer g ξ (trialCalls c))
  refine ⟨hio, ?_⟩
  have hbnd := integral_mono hio hdom (fun ξ => path_output_energy_bound p c answer g ξ (trialCalls c))
  simp only [Pi.add_apply] at hbnd
  rw [integral_add hh.1 (integrable_const _), integral_const] at hbnd
  simp only [probReal_univ, one_smul] at hbnd
  linarith [hh.2]

end LongTails.Proofs.HystereticHessianExpectation
