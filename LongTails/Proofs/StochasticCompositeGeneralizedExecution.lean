import Mathlib.MeasureTheory.Function.Floor
import LongTails.Algorithms.StochasticCompositeGeneralizedAccelerated
import LongTails.Proofs.RobustPilot
import LongTails.Proofs.RobustEstimatorMoments
import LongTails.Proofs.CompositeGeneralizedStep
import LongTails.Proofs.SgdExecution

open MeasureTheory
namespace OracleTemplate.StochasticCompositeGeneralized
open LongTails.Setups.StochasticCompositeGeneralizedSmooth

abbrev StateCode (E : Type*) := ℕ × ℕ × ℝ × E × E × ℝ × E × E × ℕ × (ℕ → E)
def stateCode {E : Type*} (s : State E) : StateCode E :=
  (s.stage, s.iteration, s.A, s.x, s.z, s.M, s.center, s.total, s.received, s.replies)
instance measurableSpaceState {E : Type*} [MeasurableSpace E] : MeasurableSpace (State E) :=
  MeasurableSpace.comap stateCode inferInstance
lemma measurable_stateCode {E : Type*} [MeasurableSpace E] : Measurable (@stateCode E) :=
  comap_measurable _

@[fun_prop] lemma measurable_state_stage {E : Type*} [MeasurableSpace E] :
    Measurable (@State.stage E) := measurable_stateCode.fst

@[fun_prop] lemma measurable_state_iteration {E : Type*} [MeasurableSpace E] :
    Measurable (@State.iteration E) := measurable_stateCode.snd.fst

@[fun_prop] lemma measurable_state_A {E : Type*} [MeasurableSpace E] :
    Measurable (@State.A E) := measurable_stateCode.snd.snd.fst

@[fun_prop] lemma measurable_state_x {E : Type*} [MeasurableSpace E] :
    Measurable (@State.x E) := measurable_stateCode.snd.snd.snd.fst

@[fun_prop] lemma measurable_state_z {E : Type*} [MeasurableSpace E] :
    Measurable (@State.z E) := measurable_stateCode.snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_state_M {E : Type*} [MeasurableSpace E] :
    Measurable (@State.M E) := measurable_stateCode.snd.snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_state_center {E : Type*} [MeasurableSpace E] :
    Measurable (@State.center E) := measurable_stateCode.snd.snd.snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_state_total {E : Type*} [MeasurableSpace E] :
    Measurable (@State.total E) := measurable_stateCode.snd.snd.snd.snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_state_received {E : Type*} [MeasurableSpace E] :
    Measurable (@State.received E) := measurable_stateCode.snd.snd.snd.snd.snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_state_replies {E : Type*} [MeasurableSpace E] :
    Measurable (@State.replies E) := measurable_stateCode.snd.snd.snd.snd.snd.snd.snd.snd.snd

@[fun_prop] lemma measurable_stepWeight (p : Public) : Measurable (stepWeight p) := by
  unfold stepWeight CompositeGeneralized.weight
  fun_prop
@[fun_prop] lemma measurable_queryPoint (p : Public) : Measurable (queryPoint p) := by
  unfold queryPoint CompositeGeneralized.mixPoint
  fun_prop
@[fun_prop] lemma measurable_batchSize (p : Public) :
    Measurable (fun w : ℕ × ℝ => batchSize p w.1 w.2) := by
  apply measurable_from_prod_countable_right
  intro k
  unfold batchSize
  fun_prop
@[fun_prop] lemma measurable_samplePilot (p : Public) :
    Measurable (fun w : ℕ × (ℕ → p.E) => samplePilot p w.1 w.2) := by
  apply measurable_from_prod_countable_right
  intro k
  exact (RobustGradient.measurable_pilotCenter (pilotSize p k)).comp
    (measurable_const.prodMk (Measurable.of_eval (fun i => measurable_pi_apply i.val)))

@[fun_prop] lemma measurable_state_mk {E W : Type*} [MeasurableSpace E] [MeasurableSpace W]
    {stage iteration received : W → ℕ} {A M : W → ℝ} {x z center total : W → E}
    {replies : W → ℕ → E} (hs : Measurable stage) (hi : Measurable iteration)
    (hA : Measurable A) (hx : Measurable x) (hz : Measurable z) (hM : Measurable M)
    (hc : Measurable center) (ht : Measurable total) (hr : Measurable received)
    (hv : Measurable replies) :
    Measurable (fun w => State.mk (stage w) (iteration w) (A w) (x w) (z w) (M w)
      (center w) (total w) (received w) (replies w)) := by
  apply measurable_comap_iff.mpr
  exact hs.prodMk (hi.prodMk (hA.prodMk (hx.prodMk (hz.prodMk
    (hM.prodMk (hc.prodMk (ht.prodMk (hr.prodMk hv))))))))

@[fun_prop] lemma measurable_pilotSize (p : Public) : Measurable (pilotSize p) :=
  measurable_of_countable _
@[fun_prop] lemma measurable_clipRadius (p : Public) : Measurable (clipRadius p) :=
  measurable_of_countable _

lemma measurable_reply_update (p : Public) :
    Measurable (fun w : State p.E × p.E => Function.update w.1.replies w.1.received w.2) := by
  classical
  apply Measurable.of_eval
  intro i
  simp only [Function.update_apply]
  exact measurable_snd.ite
    (measurableSet_eq_fun measurable_const (measurable_state_received.comp measurable_fst))
    ((measurable_pi_apply i).comp (measurable_state_replies.comp measurable_fst))


lemma measurable_update (p : Public) :
    Measurable (fun w : State p.E × p.E => update p w.1 w.2) := by
  have hfst : Measurable (Prod.fst : State p.E × p.E → State p.E) := measurable_fst
  have hstage := (measurable_state_stage (E := p.E)).comp hfst
  have hi := (measurable_state_iteration (E := p.E)).comp hfst
  have hA := (measurable_state_A (E := p.E)).comp hfst
  have hx := (measurable_state_x (E := p.E)).comp hfst
  have hz := (measurable_state_z (E := p.E)).comp hfst
  have hM := (measurable_state_M (E := p.E)).comp hfst
  have hcenter := (measurable_state_center (E := p.E)).comp hfst
  have htotal := (measurable_state_total (E := p.E)).comp hfst
  have hr := (measurable_state_received (E := p.E)).comp hfst
  have hv := (measurable_state_replies (E := p.E)).comp hfst
  have ha := (measurable_stepWeight p).comp hfst
  have hu := measurable_reply_update p
  have hp := (measurable_samplePilot p).comp (hi.prodMk hu)
  have hc := RobustGradient.measurable_centeredClip_joint.comp
    (((measurable_clipRadius p).comp hi).prodMk (hcenter.prodMk measurable_snd))
  have hb := (measurable_batchSize p).comp (hi.prodMk ha)
  have hmorepilot := measurableSet_lt (hr.add_const 1) ((measurable_pilotSize p).comp hi)
  have hmorebatch := measurableSet_lt (hr.add_const 1) hb
  have hnewA := hA.add ha
  have hdone : Measurable (fun w : State p.E × p.E =>
      if 4 * p.R ^ 2 / p.ε ≤ w.1.A + stepWeight p w.1 then (4 : ℕ) else 0) :=
    measurable_const.ite (measurableSet_le measurable_const hnewA) measurable_const
  have hnewx : Measurable (fun w : State p.E × p.E =>
      CompositeGeneralized.mixPoint w.1.A (stepWeight p w.1) w.1.x w.2) :=
    ((hA.div hnewA).smul hx).add ((ha.div hnewA).smul measurable_snd)
  unfold update
  dsimp only
  apply Measurable.ite (measurableSet_eq_fun hstage measurable_const)
  · apply Measurable.ite hmorepilot
    · exact measurable_state_mk hstage hi hA hx hz hM hcenter htotal (hr.add_const 1) hu
    · exact measurable_state_mk measurable_const hi hA hx hz
        (measurable_const.add (measurable_const.mul (hp.norm.add_const (96 * p.σ))))
        hcenter htotal measurable_const measurable_const
  · apply Measurable.ite (measurableSet_eq_fun hstage measurable_const)
    · apply Measurable.ite hmorepilot
      · exact measurable_state_mk hstage hi hA hx hz hM hcenter htotal (hr.add_const 1) hu
      · exact measurable_state_mk measurable_const hi hA hx hz hM hp measurable_const
          measurable_const measurable_const
    · apply Measurable.ite (measurableSet_eq_fun hstage measurable_const)
      · apply Measurable.ite hmorebatch
        · exact measurable_state_mk hstage hi hA hx hz hM hcenter (htotal.add hc) (hr.add_const 1) hv
        · exact measurable_state_mk measurable_const hi hA hx hz hM hcenter (htotal.add hc) hr hv
      · apply Measurable.ite (measurableSet_eq_fun hstage measurable_const)
        · exact measurable_state_mk hdone (hi.add_const 1) hnewA hnewx measurable_snd
            measurable_const measurable_const measurable_const measurable_const measurable_const
        · exact measurable_fst


def WellFormed {E : Type*} (s : State E) : Prop :=
  0 < s.A ∧ (s.stage = 1 ∨ s.stage = 2 ∨ s.stage = 3 → 0 < s.M)

lemma initialState_wellFormed (p : Public) (hR : 0 < p.R) (hΔ : 0 < p.Δ) :
    WellFormed (initialState p) := by
  unfold initialState WellFormed
  split <;> norm_num <;> positivity

lemma stepWeight_pos (p : Public) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R)
    {s : State p.E} (hs : WellFormed s) (hst : s.stage = 1 ∨ s.stage = 2 ∨ s.stage = 3) :
    0 < stepWeight p s :=
  (CompositeGeneralized.weight_spec hL1 (by positivity) hs.1 (hs.2 hst)).1

lemma update_wellFormed (p : Public) (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1)
    (hR : 0 < p.R) (hσ : 0 ≤ p.σ) {s : State p.E} (hs : WellFormed s) (reply : p.E) :
    WellFormed (update p s reply) := by
  have hA := hs.1
  by_cases h0 : s.stage = 0
  · unfold update
    rw [ite_eq_left h0]
    split
    · simpa [WellFormed, h0] using hA
    · dsimp [WellFormed]
      refine ⟨hA, ?_⟩
      intro _
      positivity
  · by_cases h1 : s.stage = 1
    · have hM := hs.2 (Or.inl h1)
      unfold update
      rw [ite_eq_right h0, ite_eq_left h1]
      split <;> simp [WellFormed, h1, hA, hM]
    · by_cases h2 : s.stage = 2
      · have hM := hs.2 (Or.inr (Or.inl h2))
        unfold update
        rw [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]
        split <;> simp [WellFormed, h2, hA, hM]
      · by_cases h3 : s.stage = 3
        · have ha := stepWeight_pos p hL1 hR hs (Or.inr (Or.inr h3))
          unfold update
          rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
          dsimp only
          split <;> simp [WellFormed, show 0 < s.A + stepWeight p s by linarith]
        · simpa [update, h0, h1, h2, h3] using hs

noncomputable def oracleReply (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (query : Query p) (ω : p.Ω) : p.E :=
  match query with
  | .gradient x => g x ω
  | .prox a z v => I.prox a z v

noncomputable def canonicalReply (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (s : State p.E) (ω : p.Ω) : p.E :=
  if s.stage = 0 then g s.x ω
  else if s.stage = 1 ∨ s.stage = 2 then g (queryPoint p s) ω
  else if s.stage = 3 then
    if 0 < stepWeight p s then
      I.prox (stepWeight p s) s.z ((1 / (batchSize p s.iteration (stepWeight p s) : ℝ)) • s.total)
    else 0
  else g s.x ω

lemma canonicalReply_eq (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) {s : State p.E} (hs : WellFormed s) (ω : p.Ω) :
    canonicalReply p I g s ω = oracleReply p I g ((algorithm p).query s).2 ω := by
  unfold canonicalReply algorithm
  dsimp only
  by_cases h0 : s.stage = 0
  · simp [h0, oracleReply]
  · by_cases h12 : s.stage = 1 ∨ s.stage = 2
    · simp [h0, h12, oracleReply]
    · by_cases h3 : s.stage = 3
      · have ha := stepWeight_pos p hL1 hR hs (Or.inr (Or.inr h3))
        simp [h3, ha, oracleReply]
      · simp [h0, h12, h3, oracleReply]

noncomputable def rawAdvance (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (n call : ℕ) (s : State p.E) : State p.E :=
  StochasticGradient.advance (fun k s => update p s
    (oracleReply p I g ((algorithm p).query s).2 (ξ k))) n call s

noncomputable def canonicalAdvance (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → p.Ω) (n call : ℕ) (s : State p.E) : State p.E :=
  StochasticGradient.advance (fun k s => update p s (canonicalReply p I g s (ξ k))) n call s

lemma canonicalAdvance_eq (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (ξ : ℕ → p.Ω) (n call : ℕ) {s : State p.E} (hs : WellFormed s) :
    canonicalAdvance p I g ξ n call s = rawAdvance p I g ξ n call s := by
  induction n generalizing s call with
  | zero => rfl
  | succ n ih =>
    simp only [canonicalAdvance, rawAdvance, StochasticGradient.advance]
    rw [canonicalReply_eq p I g hL1 hR hs]
    exact ih (call + 1) (update_wellFormed p hL0 hL1 hR hσ hs _)

lemma rawAdvance_wellFormed (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (ξ : ℕ → p.Ω) (n call : ℕ) {s : State p.E} (hs : WellFormed s) :
    WellFormed (rawAdvance p I g ξ n call s) := by
  induction n generalizing s call with
  | zero => exact hs
  | succ n ih =>
    exact ih (call + 1) (update_wellFormed p hL0 hL1 hR hσ hs _)


lemma execute_eq_rawAdvance (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (P : ProbabilityMeasure (ℕ → p.Ω)) (K : ℕ) (seed : (algorithm p).Seed) (ξ : ℕ → p.Ω) :
    execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, query) ω => oracleReply p I g query ω }
      (algorithm p) (fun _ => K) seed ξ =
      (rawAdvance p I g ξ K 0 (initialState p)).x := by
  erw [StochasticGradient.execute_advance]
  rfl

lemma execute_eq_canonicalAdvance (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (hΔ : 0 < p.Δ)
    (P : ProbabilityMeasure (ℕ → p.Ω)) (K : ℕ) (seed : (algorithm p).Seed) (ξ : ℕ → p.Ω) :
    execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, query) ω => oracleReply p I g query ω }
      (algorithm p) (fun _ => K) seed ξ =
      (canonicalAdvance p I g ξ K 0 (initialState p)).x := by
  rw [execute_eq_rawAdvance,
    canonicalAdvance_eq p I g hL0 hL1 hR hσ ξ K 0 (initialState_wellFormed p hR hΔ)]


lemma measurable_canonicalReply (p : Public) (I : Instance p) {g : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry g))
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0)) :
    Measurable (fun w : State p.E × p.Ω => canonicalReply p I g w.1 w.2) := by
  have hfst : Measurable (Prod.fst : State p.E × p.Ω → State p.E) := measurable_fst
  have hstage := (measurable_state_stage (E := p.E)).comp hfst
  have hx := (measurable_state_x (E := p.E)).comp hfst
  have hz := (measurable_state_z (E := p.E)).comp hfst
  have ht := (measurable_state_total (E := p.E)).comp hfst
  have hi := (measurable_state_iteration (E := p.E)).comp hfst
  have ha := (measurable_stepWeight p).comp hfst
  have hb := (measurable_batchSize p).comp (hi.prodMk ha)
  have hv : Measurable (fun w : State p.E × p.Ω =>
      (1 / (batchSize p w.1.iteration (stepWeight p w.1) : ℝ)) • w.1.total) := by
    exact (measurable_const.div ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hb)).smul ht
  have hprox' := hprox.comp (ha.prodMk (hz.prodMk hv))
  unfold canonicalReply
  apply Measurable.ite (measurableSet_eq_fun hstage measurable_const)
  · exact hg.comp (hx.prodMk measurable_snd)
  · apply Measurable.ite
      ((measurableSet_eq_fun hstage (measurable_const (a := 1))).union
        (measurableSet_eq_fun hstage (measurable_const (a := 2))))
    · exact hg.comp (((measurable_queryPoint p).comp measurable_fst).prodMk measurable_snd)
    · exact Measurable.ite (measurableSet_eq_fun hstage measurable_const) hprox'
        (hg.comp (hx.prodMk measurable_snd))

lemma update_feasible (p : Public) (Q : Set p.E) (hQ : Convex ℝ Q)
    (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) {s : State p.E} (hs : WellFormed s)
    (hx : s.x ∈ Q) (hz : s.z ∈ Q) (reply : p.E) (hp : s.stage = 3 → reply ∈ Q) :
    (update p s reply).x ∈ Q ∧ (update p s reply).z ∈ Q := by
  by_cases h3 : s.stage = 3
  · have h0 : s.stage ≠ 0 := by omega
    have h1 : s.stage ≠ 1 := by omega
    have h2 : s.stage ≠ 2 := by omega
    have ha := stepWeight_pos p hL1 hR hs (Or.inr (Or.inr h3))
    unfold update
    rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
    dsimp only
    exact ⟨CompositeGeneralized.mix_mem hQ hs.1.le ha.le (by linarith [hs.1]) hx (hp h3), hp h3⟩
  · have hpos : (update p s reply).x = s.x ∧ (update p s reply).z = s.z := by
      unfold update
      split_ifs <;> simp_all
    exact ⟨hpos.1 ▸ hx, hpos.2 ▸ hz⟩

lemma rawAdvance_feasible (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ)
    (hQ : Convex ℝ I.Q) (hprox : ∀ a, 0 < a → ∀ z v, I.prox a z v ∈ I.Q)
    (ξ : ℕ → p.Ω) (n call : ℕ) {s : State p.E} (hs : WellFormed s)
    (hx : s.x ∈ I.Q) (hz : s.z ∈ I.Q) :
    (rawAdvance p I g ξ n call s).x ∈ I.Q ∧ (rawAdvance p I g ξ n call s).z ∈ I.Q := by
  induction n generalizing s call with
  | zero => exact ⟨hx, hz⟩
  | succ n ih =>
    have hreply : s.stage = 3 → oracleReply p I g ((algorithm p).query s).2 (ξ call) ∈ I.Q := by
      intro h3
      have ha := stepWeight_pos p hL1 hR hs (Or.inr (Or.inr h3))
      simpa [algorithm, h3, oracleReply] using hprox (stepWeight p s) ha s.z
        ((1 / (batchSize p s.iteration (stepWeight p s) : ℝ)) • s.total)
    have hf := update_feasible p I.Q hQ hL1 hR hs hx hz _ hreply
    exact ih (call + 1) (update_wellFormed p hL0 hL1 hR hσ hs _) hf.1 hf.2

lemma execute_feasible (p : Public) (I : Instance p) (g : p.E → p.Ω → p.E)
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (hΔ : 0 < p.Δ)
    (hQ : Convex ℝ I.Q) (hprox : ∀ a, 0 < a → ∀ z v, I.prox a z v ∈ I.Q)
    (hx0 : p.x0 ∈ I.Q) (P : ProbabilityMeasure (ℕ → p.Ω)) (K : ℕ)
    (seed : (algorithm p).Seed) (ξ : ℕ → p.Ω) :
    execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, query) ω => oracleReply p I g query ω }
      (algorithm p) (fun _ => K) seed ξ ∈ I.Q := by
  rw [execute_eq_rawAdvance]
  exact (rawAdvance_feasible p I g hL0 hL1 hR hσ hQ hprox ξ K 0
    (initialState_wellFormed p hR hΔ) hx0 hx0).1

lemma measurable_canonicalAdvance (p : Public) (I : Instance p) {g : p.E → p.Ω → p.E}
    (hg : Measurable (Function.uncurry g))
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0)) (n call : ℕ) :
    Measurable (fun w : State p.E × (ℕ → p.Ω) => canonicalAdvance p I g w.2 n call w.1) := by
  induction n generalizing call with
  | zero => exact measurable_fst
  | succ n ih =>
    have hreply : Measurable (fun w : State p.E × (ℕ → p.Ω) =>
        canonicalReply p I g w.1 (w.2 call)) := (measurable_canonicalReply p I hg hprox).comp
      (measurable_fst.prodMk ((measurable_pi_apply call).comp measurable_snd))
    have hu : Measurable (fun w : State p.E × (ℕ → p.Ω) =>
        update p w.1 (canonicalReply p I g w.1 (w.2 call))) :=
      (measurable_update p).comp (measurable_fst.prodMk hreply)
    exact (ih (call + 1)).comp (hu.prodMk measurable_snd)

lemma measurable_execute_output (p : Public) (I : Instance p) {g : p.E → p.Ω → p.E}
    (hL0 : 0 < p.L0) (hL1 : 0 ≤ p.L1) (hR : 0 < p.R) (hσ : 0 ≤ p.σ) (hΔ : 0 < p.Δ)
    (hg : Measurable (Function.uncurry g))
    (hprox : Measurable (fun t : ℝ × p.E × p.E =>
      if 0 < t.1 then I.prox t.1 t.2.1 t.2.2 else 0))
    (P : ProbabilityMeasure (ℕ → p.Ω)) (K : ℕ) :
    Measurable (fun w : Unit × (ℕ → p.Ω) =>
      execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, query) ω => oracleReply p I g query ω }
        (algorithm p) (fun _ => K) w.1 w.2) := by
  have hstart : Measurable (fun w : Unit × (ℕ → p.Ω) => (initialState p, w.2)) :=
    measurable_const.prodMk measurable_snd
  have hrun := (measurable_canonicalAdvance p I hg hprox K 0).comp hstart
  have hm := (measurable_state_x (E := p.E)).comp hrun
  simp only [Function.comp_def] at hm
  have he : (fun w : Unit × (ℕ → p.Ω) =>
      execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, query) ω => oracleReply p I g query ω }
        (algorithm p) (fun _ => K) w.1 w.2) =
      (fun w : Unit × (ℕ → p.Ω) => (canonicalAdvance p I g w.2 K 0 (initialState p)).x) :=
    funext (fun w => execute_eq_canonicalAdvance p I g hL0 hL1 hR hσ hΔ P K w.1 w.2)
  rw [he]
  exact hm

end OracleTemplate.StochasticCompositeGeneralized
