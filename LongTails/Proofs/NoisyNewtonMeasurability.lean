import LongTails.Proofs.NoisyNewtonModel
import LongTails.Proofs.RobustGeneralizedMeasurability
import LongTails.Proofs.AdaptiveRobustGeneralizedOutput

namespace LongTails.Proofs.NoisyNewtonMeasurability

open MeasureTheory
open LongTails.Algorithms.NoisyDampedNewton
open LongTails.Setups.StochasticLocalHessianConvex
open OracleTemplate.GeneralizedAccelerated (Iterate tentativeWeight coupling)
open OracleTemplate.StochasticGeneralized (measurable_iterate_guess measurable_iterate_mk)
open LongTails.Proofs.NoisyNewtonModel

variable {E : Type*} [MeasurableSpace E]

instance measurableSpaceTrial : MeasurableSpace (Trial E) :=
  MeasurableSpace.comap (fun t => (t.previous, t.curvature, t.displacement)) inferInstance

@[fun_prop] lemma measurable_trial_previous : Measurable (fun t : Trial E => t.previous) :=
  measurable_fst.comp (comap_measurable _)

@[fun_prop] lemma measurable_trial_curvature : Measurable (fun t : Trial E => t.curvature) :=
  measurable_fst.comp (measurable_snd.comp (comap_measurable _))

@[fun_prop] lemma measurable_trial_displacement : Measurable (fun t : Trial E => t.displacement) :=
  measurable_snd.comp (measurable_snd.comp (comap_measurable _))

@[fun_prop] lemma measurable_trial_mk {X : Type*} [MeasurableSpace X]
    {s : X → Iterate E} {τ : X → ℝ} {d : X → E}
    (hs : Measurable s) (ht : Measurable τ) (hd : Measurable d) :
    Measurable (fun x => Trial.mk (s x) (τ x) (d x)) := by
  apply measurable_comap_iff.mpr
  exact hs.prodMk (ht.prodMk hd)

@[fun_prop] lemma measurable_actualWeight : Measurable (actualWeight : Trial E → ℝ) := by
  unfold actualWeight
  fun_prop


abbrev StateCode (E : Type*) :=
  (Iterate E × ℕ × (ℕ → E)) ⊕ ((Iterate E × E) ⊕ ((Trial E × ℕ × (ℕ → E)) ⊕ Iterate E))

def stateCode {E : Type*} : State E → StateCode E
  | .model s n v => .inl (s, n, v)
  | .hessian s g => .inr (.inl (s, g))
  | .correction t n v => .inr (.inr (.inl (t, n, v)))
  | .done s => .inr (.inr (.inr s))

def codeState {E : Type*} : StateCode E → State E
  | .inl (s, n, v) => .model s n v
  | .inr (.inl (s, g)) => .hessian s g
  | .inr (.inr (.inl (t, n, v))) => .correction t n v
  | .inr (.inr (.inr s)) => .done s

instance measurableSpaceState : MeasurableSpace (State E) :=
  MeasurableSpace.comap stateCode inferInstance

lemma measurable_stateCode : Measurable (@stateCode E) := comap_measurable _

lemma measurable_state_uncurry {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {F : State E → X → Y}
    (hmodel : Measurable (fun w : (Iterate E × ℕ × (ℕ → E)) × X =>
      F (.model w.1.1 w.1.2.1 w.1.2.2) w.2))
    (hhessian : Measurable (fun w : (Iterate E × E) × X => F (.hessian w.1.1 w.1.2) w.2))
    (hcorrection : Measurable (fun w : (Trial E × ℕ × (ℕ → E)) × X =>
      F (.correction w.1.1 w.1.2.1 w.1.2.2) w.2))
    (hdone : Measurable (fun w : Iterate E × X => F (.done w.1) w.2)) :
    Measurable (Function.uncurry F) := by
  have hm : Measurable (fun w : StateCode E × X => F (codeState w.1) w.2) := by
    apply (MeasurableEquiv.sumProdDistrib (Iterate E × ℕ × (ℕ → E))
      ((Iterate E × E) ⊕ ((Trial E × ℕ × (ℕ → E)) ⊕ Iterate E)) X).symm.measurable_comp_iff.mp
    apply measurable_fun_sum hmodel
    apply (MeasurableEquiv.sumProdDistrib (Iterate E × E)
      ((Trial E × ℕ × (ℕ → E)) ⊕ Iterate E) X).symm.measurable_comp_iff.mp
    apply measurable_fun_sum hhessian
    apply (MeasurableEquiv.sumProdDistrib (Trial E × ℕ × (ℕ → E)) (Iterate E) X).symm.measurable_comp_iff.mp
    exact measurable_fun_sum hcorrection hdone
  have hh := hm.comp ((measurable_stateCode.comp measurable_fst).prodMk measurable_snd)
  convert hh using 1
  funext w
  rcases w with ⟨s, x⟩
  cases s <;> rfl

@[fun_prop] lemma measurable_state_model {X : Type*} [MeasurableSpace X]
    {s : X → Iterate E} {n : X → ℕ} {v : X → ℕ → E}
    (hs : Measurable s) (hn : Measurable n) (hv : Measurable v) :
    Measurable (fun x => State.model (s x) (n x) (v x)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inl.comp (hs.prodMk (hn.prodMk hv))

@[fun_prop] lemma measurable_state_hessian {X : Type*} [MeasurableSpace X]
    {s : X → Iterate E} {g : X → E} (hs : Measurable s) (hg : Measurable g) :
    Measurable (fun x => State.hessian (s x) (g x)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inr.comp (measurable_inl.comp (hs.prodMk hg))

@[fun_prop] lemma measurable_state_correction {X : Type*} [MeasurableSpace X]
    {t : X → Trial E} {n : X → ℕ} {v : X → ℕ → E}
    (ht : Measurable t) (hn : Measurable n) (hv : Measurable v) :
    Measurable (fun x => State.correction (t x) (n x) (v x)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inr.comp (measurable_inr.comp (measurable_inl.comp (ht.prodMk (hn.prodMk hv))))

@[fun_prop] lemma measurable_state_done {X : Type*} [MeasurableSpace X]
    {s : X → Iterate E} (hs : Measurable s) : Measurable (fun x => State.done (s x)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inr.comp (measurable_inr.comp (measurable_inr.comp hs))

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]

lemma measurable_prepare {X : Type*} [MeasurableSpace X]
    (s : X → Iterate E) (H : X → E →L[ℝ] E) (g : X → E)
    (hs : Measurable s) (hH : Measurable H) (hg : Measurable g)
    (M₀ M₁ ρ δ α : ℝ) : Measurable (fun x => prepare M₀ M₁ ρ δ α (s x) (H x) (g x)) := by
  have hB : Measurable (fun x => shifted (H x) δ) := hH.add measurable_const
  have hη : Measurable (fun x => (s x).guess) := measurable_iterate_guess.comp hs
  have hi := measurable_backtrackIndex (fun x => shifted (H x) δ) (fun x => (s x).guess) g
    hB hη hg M₀ M₁ ρ (2 * δ) α
  have ht : Measurable (fun x => backtrackCurvature M₀ M₁ ρ (2 * δ) α (s x).guess (shifted (H x) δ) (g x)) :=
    hη.mul ((measurable_of_countable (fun j : ℕ => (2 : ℝ) ^ j)).comp hi)
  exact measurable_trial_mk hs ht (measurable_response _ _ _ hB ht hg)

@[fun_prop] lemma measurable_trialPoint : Measurable (trialPoint : Trial E → E) := by
  unfold trialPoint
  fun_prop


lemma measurable_finish (floor : ℝ) : Measurable (fun w : Trial E × E => finish floor w.1 w.2) := by
  classical
  unfold finish
  apply measurable_iterate_mk
  · fun_prop
  · fun_prop
  · fun_prop
  · apply Measurable.ite (measurableSet_eq_fun (by fun_prop) (by fun_prop))
    · fun_prop
    · fun_prop

@[fun_prop] lemma measurable_modelRadius (p : Params) : Measurable (modelRadius p) := by
  unfold modelRadius
  fun_prop

@[fun_prop] lemma measurable_modelSize (p : Params) : Measurable (modelSize p) := by
  unfold modelSize
  fun_prop

@[fun_prop] lemma measurable_modelCost (p : Params) : Measurable (modelCost p) := by
  unfold modelCost
  fun_prop

@[fun_prop] lemma measurable_updateRadius (p : Params) : Measurable (updateRadius p) := by
  unfold updateRadius
  fun_prop

@[fun_prop] lemma measurable_updateSize (p : Params) : Measurable (updateSize p) := by
  unfold updateSize
  fun_prop

@[fun_prop] lemma measurable_modelEstimate (p : Params) :
    Measurable (fun w : ℝ × (ℕ → Point p.d) => modelEstimate p w.1 w.2) := by
  have hr : Measurable (fun w : ℝ × (ℕ → Point p.d) => modelSize p w.1) :=
    (measurable_modelSize p).comp measurable_fst
  have hv : Measurable (fun w : ℝ × (ℕ → Point p.d) => fun i : Fin (modelGroups p) =>
      OracleTemplate.RobustGeneralized.meanBlock (i * modelSize p w.1) (modelSize p w.1) w.2) := by
    apply Measurable.of_eval
    intro i
    have hmap : Measurable (fun w : ℝ × (ℕ → Point p.d) =>
        (((i : ℕ) * modelSize p w.1, modelSize p w.1), w.2)) :=
      ((hr.const_mul (i : ℕ)).prodMk hr).prodMk measurable_snd
    have hh := (OracleTemplate.RobustGeneralized.measurable_meanBlock_all (E := Point p.d)).comp hmap
    simpa only [Function.comp_def] using hh
  have hh := (OracleTemplate.RobustGradient.measurable_pilotCenter (E := Point p.d) (modelGroups p)).comp
    (((measurable_modelRadius p).comp measurable_fst).prodMk hv)
  simpa only [Function.comp_def, modelEstimate] using hh

@[fun_prop] lemma measurable_updateEstimate (p : Params) :
    Measurable (fun w : Trial (Point p.d) × (ℕ → Point p.d) => updateEstimate p w.1 w.2) := by
  have ha : Measurable (fun w : Trial (Point p.d) × (ℕ → Point p.d) => actualWeight w.1) :=
    measurable_actualWeight.comp measurable_fst
  have hm := (measurable_updateSize p).comp ha
  have hmap : Measurable (fun w : Trial (Point p.d) × (ℕ → Point p.d) =>
      ((0, updateSize p (actualWeight w.1)), w.2)) :=
    (measurable_const.prodMk hm).prodMk measurable_snd
  have hmean : Measurable (fun w : Trial (Point p.d) × (ℕ → Point p.d) =>
      OracleTemplate.RobustGeneralized.meanBlock 0 (updateSize p (actualWeight w.1)) w.2) := by
    have hh := (OracleTemplate.RobustGeneralized.measurable_meanBlock_all (E := Point p.d)).comp hmap
    simpa only [Function.comp_def] using hh
  have hc : Measurable (fun w : Trial (Point p.d) × (ℕ → Point p.d) =>
      -(w.1.curvature • w.1.displacement)) := by fun_prop
  have hh := (OracleTemplate.RobustGradient.measurable_centeredClip_joint (E := Point p.d)).comp
    (((measurable_updateRadius p).comp ha).prodMk (hc.prodMk hmean))
  simpa only [Function.comp_def, updateEstimate] using hh

instance measurableSpaceAlgorithmState (p : Params) : MeasurableSpace (algorithm p).State :=
  inferInstanceAs (MeasurableSpace (State (Point p.d)))

@[fun_prop] lemma measurable_resume (p : Params) : Measurable (resume p) := by
  unfold resume
  apply Measurable.ite (measurableSet_le measurable_const OracleTemplate.StochasticGeneralized.measurable_iterate_A)
  · fun_prop
  · fun_prop

lemma measurable_algorithm_query (p : Params) : Measurable (algorithm p).query := by
  have hh : Measurable (fun w : State (Point p.d) × Unit => (algorithm p).query w.1) := by
    apply measurable_state_uncurry (F := fun s (_ : Unit) => (algorithm p).query s)
    all_goals dsimp [algorithm]; fun_prop
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))

lemma measurable_algorithm_output (p : Params) : Measurable (algorithm p).output := by
  have hh : Measurable (fun w : State (Point p.d) × Unit => (algorithm p).output w.1) := by
    apply measurable_state_uncurry (F := fun s (_ : Unit) => (algorithm p).output s)
    all_goals dsimp [algorithm]; fun_prop
  exact hh.comp (measurable_id.prodMk (measurable_const (a := ())))

lemma measurable_gradientReply (p : Params) :
    Measurable (fun r : Point p.d ⊕ (Point p.d →L[ℝ] Point p.d) => match r with
      | .inl g => g
      | .inr _ => 0) := measurable_fun_sum measurable_id measurable_const

lemma measurable_hessianReply (p : Params) :
    Measurable (fun r : Point p.d ⊕ (Point p.d →L[ℝ] Point p.d) => match r with
      | .inl _ => 0
      | .inr H => H) := measurable_fun_sum measurable_const measurable_id

lemma measurable_algorithm_update (p : Params) : Measurable (Function.uncurry (algorithm p).update) := by
  classical
  change @Measurable (State (Point p.d) × (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)))
    (State (Point p.d)) inferInstance measurableSpaceState (fun w => (algorithm p).update w.1 w.2)
  apply measurable_state_uncurry
  · have hv : Measurable (fun w : (Iterate (Point p.d) × ℕ × (ℕ → Point p.d)) ×
        (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)) =>
        Function.update w.1.2.2 w.1.2.1 (match w.2 with | .inl g => g | .inr _ => 0)) :=
      OracleTemplate.AdaptiveRobustGeneralized.measurable_reply_update (by fun_prop) (by fun_prop)
        ((measurable_gradientReply p).comp measurable_snd)
    dsimp only [algorithm]
    apply Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
    · exact measurable_state_model (by fun_prop) (by fun_prop) hv
    · apply measurable_state_hessian (by fun_prop)
      have hh := (measurable_modelEstimate p).comp
        ((by fun_prop : Measurable (fun w : (Iterate (Point p.d) × ℕ × (ℕ → Point p.d)) ×
          (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)) => tentativeWeight w.1.1)).prodMk hv)
      convert hh using 1
      funext w
      congr 1
  · dsimp only [algorithm]
    apply measurable_state_correction _ measurable_const measurable_const
    exact measurable_prepare _ _ _ (by fun_prop)
      ((measurable_hessianReply p).comp measurable_snd) (by fun_prop) _ _ _ _ _
  · have hv : Measurable (fun w : (Trial (Point p.d) × ℕ × (ℕ → Point p.d)) ×
        (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)) =>
        Function.update w.1.2.2 w.1.2.1 (match w.2 with | .inl g => g | .inr _ => 0)) :=
      OracleTemplate.AdaptiveRobustGeneralized.measurable_reply_update (by fun_prop) (by fun_prop)
        ((measurable_gradientReply p).comp measurable_snd)
    dsimp only [algorithm]
    apply Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
    · exact measurable_state_correction (by fun_prop) (by fun_prop) hv
    · have ht : Measurable (fun w : (Trial (Point p.d) × ℕ × (ℕ → Point p.d)) ×
          (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)) => w.1.1) := by fun_prop
      have hu := (measurable_updateEstimate p).comp (ht.prodMk hv)
      have hh := (measurable_resume p).comp ((measurable_finish (curvatureFloor p)).comp (ht.prodMk hu))
      convert hh using 1
      funext w
      congr 1
  · dsimp only [algorithm]
    fun_prop

noncomputable def budgetRun (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) :
    ℕ → (Fin 2 → ℕ) → ℕ → (algorithm p).State → (ℕ → p.Ω) → Point p.d
  | 0, _, _, s, _ => (algorithm p).output s
  | k + 1, remaining, call, s, ξ =>
    let q := (algorithm p).query s
    if remaining q.1 = 0 then (algorithm p).output s else
      budgetRun p g H k (Function.update remaining q.1 (remaining q.1 - 1)) (call + 1)
        ((algorithm p).update s (if q.1 = 0 then .inl (g q.2 (ξ call)) else .inr (H q.2))) ξ

lemma measurable_budgetRun (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable H)
    (fuel : ℕ) (remaining : Fin 2 → ℕ) (call : ℕ) :
    Measurable (fun w : State (Point p.d) × (ℕ → p.Ω) => budgetRun p g H fuel remaining call w.1 w.2) := by
  induction fuel generalizing remaining call with
  | zero => exact (measurable_algorithm_output p).comp measurable_fst
  | succ fuel ih =>
    have hq : Measurable (fun w : State (Point p.d) × (ℕ → p.Ω) => (algorithm p).query w.1) :=
      (measurable_algorithm_query p).comp measurable_fst
    have hch := measurable_fst.comp hq
    have hx := measurable_snd.comp hq
    have hξ : Measurable (fun w : State (Point p.d) × (ℕ → p.Ω) => w.2 call) :=
      (measurable_pi_apply call).comp measurable_snd
    have hr : Measurable (fun w : State (Point p.d) × (ℕ → p.Ω) =>
        if ((algorithm p).query w.1).1 = 0 then
          (Sum.inl (g ((algorithm p).query w.1).2 (w.2 call)) : Point p.d ⊕ (Point p.d →L[ℝ] Point p.d))
        else Sum.inr (H ((algorithm p).query w.1).2)) :=
      Measurable.ite (measurableSet_eq_fun hch measurable_const)
        (measurable_inl.comp (hg.comp (hx.prodMk hξ))) (measurable_inr.comp (hH.comp hx))
    let next := fun w : State (Point p.d) × (ℕ → p.Ω) =>
      (algorithm p).update w.1 (if ((algorithm p).query w.1).1 = 0 then
        .inl (g ((algorithm p).query w.1).2 (w.2 call)) else .inr (H ((algorithm p).query w.1).2))
    have hn : Measurable next := (measurable_algorithm_update p).comp (measurable_fst.prodMk hr)
    have hrec : Measurable (fun w : (State (Point p.d) × (ℕ → p.Ω)) × Fin 2 =>
        budgetRun p g H fuel (Function.update remaining w.2 (remaining w.2 - 1)) (call + 1) w.1.1 w.1.2) :=
      measurable_from_prod_countable_left (fun ch => ih (Function.update remaining ch (remaining ch - 1)) (call + 1))
    have hc := hrec.comp ((hn.prodMk measurable_snd).prodMk hch)
    have hm : Measurable (fun w : State (Point p.d) × (ℕ → p.Ω) => remaining ((algorithm p).query w.1).1) :=
      (measurable_of_countable remaining).comp hch
    exact Measurable.ite (measurableSet_eq_fun hm measurable_const)
      ((measurable_algorithm_output p).comp measurable_fst) hc

lemma execute_eq_budgetRun (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (P : ProbabilityMeasure (ℕ → p.Ω))
    (budget : Fin 2 → ℕ) (ξ : ℕ → p.Ω) :
    let O : OracleTemplate.Oracle (Point p.d) (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)) 2 :=
      { Seed := fun _ => p.Ω, law := P,
        answer := fun _ q ω => if q.1 = 0 then .inl (g q.2 ω) else .inr (H q.2) }
    OracleTemplate.execute O (algorithm p) budget () ξ =
      budgetRun p g H (∑ ch, budget ch) budget 0 ((algorithm p).initial ()) ξ := by
  intro O
  unfold OracleTemplate.execute OracleTemplate.executeWithTrace
  generalize hf : (∑ ch, budget ch) = fuel
  generalize hs : (algorithm p).initial () = s
  generalize hb : budget = remaining
  generalize hh : ([] : List ((Fin 2 × Point p.d) × (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)))) = history
  have hlen : history.length = 0 := by rw [← hh]; rfl
  conv_rhs => arg 6; rw [← hlen]
  clear hf hs hb hh hlen
  induction fuel generalizing history remaining s with
  | zero => rfl
  | succ fuel ih =>
    change (if remaining ((algorithm p).query s).1 = 0 then ((algorithm p).output s, history) else _).1 = _
    rw [budgetRun.eq_def]
    by_cases hz : remaining ((algorithm p).query s).1 = 0
    · simp only [hz, ite_true]
    · simp only [hz, ite_false]
      have hrec := ih (history := history ++ [((algorithm p).query s,
          if ((algorithm p).query s).1 = 0 then .inl (g ((algorithm p).query s).2 (ξ history.length))
          else .inr (H ((algorithm p).query s).2))])
          (remaining := Function.update remaining ((algorithm p).query s).1
            (remaining ((algorithm p).query s).1 - 1))
          (s := (algorithm p).update s (if ((algorithm p).query s).1 = 0 then
            .inl (g ((algorithm p).query s).2 (ξ history.length)) else .inr (H ((algorithm p).query s).2)))
      convert hrec using 1
      congr 1
      simp only [List.length_append, List.length_singleton]

lemma measurable_execute_output (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (hg : Measurable (Function.uncurry g)) (hH : Measurable H)
    (P : ProbabilityMeasure (ℕ → p.Ω)) (budget : Fin 2 → ℕ) :
    let O : OracleTemplate.Oracle (Point p.d) (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)) 2 :=
      { Seed := fun _ => p.Ω, law := P,
        answer := fun _ q ω => if q.1 = 0 then .inl (g q.2 ω) else .inr (H q.2) }
    Measurable (fun ξ => output p budget O ξ) := by
  intro O
  have hm := (measurable_budgetRun p g H hg hH (∑ ch, budget ch) budget 0).comp
    ((measurable_const (a := (algorithm p).initial ())).prodMk measurable_id)
  convert hm using 1
  funext ξ
  exact execute_eq_budgetRun p g H P budget ξ

end LongTails.Proofs.NoisyNewtonMeasurability
