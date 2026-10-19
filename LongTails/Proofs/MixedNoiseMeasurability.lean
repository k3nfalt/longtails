import LongTails.Proofs.MixedNoiseExecution
import LongTails.Proofs.SgdExecution

open MeasureTheory

namespace OracleTemplate.MixedNoise

abbrev StateCode (cfg : Config) (E : Type) :=
  (RepresentativeSeed cfg × ℕ × ℕ × Bool) × (E × E × E × (ℕ → E) × (ℕ → E))

def stateCode (cfg : Config) {E : Type} (s : RepresentativeState cfg E) : StateCode cfg E :=
  ((s.seed, s.taskIndex, s.sampleIndex, s.second),
    s.firstReply, s.secondPoint, s.accumulator, s.xs, s.estimates)

instance stateMeasurableSpace (cfg : Config) {E : Type} [MeasurableSpace E] :
    MeasurableSpace (RepresentativeState cfg E) := MeasurableSpace.comap (stateCode cfg) inferInstance

@[fun_prop] lemma measurable_stateCode (cfg : Config) {E : Type} [MeasurableSpace E] :
    Measurable (stateCode cfg (E := E)) := comap_measurable _

@[fun_prop] lemma measurable_state_seed (cfg : Config) {E : Type} [MeasurableSpace E] :
    Measurable (fun s : RepresentativeState cfg E => s.seed) :=
  (measurable_stateCode cfg).fst.fst

@[fun_prop] lemma measurable_state_index (cfg : Config) {E : Type} [MeasurableSpace E] :
    Measurable (fun s : RepresentativeState cfg E => s.taskIndex) :=
  (measurable_stateCode cfg).fst.snd.fst

@[fun_prop] lemma measurable_state_sample (cfg : Config) {E : Type} [MeasurableSpace E] :
    Measurable (fun s : RepresentativeState cfg E => s.sampleIndex) :=
  (measurable_stateCode cfg).fst.snd.snd.fst

@[fun_prop] lemma measurable_state_second (cfg : Config) {E : Type} [MeasurableSpace E] :
    Measurable (fun s : RepresentativeState cfg E => s.second) :=
  (measurable_stateCode cfg).fst.snd.snd.snd

@[fun_prop] lemma measurable_state_firstReply (cfg : Config) {E : Type} [MeasurableSpace E] :
    Measurable (fun s : RepresentativeState cfg E => s.firstReply) :=
  (measurable_stateCode cfg).snd.fst

@[fun_prop] lemma measurable_state_secondPoint (cfg : Config) {E : Type} [MeasurableSpace E] :
    Measurable (fun s : RepresentativeState cfg E => s.secondPoint) :=
  (measurable_stateCode cfg).snd.snd.fst

@[fun_prop] lemma measurable_state_accumulator (cfg : Config) {E : Type} [MeasurableSpace E] :
    Measurable (fun s : RepresentativeState cfg E => s.accumulator) :=
  (measurable_stateCode cfg).snd.snd.snd.fst

@[fun_prop] lemma measurable_state_xs (cfg : Config) {E : Type} [MeasurableSpace E] :
    Measurable (fun s : RepresentativeState cfg E => s.xs) :=
  (measurable_stateCode cfg).snd.snd.snd.snd.fst

@[fun_prop] lemma measurable_state_estimates (cfg : Config) {E : Type} [MeasurableSpace E] :
    Measurable (fun s : RepresentativeState cfg E => s.estimates) :=
  (measurable_stateCode cfg).snd.snd.snd.snd.snd

lemma measurable_variable_eval {α E : Type*} [MeasurableSpace α] [MeasurableSpace E]
    {f : α → ℕ → E} {n : α → ℕ} (hf : Measurable f) (hn : Measurable n) :
    Measurable (fun a => f a (n a)) := by
  have hm : Measurable (fun z : (ℕ → E) × ℕ => z.1 z.2) :=
    measurable_from_prod_countable_left (fun k => measurable_pi_apply k)
  exact hm.comp (hf.prodMk hn)

@[fun_prop] lemma measurable_state_mk (cfg : Config) {α : Type*} {E : Type}
    [MeasurableSpace α] [MeasurableSpace E]
    {seed : α → RepresentativeSeed cfg} {task sample : α → ℕ} {second : α → Bool}
    {first point acc : α → E} {xs estimates : α → ℕ → E}
    (hseed : Measurable seed) (htask : Measurable task) (hsample : Measurable sample)
    (hsecond : Measurable second) (hfirst : Measurable first) (hpoint : Measurable point)
    (hacc : Measurable acc) (hxs : Measurable xs) (hestimates : Measurable estimates) :
    Measurable (fun a => (⟨seed a, task a, sample a, second a, first a, point a,
      acc a, xs a, estimates a⟩ : RepresentativeState cfg E)) := by
  apply measurable_comap_iff.mpr
  exact (hseed.prodMk (htask.prodMk (hsample.prodMk hsecond))).prodMk
    (hfirst.prodMk (hpoint.prodMk (hacc.prodMk (hxs.prodMk hestimates))))

@[fun_prop] lemma measurable_variable_update {α E : Type*} [MeasurableSpace α] [MeasurableSpace E]
    {f : α → ℕ → E} {n : α → ℕ} {v : α → E}
    (hf : Measurable f) (hn : Measurable n) (hv : Measurable v) :
    Measurable (fun a => Function.update (f a) (n a) (v a)) := by
  classical
  apply Measurable.of_eval
  intro k
  simp only [Function.update_apply]
  exact Measurable.ite (measurableSet_eq_fun measurable_const hn) hv (hf.eval)

lemma measurable_task_field (cfg : Config) {E α : Type}
    [MeasurableSpace E] [MeasurableSpace α] (f : BatchTask → α) :
    Measurable (fun s : RepresentativeState cfg E => f (cfg.tasks[s.taskIndex]!)) :=
  (measurable_of_countable (f := fun k => f (cfg.tasks[k]!))).comp (measurable_state_index cfg)

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma taskPoints_measurable (cfg : Config) :
    Measurable (taskPoints cfg (E := E)) := by
  have ha (next : Bool) : Measurable (fun s : RepresentativeState cfg E =>
      s.xs (anchorIndex cfg s.seed (cfg.tasks[s.taskIndex]!).t
        (if next then (cfg.tasks[s.taskIndex]!).level + 1 else (cfg.tasks[s.taskIndex]!).level))) := by
    apply measurable_variable_eval (measurable_state_xs cfg)
    exact (measurable_of_countable (f := fun z : RepresentativeSeed cfg × ℕ =>
      anchorIndex cfg z.1 (cfg.tasks[z.2]!).t
        (if next then (cfg.tasks[z.2]!).level + 1 else (cfg.tasks[z.2]!).level))).comp
      ((measurable_state_seed cfg).prodMk (measurable_state_index cfg))
  have hl : Measurable (fun s : RepresentativeState cfg E => (cfg.tasks[s.taskIndex]!).level) :=
    (measurable_of_countable (f := fun k => (cfg.tasks[k]!).level)).comp (measurable_state_index cfg)
  unfold taskPoints
  apply Measurable.ite (measurableSet_eq_fun hl measurable_const)
  · exact (ha false).prodMk (ha false)
  · exact (ha false).prodMk (ha true)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma representativeQuery_measurable (cfg : Config) :
    Measurable (representativeQuery cfg (E := E)) := by
  apply Measurable.ite (measurableSet_eq_fun (measurable_state_second cfg) measurable_const)
  · exact measurable_state_secondPoint cfg
  · exact (taskPoints_measurable cfg).fst

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma representativeOutput_measurable (cfg : Config) :
    Measurable (representativeOutput (cfg := cfg) (E := E)) := by
  apply measurable_variable_eval (measurable_state_xs cfg)
  exact (measurable_of_countable (f := fun s : RepresentativeSeed cfg => s.outputIndex.val)).comp
    (measurable_state_seed cfg)

lemma representativeCommit_measurable (cfg : Config) :
    Measurable (Function.uncurry (representativeCommit cfg (E := E))) := by
  classical
  have ht : Measurable (fun z : RepresentativeState cfg E × E => (cfg.tasks[z.1.taskIndex]!).t) :=
    (measurable_task_field cfg BatchTask.t).comp measurable_fst
  have hs : Measurable (fun z : RepresentativeState cfg E × E => (cfg.tasks[z.1.taskIndex]!).size) :=
    (measurable_task_field cfg BatchTask.size).comp measurable_fst
  have hl : Measurable (fun z : RepresentativeState cfg E × E => (cfg.tasks[z.1.taskIndex]!).level) :=
    (measurable_task_field cfg BatchTask.level).comp measurable_fst
  have hf : Measurable (fun z : RepresentativeState cfg E × E => (cfg.tasks[z.1.taskIndex]!).finish) :=
    (measurable_task_field cfg BatchTask.finish).comp measurable_fst
  have he : Measurable (fun z : RepresentativeState cfg E × E =>
      Function.update z.1.estimates (cfg.tasks[z.1.taskIndex]!).level
        (((cfg.tasks[z.1.taskIndex]!).size : ℝ)⁻¹ • z.2)) := by
    apply measurable_variable_update ((measurable_state_estimates cfg).comp measurable_fst) hl
    exact ((measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp hs).inv.smul measurable_snd
  have hv := Finset.measurable_sum (Finset.range (cfg.m + 1)) (fun l _ => he.eval (a := l))
  have hx : Measurable (fun z : RepresentativeState cfg E × E => z.1.xs (cfg.tasks[z.1.taskIndex]!).t) :=
    measurable_variable_eval ((measurable_state_xs cfg).comp measurable_fst) ht
  unfold Function.uncurry representativeCommit
  apply measurable_state_mk
  · fun_prop
  · fun_prop
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · exact measurable_const
  · apply Measurable.ite (measurableSet_eq_fun hf measurable_const)
    · exact measurable_variable_update ((measurable_state_xs cfg).comp measurable_fst)
        (ht.add_const 1) (hx.sub (hv.const_smul cfg.η))
    · exact (measurable_state_xs cfg).comp measurable_fst
  · exact he

lemma representativeUpdate_measurable (cfg : Config) :
    Measurable (Function.uncurry (representativeUpdate cfg (E := E))) := by
  classical
  have hi : Measurable (fun z : RepresentativeState cfg E × E => z.1.taskIndex) := by fun_prop
  have hn : Measurable (fun z : RepresentativeState cfg E × E => z.1.sampleIndex + 1) := by fun_prop
  have hb : Measurable (fun z : RepresentativeState cfg E × E => z.1.second) := by fun_prop
  have hs : Measurable (fun z : RepresentativeState cfg E × E => (cfg.tasks[z.1.taskIndex]!).size) :=
    (measurable_task_field cfg BatchTask.size).comp measurable_fst
  have hl : Measurable (fun z : RepresentativeState cfg E × E => (cfg.tasks[z.1.taskIndex]!).level) :=
    (measurable_task_field cfg BatchTask.level).comp measurable_fst
  have hp : Measurable (fun z : RepresentativeState cfg E × E => (taskPoints cfg z.1).2) :=
    (taskPoints_measurable cfg).snd.comp measurable_fst
  have ha : Measurable (fun z : RepresentativeState cfg E × E => z.1.accumulator +
      (if (cfg.tasks[z.1.taskIndex]!).level = cfg.m then z.1.firstReply else z.1.firstReply - z.2)) := by
    apply Measurable.add
    · fun_prop
    · apply Measurable.ite (measurableSet_eq_fun hl measurable_const) <;> fun_prop
  have hc : Measurable (fun z : RepresentativeState cfg E × E => representativeCommit cfg z.1
      (z.1.accumulator + (if (cfg.tasks[z.1.taskIndex]!).level = cfg.m then
        z.1.firstReply else z.1.firstReply - z.2))) :=
    (representativeCommit_measurable (E := E) cfg).comp
      ((measurable_fst : Measurable (Prod.fst : RepresentativeState cfg E × E → _)).prodMk ha)
  unfold Function.uncurry representativeUpdate
  apply Measurable.ite (measurableSet_le measurable_const hi)
  · exact measurable_fst
  · apply Measurable.ite (measurableSet_eq_fun hb measurable_const)
    · apply Measurable.ite (measurableSet_lt hn hs)
      · apply measurable_state_mk <;> first | exact ha | fun_prop
      · exact hc
    · apply measurable_state_mk <;> first | exact hp | fun_prop

instance algorithmStateMeasurableSpace (cfg : Config) (x0 : E) :
    MeasurableSpace (multiscaleRepresentatives cfg x0).State :=
  inferInstanceAs (MeasurableSpace (RepresentativeState cfg E))

omit [BorelSpace E] [SecondCountableTopology E] in
lemma initial_measurable (cfg : Config) (x0 : E) :
    Measurable (fun seed : RepresentativeSeed cfg =>
      ((multiscaleRepresentatives cfg x0).initial seed : RepresentativeState cfg E)) := by
  apply measurable_state_mk <;> first | exact measurable_id | exact measurable_const

variable {Ω : Type} [MeasurableSpace Ω]

lemma raw_step_measurable (cfg : Config) (g : E → Ω → E)
    (hg : Measurable (Function.uncurry g)) (k : ℕ) :
    Measurable (fun z : RepresentativeState cfg E × (ℕ → Ω) =>
      representativeUpdate cfg z.1 (g (representativeQuery cfg z.1) (z.2 k))) :=
  (representativeUpdate_measurable cfg).comp (measurable_fst.prodMk
    (hg.comp (((representativeQuery_measurable cfg).comp measurable_fst).prodMk
      ((measurable_pi_apply k).comp measurable_snd))))

lemma advance_measurable (cfg : Config) (g : E → Ω → E)
    (hg : Measurable (Function.uncurry g)) (n call : ℕ) :
    Measurable (fun z : RepresentativeState cfg E × (ℕ → Ω) =>
      StochasticGradient.advance (fun k s =>
        representativeUpdate cfg s (g (representativeQuery cfg s) (z.2 k))) n call z.1) := by
  induction n generalizing call with
  | zero => exact measurable_fst
  | succ n ih =>
    exact (ih (call + 1)).comp ((raw_step_measurable cfg g hg call).prodMk measurable_snd)

lemma execute_measurable (cfg : Config) (g : E → Ω → E)
    (hg : Measurable (Function.uncurry g)) (x0 : E) (P : ProbabilityMeasure (ℕ → Ω)) (K : ℕ) :
    Measurable (fun z : RepresentativeSeed cfg × (ℕ → Ω) =>
      execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (multiscaleRepresentatives cfg x0) (fun _ => K) z.1 z.2) := by
  have hstart : Measurable (fun z : RepresentativeSeed cfg × (ℕ → Ω) =>
      (((multiscaleRepresentatives cfg x0).initial z.1 : RepresentativeState cfg E), z.2)) :=
    ((initial_measurable cfg x0).comp measurable_fst).prodMk measurable_snd
  have hrun := (advance_measurable cfg g hg K 0).comp hstart
  have hm := (representativeOutput_measurable (E := E) cfg).comp hrun
  convert hm using 1
  funext z
  erw [StochasticGradient.execute_advance]
  rfl

end OracleTemplate.MixedNoise
