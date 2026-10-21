import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Tactic.FunProp

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OnlineTemplate

universe uP uD uI uO uA uF uY uB

abbrev Round (Observation : Type uO) (Action : Type uA) (Feedback : Type uF)
    (Outcome : Type uY) := Observation × Action × Feedback × Outcome

abbrev Trace (Observation : Type uO) (Action : Type uA) (Feedback : Type uF)
    (Outcome : Type uY) (T : ℕ) := Fin T → Round Observation Action Feedback Outcome

namespace Trace

variable {Observation : Type uO} {Action : Type uA} {Feedback : Type uF}
    {Outcome : Type uY} {T : ℕ}

def take {N : ℕ} (h : T ≤ N) (history : Trace Observation Action Feedback Outcome N) :
    Trace Observation Action Feedback Outcome T :=
  fun i => history (i.castLE h)

@[simp]
lemma take_apply {N : ℕ} (h : T ≤ N)
    (history : Trace Observation Action Feedback Outcome N) (i : Fin T) :
    take h history i = history (i.castLE h) := rfl

@[simp]
lemma take_refl (history : Trace Observation Action Feedback Outcome T) :
    take le_rfl history = history := rfl

@[simp]
lemma take_take {N M : ℕ} (h : T ≤ N) (h' : N ≤ M)
    (history : Trace Observation Action Feedback Outcome M) :
    take h (take h' history) = take (h.trans h') history := rfl

@[fun_prop]
lemma measurable_take [MeasurableSpace Observation] [MeasurableSpace Action]
    [MeasurableSpace Feedback] [MeasurableSpace Outcome] {N : ℕ} (h : T ≤ N) :
    Measurable (take (Observation := Observation) (Action := Action)
      (Feedback := Feedback) (Outcome := Outcome) h) := by
  exact Measurable.of_eval (fun i => measurable_pi_apply (i.castLE h))

def append (history : Trace Observation Action Feedback Outcome T)
    (round : Round Observation Action Feedback Outcome) :
    Trace Observation Action Feedback Outcome (T + 1) :=
  fun i => if h : i.val < T then history ⟨i.val, h⟩ else round

@[simp]
lemma append_castSucc (history : Trace Observation Action Feedback Outcome T)
    (round : Round Observation Action Feedback Outcome) (i : Fin T) :
    append history round i.castSucc = history i := by
  simp [append, i.isLt]

@[simp]
lemma append_last (history : Trace Observation Action Feedback Outcome T)
    (round : Round Observation Action Feedback Outcome) :
    append history round (Fin.last T) = round := by
  simp [append]

@[simp]
lemma take_append (history : Trace Observation Action Feedback Outcome T)
    (round : Round Observation Action Feedback Outcome) :
    take (Nat.le_succ T) (append history round) = history := by
  funext i
  exact append_castSucc history round i

@[fun_prop]
lemma measurable_append [MeasurableSpace Observation] [MeasurableSpace Action]
    [MeasurableSpace Feedback] [MeasurableSpace Outcome] :
    Measurable (fun p : Trace Observation Action Feedback Outcome T ×
      Round Observation Action Feedback Outcome => append p.1 p.2) := by
  apply Measurable.of_eval
  intro i
  dsimp only [append]
  split_ifs <;> fun_prop

end Trace

structure Algorithm (Observation : Type uO) (Action : Type uA) (Feedback : Type uF)
    [MeasurableSpace Observation] [MeasurableSpace Action] [MeasurableSpace Feedback] where
  State : Type (max uO uA uF)
  [stateSpace : MeasurableSpace State]
  initial : ProbabilityMeasure State
  choose : ℕ → Kernel (State × Observation) (Action × State)
  [chooseMarkov : ∀ t, IsMarkovKernel (choose t)]
  update : ℕ → Kernel (State × Observation × Action × Feedback) State
  [updateMarkov : ∀ t, IsMarkovKernel (update t)]

attribute [instance] Algorithm.stateSpace Algorithm.chooseMarkov Algorithm.updateMarkov

structure Environment (Observation : Type uO) (Action : Type uA) (Feedback : Type uF)
    (Outcome : Type uY) [MeasurableSpace Observation] [MeasurableSpace Action]
    [MeasurableSpace Feedback] [MeasurableSpace Outcome] where
  State : Type (max uO uA uF uY)
  [stateSpace : MeasurableSpace State]
  initial : ProbabilityMeasure State
  observe : ℕ → Kernel State (Observation × State)
  [observeMarkov : ∀ t, IsMarkovKernel (observe t)]
  respond : ℕ → Kernel (State × Observation × Action) (Feedback × Outcome × State)
  [respondMarkov : ∀ t, IsMarkovKernel (respond t)]

attribute [instance] Environment.stateSpace Environment.observeMarkov Environment.respondMarkov

section Execution

variable {Observation : Type uO} {Action : Type uA} {Feedback : Type uF}
    {Outcome : Type uY} [MeasurableSpace Observation] [MeasurableSpace Action]
    [MeasurableSpace Feedback] [MeasurableSpace Outcome]

abbrev RunState (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) (T : ℕ) :=
  A.State × E.State × Trace Observation Action Feedback Outcome T

private noncomputable def keepInput {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) : Kernel α (α × β) := Kernel.id ×ₖ κ

private instance keepInput_markov {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] : IsMarkovKernel (keepInput κ) := by
  unfold keepInput
  infer_instance

private noncomputable def mapKernel {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (κ : Kernel α β)
    (f : β → γ) (hf : Measurable f) : Kernel α γ := κ.mapOfMeasurable f hf

private instance mapKernel_markov {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (κ : Kernel α β) [IsMarkovKernel κ]
    (f : β → γ) (hf : Measurable f) : IsMarkovKernel (mapKernel κ f hf) := by
  unfold mapKernel
  rw [Kernel.mapOfMeasurable_eq_map]
  exact Kernel.IsMarkovKernel.map κ hf

noncomputable def step (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) (t : ℕ) :
    Kernel (RunState A E t) (RunState A E (t + 1)) :=
  let observe := keepInput ((E.observe t).comap
    (fun s : RunState A E t => s.2.1) (by fun_prop))
  let choose := keepInput ((A.choose t).comap
    (fun s : RunState A E t × (Observation × E.State) => (s.1.1, s.2.1))
    (by fun_prop))
  let respond := keepInput ((E.respond t).comap
    (fun s : (RunState A E t × (Observation × E.State)) × (Action × A.State) =>
      (s.1.2.2, s.1.2.1, s.2.1)) (by fun_prop))
  let update := keepInput ((A.update t).comap
    (fun s : ((RunState A E t × (Observation × E.State)) × (Action × A.State)) ×
        (Feedback × Outcome × E.State) =>
      (s.1.2.2, s.1.1.2.1, s.1.2.1, s.2.1)) (by fun_prop))
  let finish := fun s : (((RunState A E t × (Observation × E.State)) ×
      (Action × A.State)) × (Feedback × Outcome × E.State)) × A.State =>
    let history := s.1.1.1.1.2.2
    let observation := s.1.1.1.2.1
    let action := s.1.1.2.1
    let feedback := s.1.2.1
    let outcome := s.1.2.2.1
    (s.2, s.1.2.2.2, Trace.append history (observation, action, feedback, outcome))
  mapKernel update finish (by fun_prop) ∘ₖ respond ∘ₖ choose ∘ₖ observe

instance step_markov (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) (t : ℕ) :
    IsMarkovKernel (step A E t) := by
  unfold step
  infer_instance

lemma lintegral_step (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) (t : ℕ) (s : RunState A E t)
    (f : RunState A E (t + 1) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂step A E t s =
      ∫⁻ observation, ∫⁻ action, ∫⁻ response, ∫⁻ state,
        f (state, response.2.2,
          Trace.append s.2.2 (observation.1, action.1, response.1, response.2.1))
        ∂A.update t (action.2, observation.1, action.1, response.1)
        ∂E.respond t (observation.2, observation.1, action.1)
        ∂A.choose t (s.1, observation.1) ∂E.observe t s.2.1 := by
  unfold step mapKernel
  simp only [Kernel.lintegral_comp _ _ _ hf]
  simp only [Kernel.mapOfMeasurable_eq_map]
  unfold keepInput
  rw [Kernel.lintegral_id_prod (by fun_prop)]
  simp only [Kernel.comap_apply]
  congr 1
  funext observation
  rw [Kernel.lintegral_id_prod (by fun_prop)]
  simp only [Kernel.comap_apply]
  congr 1
  funext action
  rw [Kernel.lintegral_id_prod (by fun_prop)]
  simp only [Kernel.comap_apply]
  congr 1
  funext response
  rw [Kernel.lintegral_map _ (by fun_prop) _ hf]
  rw [Kernel.lintegral_id_prod (by fun_prop)]
  rfl

lemma lintegral_step_observation_action (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) (t : ℕ) (s : RunState A E t)
    (f : Observation × Action → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f ((z.2.2 (Fin.last t)).1, (z.2.2 (Fin.last t)).2.1) ∂step A E t s =
      ∫⁻ observation, ∫⁻ action, f (observation.1, action.1)
        ∂A.choose t (s.1, observation.1) ∂E.observe t s.2.1 := by
  rw [lintegral_step _ _ _ _ _ (by fun_prop)]
  simp

noncomputable def executionKernel (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) :
    (T : ℕ) → Kernel Unit (RunState A E T)
  | 0 => mapKernel (Kernel.const Unit ((A.initial : Measure A.State).prod
      (E.initial : Measure E.State)))
        (fun s => (s.1, s.2, fun i : Fin 0 => Fin.elim0 i)) (by fun_prop)
  | T + 1 => step A E T ∘ₖ executionKernel A E T

instance executionKernel_markov (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) (T : ℕ) :
    IsMarkovKernel (executionKernel A E T) := by
  induction T with
  | zero => unfold executionKernel; infer_instance
  | succ T ih => unfold executionKernel; infer_instance

lemma executionKernel_zero_apply (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) :
    executionKernel A E 0 () = ((A.initial : Measure A.State).prod
      (E.initial : Measure E.State)).map
        (fun s => (s.1, s.2, fun i : Fin 0 => Fin.elim0 i)) := rfl

lemma executionKernel_succ_apply (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) (T : ℕ) :
    executionKernel A E (T + 1) () =
      (executionKernel A E T ()).bind (step A E T) := rfl

noncomputable def execute (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) (T : ℕ) :
    ProbabilityMeasure (Trace Observation Action Feedback Outcome T) :=
  ⟨mapKernel (executionKernel A E T) (fun s => s.2.2) (by fun_prop) (), inferInstance⟩

lemma execute_toMeasure (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) (T : ℕ) :
    (execute A E T).toMeasure = (executionKernel A E T ()).map (fun s => s.2.2) := rfl

lemma lintegral_execute (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) (T : ℕ)
    (f : Trace Observation Action Feedback Outcome T → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ history, f history ∂(execute A E T).toMeasure =
      ∫⁻ s, f s.2.2 ∂executionKernel A E T () := by
  rw [execute_toMeasure, lintegral_map hf (by fun_prop)]

lemma execute_zero (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) :
    (execute A E 0).toMeasure = Measure.dirac (fun i : Fin 0 => Fin.elim0 i) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_execute _ _ _ _ hf, executionKernel_zero_apply,
    lintegral_map (by fun_prop) (by fun_prop), lintegral_dirac' _ hf]
  simp

lemma lintegral_step_take (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) (t : ℕ) (s : RunState A E t)
    (f : Trace Observation Action Feedback Outcome t → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f (Trace.take (Nat.le_succ t) z.2.2) ∂step A E t s = f s.2.2 := by
  rw [lintegral_step _ _ _ _ _ (by fun_prop)]
  simp

lemma execute_take_succ (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) (T : ℕ) :
    ((execute A E (T + 1)).toMeasure).map (Trace.take (Nat.le_succ T)) =
      (execute A E T).toMeasure := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop), lintegral_execute _ _ _ _ (by fun_prop),
    executionKernel_succ_apply, Measure.lintegral_bind (step A E T).aemeasurable
      (by fun_prop), lintegral_execute _ _ _ _ hf]
  exact lintegral_congr (fun s => lintegral_step_take A E T s f hf)

lemma execute_take (A : Algorithm Observation Action Feedback)
    (E : Environment Observation Action Feedback Outcome) {T N : ℕ} (h : T ≤ N) :
    ((execute A E N).toMeasure).map (Trace.take h) = (execute A E T).toMeasure := by
  induction N, h using Nat.le_induction with
  | base =>
    change Measure.map id _ = _
    exact Measure.map_id
  | succ N h ih =>
    change Measure.map (Trace.take h ∘ Trace.take (Nat.le_succ N)) _ = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop), execute_take_succ, ih]

end Execution

structure Setup where
  Params : Type uP
  Public : Type uD
  Instance : Public → Type uI
  Observation : Public → Type uO
  Action : Public → Type uA
  Feedback : Public → Type uF
  Outcome : Public → Type uY
  [observationSpace : ∀ p, MeasurableSpace (Observation p)]
  [actionSpace : ∀ p, MeasurableSpace (Action p)]
  [feedbackSpace : ∀ p, MeasurableSpace (Feedback p)]
  [outcomeSpace : ∀ p, MeasurableSpace (Outcome p)]
  Bound : Params → Type uB
  publicInput : Params → Public
  horizon : Params → ℕ
  valid : Params → Prop
  admissible : (p : Params) → Instance (publicInput p) →
    Environment (Observation (publicInput p)) (Action (publicInput p))
      (Feedback (publicInput p)) (Outcome (publicInput p)) → Prop
  successful : (p : Params) → Instance (publicInput p) → Bound p →
    ProbabilityMeasure (Trace (Observation (publicInput p)) (Action (publicInput p))
      (Feedback (publicInput p)) (Outcome (publicInput p)) (horizon p)) → Prop
  allowedAction : (p : Public) → Observation p → Action p → Prop := fun _ _ _ => True
  allowedAlgorithm : (p : Public) → Algorithm (Observation p) (Action p) (Feedback p) → Prop :=
    fun _ _ => True

attribute [instance] Setup.observationSpace Setup.actionSpace Setup.feedbackSpace Setup.outcomeSpace

def Guarantee (S : Setup)
    (makeAlgorithm : (p : S.Public) → Algorithm (S.Observation p) (S.Action p) (S.Feedback p))
    (bound : (p : S.Params) → S.Bound p) : Prop :=
  (∀ p, S.valid p → S.allowedAlgorithm (S.publicInput p) (makeAlgorithm (S.publicInput p))) ∧
    ∀ p, S.valid p → ∀ (I : S.Instance (S.publicInput p))
      (E : Environment (S.Observation (S.publicInput p)) (S.Action (S.publicInput p))
        (S.Feedback (S.publicInput p)) (S.Outcome (S.publicInput p))),
      S.admissible p I E →
        let law := execute (makeAlgorithm (S.publicInput p)) E (S.horizon p)
        (∀ᵐ history ∂law.toMeasure, ∀ t,
          S.allowedAction (S.publicInput p) (history t).1 (history t).2.1) ∧
        S.successful p I (bound p) law

def Achievable (S : Setup) (bound : (p : S.Params) → S.Bound p) : Prop :=
  ∃ makeAlgorithm : (p : S.Public) → Algorithm (S.Observation p) (S.Action p) (S.Feedback p),
    Guarantee S makeAlgorithm bound

end OnlineTemplate
