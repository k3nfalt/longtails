import LongTails.Algorithms.DistributedReplyTransform
import LongTails.Proofs.DistributedExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DistributedReplySimulation

open MeasureTheory DistributedTemplate LongTails.Setups.StarNetwork
open LongTails.Algorithms.DistributedReplyTransform

variable {X Y Z U V Output : Type} {n : ℕ} [MeasurableSpace U] [MeasurableSpace V]
variable (N : Network n) (g : Fin n → X → U → ℕ → Y) (P : ProbabilityMeasure U)
    (g' : Fin n → X → V → ℕ → Z) (P' : ProbabilityMeasure V) (liftSeed : U → V)
    (A : Protocol X Z Output n) (seed : A.Seed)
    (transform : Fin (n + 1) → ℕ → X → Y → Z)

local notation "O" => system N g P
local notation "O'" => system N g' P'
local notation "A₀" => algorithm A seed transform

def liftComputation (s : ComputationState X U) : ComputationState X V :=
  ⟨s.pending, liftSeed s.seed, s.used⟩

noncomputable def liftOracle (s : OracleState O) : OracleState O' :=
  ⟨fun v => liftComputation liftSeed (s.computation v), s.communication⟩

noncomputable def forget (c : ExecutionState O A₀) : ExecutionState O' A :=
  ⟨c.time, c.deadline, fun v => (c.workers v).1, c.wakeTime, c.turn,
    liftOracle N g P g' P' liftSeed c.oracle⟩

def Counts (c : ExecutionState O A₀) : Prop :=
  ∀ v, (c.workers v).2 = (c.oracle.computation v).used

variable (hvalue : ∀ i x s k, g' i x (liftSeed s) k = transform i.succ k x (g i x s k))

omit [MeasurableSpace U] [MeasurableSpace V] in
include hvalue in
lemma computation_answer (s : ComputationState X U) (v : Fin (n + 1)) (t : Time) :
    (computation N g').answer v (liftComputation liftSeed s) t =
      ((computation N g).answer v s t).map (fun (r, s') => match r with
        | .computed x y => (.computed x (transform v s.used x y), liftComputation liftSeed s')) := by
  refine Fin.cases ?_ (fun i => ?_) v
  · rfl
  · cases h : s.pending with
    | none => simp [computation, liftComputation, h]
    | some pair =>
      rcases pair with ⟨finish, x⟩
      by_cases ht : finish ≤ t <;> simp [computation, liftComputation, h, ht, hvalue]

omit [MeasurableSpace U] [MeasurableSpace V] in
lemma submit_map (s : ComputationState X U) (v : Fin (n + 1)) (t : Time)
    (q : ComputeQuery X) :
    (computation N g').submit v (liftComputation liftSeed s) t q =
      liftComputation liftSeed ((computation N g).submit v s t q) := by
  cases q with
  | abort => rfl
  | evaluate x =>
    refine Fin.cases ?_ (fun i => ?_) v
    · rfl
    · cases h : s.pending <;> simp [computation, liftComputation, h]

omit [MeasurableSpace U] in
lemma submit_used (s : ComputationState X U) (v : Fin (n + 1)) (t : Time)
    (q : ComputeQuery X) : ((computation N g).submit v s t q).used = s.used := by
  cases q with
  | abort => rfl
  | evaluate x =>
    refine Fin.cases ?_ (fun i => ?_) v
    · rfl
    · cases h : s.pending <;> simp [computation, h]

lemma lift_update (s : OracleState O) (v : Fin (n + 1)) (a : ComputationState X U) :
    liftOracle N g P g' P' liftSeed {s with computation := Function.update s.computation v a} =
      ⟨Function.update (fun j => liftComputation liftSeed (s.computation j)) v
        (liftComputation liftSeed a), s.communication⟩ := by
  unfold liftOracle
  congr 1
  funext j
  by_cases hj : j = v <;> simp [hj]

private lemma map_find {α β γ : Type*} (l : List α) (f : α → Option β) (m : β → γ) :
    l.findSome? (fun i => (f i).map m) = (l.findSome? f).map m := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : f a <;> simp [List.findSome?, h, ih]

noncomputable def liftHit (s : OracleState O)
    (hit : (Fin (n + 1) × Event (ComputeReply X Y) (CommReply n)) × OracleState O) :
    (Fin (n + 1) × Event (ComputeReply X Z) (CommReply n)) × OracleState O' :=
  let ((v, e), os) := hit
  ((v, LongTails.Algorithms.DistributedReplyTransform.event transform v (s.computation v).used e),
    liftOracle N g P g' P' liftSeed os)

private abbrev Hit {Q R C : Type} {m : ℕ} (orcl : Oracle Q R C m) :=
  (Fin m × Event R C) × OracleState orcl

private noncomputable def cpuHit {Q R C : Type} {m : ℕ} (orcl : Oracle Q R C m)
    (s : OracleState orcl) (t : Time) (v : Fin m) : Option (Hit orcl) :=
  (orcl.computation.answer v (s.computation v) t).map fun (r, st) =>
    ((v, .computed r), {s with computation := Function.update s.computation v st})

private noncomputable def wireHit {Q R C : Type} {m : ℕ} (orcl : Oracle Q R C m)
    (s : OracleState orcl) (t : Time) : Option (Hit orcl) :=
  (orcl.communication.answer s.communication t).map fun ((v,r),st) =>
    ((v, .received r), {s with communication := st})

include hvalue in
lemma oracle_answer (s : OracleState O) (t : Time) :
    (O').answer (liftOracle N g P g' P' liftSeed s) t =
      ((O).answer s t).map (liftHit N g P g' P' liftSeed transform s) := by
  let s' := liftOracle N g P g' P' liftSeed s
  let m := liftHit N g P g' P' liftSeed transform s
  have hcpu (v : Fin (n + 1)) : cpuHit O' s' t v = (cpuHit O s t v).map m := by
    unfold cpuHit
    change ((computation N g').answer v (liftComputation liftSeed (s.computation v)) t).map _ = _
    rw [computation_answer N g g' liftSeed transform hvalue]
    change _ = (((computation N g).answer v (s.computation v) t).map _).map m
    cases he : (computation N g).answer v (s.computation v) t with
    | none => rfl
    | some entry =>
      rcases entry with ⟨⟨x,y⟩,st⟩
      simp only [Option.map_some, m, liftHit, LongTails.Algorithms.DistributedReplyTransform.event]
      rw [lift_update]
      rfl
  have hwire : wireHit O' s' t = (wireHit O s t).map m := by
    unfold wireHit
    change ((communication (Seed := V) N).answer s.communication t).map _ =
      (((communication (Seed := U) N).answer s.communication t).map _).map m
    rw [show (communication (Seed := V) N).answer s.communication t =
      (communication (Seed := U) N).answer s.communication t from rfl]
    generalize ((communication (Seed := U) N).answer s.communication t) = packets
    cases packets <;> rfl
  have hf : (List.finRange (n + 1)).findSome? (cpuHit O' s' t) =
      ((List.finRange (n + 1)).findSome? (cpuHit O s t)).map m := by
    rw [show cpuHit O' s' t = _ from funext hcpu, map_find]
  unfold Oracle.answer
  unfold cpuHit at hf
  unfold wireHit at hwire
  dsimp only [s'] at hf hwire
  rw [hf, hwire]
  generalize (List.finRange (n + 1)).findSome? _ = table
  cases table <;> rfl

local notation "F" => forget N g P g' P' liftSeed A seed transform
local notation "M" => liftHit N g P g' P' liftSeed transform
local notation "D" => DistributedTemplate.event

include hvalue in
lemma event_map (c : ExecutionState O A₀) (t : Time) :
    D O' A (F c) t = (D O A₀ c t).map (M c.oracle) := by
  unfold DistributedTemplate.event
  dsimp only [forget]
  rw [oracle_answer N g P g' P' liftSeed transform hvalue]
  cases ho : (O).answer c.oracle t with
  | some r => rfl
  | none =>
    cases ((List.finRange (n + 1)).rotate c.turn).find?
      (fun v => decide (c.wakeTime v ≤ t)) <;> rfl

include hvalue in
lemma next_time (c : ExecutionState O A₀) :
    nextTime (D O' A (F c)) c.time c.deadline = nextTime (D O A₀ c) c.time c.deadline := by
  have he (t : Time) : (D O' A (F c) t).isSome = (D O A₀ c t).isSome := by
    rw [event_map N g P g' P' liftSeed A seed transform hvalue, Option.isSome_map]
  classical
  let chooseTime (ready : Time → Bool) : Time := if h : ∃ t,
      IsLeast {t | c.time ≤ t ∧ t ≤ c.deadline ∧ (t = c.deadline ∨ ready t)} t
    then Classical.choose h else c.time
  exact congrArg chooseTime (funext he)

lemma event_count (c : ExecutionState O A₀) (t : Time) (v : Fin (n + 1))
    (e : Event (ComputeReply X Y) (CommReply n)) (os : OracleState O)
    (he : D O A₀ c t = some ((v,e), os)) (j : Fin (n + 1)) :
    (os.computation j).used = Function.update (fun i => (c.oracle.computation i).used) v
      (nextCount (c.oracle.computation v).used e) j := by
  cases e with
  | wake =>
    obtain ⟨rfl, _⟩ := DistributedExecution.wake_event O A₀ c t v os he
    by_cases hj : j = v <;> simp [hj, nextCount]
  | received r =>
    obtain ⟨_, _, rfl⟩ := DistributedExecution.received_event O A₀ c t v r os he
    by_cases hj : j = v <;> simp [hj, nextCount]
  | computed r =>
    obtain ⟨st, ha, rfl⟩ := DistributedExecution.computed_event O A₀ c t v r os he
    have hst : st.used = (c.oracle.computation v).used + 1 := by
      revert ha
      induction v using Fin.cases with
      | zero => simp [system, computation]
      | succ i =>
        intro hv
        obtain ⟨x,y⟩ := r
        obtain ⟨_, _, _, _, rfl⟩ := DistributedExecution.computation_completed_data N g i _ st t x y hv
        rfl
    by_cases hj : j = v <;> simp [hj, nextCount, hst]

private lemma workers_map {S : Type} (w : Fin (n + 1) → S × ℕ)
    (v : Fin (n + 1)) (s : S) (k : ℕ) :
    (fun j => (Function.update w v (s,k) j).1) = Function.update (fun j => (w j).1) v s := by
  funext j
  by_cases hj : j = v <;> simp [hj]

include hvalue in
lemma step_map (c : ExecutionState O A₀) (hc : Counts N g P A seed transform c) :
    step O' A (F c) = (step O A₀ c).map F := by
  classical
  unfold step
  dsimp only [forget]
  by_cases hd : c.deadline < c.time
  · simp [hd]
  simp only [hd, ↓reduceIte]
  have hem := event_map N g P g' P' liftSeed A seed transform hvalue c c.time
  have hn := next_time N g P g' P' liftSeed A seed transform hvalue c
  dsimp only [forget] at hem hn
  rw [hem]
  cases he : D O A₀ c c.time with
  | none =>
    by_cases ht : c.time = c.deadline <;> simp [ht, hn, forget]
  | some hit =>
    obtain ⟨⟨v,e⟩,os⟩ := hit
    have hcount := hc v
    let ev := LongTails.Algorithms.DistributedReplyTransform.event transform v (c.oracle.computation v).used e
    cases hq : A.query v (A.update v (c.workers v).1 (A.clock c.time) ev) (A.clock c.time) with
    | mk act st =>
      dsimp only [ev] at hq
      cases act with
      | compute q =>
        simp [liftHit, algorithm, hcount, hq, forget, liftOracle, workers_map]
        funext j
        by_cases hj : j = v
        · subst j
          simpa only [Function.update_self, system] using submit_map N g g' liftSeed (os.computation v) v c.time q
        · simp [hj]
      | communicate q =>
        rcases q with ⟨target,bits⟩
        simp [liftHit, algorithm, hcount, hq, forget, liftOracle, workers_map]
        rfl
      | advance target =>
        simp [liftHit, algorithm, hcount, hq, forget, liftOracle, workers_map]

lemma step_counts (c next : ExecutionState O A₀) (hc : Counts N g P A seed transform c)
    (hs : step O A₀ c = some next) : Counts N g P A seed transform next := by
  classical
  unfold step at hs
  split at hs
  · contradiction
  · cases he : D O A₀ c c.time with
    | none =>
      rw [he] at hs
      by_cases ht : c.time = c.deadline
      · simp [ht] at hs
      · simp [ht] at hs
        subst next
        exact hc
    | some hit =>
      obtain ⟨⟨v,e⟩,os⟩ := hit
      rw [he] at hs
      have hk := event_count N g P A seed transform c c.time v e os he
      let ev := LongTails.Algorithms.DistributedReplyTransform.event transform v (c.workers v).2 e
      cases hq : A.query v (A.update v (c.workers v).1 (A.clock c.time) ev) (A.clock c.time) with
      | mk act st =>
        dsimp only [ev] at hq
        cases act with
        | compute q =>
          simp [algorithm, hq] at hs
          subst next
          intro j
          by_cases hj : j = v
          · subst j
            simpa [algorithm, submit_used, system, hc v] using (hk v).symm
          · simpa [hj] using (hc j).trans (by simpa [hj] using (hk j).symm)
        | communicate q =>
          rcases q with ⟨target,bits⟩
          simp [algorithm, hq] at hs
          subst next
          intro j
          by_cases hj : j = v
          · subst j
            simpa [hc v] using (hk v).symm
          · simpa [hj] using (hc j).trans (by simpa [hj] using (hk j).symm)
        | advance target =>
          simp [algorithm, hq] at hs
          subst next
          intro j
          by_cases hj : j = v
          · subst j
            simpa [hc v] using (hk v).symm
          · simpa [hj] using (hc j).trans (by simpa [hj] using (hk j).symm)

include hvalue in
lemma run_map (k : ℕ) (c : ExecutionState O A₀) (hc : Counts N g P A seed transform c) :
    run O' A k (F c) = F (run O A₀ k c) ∧ Counts N g P A seed transform (run O A₀ k c) := by
  induction k generalizing c with
  | zero => exact ⟨rfl, hc⟩
  | succ k ih =>
    simp only [run, step_map N g P g' P' liftSeed A seed transform hvalue c hc]
    cases he : step O A₀ c with
    | none => exact ⟨rfl, hc⟩
    | some next => exact ih next (step_counts N g P A seed transform c next hc he)

include hvalue in
lemma terminal_transfer (T : Time) (s : U) (k : ℕ) :
    step O' A (run O' A k (initial O' A T (seed,liftSeed s))) = none →
      step O A₀ (run O A₀ k (initial O A₀ T ((),s))) = none := by
  let c := initial O A₀ T ((),s)
  have hc : Counts N g P A seed transform c := fun _ => rfl
  obtain ⟨hr, hk⟩ := run_map N g P g' P' liftSeed A seed transform hvalue k c hc
  have hi : F c = initial O' A T (seed, liftSeed s) := rfl
  intro h
  rw [← hi, hr, step_map N g P g' P' liftSeed A seed transform hvalue _ hk] at h
  exact Option.map_eq_none_iff.mp h

include hvalue in
lemma execution_transfer (T : Time) (s : U)
    (hf : FiniteEvents O' A T (seed, liftSeed s)) :
    FiniteEvents O A₀ T ((),s) ∧ execute O A₀ T () s = execute O' A T seed (liftSeed s) := by
  have htrans := terminal_transfer N g P g' P' liftSeed A seed transform hvalue
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨k,hk⟩ := hf t ht
    exact ⟨k,htrans t s k hk⟩
  · obtain ⟨k,hk⟩ := hf T le_rfl
    have hp := htrans T s k hk
    rw [DistributedExecution.execute_eq_terminal O A₀ T ((),s) k hp,
      DistributedExecution.execute_eq_terminal O' A T (seed,liftSeed s) k hk]
    let c := initial O A₀ T ((),s)
    have hc : Counts N g P A seed transform c := fun _ => rfl
    have h := (run_map N g P g' P' liftSeed A seed transform hvalue k c hc).1
    change run O' A k (initial O' A T (seed,liftSeed s)) = F (run O A₀ k c) at h
    rw [h]
    rfl

end LongTails.Proofs.DistributedReplySimulation
