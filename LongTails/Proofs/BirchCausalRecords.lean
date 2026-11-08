import LongTails.Proofs.BirchCausalConstruction
import LongTails.Proofs.BirchCausalStates

namespace LongTails.Proofs.BirchCausalRecords

open Finset
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchCausalPackets
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchCausalConstruction
open LongTails.Proofs.BirchCausalStates

structure GraphLabels where
  next : ℕ
  atoms : ℕ
  raw : ℕ → ℕ
  sharp : ℕ → ℕ

def labelStep (node : GraphNode) (state : GraphLabels) : GraphLabels :=
  match node with
  | .query _ _ => {
      next := state.next + 6
      atoms := state.atoms + 1
      raw := Function.update state.raw state.atoms (state.next + 2)
      sharp := Function.update state.sharp state.atoms (state.next + 4) }
  | .merge _ _ _ _ => { state with next := state.next + 11 }

def labelFold (nodes : List GraphNode) (state : GraphLabels) : GraphLabels :=
  nodes.foldl (flip labelStep) state

lemma labelStep_atoms (node : GraphNode) (state : GraphLabels) :
    (labelStep node state).atoms = state.atoms + node.calls := by
  cases node <;> rfl

lemma labelStep_next (node : GraphNode) (state : GraphLabels) :
    (labelStep node state).next = state.next + nodeLength node := by
  cases node <;> rfl

lemma labelStep_old (node : GraphNode) (state : GraphLabels) (i : ℕ) (hi : i < state.atoms) :
    (labelStep node state).raw i = state.raw i ∧ (labelStep node state).sharp i = state.sharp i := by
  cases node <;> simp [labelStep, ne_of_lt hi]

lemma labelFold_old (nodes : List GraphNode) (state : GraphLabels) (i : ℕ) (hi : i < state.atoms) :
    (labelFold nodes state).raw i = state.raw i ∧ (labelFold nodes state).sharp i = state.sharp i := by
  induction nodes generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons node rest ih =>
      have hi' : i < (labelStep node state).atoms := by rw [labelStep_atoms]; omega
      have h := ih (labelStep node state) hi'
      have hold := labelStep_old node state i hi
      exact ⟨h.1.trans hold.1, h.2.trans hold.2⟩

def LabelsMatch (raw sharp : ℕ → ℕ) : List GraphNode → GraphLabels → Prop
  | [], _ => True
  | .query worker source :: rest, state =>
      raw state.atoms = state.next + 2 ∧ sharp state.atoms = state.next + 4 ∧
        LabelsMatch raw sharp rest (labelStep (.query worker source) state)
  | .merge worker left right common :: rest, state =>
      LabelsMatch raw sharp rest (labelStep (.merge worker left right common) state)

lemma labelsMatch_final (nodes : List GraphNode) (state : GraphLabels) :
    LabelsMatch (labelFold nodes state).raw (labelFold nodes state).sharp nodes state := by
  induction nodes generalizing state with
  | nil => trivial
  | cons node rest ih =>
      cases node with
      | query worker source =>
          have hold := labelFold_old rest (labelStep (.query worker source) state) state.atoms (by
            simp [labelStep])
          refine ⟨?_, ?_, ih _⟩
          · exact hold.1.trans (Function.update_self _ _ _)
          · exact hold.2.trans (Function.update_self _ _ _)
      | merge worker left right common => exact ih _

lemma labelFold_atoms (nodes : List GraphNode) (state : GraphLabels) :
    (labelFold nodes state).atoms = state.atoms + (nodes.map GraphNode.calls).sum := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node rest ih =>
      change (labelFold rest (labelStep node state)).atoms = _
      rw [ih, labelStep_atoms]
      simp [Nat.add_assoc]

lemma labelFold_next (nodes : List GraphNode) (state : GraphLabels) :
    (labelFold nodes state).next = state.next + (nodes.map nodeLength).sum := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node rest ih =>
      change (labelFold rest (labelStep node state)).next = _
      rw [ih, labelStep_next]
      simp [Nat.add_assoc]

def Reads (t : Tuning) (state : GraphState) (s : CodeState) (values : GraphValues LinearValue) : Prop :=
  (∀ i, (codeSymbolic t s).points (state.states i).point = values.points i) ∧
    ∀ i, (codeSymbolic t s).vectors (state.states i).momentum = values.momenta i

lemma graphStep_reads (workers H round B : ℕ) (η : ℝ) (node : GraphNode)
    (state : GraphState) (s : CodeState) (values : GraphValues LinearValue)
    (raw direction : ℕ → LinearValue)
    (hs : CodeValid workers (canonicalTuning η B) s)
    (howned : ∀ i, OwnedValid workers (canonicalTuning η B) s (state.states i))
    (hnext : state.next = values.next)
    (hread : Reads (canonicalTuning η B) state s values)
    (hnames : ∀ worker source, node = .query worker source →
      raw values.atoms = (Finsupp.single (s.next + 2) 1, 0) ∧
      direction values.atoms = (0, Finsupp.single (s.next + 4) 1)) :
    let z := graphStep H round node state s
    Reads (canonicalTuning η B) z.1 z.2
      (valueStep (1 / (B : ℝ)) (1 / (H : ℝ) * η) raw direction node values) := by
  let t := canonicalTuning η B
  have hn := codeValid_symbolic_next workers t s hs
  have hbound := codeValid_register_bound workers t s hs
  have hold (i : ℕ) :
      (codeSymbolic t (graphNodeCode H round node state s).2).points (state.states i).point = values.points i ∧
      (codeSymbolic t (graphNodeCode H round node state s).2).vectors (state.states i).momentum = values.momenta i := by
    have hx := codeExtends_symbolic t s _ (graphNodeCode_extends H round node state s)
      (state.states i).point (by rw [← hn]; exact hbound.1 _ _ (howned i).2.1)
    have hm := codeExtends_symbolic t s _ (graphNodeCode_extends H round node state s)
      (state.states i).momentum (by rw [← hn]; exact hbound.2 _ _ (howned i).2.2)
    exact ⟨hx.1.trans (hread.1 i), hm.2.1.trans (hread.2 i)⟩
  cases node with
  | query worker source =>
      have hsym := graphQuery_symbolic H round worker source state s t hn
        (hbound.2 _ _ (howned source).2.2)
      have hname := hnames worker source rfl
      constructor
      · intro i
        dsimp only [graphStep, state_bind_apply, state_pure_apply, valueStep]
        by_cases hi : i = state.next
        · subst i
          rw [Function.update_self, hnext, Function.update_self]
          rw [hsym.2.1, hread.1 source, ← hname.2]
          rfl
        · rw [Function.update_of_ne hi, Function.update_of_ne (by simpa [← hnext] using hi)]
          exact (hold i).1
      · intro i
        dsimp only [graphStep, state_bind_apply, state_pure_apply, valueStep]
        by_cases hi : i = state.next
        · subst i
          rw [Function.update_self, hnext, Function.update_self]
          rw [hsym.1, hread.2 source, ← hname.1]
          rfl
        · rw [Function.update_of_ne hi, Function.update_of_ne (by simpa [← hnext] using hi)]
          exact (hold i).2
  | merge worker left right common =>
      have hsym := graphMerge_symbolic H round worker left right common state s t hn
        (hbound.2 _ _ (howned left).2.2) (hbound.2 _ _ (howned right).2.2)
        (hbound.2 _ _ (howned common).2.2)
      constructor
      · intro i
        dsimp only [graphStep, state_bind_apply, state_pure_apply, valueStep]
        by_cases hi : i = state.next
        · subst i
          rw [Function.update_self, hnext, Function.update_self, hsym.1,
            hread.1 left, hread.1 right, hread.1 common]
        · rw [Function.update_of_ne hi, Function.update_of_ne (by simpa [← hnext] using hi)]
          exact (hold i).1
      · intro i
        dsimp only [graphStep, state_bind_apply, state_pure_apply, valueStep]
        by_cases hi : i = state.next
        · subst i
          rw [Function.update_self, hnext, Function.update_self, hsym.2,
            hread.2 left, hread.2 right, hread.2 common]
        · rw [Function.update_of_ne hi, Function.update_of_ne (by simpa [← hnext] using hi)]
          exact (hold i).2

lemma graphMerge_trace (H round worker left right common : ℕ) (state : GraphState)
    (s : CodeState) (t : Tuning) :
    let z := graphNodeCode H round (.merge worker left right common) state s
    (codeSymbolic t z.2).queryPoints = (codeSymbolic t s).queryPoints ∧
      (codeSymbolic t z.2).sharpInputs = (codeSymbolic t s).sharpInputs ∧
      (codeSymbolic t z.2).queries = (codeSymbolic t s).queries ∧
      (codeSymbolic t z.2).sharps = (codeSymbolic t s).sharps ∧
      (codeSymbolic t z.2).units = (codeSymbolic t s).units := by
  simp only [graphNodeCode, sendState, join, state_bind_apply, state_pure_apply,
    codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform, symbolicStore]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

structure Trace (t : Tuning) (s : CodeState) (values : GraphValues LinearValue)
    (raw sharp : ℕ → ℕ) (α : ℝ) : Prop where
  query_bound : ∀ i < values.atoms, raw i < (codeSymbolic t s).next
  sharp_bound : ∀ i < values.atoms, sharp i < (codeSymbolic t s).next
  point : ∀ i < values.atoms, (codeSymbolic t s).queryPoints (raw i) = values.queryPoints i
  input : ∀ i < values.atoms, (codeSymbolic t s).sharpInputs (sharp i) =
    α • (Finsupp.single (raw i) 1, 0) + (1 - α) • values.queryMomenta i

lemma graphStep_trace (workers H round B : ℕ) (η : ℝ) (node : GraphNode)
    (state : GraphState) (s : CodeState) (values : GraphValues LinearValue)
    (raw sharp : ℕ → ℕ)
    (hs : CodeValid workers (canonicalTuning η B) s)
    (howned : ∀ i, OwnedValid workers (canonicalTuning η B) s (state.states i))
    (hread : Reads (canonicalTuning η B) state s values)
    (htrace : Trace (canonicalTuning η B) s values raw sharp (1 / (B : ℝ)))
    (hnames : ∀ worker source, node = .query worker source →
      raw values.atoms = s.next + 2 ∧ sharp values.atoms = s.next + 4) :
    let z := graphStep H round node state s
    Trace (canonicalTuning η B) z.2
      (valueStep (1 / (B : ℝ)) (1 / (H : ℝ) * η)
        (fun i => (Finsupp.single (raw i) 1, 0))
        (fun i => (0, Finsupp.single (sharp i) 1)) node values) raw sharp (1 / (B : ℝ)) := by
  let t := canonicalTuning η B
  have hn := codeValid_symbolic_next workers t s hs
  have hbound := codeValid_register_bound workers t s hs
  have he := graphNodeCode_extends H round node state s
  have hnew : (codeSymbolic t (graphStep H round node state s).2).next =
      (codeSymbolic t s).next + nodeLength node := by
    cases node <;> simp only [graphStep, graphNodeCode, sendState, atom, join,
      state_bind_apply, state_pure_apply, codeSymbolic_emit, InstructionTemplate.instantiate,
      symbolicPerform, symbolicStore, nodeLength, Nat.add_assoc, Nat.reduceAdd]
  cases node with
  | query worker source =>
      have hsym := graphQuery_symbolic H round worker source state s t hn
        (hbound.2 _ _ (howned source).2.2)
      have hname := hnames worker source rfl
      constructor
      · intro i hi
        change i < values.atoms + 1 at hi
        by_cases heq : i = values.atoms
        · subst i; rw [hname.1, hnew, ← hn]; simp only [nodeLength]; omega
        · have hi' : i < values.atoms := by omega
          rw [hnew]; exact lt_of_lt_of_le (htrace.query_bound i hi') (Nat.le_add_right _ _)
      · intro i hi
        change i < values.atoms + 1 at hi
        by_cases heq : i = values.atoms
        · subst i; rw [hname.2, hnew, ← hn]; simp only [nodeLength]; omega
        · have hi' : i < values.atoms := by omega
          rw [hnew]; exact lt_of_lt_of_le (htrace.sharp_bound i hi') (Nat.le_add_right _ _)
      · intro i hi
        change i < values.atoms + 1 at hi
        by_cases heq : i = values.atoms
        · subst i
          dsimp only [valueStep, graphStep, state_bind_apply, state_pure_apply]
          rw [hname.1, Function.update_self, hsym.2.2.1, hread.1 source]
        · have hi' : i < values.atoms := by omega
          dsimp only [valueStep, graphStep, state_bind_apply, state_pure_apply]
          rw [Function.update_of_ne heq,
            (codeExtends_symbolic t s _ he _ (htrace.query_bound i hi')).2.2.1,
            htrace.point i hi']
      · intro i hi
        change i < values.atoms + 1 at hi
        by_cases heq : i = values.atoms
        · subst i
          dsimp only [valueStep, graphStep, state_bind_apply, state_pure_apply]
          rw [hname.2, Function.update_self, hsym.2.2.2.1, hname.1, hread.2 source]
          rfl
        · have hi' : i < values.atoms := by omega
          dsimp only [valueStep, graphStep, state_bind_apply, state_pure_apply]
          rw [Function.update_of_ne heq,
            (codeExtends_symbolic t s _ he _ (htrace.sharp_bound i hi')).2.2.2,
            htrace.input i hi']
  | merge worker left right common =>
      have hsym := graphMerge_trace H round worker left right common state s t
      constructor
      · intro i hi; rw [hnew]; exact lt_of_lt_of_le (htrace.query_bound i hi) (Nat.le_add_right _ _)
      · intro i hi; rw [hnew]; exact lt_of_lt_of_le (htrace.sharp_bound i hi) (Nat.le_add_right _ _)
      · intro i hi; exact (congrFun hsym.1 (raw i)).trans (htrace.point i hi)
      · intro i hi; exact (congrFun hsym.2.1 (sharp i)).trans (htrace.input i hi)

structure RuntimeInvariant (workers B : ℕ) (η : ℝ) (state : GraphState) (s : CodeState)
    (labels : GraphLabels) (values : GraphValues LinearValue) (raw sharp : ℕ → ℕ) : Prop where
  valid : CodeValid workers (canonicalTuning η B) s
  owned : ∀ i, OwnedValid workers (canonicalTuning η B) s (state.states i)
  state_next : state.next = values.next
  state_atoms : state.atoms = values.atoms
  label_next : labels.next = s.next
  label_atoms : labels.atoms = values.atoms
  reads : Reads (canonicalTuning η B) state s values
  trace : Trace (canonicalTuning η B) s values raw sharp (1 / (B : ℝ))

lemma runtimeInvariant_step (workers H round B : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (node : GraphNode) (hw : node.worker < workers)
    (state : GraphState) (s : CodeState) (labels : GraphLabels)
    (values : GraphValues LinearValue) (raw sharp : ℕ → ℕ)
    (h : RuntimeInvariant workers B η state s labels values raw sharp)
    (hnames : ∀ worker source, node = .query worker source →
      raw labels.atoms = labels.next + 2 ∧ sharp labels.atoms = labels.next + 4) :
    let z := graphStep H round node state s
    RuntimeInvariant workers B η z.1 z.2 (labelStep node labels)
      (valueStep (1 / (B : ℝ)) (1 / (H : ℝ) * η)
        (fun i => (Finsupp.single (raw i) 1, 0))
        (fun i => (0, Finsupp.single (sharp i) 1)) node values) raw sharp := by
  have hn : ∀ worker source, node = .query worker source →
      raw values.atoms = s.next + 2 ∧ sharp values.atoms = s.next + 4 := by
    simpa only [h.label_atoms, h.label_next] using hnames
  have hv := graphStep_valid workers H round (canonicalTuning η B) ht node state s h.valid hw h.owned
  refine ⟨hv.1, hv.2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases node <;> simpa only [graphStep, state_bind_apply, state_pure_apply, valueStep] using congrArg (· + 1) h.state_next
  · cases node <;> simp only [graphStep, state_bind_apply, state_pure_apply, valueStep, h.state_atoms, Nat.add_zero]
  · rw [(graphStep_meta H round node state s).2.2, labelStep_next, h.label_next]
  · cases node <;> simp only [labelStep, valueStep, h.label_atoms]
  · apply graphStep_reads workers H round B η node state s values _ _ h.valid h.owned h.state_next h.reads
    intro worker source he
    obtain ⟨hq, hd⟩ := hn worker source he
    exact ⟨by rw [hq], by rw [hd]⟩
  · exact graphStep_trace workers H round B η node state s values raw sharp
      h.valid h.owned h.reads h.trace hn

lemma runtimeInvariant_fold (workers H round B : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (nodes : List GraphNode)
    (hw : ∀ node ∈ nodes, node.worker < workers)
    (state : GraphState) (s : CodeState) (labels : GraphLabels)
    (values : GraphValues LinearValue) (raw sharp : ℕ → ℕ)
    (h : RuntimeInvariant workers B η state s labels values raw sharp)
    (hnames : LabelsMatch raw sharp nodes labels) :
    let z := (forIn nodes state (fun node state => ForInStep.yield <$> graphStep H round node state) :
      StateM CodeState GraphState) s
    RuntimeInvariant workers B η z.1 z.2 (labelFold nodes labels)
      (nodes.foldl (flip (valueStep (1 / (B : ℝ)) (1 / (H : ℝ) * η)
        (fun i => (Finsupp.single (raw i) 1, 0))
        (fun i => (0, Finsupp.single (sharp i) 1)))) values) raw sharp := by
  induction nodes generalizing state s labels values with
  | nil => exact h
  | cons node rest ih =>
      rw [state_forIn_cons]
      have hn : ∀ worker source, node = .query worker source →
          raw labels.atoms = labels.next + 2 ∧ sharp labels.atoms = labels.next + 4 := by
        intro worker source he
        subst node
        exact ⟨hnames.1, hnames.2.1⟩
      have hrest : LabelsMatch raw sharp rest (labelStep node labels) := by
        cases node with
        | query worker source => exact hnames.2.2
        | merge worker left right common => exact hnames
      exact ih (fun node hn => hw node (List.mem_cons_of_mem _ hn)) _ _ _ _
        (runtimeInvariant_step workers H round B η ht node (hw node List.mem_cons_self)
          state s labels values raw sharp h hn) hrest

lemma graphCode_runtime (workers H round B output coordinator x m : ℕ) (η : ℝ)
    (ht : (canonicalTuning η B).Valid) (nodes : List GraphNode)
    (hw : ∀ node ∈ nodes, node.worker < workers) (s : CodeState)
    (hs : CodeValid workers (canonicalTuning η B) s) (hc : coordinator < workers)
    (hx : x ∈ (codeLayout (canonicalTuning η B) s).points coordinator)
    (hm : m ∈ (codeLayout (canonicalTuning η B) s).vectors coordinator) :
    let labels := labelFold nodes ⟨s.next, 0, fun _ => 0, fun _ => 0⟩
    let values := nodes.foldl (flip (valueStep (1 / (B : ℝ)) (1 / (H : ℝ) * η)
      (fun i => (Finsupp.single (labels.raw i) 1, 0))
      (fun i => (0, Finsupp.single (labels.sharp i) 1))))
      (initialValues ((codeSymbolic (canonicalTuning η B) s).points x)
        ((codeSymbolic (canonicalTuning η B) s).vectors m))
    let z := graphCode H round nodes output coordinator x m s
    (codeSymbolic (canonicalTuning η B) z.2).points z.1.1 = values.points output ∧
      (codeSymbolic (canonicalTuning η B) z.2).vectors z.1.2 = values.momenta output ∧
      Trace (canonicalTuning η B) z.2 values labels.raw labels.sharp (1 / (B : ℝ)) := by
  let t := canonicalTuning η B
  let initial : GraphState := ⟨fun _ => ⟨coordinator, x, m⟩, 1, 0⟩
  let labels0 : GraphLabels := ⟨s.next, 0, fun _ => 0, fun _ => 0⟩
  let labels := labelFold nodes labels0
  let values0 := initialValues ((codeSymbolic t s).points x) ((codeSymbolic t s).vectors m)
  let values := nodes.foldl (flip (valueStep (1 / (B : ℝ)) (1 / (H : ℝ) * η)
    (fun i => (Finsupp.single (labels.raw i) 1, 0))
    (fun i => (0, Finsupp.single (labels.sharp i) 1)))) values0
  have hi : RuntimeInvariant workers B η initial s labels0 values0 labels.raw labels.sharp := by
    refine ⟨hs, fun _ => ⟨hc, hx, hm⟩, rfl, rfl, rfl, rfl, ⟨fun _ => rfl, fun _ => rfl⟩, ?_⟩
    constructor <;> intro i h <;> exact (Nat.not_lt_zero i h).elim
  have hr := runtimeInvariant_fold workers H round B η ht nodes hw initial s labels0 values0
    labels.raw labels.sharp hi (labelsMatch_final nodes labels0)
  let z := (forIn nodes initial (fun node state => ForInStep.yield <$> graphStep H round node state) :
    StateM CodeState GraphState) s
  have hrun : RuntimeInvariant workers B η z.1 z.2 labels values labels.raw labels.sharp := hr
  have hmem := sendState_symbolic t (z.1.states output).worker coordinator
    (z.1.states output).point (z.1.states output).momentum z.2
  refine ⟨?_, ?_, ?_⟩
  · change (codeSymbolic t (sendState (z.1.states output).worker coordinator
      (z.1.states output).point (z.1.states output).momentum z.2).2).points
      (z.1.states output).point = values.points output
    rw [hmem]
    exact hrun.reads.1 output
  · change (codeSymbolic t (sendState (z.1.states output).worker coordinator
      (z.1.states output).point (z.1.states output).momentum z.2).2).vectors
      (z.1.states output).momentum = values.momenta output
    rw [hmem]
    exact hrun.reads.2 output
  · change Trace t (sendState (z.1.states output).worker coordinator
      (z.1.states output).point (z.1.states output).momentum z.2).2 values labels.raw labels.sharp _
    constructor
    · intro i hi; rw [hmem]; exact lt_of_lt_of_le (hrun.trace.query_bound i hi) (Nat.le_add_right _ _)
    · intro i hi; rw [hmem]; exact lt_of_lt_of_le (hrun.trace.sharp_bound i hi) (Nat.le_add_right _ _)
    · intro i hi; rw [hmem]; exact hrun.trace.point i hi
    · intro i hi; rw [hmem]; exact hrun.trace.input i hi

lemma graphQuery_sets (H round worker source : ℕ) (state : GraphState) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    let z := graphNodeCode H round (.query worker source) state s
    (codeSymbolic t z.2).queries = insert (s.next + 2) (codeSymbolic t s).queries ∧
      (codeSymbolic t z.2).sharps = insert (s.next + 4) (codeSymbolic t s).sharps ∧
      (codeSymbolic t z.2).units = (codeSymbolic t s).units := by
  simp only [graphNodeCode, sendState, atom, state_bind_apply, state_pure_apply,
    codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform, symbolicStore,
    Nat.add_assoc, Nat.reduceAdd]
  rw [← hn]
  exact ⟨rfl, rfl, trivial⟩

structure Support (t : Tuning) (s : CodeState) (n : ℕ) (raw sharp : ℕ → ℕ)
    (queries sharps units : Finset ℕ) : Prop where
  query_set : (codeSymbolic t s).queries = queries ∪ (range n).image raw
  sharp_set : (codeSymbolic t s).sharps = sharps ∪ (range n).image sharp
  unit_set : (codeSymbolic t s).units = units

lemma graphStep_symbolic_next (H round : ℕ) (node : GraphNode) (state : GraphState)
    (s : CodeState) (t : Tuning) :
    (codeSymbolic t (graphStep H round node state s).2).next =
      (codeSymbolic t s).next + nodeLength node := by
  cases node <;> simp only [graphStep, graphNodeCode, sendState, atom, join,
    state_bind_apply, state_pure_apply, codeSymbolic_emit, InstructionTemplate.instantiate,
    symbolicPerform, symbolicStore, nodeLength, Nat.add_assoc, Nat.reduceAdd]

lemma graphStep_support (H round : ℕ) (node : GraphNode) (state : GraphState)
    (s : CodeState) (t : Tuning) (n : ℕ) (raw sharp : ℕ → ℕ)
    (queries sharps units : Finset ℕ) (hn : s.next = (codeSymbolic t s).next)
    (h : Support t s n raw sharp queries sharps units)
    (hnames : ∀ worker source, node = .query worker source →
      raw n = s.next + 2 ∧ sharp n = s.next + 4) :
    Support t (graphStep H round node state s).2 (n + node.calls) raw sharp queries sharps units := by
  cases node with
  | query worker source =>
      have hh := graphQuery_sets H round worker source state s t hn
      have hname := hnames worker source rfl
      constructor
      · dsimp only [graphStep, state_bind_apply, state_pure_apply, GraphNode.calls]
        rw [hh.1, h.query_set, range_add_one, image_insert, hname.1]
        exact (union_insert _ _ _).symm
      · dsimp only [graphStep, state_bind_apply, state_pure_apply, GraphNode.calls]
        rw [hh.2.1, h.sharp_set, range_add_one, image_insert, hname.2]
        exact (union_insert _ _ _).symm
      · exact hh.2.2.trans h.unit_set
  | merge worker left right common =>
      have hh := graphMerge_trace H round worker left right common state s t
      exact ⟨hh.2.2.1.trans h.query_set, hh.2.2.2.1.trans h.sharp_set,
        hh.2.2.2.2.trans h.unit_set⟩

lemma graphFold_support (H round : ℕ) (nodes : List GraphNode) (state : GraphState)
    (s : CodeState) (t : Tuning) (labels : GraphLabels) (raw sharp : ℕ → ℕ)
    (queries sharps units : Finset ℕ) (hn : s.next = (codeSymbolic t s).next)
    (hl : labels.next = s.next) (h : Support t s labels.atoms raw sharp queries sharps units)
    (hnames : LabelsMatch raw sharp nodes labels) :
    let z := graphRun H round nodes state s
    Support t z.2 (labelFold nodes labels).atoms raw sharp queries sharps units := by
  induction nodes generalizing state s labels with
  | nil => exact h
  | cons node rest ih =>
      change Support t
        ((forIn (node :: rest) state (fun node state => ForInStep.yield <$> graphStep H round node state) :
          StateM CodeState GraphState) s).2 _ _ _ _ _ _
      rw [state_forIn_cons]
      have hname : ∀ worker source, node = .query worker source →
          raw labels.atoms = s.next + 2 ∧ sharp labels.atoms = s.next + 4 := by
        intro worker source he
        subst node
        simpa only [hl] using And.intro hnames.1 hnames.2.1
      have hrest : LabelsMatch raw sharp rest (labelStep node labels) := by
        cases node with
        | query worker source => exact hnames.2.2
        | merge worker left right common => exact hnames
      apply ih (graphStep H round node state s).1 (graphStep H round node state s).2
        (labelStep node labels)
      · rw [(graphStep_meta H round node state s).2.2, graphStep_symbolic_next, hn]
      · rw [labelStep_next, (graphStep_meta H round node state s).2.2, hl]
      · rw [labelStep_atoms]
        exact graphStep_support H round node state s t labels.atoms raw sharp queries sharps units hn h hname
      · exact hrest

structure IndexMap (start next n : ℕ) (index : ℕ → ℕ) : Prop where
  lower : ∀ i < n, start ≤ index i
  upper : ∀ i < n, index i < next
  strict : ∀ i j, i < j → j < n → index i < index j

lemma IndexMap.mono {start next n : ℕ} {index : ℕ → ℕ}
    (h : IndexMap start next n index) (newNext : ℕ) (hn : next ≤ newNext) :
    IndexMap start newNext n index :=
  ⟨h.lower, fun i hi => (h.upper i hi).trans_le hn, h.strict⟩

lemma IndexMap.append {start next n : ℕ} {index : ℕ → ℕ}
    (h : IndexMap start next n index) (value newNext : ℕ)
    (hs : start ≤ value) (hn : next ≤ value) (hv : value < newNext) :
    IndexMap start newNext (n + 1) (Function.update index n value) := by
  constructor
  · intro i hi
    by_cases he : i = n
    · subst i; simpa only [Function.update_self] using hs
    · rw [Function.update_of_ne he]; exact h.lower i (by omega)
  · intro i hi
    by_cases he : i = n
    · subst i; simpa only [Function.update_self] using hv
    · rw [Function.update_of_ne he]; exact (h.upper i (by omega)).trans_le (by omega)
  · intro i j hij hj
    have hin : i < n := by omega
    rw [Function.update_of_ne (ne_of_lt hin)]
    by_cases he : j = n
    · subst j; rw [Function.update_self]; exact (h.upper i hin).trans_le hn
    · rw [Function.update_of_ne he]; exact h.strict i j hij (by omega)

lemma IndexMap.injective {start next n : ℕ} {index : ℕ → ℕ}
    (h : IndexMap start next n index) (i j : ℕ) (hi : i < n) (hj : j < n)
    (he : index i = index j) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have := h.strict i j hij hj; omega
  · exact hij
  · have := h.strict j i hij hi; omega

def LabelInvariant (start : ℕ) (labels : GraphLabels) : Prop :=
  start ≤ labels.next ∧ IndexMap start labels.next labels.atoms labels.raw ∧
    IndexMap start labels.next labels.atoms labels.sharp

lemma labelInvariant_step (start : ℕ) (node : GraphNode) (labels : GraphLabels)
    (h : LabelInvariant start labels) : LabelInvariant start (labelStep node labels) := by
  have hs := h.1
  cases node with
  | query worker source =>
      refine ⟨by dsimp [labelStep]; omega, ?_, ?_⟩
      · exact h.2.1.append (labels.next + 2) (labels.next + 6) (by omega) (by omega) (by omega)
      · exact h.2.2.append (labels.next + 4) (labels.next + 6) (by omega) (by omega) (by omega)
  | merge worker left right common =>
      exact ⟨by dsimp [labelStep]; omega, h.2.1.mono (labels.next + 11) (by omega), h.2.2.mono (labels.next + 11) (by omega)⟩

lemma labelInvariant_fold (start : ℕ) (nodes : List GraphNode) (labels : GraphLabels)
    (h : LabelInvariant start labels) : LabelInvariant start (labelFold nodes labels) := by
  induction nodes generalizing labels with
  | nil => exact h
  | cons node rest ih => exact ih _ (labelInvariant_step start node labels h)

lemma labelFold_fresh (start : ℕ) (nodes : List GraphNode) :
    LabelInvariant start (labelFold nodes ⟨start, 0, fun _ => 0, fun _ => 0⟩) := by
  apply labelInvariant_fold
  refine ⟨le_rfl, ?_, ?_⟩
  all_goals constructor <;> simp

end LongTails.Proofs.BirchCausalRecords
