import LongTails.Proofs.BirchCollectionStructure
import LongTails.Proofs.BirchNonEuclideanRecords

namespace LongTails.Proofs.BirchCollectionReplay

open LongTails.Setups.BirchCollections
open LongTails.Algorithms.BirchCollections
open LongTails.Setups.BirchNonEuclidean (LinearValue SymbolicMemory symbolicPerform symbolicStore)
open LongTails.Proofs.BirchCollectionExecution
open LongTails.Proofs.BirchNonEuclideanRecords (symbolic_next symbolic_old_records)
open LongTails.Proofs.BirchCollectionStructure (Histories)

def RegisterBounds (s : TraceState) (r : Registers) : Prop :=
  (∀ j, j < s.nextState → r.point j < r.next) ∧
  (∀ j, j < s.nextState → r.momentum j < r.next) ∧
  (∀ j, j < s.nextRaw → r.raw j < r.next) ∧
  (∀ j, j < s.nextDirection → r.mean j < r.next) ∧
  (∀ j, j < s.nextDirection → r.estimator j < r.next) ∧
  (∀ j, j < s.nextDirection → r.sharp j < r.next)

lemma bounded_update (f : ℕ → ℕ) (M N v : ℕ)
    (hf : ∀ j, j < M → f j < N) (hv : v < N) :
    ∀ j, j < M + 1 → Function.update f M v j < N := by
  intro j hj
  by_cases he : j = M
  · simp [he, hv]
  · rw [Function.update_of_ne he]
    exact hf j (by omega)

lemma registerBounds_initial : RegisterBounds ({} : TraceState) ({} : Registers) := by
  simp [RegisterBounds]

lemma registerBounds_step (τ : ℝ) (s : TraceState) (r : Registers) (e : Event)
    (h : RegisterBounds s r) : RegisterBounds (step s e) (registerStep τ s r e) := by
  obtain ⟨hp, hm, hr, hav, he, hd⟩ := h
  cases e <;> dsimp [RegisterBounds, step, registerStep, eventCode]
  all_goals refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | apply bounded_update
    | skip
  all_goals first
    | omega
    | (intro j hj
       first
       | have hh := hp j hj; omega
       | have hh := hm j hj; omega
       | have hh := hr j hj; omega
       | have hh := hav j hj; omega
       | have hh := he j hj; omega
       | have hh := hd j hj; omega)

lemma registerBounds_fold (τ : ℝ) (events : List Event) (c : Compilation)
    (h : RegisterBounds c.trace c.registers) :
    RegisterBounds (events.foldl (compileStep τ) c).trace
      (events.foldl (compileStep τ) c).registers := by
  induction events generalizing c with
  | nil => exact h
  | cons e rest ih =>
      exact ih (compileStep τ c e) (registerBounds_step τ c.trace c.registers e h)

lemma registerBounds_compile (τ : ℝ) (events : List Event) :
    RegisterBounds (compile τ events).trace (compile τ events).registers :=
  registerBounds_fold τ events {} registerBounds_initial

noncomputable def symbolicStep (τ : ℝ) (s : TraceState) (r : Registers)
    (m : SymbolicMemory) (e : Event) : SymbolicMemory :=
  (eventCode τ s r e).foldl symbolicPerform m

noncomputable def rawBasis (q : ℕ) : LinearValue := (Finsupp.single q 1, 0)

noncomputable def sharpBasis (q : ℕ) : LinearValue := (0, Finsupp.single q 1)

noncomputable def collectionMean (s : TraceState) (r : Registers) (m : SymbolicMemory)
    (c : ℕ) : LinearValue :=
  (1 / ((s.collections c).size : ℝ)) •
    ((s.collections c).delivered.map (fun q => m.vectors (r.raw q))).sum

noncomputable def collectionEstimator (s : TraceState) (r : Registers) (m : SymbolicMemory)
    (c : ℕ) : LinearValue :=
  (s.collections c).refresh • collectionMean s r m c +
    (1 - (s.collections c).refresh) • m.vectors (r.momentum (s.collections c).source)

lemma symbolic_issue (τ : ℝ) (s : TraceState) (r : Registers) (m : SymbolicMemory)
    (c worker : ℕ) (hn : m.next = r.next) :
    let v := symbolicStep τ s r m (.issue c worker)
    v.vectors (r.next + 1) = rawBasis (r.next + 1) ∧
      v.queryPoints (r.next + 1) = m.points (r.point (s.collections c).source) ∧
      v.queries = insert (r.next + 1) m.queries := by
  simp [symbolicStep, eventCode, symbolicPerform, symbolicStore, hn, rawBasis]

lemma symbolic_finish (τ : ℝ) (s : TraceState) (r : Registers) (m : SymbolicMemory)
    (c : ℕ) (hn : m.next = r.next)
    (hm : r.momentum (s.collections c).source < r.next) :
    let v := symbolicStep τ s r m (.finish c)
    v.vectors r.next = collectionMean s r m c ∧
      v.vectors (r.next + 1) = collectionEstimator s r m c ∧
      v.sharpInputs (r.next + 2) = collectionEstimator s r m c ∧
      v.vectors (r.next + 2) = sharpBasis (r.next + 2) ∧
      v.points (r.next + 3) = m.points (r.point (s.collections c).source) +
        (τ * (s.collections c).movement) • sharpBasis (r.next + 2) := by
  have hne : r.momentum (s.collections c).source ≠ r.next := ne_of_lt hm
  have hsum : (((s.collections c).delivered.map
      (fun q => (1 / ((s.collections c).size : ℝ), r.raw q))).map
      (fun t => t.1 • m.vectors t.2)).sum = collectionMean s r m c := by
    simp [collectionMean, List.map_map, Function.comp_def, List.smul_sum]
  simp only [List.map_map, Function.comp_def, one_div] at hsum
  simp [symbolicStep, eventCode, symbolicPerform, symbolicStore, hn, hsum, hne,
    collectionEstimator, sharpBasis, Nat.add_assoc, Function.comp_def]

lemma symbolic_merge (τ : ℝ) (s : TraceState) (r : Registers) (m : SymbolicMemory)
    (worker left right common : ℕ) (hn : m.next = r.next)
    (hl : r.momentum left < r.next) (hr : r.momentum right < r.next)
    (hc : r.momentum common < r.next) :
    let v := symbolicStep τ s r m (.merge worker left right common)
    v.points (r.next + 7) = m.points (r.point left) + m.points (r.point right) -
      m.points (r.point common) ∧
      v.vectors (r.next + 8) = m.vectors (r.momentum left) + m.vectors (r.momentum right) -
        m.vectors (r.momentum common) := by
  have hl6 : r.momentum left ≠ r.next + 6 := by omega
  have hr6 : r.momentum right ≠ r.next + 6 := by omega
  have hc6 : r.momentum common ≠ r.next + 6 := by omega
  simp [symbolicStep, eventCode, symbolicPerform, symbolicStore, hn, hl6, hr6, hc6,
    sub_eq_add_neg, add_assoc]
  exact neg_one_smul ℝ (m.vectors (r.momentum common))

lemma symbolic_old_values (code : List LongTails.Setups.BirchNonEuclidean.Instruction)
    (m : SymbolicMemory) (j : ℕ) (hj : j < m.next) :
    (code.foldl symbolicPerform m).points j = m.points j ∧
      (code.foldl symbolicPerform m).vectors j = m.vectors j := by
  induction code generalizing m with
  | nil => exact ⟨rfl, rfl⟩
  | cons i rest ih =>
      have hnext : j < (symbolicPerform m i).next := by
        cases i <;> simp [symbolicPerform, symbolicStore] <;> omega
      have hne : j ≠ m.next := ne_of_lt hj
      rw [List.foldl_cons]
      have hh := ih (symbolicPerform m i) hnext
      cases i <;> simpa [symbolicPerform, symbolicStore, hne] using hh

lemma symbolicStep_next (τ : ℝ) (s : TraceState) (r : Registers) (m : SymbolicMemory)
    (e : Event) (hn : m.next = r.next) :
    (symbolicStep τ s r m e).next = (registerStep τ s r e).next := by
  rw [registerStep_next, symbolicStep, symbolic_next, hn]

lemma symbolicStep_units (τ : ℝ) (s : TraceState) (r : Registers) (m : SymbolicMemory)
    (e : Event) : (symbolicStep τ s r m e).units = m.units := by
  cases e <;> simp [symbolicStep, eventCode, symbolicPerform, symbolicStore]

lemma registerStep_old_state (τ : ℝ) (s : TraceState) (r : Registers) (e : Event)
    (j : ℕ) (hj : j < s.nextState) :
    (registerStep τ s r e).point j = r.point j ∧
      (registerStep τ s r e).momentum j = r.momentum j := by
  have hne := ne_of_lt hj
  cases e <;> simp [registerStep, hne]

lemma registerStep_old_raw (τ : ℝ) (s : TraceState) (r : Registers) (e : Event)
    (j : ℕ) (hj : j < s.nextRaw) : (registerStep τ s r e).raw j = r.raw j := by
  have hne := ne_of_lt hj
  cases e <;> simp [registerStep, hne]

lemma registerStep_old_direction (τ : ℝ) (s : TraceState) (r : Registers) (e : Event)
    (j : ℕ) (hj : j < s.nextDirection) :
    (registerStep τ s r e).mean j = r.mean j ∧
      (registerStep τ s r e).estimator j = r.estimator j ∧
      (registerStep τ s r e).sharp j = r.sharp j := by
  have hne := ne_of_lt hj
  cases e <;> simp [registerStep, hne]

structure Preserves (s : TraceState) (r r' : Registers) (m m' : SymbolicMemory) : Prop where
  point : ∀ j, j < s.nextState → m'.points (r'.point j) = m.points (r.point j)
  momentum : ∀ j, j < s.nextState → m'.vectors (r'.momentum j) = m.vectors (r.momentum j)
  raw : ∀ j, j < s.nextRaw → m'.vectors (r'.raw j) = m.vectors (r.raw j)
  query : ∀ j, j < s.nextRaw → m'.queryPoints (r'.raw j) = m.queryPoints (r.raw j)
  mean : ∀ j, j < s.nextDirection → m'.vectors (r'.mean j) = m.vectors (r.mean j)
  estimator : ∀ j, j < s.nextDirection →
    m'.vectors (r'.estimator j) = m.vectors (r.estimator j)
  sharp : ∀ j, j < s.nextDirection → m'.vectors (r'.sharp j) = m.vectors (r.sharp j)
  input : ∀ j, j < s.nextDirection →
    m'.sharpInputs (r'.sharp j) = m.sharpInputs (r.sharp j)

lemma symbolicStep_preserves (τ : ℝ) (s : TraceState) (r : Registers)
    (m : SymbolicMemory) (e : Event) (hb : RegisterBounds s r) (hn : m.next = r.next) :
    Preserves s r (registerStep τ s r e) m (symbolicStep τ s r m e) := by
  have hp := registerStep_old_state τ s r e
  have hr := registerStep_old_raw τ s r e
  have hd := registerStep_old_direction τ s r e
  have hv (j : ℕ) (hj : j < r.next) :=
    symbolic_old_values (eventCode τ s r e) m j (by simpa [hn] using hj)
  have hc (j : ℕ) (hj : j < r.next) :=
    symbolic_old_records (eventCode τ s r e) m j (by simpa [hn] using hj)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj; rw [(hp j hj).1]; exact (hv _ (hb.1 j hj)).1
  · intro j hj; rw [(hp j hj).2]; exact (hv _ (hb.2.1 j hj)).2
  · intro j hj; rw [hr j hj]; exact (hv _ (hb.2.2.1 j hj)).2
  · intro j hj; rw [hr j hj]; exact (hc _ (hb.2.2.1 j hj)).1
  · intro j hj; rw [(hd j hj).1]; exact (hv _ (hb.2.2.2.1 j hj)).2
  · intro j hj; rw [(hd j hj).2.1]; exact (hv _ (hb.2.2.2.2.1 j hj)).2
  · intro j hj; rw [(hd j hj).2.2]; exact (hv _ (hb.2.2.2.2.2 j hj)).2
  · intro j hj; rw [(hd j hj).2.2]; exact (hc _ (hb.2.2.2.2.2 j hj)).2

noncomputable def pointIncrement (τ : ℝ) (s : TraceState) (r : Registers)
    (m : SymbolicMemory) (j : ℕ) : LinearValue :=
  (τ * (s.directions j).movement) • m.vectors (r.sharp j)

noncomputable def momentumIncrement (s : TraceState) (r : Registers)
    (m : SymbolicMemory) (j : ℕ) : LinearValue :=
  m.vectors (r.estimator j) - m.vectors (r.momentum (s.directions j).source)

structure StateValues (τ : ℝ) (s : TraceState) (r : Registers) (m : SymbolicMemory) : Prop where
  point : ∀ a, a < s.nextState → m.points (r.point a) =
    ∑ j ∈ (s.states a).history, pointIncrement τ s r m j
  momentum : ∀ a, a < s.nextState → m.vectors (r.momentum a) =
    ∑ j ∈ (s.states a).history, momentumIncrement s r m j

lemma pointIncrement_preserved (τ : ℝ) (s : TraceState) (r : Registers)
    (m : SymbolicMemory) (e : Event) (hp : Preserves s r (registerStep τ s r e)
      m (symbolicStep τ s r m e)) (j : ℕ) (hj : j < s.nextDirection) :
    pointIncrement τ (step s e) (registerStep τ s r e) (symbolicStep τ s r m e) j =
      pointIncrement τ s r m j := by
  unfold pointIncrement
  rw [step_old_direction s e j hj, hp.sharp j hj]

lemma momentumIncrement_preserved (τ : ℝ) (s : TraceState) (r : Registers)
    (m : SymbolicMemory) (e : Event) (hp : Preserves s r (registerStep τ s r e)
      m (symbolicStep τ s r m e)) (hh : Histories s) (j : ℕ) (hj : j < s.nextDirection) :
    momentumIncrement (step s e) (registerStep τ s r e) (symbolicStep τ s r m e) j =
      momentumIncrement s r m j := by
  unfold momentumIncrement
  rw [step_old_direction s e j hj, hp.estimator j hj, hp.momentum _ (hh.direction j hj).1]

lemma stateValues_initial (τ : ℝ) : StateValues τ {} {} {} := by
  constructor <;> simp [pointIncrement, momentumIncrement]

lemma stateValues_step (τ : ℝ) (workers : ℕ) (s : TraceState) (r : Registers)
    (m : SymbolicMemory) (e : Event) (hb : RegisterBounds s r) (hn : m.next = r.next)
    (hh : Histories s) (hv : StateValues τ s r m) (he : e.Valid workers s) :
    StateValues τ (step s e) (registerStep τ s r e) (symbolicStep τ s r m e) := by
  let r' := registerStep τ s r e
  let m' := symbolicStep τ s r m e
  have hp := symbolicStep_preserves τ s r m e hb hn
  have hps (a : ℕ) (ha : a < s.nextState) :
      (∑ j ∈ (s.states a).history, pointIncrement τ (step s e) r' m' j) =
        m.points (r.point a) := by
    rw [hv.point a ha]
    apply Finset.sum_congr rfl
    intro j hj
    exact pointIncrement_preserved τ s r m e hp j (Finset.mem_range.mp (hh.state_past a ha hj))
  have hms (a : ℕ) (ha : a < s.nextState) :
      (∑ j ∈ (s.states a).history, momentumIncrement (step s e) r' m' j) =
        m.vectors (r.momentum a) := by
    rw [hv.momentum a ha]
    apply Finset.sum_congr rfl
    intro j hj
    exact momentumIncrement_preserved τ s r m e hp hh j
      (Finset.mem_range.mp (hh.state_past a ha hj))
  dsimp only [r', m'] at hps hms
  constructor
  · intro a ha
    by_cases hoa : a < s.nextState
    · rw [step_old_state s e a hoa, hp.point a hoa]
      exact (hps a hoa).symm
    · cases e <;> simp only [step] at ha ⊢
      all_goals try omega
      · rename_i c
        simp only [step] at hps hms
        have hae : a = s.nextState := by omega
        have hs := hh.source c he.1
        have hnot : s.nextDirection ∉ (s.states (s.collections c).source).history := by
          intro hmem
          exact Nat.lt_irrefl _ (Finset.mem_range.mp (hh.state_past _ hs hmem))
        rw [hae, Function.update_self, Finset.sum_insert hnot]
        have hsum := hps _ hs
        have hf := symbolic_finish τ s r m c hn (hb.2.1 _ hs)
        rw [show (registerStep τ s r (.finish c)).point s.nextState = r.next + 3 by
          simp [registerStep]]
        rw [hsum]
        rw [hf.2.2.2.2]
        simp only [pointIncrement, Function.update_self, registerStep]
        rw [hf.2.2.2.1]
        exact add_comm _ _
      · rename_i worker left right common
        simp only [step] at hps hms
        have hae : a = s.nextState := by omega
        rw [hae, Function.update_self]
        have hf := symbolic_merge τ s r m worker left right common hn
          (hb.2.1 left he.2.1) (hb.2.1 right he.2.2.1) (hb.2.1 common he.2.2.2.1)
        rw [show (registerStep τ s r (.merge worker left right common)).point s.nextState =
          r.next + 7 by simp [registerStep]]
        rw [hf.1]
        have hu := LongTails.Proofs.BirchCausalMerges.aggregate_union
          (s.states left).history (s.states right).history (0 : LinearValue)
          (pointIncrement τ (step s (.merge worker left right common))
            (registerStep τ s r (.merge worker left right common))
            (symbolicStep τ s r m (.merge worker left right common)))
        simp only [zero_add, step] at hu
        rw [hu]
        rw [hps left he.2.1, hps right he.2.2.1, ← he.2.2.2.2, hps common he.2.2.2.1]
  · intro a ha
    by_cases hoa : a < s.nextState
    · rw [step_old_state s e a hoa, hp.momentum a hoa]
      exact (hms a hoa).symm
    · cases e <;> simp only [step] at ha ⊢
      all_goals try omega
      · rename_i c
        simp only [step] at hps hms
        have hae : a = s.nextState := by omega
        have hs := hh.source c he.1
        have hnot : s.nextDirection ∉ (s.states (s.collections c).source).history := by
          intro hmem
          exact Nat.lt_irrefl _ (Finset.mem_range.mp (hh.state_past _ hs hmem))
        rw [hae, Function.update_self, Finset.sum_insert hnot, hms _ hs]
        rw [show (registerStep τ s r (.finish c)).momentum s.nextState = r.next + 1 by
          simp [registerStep]]
        have hsource := hp.momentum _ hs
        simp only [momentumIncrement, Function.update_self]
        rw [hsource]
        simp [registerStep]
      · rename_i worker left right common
        simp only [step] at hps hms
        have hae : a = s.nextState := by omega
        rw [hae, Function.update_self]
        have hf := symbolic_merge τ s r m worker left right common hn
          (hb.2.1 left he.2.1) (hb.2.1 right he.2.2.1) (hb.2.1 common he.2.2.2.1)
        rw [show (registerStep τ s r (.merge worker left right common)).momentum s.nextState =
          r.next + 8 by simp [registerStep]]
        rw [hf.2]
        have hu := LongTails.Proofs.BirchCausalMerges.aggregate_union
          (s.states left).history (s.states right).history (0 : LinearValue)
          (momentumIncrement (step s (.merge worker left right common))
            (registerStep τ s r (.merge worker left right common))
            (symbolicStep τ s r m (.merge worker left right common)))
        simp only [zero_add, step] at hu
        rw [hu]
        rw [hms left he.2.1, hms right he.2.2.1, ← he.2.2.2.2, hms common he.2.2.2.1]

lemma stateValues_fold (τ : ℝ) (workers : ℕ) (events : List Event) (c : Compilation)
    (hb : RegisterBounds c.trace c.registers)
    (hn : (c.code.foldl symbolicPerform {}).next = c.registers.next)
    (hh : Histories c.trace)
    (hv : StateValues τ c.trace c.registers (c.code.foldl symbolicPerform {}))
    (he : ValidFrom workers c.trace events) :
    let z := events.foldl (compileStep τ) c
    StateValues τ z.trace z.registers (z.code.foldl symbolicPerform {}) := by
  induction events generalizing c with
  | nil => exact hv
  | cons e rest ih =>
      apply ih (compileStep τ c e)
      · exact registerBounds_step τ c.trace c.registers e hb
      · simpa only [compileStep, List.foldl_append, symbolicStep] using
          symbolicStep_next τ c.trace c.registers (c.code.foldl symbolicPerform {}) e hn
      · exact LongTails.Proofs.BirchCollectionStructure.histories_step workers c.trace e hh he.1
      · simpa only [compileStep, List.foldl_append, symbolicStep] using
          stateValues_step τ workers c.trace c.registers (c.code.foldl symbolicPerform {})
            e hb hn hh hv he.1
      · exact he.2

lemma stateValues_compile (τ : ℝ) (workers : ℕ) (events : List Event)
    (he : ValidFrom workers {} events) :
    let z := compile τ events
    StateValues τ z.trace z.registers (z.code.foldl symbolicPerform {}) :=
  stateValues_fold τ workers events {} registerBounds_initial rfl
    LongTails.Proofs.BirchCollectionStructure.histories_initial (stateValues_initial τ) he

structure RawValues (s : TraceState) (r : Registers) (m : SymbolicMemory) : Prop where
  value : ∀ q, q < s.nextRaw → m.vectors (r.raw q) = rawBasis (r.raw q)
  query : ∀ q, q < s.nextRaw → m.queryPoints (r.raw q) =
    m.points (r.point (s.collections (s.raws q).collection).source)

lemma rawValues_initial : RawValues {} {} {} := by constructor <;> simp

lemma rawValues_step (τ : ℝ) (workers : ℕ) (s : TraceState) (r : Registers)
    (m : SymbolicMemory) (e : Event) (hb : RegisterBounds s r) (hn : m.next = r.next)
    (hh : Histories s) (hl : LongTails.Proofs.BirchCollectionStructure.RawLedger s)
    (hv : RawValues s r m) (he : e.Valid workers s) :
    RawValues (step s e) (registerStep τ s r e) (symbolicStep τ s r m e) := by
  have hp := symbolicStep_preserves τ s r m e hb hn
  constructor
  · intro q hq
    by_cases hold : q < s.nextRaw
    · rw [hp.raw q hold, hv.value q hold, registerStep_old_raw τ s r e q hold]
    · cases e <;> simp only [step] at hq ⊢
      all_goals try omega
      rename_i c worker
      have hqe : q = s.nextRaw := by omega
      subst q
      simpa only [registerStep, Function.update_self] using
        (symbolic_issue τ s r m c worker hn).1
  · intro q hq
    by_cases hold : q < s.nextRaw
    · rw [hp.query q hold, hv.query q hold, step_old_raw s e q hold,
        LongTails.Proofs.BirchCollectionStructure.step_old_collection_source s e
          (s.raws q).collection (hl.assignment q hold),
        hp.point _ (hh.source _ (hl.assignment q hold))]
    · cases e <;> simp only [step] at hq ⊢
      all_goals try omega
      rename_i c worker
      have hqe : q = s.nextRaw := by omega
      subst q
      simp only [Function.update_self]
      rw [show (registerStep τ s r (.issue c worker)).raw s.nextRaw = r.next + 1 by
        simp [registerStep]]
      rw [(symbolic_issue τ s r m c worker hn).2.1]
      exact (hp.point _ (hh.source c he.1)).symm

lemma rawValues_fold (τ : ℝ) (workers : ℕ) (events : List Event) (c : Compilation)
    (hb : RegisterBounds c.trace c.registers)
    (hn : (c.code.foldl symbolicPerform {}).next = c.registers.next)
    (hh : Histories c.trace) (hl : LongTails.Proofs.BirchCollectionStructure.RawLedger c.trace)
    (hv : RawValues c.trace c.registers (c.code.foldl symbolicPerform {}))
    (he : ValidFrom workers c.trace events) :
    let z := events.foldl (compileStep τ) c
    RawValues z.trace z.registers (z.code.foldl symbolicPerform {}) := by
  induction events generalizing c with
  | nil => exact hv
  | cons e rest ih =>
      apply ih (compileStep τ c e)
      · exact registerBounds_step τ c.trace c.registers e hb
      · simpa only [compileStep, List.foldl_append, symbolicStep] using
          symbolicStep_next τ c.trace c.registers (c.code.foldl symbolicPerform {}) e hn
      · exact LongTails.Proofs.BirchCollectionStructure.histories_step workers c.trace e hh he.1
      · exact LongTails.Proofs.BirchCollectionStructure.rawLedger_step workers c.trace e hl he.1
      · simpa only [compileStep, List.foldl_append, symbolicStep] using
          rawValues_step τ workers c.trace c.registers (c.code.foldl symbolicPerform {})
            e hb hn hh hl hv he.1
      · exact he.2

lemma rawValues_compile (τ : ℝ) (workers : ℕ) (events : List Event)
    (he : ValidFrom workers {} events) :
    let z := compile τ events
    RawValues z.trace z.registers (z.code.foldl symbolicPerform {}) :=
  rawValues_fold τ workers events {} registerBounds_initial rfl
    LongTails.Proofs.BirchCollectionStructure.histories_initial
    LongTails.Proofs.BirchCollectionStructure.rawLedger_initial rawValues_initial he

noncomputable def directionAverage (s : TraceState) (r : Registers) (m : SymbolicMemory)
    (j : ℕ) : LinearValue :=
  (1 / ((s.directions j).raw.length : ℝ)) •
    ((s.directions j).raw.map (fun q => m.vectors (r.raw q))).sum

structure DirectionValues (s : TraceState) (r : Registers) (m : SymbolicMemory) : Prop where
  mean : ∀ j, j < s.nextDirection → m.vectors (r.mean j) = directionAverage s r m j
  estimator : ∀ j, j < s.nextDirection → m.vectors (r.estimator j) =
    (s.directions j).refresh • m.vectors (r.mean j) +
      (1 - (s.directions j).refresh) • m.vectors (r.momentum (s.directions j).source)
  sharp : ∀ j, j < s.nextDirection → m.vectors (r.sharp j) = sharpBasis (r.sharp j)
  input : ∀ j, j < s.nextDirection → m.sharpInputs (r.sharp j) = m.vectors (r.estimator j)

lemma directionAverage_preserved (τ : ℝ) (s : TraceState) (r : Registers)
    (m : SymbolicMemory) (e : Event) (hp : Preserves s r (registerStep τ s r e)
      m (symbolicStep τ s r m e))
    (hl : LongTails.Proofs.BirchCollectionStructure.RawLedger s)
    (hc : LongTails.Proofs.BirchCollectionStructure.CompletedLedger s)
    (j : ℕ) (hj : j < s.nextDirection) :
    directionAverage (step s e) (registerStep τ s r e) (symbolicStep τ s r m e) j =
      directionAverage s r m j := by
  unfold directionAverage
  rw [step_old_direction s e j hj]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro q hq
  exact hp.raw q ((LongTails.Proofs.BirchCollectionStructure.completed_raw s hl hc j hj).2 q hq).1

lemma directionValues_initial : DirectionValues {} {} {} := by constructor <;> simp

lemma directionValues_step (τ : ℝ) (workers : ℕ) (s : TraceState) (r : Registers)
    (m : SymbolicMemory) (e : Event) (hb : RegisterBounds s r) (hn : m.next = r.next)
    (hh : Histories s) (hl : LongTails.Proofs.BirchCollectionStructure.RawLedger s)
    (hc : LongTails.Proofs.BirchCollectionStructure.CompletedLedger s)
    (hv : DirectionValues s r m) (he : e.Valid workers s) :
    DirectionValues (step s e) (registerStep τ s r e) (symbolicStep τ s r m e) := by
  have hp := symbolicStep_preserves τ s r m e hb hn
  have hold (j : ℕ) (hj : j < s.nextDirection) :
      (symbolicStep τ s r m e).vectors ((registerStep τ s r e).mean j) =
        directionAverage (step s e) (registerStep τ s r e) (symbolicStep τ s r m e) j ∧
      (symbolicStep τ s r m e).vectors ((registerStep τ s r e).estimator j) =
        ((step s e).directions j).refresh •
          (symbolicStep τ s r m e).vectors ((registerStep τ s r e).mean j) +
        (1 - ((step s e).directions j).refresh) •
          (symbolicStep τ s r m e).vectors
            ((registerStep τ s r e).momentum ((step s e).directions j).source) ∧
      (symbolicStep τ s r m e).vectors ((registerStep τ s r e).sharp j) =
        sharpBasis ((registerStep τ s r e).sharp j) ∧
      (symbolicStep τ s r m e).sharpInputs ((registerStep τ s r e).sharp j) =
        (symbolicStep τ s r m e).vectors ((registerStep τ s r e).estimator j) := by
    rw [hp.mean j hj, hp.estimator j hj, hp.sharp j hj, hp.input j hj,
      directionAverage_preserved τ s r m e hp hl hc j hj, step_old_direction s e j hj,
      hp.momentum _ (hh.direction j hj).1, (registerStep_old_direction τ s r e j hj).2.2]
    exact ⟨hv.mean j hj, hv.estimator j hj, hv.sharp j hj, hv.input j hj⟩
  have hnew (c : ℕ) (hec : (.finish c : Event).Valid workers s) :
      let r' := registerStep τ s r (.finish c)
      let m' := symbolicStep τ s r m (.finish c)
      let s' := step s (.finish c)
      m'.vectors (r'.mean s.nextDirection) = directionAverage s' r' m' s.nextDirection ∧
      m'.vectors (r'.estimator s.nextDirection) =
        (s'.directions s.nextDirection).refresh • m'.vectors (r'.mean s.nextDirection) +
        (1 - (s'.directions s.nextDirection).refresh) •
          m'.vectors (r'.momentum (s'.directions s.nextDirection).source) ∧
      m'.vectors (r'.sharp s.nextDirection) = sharpBasis (r'.sharp s.nextDirection) ∧
      m'.sharpInputs (r'.sharp s.nextDirection) = m'.vectors (r'.estimator s.nextDirection) := by
    have hs := hh.source c hec.1
    have hf := symbolic_finish τ s r m c hn (hb.2.1 _ hs)
    have hpres := symbolicStep_preserves τ s r m (.finish c) hb hn
    have hav : directionAverage (step s (.finish c)) (registerStep τ s r (.finish c))
        (symbolicStep τ s r m (.finish c)) s.nextDirection = collectionMean s r m c := by
      simp only [directionAverage, step, Function.update_self, hec.2.2, collectionMean]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro q hq
      exact hpres.raw q ((hl.delivered c hec.1).2 q hq).1
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hav]
      simpa only [registerStep, Function.update_self] using hf.1
    · simp only [step, Function.update_self]
      rw [hpres.momentum _ hs]
      simp only [registerStep, Function.update_self, hf.1, hf.2.1]
      rfl
    · simpa only [registerStep, Function.update_self] using hf.2.2.2.1
    · simpa only [registerStep, Function.update_self, hf.2.1] using hf.2.2.1
  constructor
  all_goals
    intro j hj
    by_cases hjold : j < s.nextDirection
    · first
      | exact (hold j hjold).1
      | exact (hold j hjold).2.1
      | exact (hold j hjold).2.2.1
      | exact (hold j hjold).2.2.2
    · cases e <;> simp only [step] at hj
      all_goals try omega
      rename_i c
      have hje : j = s.nextDirection := by omega
      subst j
      first
      | exact (hnew c he).1
      | exact (hnew c he).2.1
      | exact (hnew c he).2.2.1
      | exact (hnew c he).2.2.2

lemma directionValues_fold (τ : ℝ) (workers : ℕ) (events : List Event) (c : Compilation)
    (hb : RegisterBounds c.trace c.registers)
    (hn : (c.code.foldl symbolicPerform {}).next = c.registers.next)
    (hh : Histories c.trace) (hl : LongTails.Proofs.BirchCollectionStructure.RawLedger c.trace)
    (hc : LongTails.Proofs.BirchCollectionStructure.CompletedLedger c.trace)
    (hv : DirectionValues c.trace c.registers (c.code.foldl symbolicPerform {}))
    (he : ValidFrom workers c.trace events) :
    let z := events.foldl (compileStep τ) c
    DirectionValues z.trace z.registers (z.code.foldl symbolicPerform {}) := by
  induction events generalizing c with
  | nil => exact hv
  | cons e rest ih =>
      apply ih (compileStep τ c e)
      · exact registerBounds_step τ c.trace c.registers e hb
      · simpa only [compileStep, List.foldl_append, symbolicStep] using
          symbolicStep_next τ c.trace c.registers (c.code.foldl symbolicPerform {}) e hn
      · exact LongTails.Proofs.BirchCollectionStructure.histories_step workers c.trace e hh he.1
      · exact LongTails.Proofs.BirchCollectionStructure.rawLedger_step workers c.trace e hl he.1
      · exact LongTails.Proofs.BirchCollectionStructure.completedLedger_step workers c.trace e hc he.1
      · simpa only [compileStep, List.foldl_append, symbolicStep] using
          directionValues_step τ workers c.trace c.registers (c.code.foldl symbolicPerform {})
            e hb hn hh hl hc hv he.1
      · exact he.2

lemma directionValues_compile (τ : ℝ) (workers : ℕ) (events : List Event)
    (he : ValidFrom workers {} events) :
    let z := compile τ events
    DirectionValues z.trace z.registers (z.code.foldl symbolicPerform {}) :=
  directionValues_fold τ workers events {} registerBounds_initial rfl
    LongTails.Proofs.BirchCollectionStructure.histories_initial
    LongTails.Proofs.BirchCollectionStructure.rawLedger_initial
    LongTails.Proofs.BirchCollectionStructure.completedLedger_initial directionValues_initial he

lemma image_range_update (f : ℕ → ℕ) (N v : ℕ) :
    (Finset.range (N + 1)).image (Function.update f N v) =
      insert v ((Finset.range N).image f) := by
  rw [Finset.range_add_one, Finset.image_insert, Function.update_self]
  congr 1
  apply Finset.image_congr
  intro j hj
  exact Function.update_of_ne (ne_of_lt (Finset.mem_range.mp hj)) _ _

structure LabelSets (s : TraceState) (r : Registers) (m : SymbolicMemory) : Prop where
  queries : m.queries = (Finset.range s.nextRaw).image r.raw
  sharps : m.sharps = (Finset.range s.nextDirection).image r.sharp
  units : m.units = ∅

lemma labelSets_initial : LabelSets {} {} {} := by constructor <;> rfl

lemma labelSets_step (τ : ℝ) (s : TraceState) (r : Registers) (m : SymbolicMemory)
    (e : Event) (hn : m.next = r.next) (h : LabelSets s r m) :
    LabelSets (step s e) (registerStep τ s r e) (symbolicStep τ s r m e) := by
  constructor
  · cases e <;> simp [symbolicStep, eventCode, symbolicPerform, symbolicStore,
      step, registerStep, hn, h.queries, image_range_update]
  · cases e <;> simp [symbolicStep, eventCode, symbolicPerform, symbolicStore,
      step, registerStep, hn, h.sharps, image_range_update, Nat.add_assoc]
  · rw [symbolicStep_units, h.units]

lemma labelSets_fold (τ : ℝ) (events : List Event) (c : Compilation)
    (hn : (c.code.foldl symbolicPerform {}).next = c.registers.next)
    (h : LabelSets c.trace c.registers (c.code.foldl symbolicPerform {})) :
    let z := events.foldl (compileStep τ) c
    LabelSets z.trace z.registers (z.code.foldl symbolicPerform {}) := by
  induction events generalizing c with
  | nil => exact h
  | cons e rest ih =>
      apply ih (compileStep τ c e)
      · simpa only [compileStep, List.foldl_append, symbolicStep] using
          symbolicStep_next τ c.trace c.registers (c.code.foldl symbolicPerform {}) e hn
      · simpa only [compileStep, List.foldl_append, symbolicStep] using
          labelSets_step τ c.trace c.registers (c.code.foldl symbolicPerform {}) e hn h

lemma labelSets_compile (τ : ℝ) (events : List Event) :
    let z := compile τ events
    LabelSets z.trace z.registers (z.code.foldl symbolicPerform {}) :=
  labelSets_fold τ events {} rfl labelSets_initial

lemma injOn_range_update (f : ℕ → ℕ) (N v : ℕ)
    (hinj : Set.InjOn f (Finset.range N)) (hv : ∀ j, j < N → f j < v) :
    Set.InjOn (Function.update f N v) (Finset.range (N + 1)) := by
  intro i hi j hj he
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  by_cases hie : i = N
  · subst i
    by_cases hje : j = N
    · exact hje.symm
    · simp only [Function.update_self, Function.update_of_ne hje] at he
      have hh := hv j (by omega)
      omega
  · by_cases hje : j = N
    · subst j
      simp only [Function.update_self, Function.update_of_ne hie] at he
      have hh := hv i (by omega)
      omega
    · simp only [Function.update_of_ne hie, Function.update_of_ne hje] at he
      exact hinj (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by omega)) he

structure LabelInjective (s : TraceState) (r : Registers) : Prop where
  raw : Set.InjOn r.raw (Finset.range s.nextRaw)
  sharp : Set.InjOn r.sharp (Finset.range s.nextDirection)

lemma labelInjective_initial : LabelInjective {} {} := by constructor <;> simp

lemma labelInjective_step (τ : ℝ) (s : TraceState) (r : Registers) (e : Event)
    (hb : RegisterBounds s r) (h : LabelInjective s r) :
    LabelInjective (step s e) (registerStep τ s r e) := by
  constructor
  · cases e <;> simp only [step, registerStep]
    all_goals first | exact h.raw | skip
    apply injOn_range_update _ _ _ h.raw
    intro j hj
    have hh := hb.2.2.1 j hj
    omega
  · cases e <;> simp only [step, registerStep]
    all_goals first | exact h.sharp | skip
    apply injOn_range_update _ _ _ h.sharp
    intro j hj
    have hh := hb.2.2.2.2.2 j hj
    omega

lemma labelInjective_fold (τ : ℝ) (events : List Event) (c : Compilation)
    (hb : RegisterBounds c.trace c.registers) (h : LabelInjective c.trace c.registers) :
    let z := events.foldl (compileStep τ) c
    LabelInjective z.trace z.registers := by
  induction events generalizing c with
  | nil => exact h
  | cons e rest ih =>
      exact ih (compileStep τ c e) (registerBounds_step τ c.trace c.registers e hb)
        (labelInjective_step τ c.trace c.registers e hb h)

lemma labelInjective_compile (τ : ℝ) (events : List Event) :
    let z := compile τ events
    LabelInjective z.trace z.registers :=
  labelInjective_fold τ events {} registerBounds_initial labelInjective_initial

end LongTails.Proofs.BirchCollectionReplay
