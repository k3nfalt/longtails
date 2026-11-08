import LongTails.Setups.BirchNonEuclidean
import LongTails.Proofs.BirchNonEuclideanExecution

namespace LongTails.Proofs.BirchNonEuclideanSymbolic

open OracleTemplate.Rennala (Point)
open LongTails.Setups.UscgConstant (dualNorm)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Proofs.BirchNonEuclideanExecution (interpret execute_interpret)

def Represents (p : Params) (E : LinearValue →ₗ[ℝ] Point p.d)
    (s : SymbolicMemory) (m : Memory p.d) : Prop :=
  s.next = m.next ∧ (∀ j, m.points j = p.x0 + E (s.points j)) ∧
    ∀ j, m.vectors j = E (s.vectors j)

lemma represents_initial (p : Params) (E : LinearValue →ₗ[ℝ] Point p.d) :
    Represents p E {} (initialMemory p) := by
  simp [Represents, initialMemory]

lemma represents_store (p : Params) (E : LinearValue →ₗ[ℝ] Point p.d)
    (s : SymbolicMemory) (m : Memory p.d) (h : Represents p E s m)
    (v : LinearValue) (deps : Finset ℕ) :
    Represents p E (symbolicStore s v) (storeVector m (E v) deps) := by
  rcases h with ⟨hn, hp, hv⟩
  refine ⟨by change s.next + 1 = m.next + 1; omega, hp, ?_⟩
  intro j
  by_cases hj : j = m.next
  · simp [symbolicStore, storeVector, hn, hj]
  · simp [symbolicStore, storeVector, hn, hj, hv]

lemma represents_perform (p : Params) (lmo : Point p.d → Point p.d)
    (E : LinearValue →ₗ[ℝ] Point p.d) (s : SymbolicMemory) (m : Memory p.d)
    (h : Represents p E s m) (i : Instruction) (reply : Point p.d)
    (hq : ∀ w x, i = Instruction.query w x → E (Finsupp.single s.next 1, 0) = reply)
    (hu : ∀ w v, i = Instruction.lmo w v → E (0, Finsupp.single s.next 1) = lmo (m.vectors v))
    (hs : ∀ w v, i = Instruction.sharp w v → E (0, Finsupp.single s.next 1) =
      dualNorm p.N (m.vectors v) • lmo (m.vectors v)) :
    Represents p E (symbolicPerform s i) (perform p lmo m i reply) := by
  have hh := h
  obtain ⟨hn, hp, hv⟩ := hh
  cases i with
  | query w x =>
      simpa [symbolicPerform, perform, Represents, hq w x rfl] using
        represents_store p E s m h (Finsupp.single s.next 1, 0)
          (insert m.replies (m.pointSamples x))
  | mix w terms =>
      have he : E ((terms.map (fun t => t.1 • s.vectors t.2)).sum) =
          (terms.map (fun t => t.1 • m.vectors t.2)).sum := by
        simp [map_list_sum, List.map_map, Function.comp_def, hv]
      simpa only [symbolicPerform, perform, he] using
        represents_store p E s m h ((terms.map (fun t => t.1 • s.vectors t.2)).sum) (terms.foldl (fun deps t => deps ∪ m.vectorSamples t.2) ∅)
  | difference w x y =>
      have he : E (s.points x - s.points y) = m.points x - m.points y := by
        rw [map_sub, hp x, hp y]
        abel
      simpa only [symbolicPerform, perform, he] using
        represents_store p E s m h (s.points x - s.points y) (m.pointSamples x ∪ m.pointSamples y)
  | lmo w v =>
      simpa [symbolicPerform, perform, Represents, hu w v rfl] using
        represents_store p E s m h (0, Finsupp.single s.next 1) (m.vectorSamples v)
  | sharp w v =>
      simpa [symbolicPerform, perform, Represents, hs w v rfl] using
        represents_store p E s m h (0, Finsupp.single s.next 1) (m.vectorSamples v)
  | move w x v eta =>
      refine ⟨by change s.next + 1 = m.next + 1; omega, ?_, hv⟩
      intro j
      by_cases hj : j = m.next
      · simp [symbolicPerform, perform, hn, hj, hp, hv, add_assoc]
      · simp [symbolicPerform, perform, hn, hj, hp]
  | sendPoint w u x => exact ⟨by change s.next + 1 = m.next + 1; omega, hp, hv⟩
  | sendVector w u v => exact ⟨by change s.next + 1 = m.next + 1; omega, hp, hv⟩

noncomputable def runCode (p : Params) (lmo : Point p.d → Point p.d)
    (replies : ℕ → Point p.d) : List Instruction → Memory p.d → Memory p.d
  | [], m => m
  | i :: rest, m => runCode p lmo replies rest (perform p lmo m i (replies m.next))

lemma perform_next (p : Params) (lmo : Point p.d → Point p.d)
    (m : Memory p.d) (i : Instruction) (r : Point p.d) :
    (perform p lmo m i r).next = m.next + 1 := by
  cases i <;> rfl

lemma perform_old_vector (p : Params) (lmo : Point p.d → Point p.d)
    (m : Memory p.d) (i : Instruction) (r : Point p.d) (j : ℕ) (hj : j < m.next) :
    (perform p lmo m i r).vectors j = m.vectors j := by
  have hne : j ≠ m.next := ne_of_lt hj
  cases i <;> simp [perform, storeVector, hne]

lemma runCode_old_vector (p : Params) (lmo : Point p.d → Point p.d)
    (replies : ℕ → Point p.d) (code : List Instruction) (m : Memory p.d)
    (j : ℕ) (hj : j < m.next) :
    (runCode p lmo replies code m).vectors j = m.vectors j := by
  induction code generalizing m with
  | nil => rfl
  | cons i rest ih =>
      rw [runCode, ih _ (by rw [perform_next]; omega)]
      exact perform_old_vector p lmo m i _ j hj

lemma runCode_current_vector (p : Params) (lmo : Point p.d → Point p.d)
    (replies : ℕ → Point p.d) (rest : List Instruction) (m : Memory p.d) (i : Instruction) :
    (runCode p lmo replies (i :: rest) m).vectors m.next =
      (perform p lmo m i (replies m.next)).vectors m.next := by
  rw [runCode]
  apply runCode_old_vector
  rw [perform_next]
  omega

lemma represents_runCode (p : Params) (lmo : Point p.d → Point p.d)
    (replies : ℕ → Point p.d) (code : List Instruction)
    (E : LinearValue →ₗ[ℝ] Point p.d) (s : SymbolicMemory) (m : Memory p.d)
    (h : Represents p E s m)
    (hraw : ∀ j, E (Finsupp.single j 1, 0) = (runCode p lmo replies code m).vectors j)
    (hdir : ∀ j, E (0, Finsupp.single j 1) = (runCode p lmo replies code m).vectors j) :
    Represents p E (code.foldl symbolicPerform s) (runCode p lmo replies code m) := by
  induction code generalizing s m with
  | nil => exact h
  | cons i rest ih =>
      apply ih
      · apply represents_perform p lmo E s m h i (replies m.next)
        · intro w x hi
          rw [h.1, hraw, runCode_current_vector, hi]
          simp [perform, storeVector]
        · intro w v hi
          rw [h.1, hdir, runCode_current_vector, hi]
          simp [perform, storeVector]
        · intro w v hi
          rw [h.1, hdir, runCode_current_vector, hi]
          simp [perform, storeVector]
      · exact hraw
      · exact hdir

noncomputable def traceEvaluation {d : ℕ} (m : Memory d) : LinearValue →ₗ[ℝ] Point d :=
  (Finsupp.linearCombination ℝ m.vectors).comp (LinearMap.fst ℝ _ _) +
    (Finsupp.linearCombination ℝ m.vectors).comp (LinearMap.snd ℝ _ _)

lemma symbolic_represents_execution (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) (replies : ℕ → Point p.d) :
    let m := runCode p lmo replies a.instructions (initialMemory p)
    Represents p (traceEvaluation m) a.symbolic m := by
  apply represents_runCode p lmo replies a.instructions
  · exact represents_initial _ _
  · intro j
    simp [traceEvaluation]
  · intro j
    simp [traceEvaluation]

lemma interpret_old_vector (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (code : List Instruction) (m : Memory p.d)
    (j : ℕ) (hj : j < m.next) :
    (interpret p lmo response code m).vectors j = m.vectors j := by
  induction code generalizing m with
  | nil => rfl
  | cons i rest ih =>
      cases i <;> simp only [interpret] <;>
        rw [ih _ (by rw [perform_next]; omega)] <;>
        exact perform_old_vector p lmo m _ _ j hj

lemma represents_interpret (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (code : List Instruction)
    (E : LinearValue →ₗ[ℝ] Point p.d) (s : SymbolicMemory) (m : Memory p.d)
    (h : Represents p E s m)
    (hraw : ∀ j, E (Finsupp.single j 1, 0) = (interpret p lmo response code m).vectors j)
    (hdir : ∀ j, E (0, Finsupp.single j 1) = (interpret p lmo response code m).vectors j) :
    Represents p E (code.foldl symbolicPerform s) (interpret p lmo response code m) := by
  induction code generalizing s m with
  | nil => exact h
  | cons i rest ih =>
      have old (reply : Point p.d) :
          (interpret p lmo response rest (perform p lmo m i reply)).vectors m.next =
            (perform p lmo m i reply).vectors m.next :=
        interpret_old_vector p lmo response rest _ _ (by rw [perform_next]; omega)
      cases i with
      | query w x =>
          apply ih
          · apply represents_perform p lmo E s m h (.query w x) (response m.replies (m.points x))
            · intro w' x' hi
              cases hi
              rw [h.1, hraw]
              simpa [interpret, perform, storeVector] using old (response m.replies (m.points x))
            · intro w' v hi; cases hi
            · intro w' v hi; cases hi
          · exact hraw
          · exact hdir
      | lmo w v =>
          apply ih
          · apply represents_perform p lmo E s m h (.lmo w v) 0
            · intro w' x' hi; cases hi
            · intro w' v' hi
              cases hi
              rw [h.1, hdir]
              simpa [interpret, perform, storeVector] using old 0
            · intro w' v' hi; cases hi
          · exact hraw
          · exact hdir
      | sharp w v =>
          apply ih
          · apply represents_perform p lmo E s m h (.sharp w v) 0
            · intro w' x' hi; cases hi
            · intro w' v' hi; cases hi
            · intro w' v' hi
              cases hi
              rw [h.1, hdir]
              simpa [interpret, perform, storeVector] using old 0
          · exact hraw
          · exact hdir
      | mix w ts | difference w x y | move w x v eta | sendPoint w u x | sendVector w u v =>
          apply ih
          · apply represents_perform p lmo E s m h _ 0 <;> intro w' v' hi <;> cases hi
          · exact hraw
          · exact hdir

lemma symbolic_represents_sampled_execution (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) (response : ℕ → Point p.d → Point p.d) :
    let m := interpret p lmo response a.instructions (initialMemory p)
    Represents p (traceEvaluation m) a.symbolic m := by
  apply represents_interpret p lmo response a.instructions
  · exact represents_initial _ _
  · intro j
    simp [traceEvaluation]
  · intro j
    simp [traceEvaluation]

lemma execute_symbolic {Ω : Type} [MeasurableSpace Ω] (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d) (ξ : ℕ → Ω) (j : Fin (a.outputCount + 1)) :
    OracleTemplate.execute (OracleTemplate.BirchSgd.gradientOracle P g)
      (programAlgorithm p a lmo) (fun _ => a.oracleCalls) j ξ =
        p.x0 + traceEvaluation
          (interpret p lmo (fun k x => g x (ξ k)) a.instructions (initialMemory p))
          (a.symbolic.points (a.outputPoint j)) := by
  rw [execute_interpret]
  exact (symbolic_represents_sampled_execution p a lmo (fun k x => g x (ξ k))).2.1 _

noncomputable def coefficientSpace (s : SymbolicMemory) : Submodule ℝ LinearValue :=
  (Finsupp.supported ℝ ℝ (s.queries : Set ℕ)).prod
    (Finsupp.supported ℝ ℝ ((s.sharps ∪ s.units : Finset ℕ) : Set ℕ))

structure MapsIn (s : SymbolicMemory) (V : Submodule ℝ LinearValue) : Prop where
  points : ∀ j, s.points j ∈ V
  vectors : ∀ j, s.vectors j ∈ V
  queryPoints : ∀ j, s.queryPoints j ∈ V
  sharpInputs : ∀ j, s.sharpInputs j ∈ V

lemma mapsIn_mono {s : SymbolicMemory} {V W : Submodule ℝ LinearValue}
    (h : MapsIn s V) (hm : V ≤ W) : MapsIn s W :=
  ⟨fun j => hm (h.points j), fun j => hm (h.vectors j),
    fun j => hm (h.queryPoints j), fun j => hm (h.sharpInputs j)⟩

lemma mapsIn_store {s : SymbolicMemory} {V : Submodule ℝ LinearValue}
    (h : MapsIn s V) (v : LinearValue) (hv : v ∈ V) : MapsIn (symbolicStore s v) V := by
  refine ⟨h.points, ?_, h.queryPoints, h.sharpInputs⟩
  intro j
  by_cases hj : j = s.next
  · simpa [symbolicStore, hj] using hv
  · simpa [symbolicStore, hj] using h.vectors j

lemma mapsIn_perform {s : SymbolicMemory} {V : Submodule ℝ LinearValue}
    (h : MapsIn s V) (i : Instruction)
    (hq : ∀ w x, i = Instruction.query w x → (Finsupp.single s.next 1, 0) ∈ V)
    (hd : ∀ w v, i = Instruction.lmo w v ∨ i = Instruction.sharp w v →
      (0, Finsupp.single s.next 1) ∈ V) : MapsIn (symbolicPerform s i) V := by
  cases i with
  | query w x =>
      have hs := mapsIn_store h (Finsupp.single s.next 1, 0) (hq w x rfl)
      refine ⟨hs.points, hs.vectors, ?_, hs.sharpInputs⟩
      intro j
      by_cases hj : j = s.next
      · simpa [symbolicPerform, hj] using h.points x
      · simpa [symbolicPerform, hj] using h.queryPoints j
  | mix w terms =>
      apply mapsIn_store h
      clear hq hd
      induction terms with
      | nil => exact V.zero_mem
      | cons t ts ih =>
          simpa only [List.map_cons, List.sum_cons] using
            V.add_mem (V.smul_mem t.1 (h.vectors t.2)) ih
  | difference w x y => exact mapsIn_store h _ (V.sub_mem (h.points x) (h.points y))
  | lmo w v =>
      have hs := mapsIn_store h (0, Finsupp.single s.next 1) (hd w v (Or.inl rfl))
      refine ⟨hs.points, hs.vectors, hs.queryPoints, ?_⟩
      intro j
      by_cases hj : j = s.next
      · simpa [symbolicPerform, hj] using h.vectors v
      · simpa [symbolicPerform, hj] using h.sharpInputs j
  | sharp w v =>
      have hs := mapsIn_store h (0, Finsupp.single s.next 1) (hd w v (Or.inr rfl))
      refine ⟨hs.points, hs.vectors, hs.queryPoints, ?_⟩
      intro j
      by_cases hj : j = s.next
      · simpa [symbolicPerform, hj] using h.vectors v
      · simpa [symbolicPerform, hj] using h.sharpInputs j
  | move w x v eta =>
      refine ⟨?_, h.vectors, h.queryPoints, h.sharpInputs⟩
      intro j
      by_cases hj : j = s.next
      · simpa [symbolicPerform, hj] using V.add_mem (h.points x) (V.smul_mem eta (h.vectors v))
      · simpa [symbolicPerform, hj] using h.points j
  | sendPoint w u x => exact ⟨h.points, h.vectors, h.queryPoints, h.sharpInputs⟩
  | sendVector w u v => exact ⟨h.points, h.vectors, h.queryPoints, h.sharpInputs⟩

lemma symbolic_queries_mono (s : SymbolicMemory) (i : Instruction) :
    s.queries ⊆ (symbolicPerform s i).queries := by
  cases i <;> simp [symbolicPerform, symbolicStore]

lemma symbolic_directions_mono (s : SymbolicMemory) (i : Instruction) :
    s.sharps ∪ s.units ⊆ (symbolicPerform s i).sharps ∪ (symbolicPerform s i).units := by
  cases i <;> simp [symbolicPerform, symbolicStore, Finset.subset_iff] <;> aesop

lemma coefficientSpace_mono (s : SymbolicMemory) (i : Instruction) :
    coefficientSpace s ≤ coefficientSpace (symbolicPerform s i) := by
  intro v hv
  exact ⟨Finsupp.supported_mono (symbolic_queries_mono s i) hv.1,
    Finsupp.supported_mono (symbolic_directions_mono s i) hv.2⟩

lemma mapsIn_step (s : SymbolicMemory) (h : MapsIn s (coefficientSpace s)) (i : Instruction) :
    MapsIn (symbolicPerform s i) (coefficientSpace (symbolicPerform s i)) := by
  apply mapsIn_perform (mapsIn_mono h (coefficientSpace_mono s i)) i
  · intro w x hi
    subst i
    simp [coefficientSpace, symbolicPerform, symbolicStore, Finsupp.single_mem_supported]
  · intro w v hi
    rcases hi with hi | hi <;> subst i <;>
      simp [coefficientSpace, symbolicPerform, symbolicStore, Finsupp.single_mem_supported]

lemma symbolic_maps_supported (a : Program) : MapsIn a.symbolic (coefficientSpace a.symbolic) := by
  have hs : MapsIn ({} : SymbolicMemory) (coefficientSpace {}) := by
    constructor <;> intro j <;> exact Submodule.zero_mem _
  unfold Program.symbolic
  generalize ({} : SymbolicMemory) = s at *
  induction a.instructions generalizing s with
  | nil => exact hs
  | cons i rest ih => exact ih _ (mapsIn_step s hs i)

def BeforeNext (s : SymbolicMemory) : Prop :=
  (∀ j ∈ s.queries, j < s.next) ∧ ∀ j ∈ s.sharps ∪ s.units, j < s.next

lemma beforeNext_step (s : SymbolicMemory) (h : BeforeNext s) (i : Instruction) :
    BeforeNext (symbolicPerform s i) := by
  cases i <;> constructor <;> intro j hj
  all_goals
    have hq : j ∈ s.queries → j < s.next + 1 := fun hj => Nat.lt_succ_of_lt (h.1 j hj)
    have hh : j ∈ s.sharps → j < s.next + 1 :=
      fun hj => Nat.lt_succ_of_lt (h.2 j (Finset.mem_union_left _ hj))
    have hu : j ∈ s.units → j < s.next + 1 :=
      fun hj => Nat.lt_succ_of_lt (h.2 j (Finset.mem_union_right _ hj))
    simp only [symbolicPerform, symbolicStore, Finset.mem_insert, Finset.mem_union] at hj ⊢
    aesop

lemma symbolic_beforeNext (a : Program) : BeforeNext a.symbolic := by
  have hs : BeforeNext ({} : SymbolicMemory) := by simp [BeforeNext]
  unfold Program.symbolic
  generalize ({} : SymbolicMemory) = s at *
  induction a.instructions generalizing s with
  | nil => exact hs
  | cons i rest ih => exact ih _ (beforeNext_step s hs i)

def CausalValue (bound : ℕ) (v : LinearValue) : Prop :=
  ∀ j, bound ≤ j → v.1 j = 0 ∧ v.2 j = 0

lemma causal_of_supported (s : SymbolicMemory) (h : BeforeNext s) (v : LinearValue)
    (hv : v ∈ coefficientSpace s) : CausalValue s.next v := by
  intro j hj
  constructor
  · apply (Finsupp.mem_supported' ℝ v.1).mp hv.1 j
    intro hmem
    have := h.1 j hmem
    omega
  · apply (Finsupp.mem_supported' ℝ v.2).mp hv.2 j
    intro hmem
    have := h.2 j hmem
    omega

def CausalRecords (s : SymbolicMemory) : Prop :=
  (∀ j, CausalValue j (s.queryPoints j)) ∧ ∀ j, CausalValue j (s.sharpInputs j)

lemma causalRecords_step (s : SymbolicMemory) (hs : MapsIn s (coefficientSpace s))
    (hb : BeforeNext s) (hc : CausalRecords s) (i : Instruction) :
    CausalRecords (symbolicPerform s i) := by
  cases i with
  | query w x =>
      refine ⟨?_, hc.2⟩
      intro j
      by_cases hj : j = s.next
      · simpa [symbolicPerform, hj] using causal_of_supported s hb (s.points x) (hs.points x)
      · simpa [symbolicPerform, hj] using hc.1 j
  | lmo w v =>
      refine ⟨hc.1, ?_⟩
      intro j
      by_cases hj : j = s.next
      · simpa [symbolicPerform, hj] using causal_of_supported s hb (s.vectors v) (hs.vectors v)
      · simpa [symbolicPerform, hj] using hc.2 j
  | sharp w v =>
      refine ⟨hc.1, ?_⟩
      intro j
      by_cases hj : j = s.next
      · simpa [symbolicPerform, hj] using causal_of_supported s hb (s.vectors v) (hs.vectors v)
      · simpa [symbolicPerform, hj] using hc.2 j
  | mix w ts | difference w x y | move w x v eta | sendPoint w u x | sendVector w u v =>
      exact ⟨hc.1, hc.2⟩

lemma symbolic_causalRecords (a : Program) : CausalRecords a.symbolic := by
  have hs : MapsIn ({} : SymbolicMemory) (coefficientSpace {}) := by
    constructor <;> intro j <;> exact Submodule.zero_mem _
  have hb : BeforeNext ({} : SymbolicMemory) := by simp [BeforeNext]
  have hc : CausalRecords ({} : SymbolicMemory) := by simp [CausalRecords, CausalValue]
  unfold Program.symbolic
  generalize ({} : SymbolicMemory) = s at *
  induction a.instructions generalizing s with
  | nil => exact hc
  | cons i rest ih =>
      exact ih _ (mapsIn_step s hs i) (beforeNext_step s hb i) (causalRecords_step s hs hb hc i)

end LongTails.Proofs.BirchNonEuclideanSymbolic
