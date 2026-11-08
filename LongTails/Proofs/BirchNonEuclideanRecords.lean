import LongTails.Proofs.BirchNonEuclideanCausality

namespace LongTails.Proofs.BirchNonEuclideanRecords

open OracleTemplate.Rennala (Point)
open LongTails.Setups.UscgConstant (dualNorm)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Proofs.BirchNonEuclideanExecution (interpret queryCount)
open LongTails.Proofs.BirchNonEuclideanSymbolic
open LongTails.Proofs.BirchNonEuclideanCausality
open MeasureTheory

lemma represents_interpret_prefix (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (code tail : List Instruction)
    (E : LinearValue →ₗ[ℝ] Point p.d) (s : SymbolicMemory) (m : Memory p.d)
    (h : Represents p E s m)
    (hraw : ∀ j, E (Finsupp.single j 1, 0) =
      (interpret p lmo response (code ++ tail) m).vectors j)
    (hdir : ∀ j, E (0, Finsupp.single j 1) =
      (interpret p lmo response (code ++ tail) m).vectors j) :
    Represents p E (code.foldl symbolicPerform s) (interpret p lmo response code m) := by
  induction code generalizing s m with
  | nil => exact h
  | cons i rest ih =>
      have old (reply : Point p.d) :
          (interpret p lmo response (rest ++ tail) (perform p lmo m i reply)).vectors m.next =
            (perform p lmo m i reply).vectors m.next :=
        interpret_old_vector p lmo response (rest ++ tail) _ _ (by rw [perform_next]; omega)
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

lemma symbolic_next (code : List Instruction) (s : SymbolicMemory) :
    (code.foldl symbolicPerform s).next = s.next + code.length := by
  induction code generalizing s with
  | nil => simp
  | cons i rest ih =>
      rw [List.foldl_cons, ih]
      cases i <;> simp [symbolicPerform, symbolicStore] <;> omega

lemma symbolic_old_records (code : List Instruction) (s : SymbolicMemory)
    (q : ℕ) (hq : q < s.next) :
    (code.foldl symbolicPerform s).queryPoints q = s.queryPoints q ∧
      (code.foldl symbolicPerform s).sharpInputs q = s.sharpInputs q := by
  induction code generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons i rest ih =>
      have hnext : q < (symbolicPerform s i).next := by
        cases i <;> simp [symbolicPerform, symbolicStore] <;> omega
      rw [List.foldl_cons]
      have hh := ih (symbolicPerform s i) hnext
      have hne : q ≠ s.next := ne_of_lt hq
      cases i <;> simpa [symbolicPerform, symbolicStore, hne] using hh

lemma query_record (a : Program) (pre rest : List Instruction) (w x : ℕ)
    (heq : a.instructions = pre ++ Instruction.query w x :: rest) :
    a.symbolic.queryPoints (pre.length + 1) = (pre.foldl symbolicPerform {}).points x := by
  let s : SymbolicMemory := pre.foldl symbolicPerform {}
  have hn : s.next = pre.length + 1 := by simp [s, symbolic_next, Nat.add_comm]
  have hh := (symbolic_old_records rest (symbolicPerform s (.query w x))
    (pre.length + 1) (by simp [symbolicPerform, symbolicStore, hn])).1
  simpa [Program.symbolic, heq, List.foldl_append, List.foldl_cons, s, hn,
    symbolicPerform] using hh

lemma sharp_record (a : Program) (pre rest : List Instruction) (w v : ℕ)
    (heq : a.instructions = pre ++ Instruction.sharp w v :: rest) :
    a.symbolic.sharpInputs (pre.length + 1) = (pre.foldl symbolicPerform {}).vectors v := by
  let s : SymbolicMemory := pre.foldl symbolicPerform {}
  have hn : s.next = pre.length + 1 := by simp [s, symbolic_next, Nat.add_comm]
  have hh := (symbolic_old_records rest (symbolicPerform s (.sharp w v))
    (pre.length + 1) (by simp [symbolicPerform, symbolicStore, hn])).2
  simpa [Program.symbolic, heq, List.foldl_append, List.foldl_cons, s, hn,
    symbolicPerform] using hh

lemma sampled_prefix_represents (p : Params) (a : Program) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (pre tail : List Instruction)
    (heq : a.instructions = pre ++ tail) :
    Represents p (traceEvaluation (interpret p lmo response a.instructions (initialMemory p)))
      (pre.foldl symbolicPerform {}) (interpret p lmo response pre (initialMemory p)) := by
  apply represents_interpret_prefix p lmo response pre tail
  · exact represents_initial _ _
  · intro j; simp [traceEvaluation, heq]
  · intro j; simp [traceEvaluation, heq]

lemma sampled_query_record (p : Params) (a : Program) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (pre rest : List Instruction) (w x : ℕ)
    (heq : a.instructions = pre ++ Instruction.query w x :: rest) :
    let m := interpret p lmo response a.instructions (initialMemory p)
    m.vectors (pre.length + 1) = response (queryCount pre)
      (p.x0 + traceEvaluation m (a.symbolic.queryPoints (pre.length + 1))) := by
  dsimp only
  have hp := sampled_prefix_represents p a lmo response pre (.query w x :: rest) heq
  rw [query_record a pre rest w x heq, ← hp.2.1 x]
  rw [heq, interpret_append]
  let mp := interpret p lmo response pre (initialMemory p)
  have hn : mp.next = pre.length + 1 := by simp [mp, interpret_next, initialMemory, Nat.add_comm]
  have hr : mp.replies = queryCount pre := by simp [mp, interpret_replies, initialMemory]
  change (interpret p lmo response (.query w x :: rest) mp).vectors _ = _
  simp only [interpret]
  rw [interpret_old_vector p lmo response rest _ _ (by rw [perform_next, hn]; omega)]
  simp [perform, storeVector, hn, hr]
  rfl

lemma sampled_sharp_record (p : Params) (a : Program) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (pre rest : List Instruction) (w v : ℕ)
    (heq : a.instructions = pre ++ Instruction.sharp w v :: rest) :
    let m := interpret p lmo response a.instructions (initialMemory p)
    m.vectors (pre.length + 1) = dualNorm p.N (traceEvaluation m
      (a.symbolic.sharpInputs (pre.length + 1))) • lmo (traceEvaluation m
      (a.symbolic.sharpInputs (pre.length + 1))) := by
  dsimp only
  have hp := sampled_prefix_represents p a lmo response pre (.sharp w v :: rest) heq
  rw [sharp_record a pre rest w v heq, ← hp.2.2 v]
  rw [heq, interpret_append]
  let mp := interpret p lmo response pre (initialMemory p)
  have hn : mp.next = pre.length + 1 := by simp [mp, interpret_next, initialMemory, Nat.add_comm]
  change (interpret p lmo response (.sharp w v :: rest) mp).vectors _ = _
  simp only [interpret]
  rw [interpret_old_vector p lmo response rest _ _ (by rw [perform_next, hn]; omega)]
  simp [perform, storeVector, hn]
  rfl

def sharpLabels : List Instruction → ℕ → Finset ℕ
  | [], _ => ∅
  | .sharp _ _ :: rest, n => insert n (sharpLabels rest (n + 1))
  | _ :: rest, n => sharpLabels rest (n + 1)

lemma symbolic_sharpLabels (code : List Instruction) (s : SymbolicMemory) :
    (code.foldl symbolicPerform s).sharps = s.sharps ∪ sharpLabels code s.next := by
  induction code generalizing s with
  | nil => simp [sharpLabels]
  | cons i rest ih =>
      rw [List.foldl_cons, ih]
      cases i <;> simp [sharpLabels, symbolicPerform, symbolicStore,
        Finset.insert_union, Finset.union_insert]

lemma sharpLabels_decompose (code : List Instruction) (n q : ℕ) (hq : q ∈ sharpLabels code n) :
    ∃ (pre rest : List Instruction) (worker vector : ℕ),
      code = pre ++ Instruction.sharp worker vector :: rest ∧ q = n + pre.length := by
  induction code generalizing n with
  | nil => simp [sharpLabels] at hq
  | cons i rest ih =>
      cases hcase : i with
      | sharp worker vector =>
          simp only [hcase, sharpLabels, Finset.mem_insert] at hq
          rcases hq with rfl | hq
          · exact ⟨[], rest, worker, vector, by simp, by simp⟩
          · obtain ⟨pre, tail, w, v, heq, hlen⟩ := ih (n + 1) hq
            refine ⟨Instruction.sharp worker vector :: pre, tail, w, v, ?_, ?_⟩
            · simp [heq]
            · simp only [List.length_cons]; omega
      | query worker point | mix worker terms | difference worker x y | lmo worker v | move worker x v η | sendPoint worker other x | sendVector worker other x =>
          simp only [hcase, sharpLabels] at hq
          obtain ⟨pre, tail, w, v, heq, hlen⟩ := ih (n + 1) hq
          refine ⟨i :: pre, tail, w, v, ?_, ?_⟩
          · simp [hcase, heq]
          · simp only [List.length_cons]; omega

lemma program_sharp_decompose (a : Program) (q : ℕ) (hq : q ∈ a.symbolic.sharps) :
    ∃ (pre rest : List Instruction) (worker vector : ℕ),
      a.instructions = pre ++ Instruction.sharp worker vector :: rest ∧ q = pre.length + 1 := by
  have hm : q ∈ sharpLabels a.instructions 1 := by
    simpa only [Program.symbolic, symbolic_sharpLabels, Finset.empty_union] using hq
  obtain ⟨pre, rest, w, v, heq, hlen⟩ := sharpLabels_decompose a.instructions 1 q hm
  exact ⟨pre, rest, w, v, heq, by omega⟩

lemma sampled_sharp_identity (p : Params) (a : Program) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (e : ℕ) (he : e ∈ a.symbolic.sharps) :
    let m := interpret p lmo response a.instructions (initialMemory p)
    m.vectors e = dualNorm p.N (traceEvaluation m (a.symbolic.sharpInputs e)) •
      lmo (traceEvaluation m (a.symbolic.sharpInputs e)) := by
  obtain ⟨pre, rest, w, v, heq, rfl⟩ := program_sharp_decompose a e he
  exact sampled_sharp_record p a lmo response pre rest w v heq

def queryRegister (a : Program) (q : ℕ) : ℕ :=
  match a.instructions[q - 1]? with
  | some (.query _ x) => x
  | _ => 0

noncomputable def sampledQueryPoint {Ω : Type} (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) (g : Point p.d → Ω → Point p.d)
    (q : ℕ) (ξ : ℕ → Ω) : Point p.d :=
  (interpret p lmo (fun k x => g x (ξ k)) (a.instructions.take (q - 1))
    (initialMemory p)).points (queryRegister a q)

lemma queryRegister_decompose (a : Program) (pre rest : List Instruction) (w x : ℕ)
    (heq : a.instructions = pre ++ Instruction.query w x :: rest) :
    queryRegister a (pre.length + 1) = x := by
  simp [queryRegister, heq]

lemma sampledQueryPoint_identity {Ω : Type} (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) (g : Point p.d → Ω → Point p.d)
    (q : ℕ) (hq : q ∈ a.symbolic.queries) (ξ : ℕ → Ω) :
    sampledQueryPoint p a lmo g q ξ = p.x0 + traceEvaluation
      (interpret p lmo (fun k x => g x (ξ k)) a.instructions (initialMemory p))
      (a.symbolic.queryPoints q) := by
  obtain ⟨pre, rest, w, x, heq, rfl⟩ := program_query_decompose a q hq
  rw [query_record a pre rest w x heq]
  have hp := sampled_prefix_represents p a lmo (fun k x => g x (ξ k)) pre
    (.query w x :: rest) heq
  rw [← hp.2.1 x]
  simp [sampledQueryPoint, queryRegister_decompose a pre rest w x heq, heq]

lemma sampled_query_identity {Ω : Type} (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) (g : Point p.d → Ω → Point p.d)
    (q : ℕ) (hq : q ∈ a.symbolic.queries) (ξ : ℕ → Ω) :
    (interpret p lmo (fun k x => g x (ξ k)) a.instructions (initialMemory p)).vectors q =
      g (sampledQueryPoint p a lmo g q ξ) (ξ (queryCount (a.instructions.take (q - 1)))) := by
  rw [sampledQueryPoint_identity p a lmo g q hq ξ]
  obtain ⟨pre, rest, w, x, heq, rfl⟩ := program_query_decompose a q hq
  have hh := sampled_query_record p a lmo (fun k x => g x (ξ k)) pre rest w x heq
  simpa only [heq, Nat.add_sub_cancel, List.take_left] using hh

lemma sampledQueryPoint_measurable {Ω : Type} [MeasurableSpace Ω] (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) (hlmo : Measurable lmo)
    {R : ℝ} (hR : ∀ v, p.N v ≤ 1 → ‖v‖ ≤ R) (hR0 : 0 ≤ R)
    (g : Point p.d → Ω → Point p.d) (hg : Measurable (Function.uncurry g)) (q : ℕ) :
    Measurable (sampledQueryPoint p a lmo g q) :=
  (interpret_prefix_measurable p lmo hlmo hR hR0 g hg (a.instructions.take (q - 1))).1 _

lemma sampledQueryPoint_past {Ω : Type} (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) (g : Point p.d → Ω → Point p.d) (q : ℕ)
    (ξ ξ' : ℕ → Ω)
    (h : ∀ j < queryCount (a.instructions.take (q - 1)), ξ j = ξ' j) :
    sampledQueryPoint p a lmo g q ξ = sampledQueryPoint p a lmo g q ξ' := by
  unfold sampledQueryPoint
  rw [interpret_sample_congr p lmo g _ _ ξ ξ' (by simpa [initialMemory] using h)]

end LongTails.Proofs.BirchNonEuclideanRecords
