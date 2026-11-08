import LongTails.Proofs.BirchNonEuclideanConstruction
import LongTails.Proofs.BirchNonEuclideanRecords
import LongTails.Proofs.BirchDelayedCoefficients

namespace LongTails.Proofs.BirchNonEuclideanCoefficients

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction

lemma state_forIn_append {σ α β : Type} (step : α → β → StateM σ β)
    (xs ys : List α) (b : β) (s : σ) :
    (forIn (xs ++ ys) b (fun i b => ForInStep.yield <$> step i b) : StateM σ β) s =
      let z := (forIn xs b (fun i b => ForInStep.yield <$> step i b) : StateM σ β) s
      (forIn ys z.1 (fun i b => ForInStep.yield <$> step i b) : StateM σ β) z.2 := by
  induction xs generalizing b s with
  | nil => rfl
  | cons i xs ih =>
      rw [List.cons_append, state_forIn_cons, ih]
      rw [state_forIn_cons]

lemma state_forIn_range_succ {σ β : Type} (step : ℕ → β → StateM σ β)
    (n : ℕ) (b : β) (s : σ) :
    (forIn (List.range (n + 1)) b (fun i b => ForInStep.yield <$> step i b) : StateM σ β) s =
      let z := (forIn (List.range n) b (fun i b => ForInStep.yield <$> step i b) : StateM σ β) s
      step n z.1 z.2 := by
  rw [List.range_succ, state_forIn_append]
  rfl

lemma codeValid_symbolic_next (workers : ℕ) (t : Tuning) (s : CodeState)
    (hs : CodeValid workers t s) : s.next = (codeSymbolic t s).next := by
  rw [codeSymbolic_next, ← codeLayout_next t s]
  exact hs.1

lemma symbolicPerform_old_values (s : SymbolicMemory) (i : Instruction) (j : ℕ)
    (hj : j < s.next) :
    (symbolicPerform s i).points j = s.points j ∧
      (symbolicPerform s i).vectors j = s.vectors j := by
  have hn : j ≠ s.next := ne_of_lt hj
  cases i <;> simp [symbolicPerform, symbolicStore, hn]

lemma symbolic_fold_old_values (code : List Instruction) (s : SymbolicMemory) (j : ℕ)
    (hj : j < s.next) :
    (code.foldl symbolicPerform s).points j = s.points j ∧
      (code.foldl symbolicPerform s).vectors j = s.vectors j := by
  induction code generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons i rest ih =>
      have hn : j < (symbolicPerform s i).next := by
        rw [LongTails.Proofs.BirchNonEuclideanExecution.symbolic_next]
        omega
      rw [List.foldl_cons]
      have hh := ih (symbolicPerform s i) hn
      have hp := symbolicPerform_old_values s i j hj
      exact ⟨hh.1.trans hp.1, hh.2.trans hp.2⟩

def CodeExtends (s s' : CodeState) : Prop := ∃ tail, s'.instructions = s.instructions ++ tail

lemma codeExtends_refl (s : CodeState) : CodeExtends s s := ⟨[], by simp⟩

lemma codeExtends_trans (s s' s'' : CodeState) (h : CodeExtends s s')
    (h' : CodeExtends s' s'') : CodeExtends s s'' := by
  obtain ⟨left, hl⟩ := h
  obtain ⟨right, hr⟩ := h'
  exact ⟨left ++ right, by rw [hr, hl, List.append_assoc]⟩

lemma codeExtends_emit (s : CodeState) (i : InstructionTemplate) : CodeExtends s (emit i s).2 :=
  ⟨[i], rfl⟩

lemma codeExtends_symbolic (t : Tuning) (s s' : CodeState) (h : CodeExtends s s')
    (j : ℕ) (hj : j < (codeSymbolic t s).next) :
    (codeSymbolic t s').points j = (codeSymbolic t s).points j ∧
      (codeSymbolic t s').vectors j = (codeSymbolic t s).vectors j ∧
      (codeSymbolic t s').queryPoints j = (codeSymbolic t s).queryPoints j ∧
      (codeSymbolic t s').sharpInputs j = (codeSymbolic t s).sharpInputs j := by
  obtain ⟨tail, ht⟩ := h
  have he : codeSymbolic t s' = (tail.map (InstructionTemplate.instantiate t)).foldl
      symbolicPerform (codeSymbolic t s) := by
    simp [codeSymbolic, codeInstructions, ht, List.foldl_append]
  rw [he]
  have hv := symbolic_fold_old_values (tail.map (InstructionTemplate.instantiate t))
    (codeSymbolic t s) j hj
  have hr := LongTails.Proofs.BirchNonEuclideanRecords.symbolic_old_records
    (tail.map (InstructionTemplate.instantiate t)) (codeSymbolic t s) j hj
  exact ⟨hv.1, hv.2, hr⟩

lemma momentumStep_next (w H round h : ℕ) (state : ℕ × ℕ) (s : CodeState) :
    (momentumStep w H round h state s).2.next = s.next + 4 := by
  simp only [momentumStep, state_bind_apply, state_pure_apply, emit_apply]

lemma momentumStep_registers (w H round h : ℕ) (state : ℕ × ℕ) (s : CodeState) :
    (momentumStep w H round h state s).1 = (s.next + 3, s.next + 1) := by
  simp only [momentumStep, state_bind_apply, state_pure_apply, emit_apply]

lemma momentumStep_extends (w H round h : ℕ) (state : ℕ × ℕ) (s : CodeState) :
    CodeExtends s (momentumStep w H round h state s).2 := by
  refine ⟨[.query w state.1,
    .mix w [(.momentum (round * H + h), s.next),
      (.add (.constant 1) (.neg (.momentum (round * H + h))), state.2)],
    .sharp w (s.next + 1),
    .move w state.1 (s.next + 2) (.mul (.constant (1 / (H : ℝ))) (.step round))], ?_⟩
  simp only [momentumStep, state_bind_apply, state_pure_apply, emit_apply]
  simp [List.append_assoc, Nat.add_assoc]

lemma momentumStep_symbolic (w H round h : ℕ) (state : ℕ × ℕ) (s : CodeState)
    (t : Tuning) (hn : s.next = (codeSymbolic t s).next)
    (hm : state.2 < s.next) :
    let z := momentumStep w H round h state s
    let old := codeSymbolic t s
    let new := codeSymbolic t z.2
    let α := t.momentum (round * H + h)
    let m := α • (Finsupp.single s.next 1, 0) + (1 - α) • old.vectors state.2
    new.vectors z.1.2 = m ∧
      new.points z.1.1 = old.points state.1 + (1 / (H : ℝ) * t.step round) •
        (0, Finsupp.single (s.next + 2) 1) ∧
      new.queryPoints s.next = old.points state.1 ∧
      new.sharpInputs (s.next + 2) = m ∧
      new.queries = insert s.next old.queries ∧
      new.sharps = insert (s.next + 2) old.sharps ∧ new.units = old.units := by
  have hm0 : state.2 ≠ (codeSymbolic t s).next := by omega
  dsimp only
  simp only [momentumStep, state_bind_apply, state_pure_apply]
  simp only [codeSymbolic_emit, InstructionTemplate.instantiate, Coefficient.eval]
  simp [symbolicPerform, symbolicStore, emit_apply, hn, hm0,
    Nat.add_assoc, sub_eq_add_neg, Coefficient.eval]

noncomputable def localPrefix (w H round n : ℕ) (state : ℕ × ℕ) (s : CodeState) :
    (ℕ × ℕ) × CodeState :=
  (forIn (List.range n) state
    (fun h state => ForInStep.yield <$> momentumStep w H round h state) :
      StateM CodeState (ℕ × ℕ)) s

lemma localPrefix_zero (w H round : ℕ) (state : ℕ × ℕ) (s : CodeState) :
    localPrefix w H round 0 state s = (state, s) := rfl

lemma localPrefix_succ (w H round n : ℕ) (state : ℕ × ℕ) (s : CodeState) :
    localPrefix w H round (n + 1) state s =
      let z := localPrefix w H round n state s
      momentumStep w H round n z.1 z.2 :=
  state_forIn_range_succ _ n state s

lemma localMomentum_prefix (w x m H round : ℕ) (s : CodeState) :
    (localMomentum w x m H round).run s = localPrefix w H round H (x, m) s := rfl

lemma localPrefix_next (w H round n : ℕ) (state : ℕ × ℕ) (s : CodeState) :
    (localPrefix w H round n state s).2.next = s.next + 4 * n := by
  induction n with
  | zero => simp [localPrefix_zero]
  | succ n ih =>
      rw [localPrefix_succ]
      dsimp only
      rw [momentumStep_next, ih]
      omega

lemma localPrefix_extends (w H round n : ℕ) (state : ℕ × ℕ) (s : CodeState) :
    CodeExtends s (localPrefix w H round n state s).2 := by
  induction n with
  | zero => exact codeExtends_refl s
  | succ n ih =>
      rw [localPrefix_succ]
      exact codeExtends_trans s _ _ ih (momentumStep_extends w H round n _ _)

lemma momentumStep_symbolic_next (w H round h : ℕ) (state : ℕ × ℕ) (s : CodeState)
    (t : Tuning) :
    (codeSymbolic t (momentumStep w H round h state s).2).next =
      (codeSymbolic t s).next + 4 := by
  simp only [momentumStep, state_bind_apply, state_pure_apply, codeSymbolic_emit,
    LongTails.Proofs.BirchNonEuclideanExecution.symbolic_next]

lemma localPrefix_aligned (w H round n : ℕ) (state : ℕ × ℕ) (s : CodeState)
    (t : Tuning) (hn : s.next = (codeSymbolic t s).next) :
    (localPrefix w H round n state s).2.next =
      (codeSymbolic t (localPrefix w H round n state s).2).next := by
  induction n with
  | zero => exact hn
  | succ n ih =>
      rw [localPrefix_succ]
      dsimp only
      rw [momentumStep_next, momentumStep_symbolic_next, ih]

lemma localPrefix_momentum_lt (w H round n : ℕ) (state : ℕ × ℕ) (s : CodeState)
    (hm : state.2 < s.next) :
    (localPrefix w H round n state s).1.2 < (localPrefix w H round n state s).2.next := by
  cases n with
  | zero => exact hm
  | succ n =>
      rw [localPrefix_succ]
      dsimp only
      rw [momentumStep_registers, momentumStep_next]
      simp

lemma localPrefix_point_lt (w H round n : ℕ) (state : ℕ × ℕ) (s : CodeState)
    (hx : state.1 < s.next) :
    (localPrefix w H round n state s).1.1 < (localPrefix w H round n state s).2.next := by
  cases n with
  | zero => exact hx
  | succ n =>
      rw [localPrefix_succ]
      dsimp only
      rw [momentumStep_registers, momentumStep_next]
      simp

noncomputable def localRaw (α : ℝ) (first : ℕ) (initial : LinearValue) : ℕ → LinearValue
  | 0 => initial
  | n + 1 => α • (Finsupp.single (first + 4 * n) 1, 0) + (1 - α) • localRaw α first initial n

noncomputable def localPath (γ : ℝ) (first : ℕ) (initial : LinearValue) : ℕ → LinearValue
  | 0 => initial
  | n + 1 => localPath γ first initial n + γ • (0, Finsupp.single (first + 4 * n + 2) 1)

lemma localPrefix_values (w H round n : ℕ) (state : ℕ × ℕ) (s : CodeState)
    (η : ℝ) (B : ℕ) (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next)
    (hm : state.2 < s.next) :
    let t := canonicalTuning η B
    let z := localPrefix w H round n state s
    let old := codeSymbolic t s
    let new := codeSymbolic t z.2
    new.vectors z.1.2 = localRaw (1 / (B : ℝ)) s.next (old.vectors state.2) n ∧
      new.points z.1.1 = localPath (1 / (H : ℝ) * η) s.next (old.points state.1) n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      let z := localPrefix w H round n state s
      have hh := momentumStep_symbolic w H round n z.1 z.2 (canonicalTuning η B)
        (localPrefix_aligned w H round n state s _ hn)
        (localPrefix_momentum_lt w H round n state s hm)
      rw [localPrefix_succ]
      dsimp only at hh ⊢
      refine ⟨?_, ?_⟩
      · rw [hh.1, ih.1]
        simp only [localRaw, canonicalTuning, z, localPrefix_next]
      · rw [hh.2.1, ih.2]
        simp only [localPath, canonicalTuning, z, localPrefix_next]

lemma localPrefix_records (w H round n : ℕ) (state : ℕ × ℕ) (s : CodeState)
    (η : ℝ) (B : ℕ) (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next)
    (hm : state.2 < s.next) :
    let t := canonicalTuning η B
    let z := localPrefix w H round n state s
    let old := codeSymbolic t s
    let new := codeSymbolic t z.2
    ∀ j < n, new.queryPoints (s.next + 4 * j) =
      localPath (1 / (H : ℝ) * η) s.next (old.points state.1) j ∧
      new.sharpInputs (s.next + 4 * j + 2) =
        localRaw (1 / (B : ℝ)) s.next (old.vectors state.2) (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      let t := canonicalTuning η B
      let z := localPrefix w H round n state s
      have ha := localPrefix_aligned w H round n state s t hn
      have hn' : z.2.next = s.next + 4 * n := localPrefix_next w H round n state s
      have hv := localPrefix_values w H round n state s η B hn hm
      have hh := momentumStep_symbolic w H round n z.1 z.2 t ha
        (localPrefix_momentum_lt w H round n state s hm)
      dsimp only
      intro j hj
      rw [localPrefix_succ]
      dsimp only
      by_cases hjn : j = n
      · subst j
        refine ⟨?_, ?_⟩
        · rw [← hn', hh.2.2.1, hv.2]
        · rw [← hn', hh.2.2.2.1, hv.1]
          simp only [localRaw, t, canonicalTuning, hn']
      · have hjn' : j < n := by omega
        have hq : s.next + 4 * j < (codeSymbolic t z.2).next := by rw [← ha, hn']; omega
        have he : s.next + 4 * j + 2 < (codeSymbolic t z.2).next := by rw [← ha, hn']; omega
        have hq' := codeExtends_symbolic t z.2 _ (momentumStep_extends w H round n z.1 z.2) _ hq
        have he' := codeExtends_symbolic t z.2 _ (momentumStep_extends w H round n z.1 z.2) _ he
        exact ⟨hq'.2.2.1.trans (ih j hjn').1, he'.2.2.2.trans (ih j hjn').2⟩

lemma localPrefix_sets (w H round n : ℕ) (state : ℕ × ℕ) (s : CodeState)
    (t : Tuning) (hn : s.next = (codeSymbolic t s).next) (hm : state.2 < s.next) :
    let z := localPrefix w H round n state s
    let old := codeSymbolic t s
    let new := codeSymbolic t z.2
    new.queries = old.queries ∪ (Finset.range n).image (fun j => s.next + 4 * j) ∧
      new.sharps = old.sharps ∪ (Finset.range n).image (fun j => s.next + 4 * j + 2) ∧
      new.units = old.units := by
  induction n with
  | zero => simp [localPrefix_zero]
  | succ n ih =>
      let z := localPrefix w H round n state s
      have hh := momentumStep_symbolic w H round n z.1 z.2 t
        (localPrefix_aligned w H round n state s t hn)
        (localPrefix_momentum_lt w H round n state s hm)
      rw [localPrefix_succ]
      dsimp only at hh ⊢
      rw [hh.2.2.2.2.1, hh.2.2.2.2.2.1, hh.2.2.2.2.2.2, ih.1, ih.2.1, ih.2.2]
      simp [z, localPrefix_next, Finset.range_add_one, Finset.union_insert]

lemma localPath_closed (γ : ℝ) (first : ℕ) (initial : LinearValue) (n : ℕ) :
    localPath γ first initial n = initial +
      γ • ∑ j ∈ Finset.range n, (0, Finsupp.single (first + 4 * j + 2) 1) := by
  induction n with
  | zero => simp [localPath]
  | succ n ih => rw [localPath, ih, Finset.sum_range_succ, smul_add, add_assoc]

lemma localRaw_closed (α : ℝ) (first : ℕ) (initial : LinearValue) (n : ℕ) :
    localRaw α first initial n = (1 - α) ^ n • initial +
      ∑ j ∈ Finset.range n, (α * (1 - α) ^ (n - 1 - j)) •
        (Finsupp.single (first + 4 * j) 1, 0) := by
  induction n with
  | zero => simp [localRaw]
  | succ n ih =>
      rw [localRaw, ih, smul_add, Finset.smul_sum, Finset.sum_range_succ]
      have he : ∑ j ∈ Finset.range n,
          (1 - α) • ((α * (1 - α) ^ (n - 1 - j)) • ((Finsupp.single (first + 4 * j) 1, 0) : LinearValue)) =
          ∑ j ∈ Finset.range n,
            (α * (1 - α) ^ (n + 1 - 1 - j)) • ((Finsupp.single (first + 4 * j) 1, 0) : LinearValue) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hn' : n + 1 - 1 - j = (n - 1 - j) + 1 := by omega
        rw [smul_smul, hn', pow_succ]
        congr 1
        ring
      rw [he, smul_smul]
      have hp : (1 - α) * (1 - α) ^ n = (1 - α) ^ (n + 1) := by rw [pow_succ]; ring
      rw [hp]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
      abel

lemma localRaw_direction (α : ℝ) (first : ℕ) (initial : LinearValue) (n : ℕ) :
    (localRaw α first initial n).2 = (1 - α) ^ n • initial.2 := by
  induction n with
  | zero => simp [localRaw]
  | succ n ih =>
      change α • (0 : ℕ →₀ ℝ) + (1 - α) • (localRaw α first initial n).2 = _
      rw [smul_zero, zero_add, ih, smul_smul, pow_succ]
      congr 1
      ring

lemma localPath_raw (γ : ℝ) (first : ℕ) (initial : LinearValue) (n : ℕ) :
    (localPath γ first initial n).1 = initial.1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [localPath] using ih

lemma localRaw_old (α : ℝ) (first : ℕ) (initial : LinearValue) (n q : ℕ) (hq : q < first) :
    (localRaw α first initial n).1 q = (1 - α) ^ n * initial.1 q := by
  induction n with
  | zero => simp [localRaw]
  | succ n ih =>
      have hn : first + 4 * n ≠ q := by omega
      simp [localRaw, hn, ih, pow_succ]
      ring

lemma localRaw_fresh (α : ℝ) (first : ℕ) (initial : LinearValue) (n j : ℕ)
    (hinit : ∀ q, first ≤ q → initial.1 q = 0) :
    (localRaw α first initial n).1 (first + 4 * j) =
      if j < n then α * (1 - α) ^ (n - 1 - j) else 0 := by
  induction n with
  | zero => simp [localRaw, hinit]
  | succ n ih =>
      by_cases hj : j = n
      · subst j
        simp [localRaw, ih]
      · by_cases hjn : j < n
        · have hjs : j < n + 1 := by omega
          have he : n - j = (n - 1 - j) + 1 := by omega
          simp [localRaw, Ne.symm hj, ih, hjn, hjs, he, pow_succ]
          ring
        · have hjs : ¬ j < n + 1 := by omega
          simp [localRaw, Ne.symm hj, ih, hjn, hjs]

noncomputable def batchPrefix (w x B n : ℕ) (s : CodeState) :
    List (Coefficient × ℕ) × CodeState :=
  (forIn (List.range n) []
    (fun h terms => ForInStep.yield <$> batchQueryStep w x B h terms) :
      StateM CodeState (List (Coefficient × ℕ))) s

lemma batchPrefix_zero (w x B : ℕ) (s : CodeState) : batchPrefix w x B 0 s = ([], s) := rfl

lemma batchPrefix_succ (w x B n : ℕ) (s : CodeState) :
    batchPrefix w x B (n + 1) s =
      let z := batchPrefix w x B n s
      batchQueryStep w x B n z.1 z.2 := state_forIn_range_succ _ n [] s

lemma batchPrefix_next (w x B n : ℕ) (s : CodeState) :
    (batchPrefix w x B n s).2.next = s.next + n := by
  induction n with
  | zero => simp [batchPrefix_zero]
  | succ n ih =>
      rw [batchPrefix_succ]
      change (batchPrefix w x B n s).2.next + 1 = s.next + (n + 1)
      rw [ih, Nat.add_assoc]

lemma batchPrefix_terms (w x B n : ℕ) (s : CodeState) :
    (batchPrefix w x B n s).1 =
      (List.range n).map (fun j => (Coefficient.constant (1 / (B : ℝ)), s.next + j)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [batchPrefix_succ]
      change (batchPrefix w x B n s).1 ++
        [(.constant (1 / (B : ℝ)), (batchPrefix w x B n s).2.next)] = _
      rw [ih, batchPrefix_next, List.range_succ, List.map_append]
      rfl

lemma batchPrefix_symbolic_step (w x B n : ℕ) (s : CodeState) (t : Tuning) :
    codeSymbolic t (batchPrefix w x B (n + 1) s).2 =
      symbolicPerform (codeSymbolic t (batchPrefix w x B n s).2) (.query w x) := by
  rw [batchPrefix_succ]
  change codeSymbolic t (emit (.query w x) (batchPrefix w x B n s).2).2 = _
  exact codeSymbolic_emit t (.query w x) _

lemma batchPrefix_aligned (w x B n : ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    (batchPrefix w x B n s).2.next = (codeSymbolic t (batchPrefix w x B n s).2).next := by
  induction n with
  | zero => exact hn
  | succ n ih =>
      rw [batchPrefix_next, batchPrefix_symbolic_step,
        LongTails.Proofs.BirchNonEuclideanExecution.symbolic_next, ← ih, batchPrefix_next]
      omega

lemma batchPrefix_points (w x B n : ℕ) (s : CodeState) (t : Tuning) :
    (codeSymbolic t (batchPrefix w x B n s).2).points = (codeSymbolic t s).points := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [batchPrefix_symbolic_step]
      exact ih

lemma batchPrefix_records (w x B n : ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    let new := codeSymbolic t (batchPrefix w x B n s).2
    ∀ j < n, new.vectors (s.next + j) = (Finsupp.single (s.next + j) 1, 0) ∧
      new.queryPoints (s.next + j) = (codeSymbolic t s).points x := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ha := batchPrefix_aligned w x B n s t hn
      have hn' := batchPrefix_next w x B n s
      have he : (codeSymbolic t (batchPrefix w x B n s).2).next = s.next + n := ha.symm.trans hn'
      dsimp only
      intro j hj
      rw [batchPrefix_symbolic_step]
      by_cases hjn : j = n
      · subst j
        simp [symbolicPerform, symbolicStore, he, batchPrefix_points]
      · have hjn' : j < n := by omega
        have hne : s.next + j ≠ s.next + n := by omega
        simpa only [symbolicPerform, symbolicStore, he, Function.update_of_ne hne] using ih j hjn'

lemma batchPrefix_sets (w x B n : ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    let new := codeSymbolic t (batchPrefix w x B n s).2
    new.queries = (codeSymbolic t s).queries ∪ (Finset.range n).image (fun j => s.next + j) ∧
      new.sharps = (codeSymbolic t s).sharps ∧ new.units = (codeSymbolic t s).units := by
  induction n with
  | zero => simp [batchPrefix_zero]
  | succ n ih =>
      have ha := batchPrefix_aligned w x B n s t hn
      have hn' := batchPrefix_next w x B n s
      have he : (codeSymbolic t (batchPrefix w x B n s).2).next = s.next + n := ha.symm.trans hn'
      dsimp only
      rw [batchPrefix_symbolic_step]
      simp [symbolicPerform, symbolicStore, he, Finset.range_add_one, Finset.union_insert,
        ih.1, ih.2.1, ih.2.2]

lemma localBatch_prefix (w x B : ℕ) (s : CodeState) :
    (localBatch w x B).run s =
      let z := batchPrefix w x B B s
      emit (.mix w z.1) z.2 := rfl

lemma localBatch_register (w x B : ℕ) (s : CodeState) :
    ((localBatch w x B).run s).1 = s.next + B := by
  rw [localBatch_prefix]
  exact batchPrefix_next w x B B s

lemma localBatch_next (w x B : ℕ) (s : CodeState) :
    ((localBatch w x B).run s).2.next = s.next + B + 1 := by
  rw [localBatch_prefix]
  change (batchPrefix w x B B s).2.next + 1 = _
  rw [batchPrefix_next]

lemma localBatch_symbolic (w x B : ℕ) (s : CodeState) (t : Tuning)
    (hn : s.next = (codeSymbolic t s).next) :
    let z := (localBatch w x B).run s
    (codeSymbolic t z.2).vectors z.1 =
      (1 / (B : ℝ)) • ∑ j ∈ Finset.range B, ((Finsupp.single (s.next + j) 1, 0) : LinearValue) := by
  rw [localBatch_prefix]
  dsimp only
  rw [codeSymbolic_emit]
  have ha := batchPrefix_aligned w x B B s t hn
  simp only [InstructionTemplate.instantiate, symbolicPerform, symbolicStore, emit_apply, ha,
    Function.update_self]
  rw [batchPrefix_terms]
  simp only [List.map_map, Function.comp_def, Coefficient.eval]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(batchPrefix_records w x B B s t hn j (Finset.mem_range.mp hj)).1]

lemma commitDifference_symbolic (w x0 m0 xcur mcur xlocal mlocal : ℕ) (s : CodeState)
    (t : Tuning) (hn : s.next = (codeSymbolic t s).next)
    (hm0 : m0 < s.next) (hmc : mcur < s.next) (hml : mlocal < s.next) :
    let z := ((do
      let dx ← emit (.difference w xlocal x0)
      let dm ← emit (.mix w [(.constant 1, mlocal), (.constant (-1), m0)])
      let _ ← emit (.sendVector w 0 dx)
      let _ ← emit (.sendVector w 0 dm)
      let x ← emit (.move 0 xcur dx (.constant 1))
      let m ← emit (.mix 0 [(.constant 1, mcur), (.constant 1, dm)])
      return (x, m)) : StateM CodeState (ℕ × ℕ)) s
    let old := codeSymbolic t s
    let new := codeSymbolic t z.2
    new.points z.1.1 = old.points xcur + (old.points xlocal - old.points x0) ∧
      new.vectors z.1.2 = old.vectors mcur + (old.vectors mlocal - old.vectors m0) := by
  have h0 : m0 ≠ (codeSymbolic t s).next := by omega
  have hc : mcur ≠ (codeSymbolic t s).next := by omega
  have hc1 : mcur ≠ (codeSymbolic t s).next + 1 := by omega
  have hl : mlocal ≠ (codeSymbolic t s).next := by omega
  dsimp only
  simp only [state_bind_apply, state_pure_apply, codeSymbolic_emit, InstructionTemplate.instantiate]
  simp [symbolicPerform, symbolicStore, emit_apply, hn, h0, hc, hc1, hl,
    Coefficient.eval, Nat.add_assoc, sub_eq_add_neg]
  exact neg_one_smul ℝ ((codeSymbolic t s).vectors m0)

lemma deltaStep_symbolic (H k : ℕ) (dispatch worker : ℕ → ℕ)
    (state : (ℕ → ℕ) × (ℕ → ℕ)) (s : CodeState) (η : ℝ) (B : ℕ)
    (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next)
    (hm : ∀ j, state.2 j < s.next) (hx : ∀ j, state.1 j < s.next) :
    let t := canonicalTuning η B
    let z := deltaStep H dispatch worker k state s
    let old := codeSymbolic t s
    let new := codeSymbolic t z.2
    new.points (z.1.1 (k + 1)) = old.points (state.1 k) +
      (1 / (H : ℝ) * η) • ∑ h ∈ Finset.range H,
        ((0, Finsupp.single (s.next + 2 + 4 * h + 2) 1) : LinearValue) ∧
      new.vectors (z.1.2 (k + 1)) = old.vectors (state.2 k) +
        (localRaw (1 / (B : ℝ)) (s.next + 2) (old.vectors (state.2 (dispatch k))) H -
          old.vectors (state.2 (dispatch k))) := by
  let t := canonicalTuning η B
  let w := worker k
  let src := dispatch k
  let s1 := (emit (.sendPoint 0 w (state.1 src)) s).2
  let s2 := (emit (.sendVector 0 w (state.2 src)) s1).2
  let packet := (localMomentum w (state.1 src) (state.2 src) H k).run s2
  have hs2n : s2.next = s.next + 2 := by simp [s2, s1, emit_apply, Nat.add_assoc]
  have hs2 : codeSymbolic t s2 = { codeSymbolic t s with next := (codeSymbolic t s).next + 2 } := by
    simp [s2, s1, codeSymbolic_emit, InstructionTemplate.instantiate, symbolicPerform, Nat.add_assoc]
  have ha2 : s2.next = (codeSymbolic t s2).next := by rw [hs2n, hs2, hn]
  have hm2 : state.2 src < s2.next := by rw [hs2n]; have := hm src; omega
  have hp := localPrefix_values w H k H (state.1 src, state.2 src) s2 η B ha2 hm2
  have hp' : (codeSymbolic t packet.2).vectors packet.1.2 =
      localRaw (1 / (B : ℝ)) s2.next ((codeSymbolic t s2).vectors (state.2 src)) H ∧
      (codeSymbolic t packet.2).points packet.1.1 =
        localPath (1 / (H : ℝ) * η) s2.next ((codeSymbolic t s2).points (state.1 src)) H := by
    simpa only [packet, localMomentum_prefix] using hp
  have hpn := localPrefix_next w H k H (state.1 src, state.2 src) s2
  have hpa := localPrefix_aligned w H k H (state.1 src, state.2 src) s2 t ha2
  have hpm := localPrefix_momentum_lt w H k H (state.1 src, state.2 src) s2 hm2
  have hglobal (j : ℕ) (hj : j < s.next) :
      (codeSymbolic t packet.2).points j = (codeSymbolic t s).points j ∧
        (codeSymbolic t packet.2).vectors j = (codeSymbolic t s).vectors j := by
    have hj2 : j < (codeSymbolic t s2).next := by rw [← ha2, hs2n]; omega
    have hh := codeExtends_symbolic t s2 packet.2
      (localPrefix_extends w H k H (state.1 src, state.2 src) s2) j hj2
    exact ⟨hh.1.trans (by rw [hs2]), hh.2.1.trans (by rw [hs2])⟩
  have hm0 : state.2 src < packet.2.next := by
    change state.2 src < (localPrefix w H k H (state.1 src, state.2 src) s2).2.next
    rw [hpn, hs2n]
    have := hm src
    omega
  have hmc : state.2 k < packet.2.next := by
    change state.2 k < (localPrefix w H k H (state.1 src, state.2 src) s2).2.next
    rw [hpn, hs2n]
    have := hm k
    omega
  have hc := commitDifference_symbolic w (state.1 src) (state.2 src) (state.1 k) (state.2 k)
    packet.1.1 packet.1.2 packet.2 t hpa hm0 hmc hpm
  constructor
  · calc
      _ = (codeSymbolic t packet.2).points (state.1 k) +
          ((codeSymbolic t packet.2).points packet.1.1 - (codeSymbolic t packet.2).points (state.1 src)) := by
        simpa only [deltaStep, state_bind_apply, state_pure_apply, Function.update_self,
          packet, s2, s1, w, src, t, StateT.run] using hc.1
      _ = _ := by
        rw [(hglobal (state.1 k) (hx k)).1, (hglobal (state.1 src) (hx src)).1,
          hp'.2, localPath_closed, hs2, hs2n]
        abel
  · calc
      _ = (codeSymbolic t packet.2).vectors (state.2 k) +
          ((codeSymbolic t packet.2).vectors packet.1.2 - (codeSymbolic t packet.2).vectors (state.2 src)) := by
        simpa only [deltaStep, state_bind_apply, state_pure_apply, Function.update_self,
          packet, s2, s1, w, src, t, StateT.run] using hc.2
      _ = _ := by
        rw [(hglobal (state.2 k) (hm k)).2, (hglobal (state.2 src) (hm src)).2, hp'.1, hs2, hs2n]

def BuildExtends {α : Type} (act : StateM CodeState α) : Prop :=
  ∀ s, CodeExtends s (act s).2

lemma buildExtends_pure {α : Type} (a : α) : BuildExtends (pure a) := codeExtends_refl

lemma buildExtends_emit (i : InstructionTemplate) : BuildExtends (emit i) :=
  fun s => codeExtends_emit s i

lemma buildExtends_bind {α β : Type} (x : StateM CodeState α) (f : α → StateM CodeState β)
    (hx : BuildExtends x) (hf : ∀ a, BuildExtends (f a)) : BuildExtends (x >>= f) := by
  intro s
  exact codeExtends_trans s (x s).2 _ (hx s) (hf (x s).1 (x s).2)

lemma buildExtends_map {α β : Type} (x : StateM CodeState α) (f : α → β)
    (hx : BuildExtends x) : BuildExtends (f <$> x) := hx

lemma buildExtends_localMomentum (w x m H round : ℕ) : BuildExtends (localMomentum w x m H round) := by
  intro s
  exact localPrefix_extends w H round H (x, m) s

lemma codeSymbolic_causal (s : CodeState) (t : Tuning) (j q : ℕ)
    (hq : (codeSymbolic t s).next ≤ q) :
    ((codeSymbolic t s).points j).1 q = 0 ∧ ((codeSymbolic t s).points j).2 q = 0 ∧
      ((codeSymbolic t s).vectors j).1 q = 0 ∧ ((codeSymbolic t s).vectors j).2 q = 0 := by
  let a : Program := {
    instructions := codeInstructions t s
    outputWorker := 0
    outputCount := 0
    outputPoint := fun _ => 0 }
  have hsup := LongTails.Proofs.BirchNonEuclideanSymbolic.symbolic_maps_supported a
  have hb := LongTails.Proofs.BirchNonEuclideanSymbolic.symbolic_beforeNext a
  have hp := LongTails.Proofs.BirchNonEuclideanSymbolic.causal_of_supported a.symbolic hb
    _ (hsup.points j) q hq
  have hv := LongTails.Proofs.BirchNonEuclideanSymbolic.causal_of_supported a.symbolic hb
    _ (hsup.vectors j) q hq
  exact ⟨hp.1, hp.2, hv⟩

end LongTails.Proofs.BirchNonEuclideanCoefficients
