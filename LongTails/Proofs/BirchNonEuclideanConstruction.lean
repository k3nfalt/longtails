import LongTails.Proofs.BirchNonEuclideanFamilies
import LongTails.Proofs.BirchNonEuclideanSymbolic

namespace LongTails.Proofs.BirchNonEuclideanConstruction

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanFamilies

def codeInstructions (t : Tuning) (s : CodeState) : List Instruction :=
  s.instructions.map (InstructionTemplate.instantiate t)

def codeLayout (t : Tuning) (s : CodeState) : Layout := finalLayout (codeInstructions t s)

def CodeValid (workers : ℕ) (t : Tuning) (s : CodeState) : Prop :=
  s.next = (codeLayout t s).next ∧ LegalFrom workers {} (codeInstructions t s)

noncomputable def codeSymbolic (t : Tuning) (s : CodeState) : SymbolicMemory :=
  (codeInstructions t s).foldl symbolicPerform {}

lemma layout_next (s : Layout) (i : Instruction) : (i.layout s).next = s.next + 1 := by
  cases i <;> rfl

lemma layout_length (code : List Instruction) (s : Layout) :
    (code.foldl (fun s i => i.layout s) s).next = s.next + code.length := by
  induction code generalizing s with
  | nil => simp
  | cons i rest ih =>
      rw [List.foldl_cons, ih, layout_next]
      simp only [List.length_cons]
      omega

lemma codeLayout_next (t : Tuning) (s : CodeState) :
    (codeLayout t s).next = 1 + s.instructions.length := by
  simp [codeLayout, finalLayout, layout_length, codeInstructions]

lemma codeSymbolic_next (t : Tuning) (s : CodeState) :
    (codeSymbolic t s).next = 1 + s.instructions.length := by
  have hh (code : List Instruction) (m : SymbolicMemory) :
      (code.foldl symbolicPerform m).next = m.next + code.length := by
    induction code generalizing m with
    | nil => simp
    | cons i rest ih =>
        rw [List.foldl_cons, ih, LongTails.Proofs.BirchNonEuclideanExecution.symbolic_next]
        simp only [List.length_cons]
        omega
  simp [codeSymbolic, codeInstructions, hh]

lemma codeValid_initial (workers : ℕ) (t : Tuning) : CodeValid workers t {} := by
  exact ⟨rfl, trivial⟩

lemma legalFrom_append (workers : ℕ) (s : Layout) (left right : List Instruction) :
    LegalFrom workers s (left ++ right) ↔ LegalFrom workers s left ∧
      LegalFrom workers (left.foldl (fun s i => i.layout s) s) right := by
  induction left generalizing s with
  | nil => simp [LegalFrom]
  | cons i rest ih => simp [LegalFrom, ih, and_assoc]

lemma codeInstructions_emit (t : Tuning) (i : InstructionTemplate) (s : CodeState) :
    codeInstructions t (emit i s).2 = codeInstructions t s ++ [i.instantiate t] := by
  simp [codeInstructions, emit_apply]

lemma codeLayout_emit (t : Tuning) (i : InstructionTemplate) (s : CodeState) :
    codeLayout t (emit i s).2 = (i.instantiate t).layout (codeLayout t s) := by
  simp [codeLayout, finalLayout, codeInstructions_emit, List.foldl_append]

lemma codeSymbolic_emit (t : Tuning) (i : InstructionTemplate) (s : CodeState) :
    codeSymbolic t (emit i s).2 = symbolicPerform (codeSymbolic t s) (i.instantiate t) := by
  simp [codeSymbolic, codeInstructions_emit, List.foldl_append]

lemma codeValid_emit (workers : ℕ) (t : Tuning) (i : InstructionTemplate) (s : CodeState)
    (hs : CodeValid workers t s) (hi : (i.instantiate t).Legal workers (codeLayout t s)) :
    CodeValid workers t (emit i s).2 := by
  refine ⟨?_, ?_⟩
  · rw [codeLayout_emit, layout_next, ← hs.1]
    rfl
  · rw [codeInstructions_emit, legalFrom_append]
    exact ⟨hs.2, hi, trivial⟩

lemma layout_points_mono (s : Layout) (i : Instruction) (w : ℕ) :
    s.points w ⊆ (i.layout s).points w := by
  intro j hj
  cases i <;> simp only [Instruction.layout]
  all_goals first | exact hj | skip
  all_goals
    simp only [Function.update_apply]
    split_ifs <;> simp_all

lemma layout_vectors_mono (s : Layout) (i : Instruction) (w : ℕ) :
    s.vectors w ⊆ (i.layout s).vectors w := by
  intro j hj
  cases i <;> simp only [Instruction.layout]
  all_goals first | exact hj | skip
  all_goals
    simp only [Function.update_apply]
    split_ifs <;> simp_all

lemma state_forIn_invariant {α β : Type} (step : α → β → StateM CodeState β)
    (xs : List α) (Inv : β → CodeState → Prop)
    (hstep : ∀ i ∈ xs, ∀ b s, Inv b s → Inv (step i b s).1 (step i b s).2)
    (b : β) (s : CodeState) (hs : Inv b s) :
    let z := (forIn xs b (fun i b => ForInStep.yield <$> step i b) : StateM CodeState β) s
    Inv z.1 z.2 := by
  induction xs generalizing b s with
  | nil => exact hs
  | cons i xs ih =>
      rw [state_forIn_cons]
      exact ih (fun j hj => hstep j (List.mem_cons_of_mem i hj)) _ _
        (hstep i (List.mem_cons_self) b s hs)

def Retains (t : Tuning) (s s' : CodeState) : Prop :=
  ∀ w, (codeLayout t s).points w ⊆ (codeLayout t s').points w ∧
    (codeLayout t s).vectors w ⊆ (codeLayout t s').vectors w

lemma retains_refl (t : Tuning) (s : CodeState) : Retains t s s := fun _ => ⟨fun _ h => h, fun _ h => h⟩

lemma retains_trans (t : Tuning) (s s' s'' : CodeState)
    (h : Retains t s s') (h' : Retains t s' s'') : Retains t s s'' :=
  fun w => ⟨(h w).1.trans (h' w).1, (h w).2.trans (h' w).2⟩

lemma retains_emit (t : Tuning) (i : InstructionTemplate) (s : CodeState) :
    Retains t s (emit i s).2 := by
  intro w
  rw [codeLayout_emit]
  exact ⟨layout_points_mono _ _ _, layout_vectors_mono _ _ _⟩

lemma query_member (workers : ℕ) (t : Tuning) (s : CodeState)
    (hs : CodeValid workers t s) (w x : ℕ) :
    (emit (.query w x) s).1 ∈ (codeLayout t (emit (.query w x) s).2).vectors w := by
  rw [codeLayout_emit]
  simp [InstructionTemplate.instantiate, Instruction.layout, emit_apply, hs.1]

lemma mix_member (workers : ℕ) (t : Tuning) (s : CodeState)
    (hs : CodeValid workers t s) (w : ℕ) (terms : List (Coefficient × ℕ)) :
    (emit (.mix w terms) s).1 ∈ (codeLayout t (emit (.mix w terms) s).2).vectors w := by
  rw [codeLayout_emit]
  simp [InstructionTemplate.instantiate, Instruction.layout, emit_apply, hs.1]

lemma sharp_member (workers : ℕ) (t : Tuning) (s : CodeState)
    (hs : CodeValid workers t s) (w v : ℕ) :
    (emit (.sharp w v) s).1 ∈ (codeLayout t (emit (.sharp w v) s).2).vectors w := by
  rw [codeLayout_emit]
  simp [InstructionTemplate.instantiate, Instruction.layout, emit_apply, hs.1]

lemma move_member (workers : ℕ) (t : Tuning) (s : CodeState)
    (hs : CodeValid workers t s) (w x v : ℕ) (η : Coefficient) :
    (emit (.move w x v η) s).1 ∈ (codeLayout t (emit (.move w x v η) s).2).points w := by
  rw [codeLayout_emit]
  simp [InstructionTemplate.instantiate, Instruction.layout, emit_apply, hs.1]

lemma mix_legal (workers : ℕ) (t : Tuning) (s : CodeState) (w : ℕ)
    (terms : List (Coefficient × ℕ)) (hw : w < workers)
    (ht : ∀ v ∈ terms, v.2 ∈ (codeLayout t s).vectors w) :
    ((InstructionTemplate.mix w terms).instantiate t).Legal workers (codeLayout t s) := by
  refine ⟨hw, ?_⟩
  intro v hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  exact ht u hu

lemma batchQueryStep_valid (workers : ℕ) (t : Tuning) (w x B i : ℕ)
    (terms : List (Coefficient × ℕ)) (s : CodeState) (hs : CodeValid workers t s)
    (hw : w < workers) (hx : x ∈ (codeLayout t s).points w)
    (ht : ∀ v ∈ terms, v.2 ∈ (codeLayout t s).vectors w) :
    let z := batchQueryStep w x B i terms s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧
      ∀ v ∈ z.1, v.2 ∈ (codeLayout t z.2).vectors w := by
  dsimp only [batchQueryStep, state_bind_apply, state_pure_apply]
  refine ⟨codeValid_emit workers t (.query w x) s hs ⟨hw, hx⟩, retains_emit t _ s, ?_⟩
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact ((retains_emit t (.query w x) s) w).2 (ht v hv)
  · simp only [List.mem_singleton] at hv
    subst v
    exact query_member workers t s hs w x

lemma localBatch_valid (workers : ℕ) (t : Tuning) (w x B : ℕ) (s : CodeState)
    (hs : CodeValid workers t s) (hw : w < workers) (hx : x ∈ (codeLayout t s).points w) :
    let z := (localBatch w x B).run s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧ z.1 ∈ (codeLayout t z.2).vectors w := by
  let Inv := fun (terms : List (Coefficient × ℕ)) (s' : CodeState) => CodeValid workers t s' ∧ Retains t s s' ∧
    ∀ v ∈ terms, v.2 ∈ (codeLayout t s').vectors w
  have hi : Inv [] s := ⟨hs, retains_refl t s, by simp⟩
  have hh := state_forIn_invariant (batchQueryStep w x B) (List.range B) Inv
    (fun i _ terms s' h => by
      obtain ⟨hc, hr, ht⟩ := batchQueryStep_valid workers t w x B i terms s'
        h.1 hw ((h.2.1 w).1 hx) h.2.2
      exact ⟨hc, retains_trans t s s' _ h.2.1 hr, ht⟩) [] s hi
  rw [localBatch_run]
  dsimp only
  let z := (forIn (List.range B) []
    (fun i terms => ForInStep.yield <$> batchQueryStep w x B i terms) :
      StateM CodeState (List (Coefficient × ℕ))) s
  change Inv z.1 z.2 at hh
  refine ⟨codeValid_emit workers t (.mix w z.1) z.2 hh.1 (mix_legal workers t z.2 w z.1 hw hh.2.2),
    retains_trans t s z.2 _ hh.2.1 (retains_emit t _ z.2), mix_member workers t z.2 hh.1 w z.1⟩

lemma sendPoint_valid (workers : ℕ) (t : Tuning) (s : CodeState) (hs : CodeValid workers t s)
    (w u x : ℕ) (hw : w < workers) (hu : u < workers) (hx : x ∈ (codeLayout t s).points w) :
    CodeValid workers t (emit (.sendPoint w u x) s).2 ∧
      x ∈ (codeLayout t (emit (.sendPoint w u x) s).2).points u := by
  refine ⟨codeValid_emit workers t _ s hs ⟨hw, hu, hx⟩, ?_⟩
  rw [codeLayout_emit]
  simp [InstructionTemplate.instantiate, Instruction.layout]

lemma sendVector_valid (workers : ℕ) (t : Tuning) (s : CodeState) (hs : CodeValid workers t s)
    (w u v : ℕ) (hw : w < workers) (hu : u < workers) (hv : v ∈ (codeLayout t s).vectors w) :
    CodeValid workers t (emit (.sendVector w u v) s).2 ∧
      v ∈ (codeLayout t (emit (.sendVector w u v) s).2).vectors u := by
  refine ⟨codeValid_emit workers t _ s hs ⟨hw, hu, hv⟩, ?_⟩
  rw [codeLayout_emit]
  simp [InstructionTemplate.instantiate, Instruction.layout]

lemma collectedStep_valid (workers : ℕ) (t : Tuning) (worker : ℕ → ℕ)
    (round point B h : ℕ) (terms : List (Coefficient × ℕ)) (s : CodeState)
    (hs : CodeValid workers t s) (hw : worker (round * B + h) < workers)
    (hx : point ∈ (codeLayout t s).points 0)
    (ht : ∀ v ∈ terms, v.2 ∈ (codeLayout t s).vectors 0) :
    let z := collectedStep worker round point B h terms s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧
      ∀ v ∈ z.1, v.2 ∈ (codeLayout t z.2).vectors 0 := by
  have hw0 : 0 < workers := by omega
  let w := worker (round * B + h)
  let s1 := (emit (.sendPoint 0 w point) s).2
  let s2 := (emit (.query w point) s1).2
  let q := (emit (.query w point) s1).1
  let s3 := (emit (.sendVector w 0 q) s2).2
  have h1 := sendPoint_valid workers t s hs 0 w point hw0 hw hx
  have h2 : CodeValid workers t s2 := codeValid_emit workers t (.query w point) s1 h1.1 ⟨hw, h1.2⟩
  have hq : q ∈ (codeLayout t s2).vectors w := query_member workers t s1 h1.1 w point
  have h3 := sendVector_valid workers t s2 h2 w 0 q hw hw0 hq
  have hr : Retains t s s3 := retains_trans t s s2 s3
    (retains_trans t s s1 s2 (retains_emit t _ s) (retains_emit t _ s1)) (retains_emit t _ s2)
  change CodeValid workers t s3 ∧ Retains t s s3 ∧
    ∀ v ∈ terms ++ [(.constant (1 / (B : ℝ)), q)], v.2 ∈ (codeLayout t s3).vectors 0
  refine ⟨h3.1, hr, ?_⟩
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact (hr 0).2 (ht v hv)
  · simp only [List.mem_singleton] at hv
    subst v
    exact h3.2

lemma collectedBatch_valid (workers : ℕ) (t : Tuning) (worker : ℕ → ℕ)
    (round point B : ℕ) (s : CodeState) (hs : CodeValid workers t s)
    (hw0 : 0 < workers) (hw : ∀ h < B, worker (round * B + h) < workers)
    (hx : point ∈ (codeLayout t s).points 0) :
    let z := (collectedBatch worker round point B).run s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧ z.1 ∈ (codeLayout t z.2).vectors 0 := by
  let Inv := fun (terms : List (Coefficient × ℕ)) (s' : CodeState) =>
    CodeValid workers t s' ∧ Retains t s s' ∧ ∀ v ∈ terms, v.2 ∈ (codeLayout t s').vectors 0
  have hi : Inv [] s := ⟨hs, retains_refl t s, by simp⟩
  have hh := state_forIn_invariant (collectedStep worker round point B) (List.range B) Inv
    (fun i hi terms s' h => by
      obtain ⟨hc, hr, ht⟩ := collectedStep_valid workers t worker round point B i terms s'
        h.1 (hw i (List.mem_range.mp hi)) ((h.2.1 0).1 hx) h.2.2
      exact ⟨hc, retains_trans t s s' _ h.2.1 hr, ht⟩) [] s hi
  rw [collectedBatch_run]
  dsimp only
  let z := (forIn (List.range B) []
    (fun i terms => ForInStep.yield <$> collectedStep worker round point B i terms) :
      StateM CodeState (List (Coefficient × ℕ))) s
  change Inv z.1 z.2 at hh
  exact ⟨codeValid_emit workers t (.mix 0 z.1) z.2 hh.1
      (mix_legal workers t z.2 0 z.1 hw0 hh.2.2),
    retains_trans t s z.2 _ hh.2.1 (retains_emit t _ z.2), mix_member workers t z.2 hh.1 0 z.1⟩

lemma batchStep_valid (workers : ℕ) (t : Tuning) (ht : t.Valid) (worker : ℕ → ℕ)
    (B k : ℕ) (points : ℕ → ℕ) (s : CodeState) (hs : CodeValid workers t s)
    (hw0 : 0 < workers) (hw : ∀ h < B, worker (k * B + h) < workers)
    (hx : ∀ j, points j ∈ (codeLayout t s).points 0) :
    let z := batchStep worker B k points s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧
      ∀ j, z.1 j ∈ (codeLayout t z.2).points 0 := by
  let z1 := (collectedBatch worker k (points k) B).run s
  let s2 := (emit (.sharp 0 z1.1) z1.2).2
  let d := (emit (.sharp 0 z1.1) z1.2).1
  let s3 := (emit (.move 0 (points k) d (.step k)) s2).2
  let x := (emit (.move 0 (points k) d (.step k)) s2).1
  have h1 := collectedBatch_valid workers t worker k (points k) B s hs hw0 hw (hx k)
  have h2 : CodeValid workers t s2 := codeValid_emit workers t (.sharp 0 z1.1) z1.2 h1.1 ⟨hw0, h1.2.2⟩
  have hd : d ∈ (codeLayout t s2).vectors 0 := sharp_member workers t z1.2 h1.1 0 z1.1
  have hr2 : Retains t s s2 := retains_trans t s z1.2 s2 h1.2.1 (retains_emit t _ z1.2)
  have h3 : CodeValid workers t s3 := codeValid_emit workers t (.move 0 (points k) d (.step k)) s2
    h2 ⟨hw0, (hr2 0).1 (hx k), hd, ht.1 k⟩
  have hx3 : x ∈ (codeLayout t s3).points 0 := move_member workers t s2 h2 0 (points k) d (.step k)
  have hr3 : Retains t s s3 := retains_trans t s s2 s3 hr2 (retains_emit t _ s2)
  change CodeValid workers t s3 ∧ Retains t s s3 ∧
    ∀ j, Function.update points (k + 1) x j ∈ (codeLayout t s3).points 0
  refine ⟨h3, hr3, ?_⟩
  intro j
  by_cases hj : j = k + 1
  · simpa [hj] using hx3
  · simpa [Function.update_of_ne hj] using (hr3 0).1 (hx j)

lemma batchCode_valid (workers : ℕ) (t : Tuning) (ht : t.Valid) (worker : ℕ → ℕ)
    (K B : ℕ) (hw0 : 0 < workers) (hw : ∀ j, worker j < workers) :
    let z := (batchCode worker K B).run {}
    CodeValid workers t z.2 ∧ ∀ j, z.1 j ∈ (codeLayout t z.2).points 0 := by
  rw [batchCode_run]
  let Inv := fun (points : ℕ → ℕ) (s : CodeState) =>
    CodeValid workers t s ∧ ∀ j, points j ∈ (codeLayout t s).points 0
  apply state_forIn_invariant (batchStep worker B) (List.range K) Inv
  · intro k _ points s h
    have hh := batchStep_valid workers t ht worker B k points s h.1 hw0 (fun h _ => hw _) h.2
    exact ⟨hh.1, hh.2.2⟩
  · exact ⟨codeValid_initial workers t, fun _ => by simp [codeLayout, codeInstructions, finalLayout]⟩

lemma minibatchFamily_legal (workers : ℕ) (t : Tuning) (ht : t.Valid) (worker : ℕ → ℕ)
    (K B : ℕ) (hw0 : 0 < workers) (hw : ∀ j, worker j < workers) :
    ((minibatchFamily worker).instantiate K B t).Legal workers := by
  have hh := batchCode_valid workers t ht worker K B hw0 hw
  exact ⟨hh.1.2, hw0, fun j => hh.2 j.val⟩

lemma momentumStep_valid (workers : ℕ) (t : Tuning) (ht : t.Valid)
    (w H round h : ℕ) (state : ℕ × ℕ) (s : CodeState) (hs : CodeValid workers t s)
    (hw : w < workers) (hx : state.1 ∈ (codeLayout t s).points w)
    (hm : state.2 ∈ (codeLayout t s).vectors w) :
    let z := momentumStep w H round h state s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧
      z.1.1 ∈ (codeLayout t z.2).points w ∧ z.1.2 ∈ (codeLayout t z.2).vectors w := by
  let s1 := (emit (.query w state.1) s).2
  let q := (emit (.query w state.1) s).1
  let α := Coefficient.momentum (round * H + h)
  let terms := [(α, q), (.add (.constant 1) (.neg α), state.2)]
  let s2 := (emit (.mix w terms) s1).2
  let m := (emit (.mix w terms) s1).1
  let s3 := (emit (.sharp w m) s2).2
  let d := (emit (.sharp w m) s2).1
  let γ := Coefficient.mul (.constant (1 / (H : ℝ))) (.step round)
  let s4 := (emit (.move w state.1 d γ) s3).2
  let x := (emit (.move w state.1 d γ) s3).1
  have h1 : CodeValid workers t s1 := codeValid_emit workers t _ s hs ⟨hw, hx⟩
  have hq : q ∈ (codeLayout t s1).vectors w := query_member workers t s hs w state.1
  have hterms : ∀ v ∈ terms, v.2 ∈ (codeLayout t s1).vectors w := by
    intro v hv
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact hq
    · exact ((retains_emit t (.query w state.1) s) w).2 hm
  have h2 : CodeValid workers t s2 :=
    codeValid_emit workers t _ s1 h1 (mix_legal workers t s1 w terms hw hterms)
  have hm2 : m ∈ (codeLayout t s2).vectors w := mix_member workers t s1 h1 w terms
  have h3 : CodeValid workers t s3 := codeValid_emit workers t _ s2 h2 ⟨hw, hm2⟩
  have hd : d ∈ (codeLayout t s3).vectors w := sharp_member workers t s2 h2 w m
  have hr2 : Retains t s s2 := retains_trans t s s1 s2 (retains_emit t _ s) (retains_emit t _ s1)
  have hr3 : Retains t s s3 := retains_trans t s s2 s3 hr2 (retains_emit t _ s2)
  have hγ : 0 ≤ γ.eval t := by
    change 0 ≤ (1 / (H : ℝ)) * t.step round
    exact mul_nonneg (by positivity) (ht.1 round)
  have h4 : CodeValid workers t s4 :=
    codeValid_emit workers t _ s3 h3 ⟨hw, (hr3 w).1 hx, hd, hγ⟩
  have hx4 : x ∈ (codeLayout t s4).points w := move_member workers t s3 h3 w state.1 d γ
  have hm4 : m ∈ (codeLayout t s4).vectors w :=
    ((retains_emit t (.move w state.1 d γ) s3) w).2
      (((retains_emit t (.sharp w m) s2) w).2 hm2)
  exact ⟨h4, retains_trans t s s3 s4 hr3 (retains_emit t _ s3), hx4, hm4⟩

lemma localMomentum_valid (workers : ℕ) (t : Tuning) (ht : t.Valid)
    (w x m H round : ℕ) (s : CodeState) (hs : CodeValid workers t s)
    (hw : w < workers) (hx : x ∈ (codeLayout t s).points w)
    (hm : m ∈ (codeLayout t s).vectors w) :
    let z := (localMomentum w x m H round).run s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧
      z.1.1 ∈ (codeLayout t z.2).points w ∧ z.1.2 ∈ (codeLayout t z.2).vectors w := by
  rw [localMomentum_run]
  let Inv := fun (state : ℕ × ℕ) (s' : CodeState) => CodeValid workers t s' ∧ Retains t s s' ∧
    state.1 ∈ (codeLayout t s').points w ∧ state.2 ∈ (codeLayout t s').vectors w
  apply state_forIn_invariant (momentumStep w H round) (List.range H) Inv
  · intro h _ state s' hp
    have hh := momentumStep_valid workers t ht w H round h state s' hp.1 hw hp.2.2.1 hp.2.2.2
    exact ⟨hh.1, retains_trans t s s' _ hp.2.1 hh.2.1, hh.2.2⟩
  · exact ⟨hs, retains_refl t s, hx, hm⟩

lemma difference_valid (workers : ℕ) (t : Tuning) (s : CodeState) (hs : CodeValid workers t s)
    (w x y : ℕ) (hw : w < workers) (hx : x ∈ (codeLayout t s).points w)
    (hy : y ∈ (codeLayout t s).points w) :
    CodeValid workers t (emit (.difference w x y) s).2 ∧
      (emit (.difference w x y) s).1 ∈ (codeLayout t (emit (.difference w x y) s).2).vectors w := by
  refine ⟨codeValid_emit workers t _ s hs ⟨hw, hx, hy⟩, ?_⟩
  rw [codeLayout_emit]
  simp [InstructionTemplate.instantiate, Instruction.layout, emit_apply, hs.1]

lemma sharedPacketStep_valid (workers m H k point momentum i : ℕ)
    (t : Tuning) (ht : t.Valid)
    (terms : List (Coefficient × ℕ) × List (Coefficient × ℕ)) (s : CodeState)
    (hs : CodeValid workers t s) (hw : i + 1 < workers)
    (hx : point ∈ (codeLayout t s).points 0)
    (hm : momentum ∈ (codeLayout t s).vectors 0)
    (hv : ∀ v ∈ terms.1 ++ terms.2, v.2 ∈ (codeLayout t s).vectors 0) :
    let z := sharedPacketStep m H k point momentum i terms s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧
      ∀ v ∈ z.1.1 ++ z.1.2, v.2 ∈ (codeLayout t z.2).vectors 0 := by
  have hw0 : 0 < workers := by omega
  let w := i + 1
  let s1 := (emit (.sendPoint 0 w point) s).2
  let s2 := (emit (.sendVector 0 w momentum) s1).2
  let z := (localMomentum w point momentum H k).run s2
  let dx := (emit (.difference w z.1.1 point) z.2).1
  let s3 := (emit (.difference w z.1.1 point) z.2).2
  let s4 := (emit (.sendVector w 0 dx) s3).2
  let s5 := (emit (.sendVector w 0 z.1.2) s4).2
  have h1 := sendPoint_valid workers t s hs 0 w point hw0 hw hx
  have h2 := sendVector_valid workers t s1 h1.1 0 w momentum hw0 hw
    (((retains_emit t (.sendPoint 0 w point) s) 0).2 hm)
  have hx2 := ((retains_emit t (.sendVector 0 w momentum) s1) w).1 h1.2
  have hz := localMomentum_valid workers t ht w point momentum H k s2 h2.1 hw hx2 h2.2
  have h3 := difference_valid workers t z.2 hz.1 w z.1.1 point hw hz.2.2.1
    ((hz.2.1 w).1 hx2)
  have h4 := sendVector_valid workers t s3 h3.1 w 0 dx hw hw0 h3.2
  have hm4 := ((retains_emit t (.sendVector w 0 dx) s3) w).2
    (((retains_emit t (.difference w z.1.1 point) z.2) w).2 hz.2.2.2)
  have h5 := sendVector_valid workers t s4 h4.1 w 0 z.1.2 hw hw0 hm4
  have hr2 : Retains t s s2 := retains_trans t s s1 s2 (retains_emit t _ s) (retains_emit t _ s1)
  have hr3 : Retains t s s3 := retains_trans t s z.2 s3
    (retains_trans t s s2 z.2 hr2 hz.2.1) (retains_emit t _ z.2)
  have hr5 : Retains t s s5 := retains_trans t s s4 s5
    (retains_trans t s s3 s4 hr3 (retains_emit t _ s3)) (retains_emit t _ s4)
  have hd5 := ((retains_emit t (.sendVector w 0 z.1.2) s4) 0).2 h4.2
  change CodeValid workers t s5 ∧ Retains t s s5 ∧
    ∀ v ∈ (terms.1 ++ [(.constant (1 / (m : ℝ)), dx)]) ++
      (terms.2 ++ [(.constant (1 / (m : ℝ)), z.1.2)]), v.2 ∈ (codeLayout t s5).vectors 0
  refine ⟨h5.1, hr5, ?_⟩
  intro v hv'
  simp only [List.mem_append, List.mem_singleton] at hv'
  rcases hv' with (hv' | rfl) | (hv' | rfl)
  · exact (hr5 0).2 (hv v (List.mem_append_left _ hv'))
  · exact hd5
  · exact (hr5 0).2 (hv v (List.mem_append_right _ hv'))
  · exact h5.2

lemma sharedRoundStep_valid (workers m H k : ℕ) (t : Tuning) (ht : t.Valid)
    (state : (ℕ → ℕ) × ℕ) (s : CodeState) (hs : CodeValid workers t s)
    (hw0 : 0 < workers) (hw : m < workers)
    (hx : ∀ j, state.1 j ∈ (codeLayout t s).points 0)
    (hm : state.2 ∈ (codeLayout t s).vectors 0) :
    let z := sharedRoundStep m H k state s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧
      (∀ j, z.1.1 j ∈ (codeLayout t z.2).points 0) ∧
      z.1.2 ∈ (codeLayout t z.2).vectors 0 := by
  let Inv := fun (terms : List (Coefficient × ℕ) × List (Coefficient × ℕ)) (s' : CodeState) =>
    CodeValid workers t s' ∧ Retains t s s' ∧
      ∀ v ∈ terms.1 ++ terms.2, v.2 ∈ (codeLayout t s').vectors 0
  have hi : Inv ([], []) s := ⟨hs, retains_refl t s, by simp⟩
  have hh := state_forIn_invariant (sharedPacketStep m H k (state.1 k) state.2)
    (List.range m) Inv (fun i hi terms s' h => by
      have hwi : i + 1 < workers := by have := List.mem_range.mp hi; omega
      have hp := sharedPacketStep_valid workers m H k (state.1 k) state.2 i t ht terms s'
        h.1 hwi ((h.2.1 0).1 (hx k)) ((h.2.1 0).2 hm) h.2.2
      exact ⟨hp.1, retains_trans t s s' _ h.2.1 hp.2.1, hp.2.2⟩) ([], []) s hi
  let z := (forIn (List.range m) ([], [])
    (fun i terms => ForInStep.yield <$> sharedPacketStep m H k (state.1 k) state.2 i terms) :
      StateM CodeState (List (Coefficient × ℕ) × List (Coefficient × ℕ))) s
  change Inv z.1 z.2 at hh
  let dx := (emit (.mix 0 z.1.1) z.2).1
  let s1 := (emit (.mix 0 z.1.1) z.2).2
  let x := (emit (.move 0 (state.1 k) dx (.constant 1)) s1).1
  let s2 := (emit (.move 0 (state.1 k) dx (.constant 1)) s1).2
  let mom := (emit (.mix 0 z.1.2) s2).1
  let s3 := (emit (.mix 0 z.1.2) s2).2
  have h1 : CodeValid workers t s1 := codeValid_emit workers t _ z.2 hh.1
    (mix_legal workers t z.2 0 z.1.1 hw0 (fun v hv => hh.2.2 v (List.mem_append_left _ hv)))
  have hd : dx ∈ (codeLayout t s1).vectors 0 := mix_member workers t z.2 hh.1 0 z.1.1
  have hr1 : Retains t s s1 := retains_trans t s z.2 s1 hh.2.1 (retains_emit t _ z.2)
  have h2 : CodeValid workers t s2 := codeValid_emit workers t _ s1 h1
    ⟨hw0, (hr1 0).1 (hx k), hd, by norm_num [InstructionTemplate.instantiate, Coefficient.eval]⟩
  have hx2 : x ∈ (codeLayout t s2).points 0 := move_member workers t s1 h1 0 (state.1 k) dx (.constant 1)
  have hrz2 : Retains t z.2 s2 := retains_trans t z.2 s1 s2 (retains_emit t _ z.2) (retains_emit t _ s1)
  have h3 : CodeValid workers t s3 := codeValid_emit workers t _ s2 h2
    (mix_legal workers t s2 0 z.1.2 hw0
      (fun v hv => (hrz2 0).2 (hh.2.2 v (List.mem_append_right _ hv))))
  have hm3 : mom ∈ (codeLayout t s3).vectors 0 := mix_member workers t s2 h2 0 z.1.2
  have hr3 : Retains t s s3 := retains_trans t s s2 s3
    (retains_trans t s z.2 s2 hh.2.1 hrz2) (retains_emit t _ s2)
  change CodeValid workers t s3 ∧ Retains t s s3 ∧
    (∀ j, Function.update state.1 (k + 1) x j ∈ (codeLayout t s3).points 0) ∧
    mom ∈ (codeLayout t s3).vectors 0
  refine ⟨h3, hr3, ?_, hm3⟩
  intro j
  by_cases hj : j = k + 1
  · simpa [hj] using ((retains_emit t (.mix 0 z.1.2) s2) 0).1 hx2
  · simpa [Function.update_of_ne hj] using (hr3 0).1 (hx j)

lemma sharedCode_valid (workers m H K B : ℕ) (t : Tuning) (ht : t.Valid)
    (hw0 : 0 < workers) (hw : m < workers) :
    let z := (sharedCode m H K B).run {}
    CodeValid workers t z.2 ∧ ∀ j, z.1 j ∈ (codeLayout t z.2).points 0 := by
  have hx : 0 ∈ (codeLayout t {}).points 0 := by simp [codeLayout, codeInstructions, finalLayout]
  have hi := localBatch_valid workers t 0 0 (m * B) {} (codeValid_initial workers t) hw0 hx
  let init := (localBatch 0 0 (m * B)).run {}
  let Inv := fun (state : (ℕ → ℕ) × ℕ) (s : CodeState) => CodeValid workers t s ∧
    (∀ j, state.1 j ∈ (codeLayout t s).points 0) ∧ state.2 ∈ (codeLayout t s).vectors 0
  have hh := state_forIn_invariant (sharedRoundStep m H) (List.range K) Inv
    (fun k _ state s h => by
      have hc := sharedRoundStep_valid workers m H k t ht state s h.1 hw0 hw h.2.1 h.2.2
      exact ⟨hc.1, hc.2.2⟩) ((fun _ => 0), init.1) init.2
      ⟨hi.1, (fun _ => (hi.2.1 0).1 hx), hi.2.2⟩
  rw [sharedCode_run]
  exact ⟨hh.1, hh.2.1⟩

lemma sharedFamily_legal (workers m H K B : ℕ) (t : Tuning) (ht : t.Valid)
    (hw0 : 0 < workers) (hw : m < workers) :
    ((sharedMomentumFamily m H).instantiate K B t).Legal workers := by
  have hh := sharedCode_valid workers m H K B t ht hw0 hw
  exact ⟨hh.1.2, hw0, fun j => hh.2 j.val⟩

lemma deltaStep_valid (workers H k : ℕ) (dispatch worker : ℕ → ℕ)
    (t : Tuning) (ht : t.Valid) (state : (ℕ → ℕ) × (ℕ → ℕ))
    (s : CodeState) (hs : CodeValid workers t s) (hw : worker k < workers)
    (hx : ∀ j, state.1 j ∈ (codeLayout t s).points 0)
    (hm : ∀ j, state.2 j ∈ (codeLayout t s).vectors 0) :
    let z := deltaStep H dispatch worker k state s
    CodeValid workers t z.2 ∧ Retains t s z.2 ∧
      (∀ j, z.1.1 j ∈ (codeLayout t z.2).points 0) ∧
      ∀ j, z.1.2 j ∈ (codeLayout t z.2).vectors 0 := by
  have hw0 : 0 < workers := by omega
  let w := worker k
  let src := dispatch k
  let x0 := state.1 src
  let m0 := state.2 src
  let s1 := (emit (.sendPoint 0 w x0) s).2
  let s2 := (emit (.sendVector 0 w m0) s1).2
  let z := (localMomentum w x0 m0 H k).run s2
  let dx := (emit (.difference w z.1.1 x0) z.2).1
  let s3 := (emit (.difference w z.1.1 x0) z.2).2
  let terms : List (Coefficient × ℕ) := [(.constant 1, z.1.2), (.constant (-1), m0)]
  let dm := (emit (.mix w terms) s3).1
  let s4 := (emit (.mix w terms) s3).2
  let s5 := (emit (.sendVector w 0 dx) s4).2
  let s6 := (emit (.sendVector w 0 dm) s5).2
  let x := (emit (.move 0 (state.1 k) dx (.constant 1)) s6).1
  let s7 := (emit (.move 0 (state.1 k) dx (.constant 1)) s6).2
  let ts : List (Coefficient × ℕ) := [(.constant 1, state.2 k), (.constant 1, dm)]
  let mom := (emit (.mix 0 ts) s7).1
  let s8 := (emit (.mix 0 ts) s7).2
  have h1 := sendPoint_valid workers t s hs 0 w x0 hw0 hw (hx src)
  have h2 := sendVector_valid workers t s1 h1.1 0 w m0 hw0 hw
    (((retains_emit t (.sendPoint 0 w x0) s) 0).2 (hm src))
  have hx2 := ((retains_emit t (.sendVector 0 w m0) s1) w).1 h1.2
  have hz := localMomentum_valid workers t ht w x0 m0 H k s2 h2.1 hw hx2 h2.2
  have h3 := difference_valid workers t z.2 hz.1 w z.1.1 x0 hw hz.2.2.1
    ((hz.2.1 w).1 hx2)
  have hr23 : Retains t s2 s3 := retains_trans t s2 z.2 s3 hz.2.1 (retains_emit t _ z.2)
  have hm3 : ∀ v ∈ terms, v.2 ∈ (codeLayout t s3).vectors w := by
    intro v hv
    simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ((retains_emit t (.difference w z.1.1 x0) z.2) w).2 hz.2.2.2
    · exact (hr23 w).2 h2.2
  have h4 : CodeValid workers t s4 := codeValid_emit workers t _ s3 h3.1
    (mix_legal workers t s3 w terms hw hm3)
  have hdm : dm ∈ (codeLayout t s4).vectors w := mix_member workers t s3 h3.1 w terms
  have h5 := sendVector_valid workers t s4 h4 w 0 dx hw hw0
    (((retains_emit t (.mix w terms) s3) w).2 h3.2)
  have h6 := sendVector_valid workers t s5 h5.1 w 0 dm hw hw0
    (((retains_emit t (.sendVector w 0 dx) s4) w).2 hdm)
  have hr02 : Retains t s s2 := retains_trans t s s1 s2 (retains_emit t _ s) (retains_emit t _ s1)
  have hr04 : Retains t s s4 := retains_trans t s s3 s4
    (retains_trans t s s2 s3 hr02 hr23) (retains_emit t _ s3)
  have hr06 : Retains t s s6 := retains_trans t s s5 s6
    (retains_trans t s s4 s5 hr04 (retains_emit t _ s4)) (retains_emit t _ s5)
  have hdx6 := ((retains_emit t (.sendVector w 0 dm) s5) 0).2 h5.2
  have h7 : CodeValid workers t s7 := codeValid_emit workers t _ s6 h6.1
    ⟨hw0, (hr06 0).1 (hx k), hdx6, by norm_num [InstructionTemplate.instantiate, Coefficient.eval]⟩
  have hr07 : Retains t s s7 := retains_trans t s s6 s7 hr06 (retains_emit t _ s6)
  have hts : ∀ v ∈ ts, v.2 ∈ (codeLayout t s7).vectors 0 := by
    intro v hv
    simp only [ts, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact (hr07 0).2 (hm k)
    · exact ((retains_emit t (.move 0 (state.1 k) dx (.constant 1)) s6) 0).2 h6.2
  have h8 : CodeValid workers t s8 := codeValid_emit workers t _ s7 h7
    (mix_legal workers t s7 0 ts hw0 hts)
  have hx7 : x ∈ (codeLayout t s7).points 0 := move_member workers t s6 h6.1 0 (state.1 k) dx (.constant 1)
  have hm8 : mom ∈ (codeLayout t s8).vectors 0 := mix_member workers t s7 h7 0 ts
  have hr08 : Retains t s s8 := retains_trans t s s7 s8 hr07 (retains_emit t _ s7)
  change CodeValid workers t s8 ∧ Retains t s s8 ∧
    (∀ j, Function.update state.1 (k + 1) x j ∈ (codeLayout t s8).points 0) ∧
    ∀ j, Function.update state.2 (k + 1) mom j ∈ (codeLayout t s8).vectors 0
  refine ⟨h8, hr08, ?_, ?_⟩
  · intro j
    by_cases hj : j = k + 1
    · simpa [hj] using ((retains_emit t (.mix 0 ts) s7) 0).1 hx7
    · simpa [Function.update_of_ne hj] using (hr08 0).1 (hx j)
  · intro j
    by_cases hj : j = k + 1
    · simpa [hj] using hm8
    · simpa [Function.update_of_ne hj] using (hr08 0).2 (hm j)

lemma deltaCode_valid (workers H K B : ℕ) (dispatch worker : ℕ → ℕ)
    (t : Tuning) (ht : t.Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers) :
    let z := (deltaCode H dispatch worker K B).run {}
    CodeValid workers t z.2 ∧ ∀ j, z.1 j ∈ (codeLayout t z.2).points 0 := by
  have hx : 0 ∈ (codeLayout t {}).points 0 := by simp [codeLayout, codeInstructions, finalLayout]
  have hi := localBatch_valid workers t 0 0 B {} (codeValid_initial workers t) hw0 hx
  let init := (localBatch 0 0 B).run {}
  let Inv := fun (state : (ℕ → ℕ) × (ℕ → ℕ)) (s : CodeState) => CodeValid workers t s ∧
    (∀ j, state.1 j ∈ (codeLayout t s).points 0) ∧ ∀ j, state.2 j ∈ (codeLayout t s).vectors 0
  have hh := state_forIn_invariant (deltaStep H dispatch worker) (List.range K) Inv
    (fun k _ state s h => by
      have hc := deltaStep_valid workers H k dispatch worker t ht state s h.1 (hw k) h.2.1 h.2.2
      exact ⟨hc.1, hc.2.2⟩) ((fun _ => 0), (fun _ => init.1)) init.2
      ⟨hi.1, (fun _ => (hi.2.1 0).1 hx), fun _ => hi.2.2⟩
  rw [deltaCode_run]
  exact ⟨hh.1, hh.2.1⟩

lemma deltaFamily_legal (workers H K B : ℕ) (dispatch worker : ℕ → ℕ)
    (t : Tuning) (ht : t.Valid) (hw0 : 0 < workers) (hw : ∀ k, worker k < workers) :
    ((deltaMomentumFamily H dispatch worker).instantiate K B t).Legal workers := by
  have hh := deltaCode_valid workers H K B dispatch worker t ht hw0 hw
  exact ⟨hh.1.2, hw0, fun j => hh.2 j.val⟩

structure LayoutBounded (s : Layout) : Prop where
  points : ∀ w j, j ∈ s.points w → j < s.next
  vectors : ∀ w j, j ∈ s.vectors w → j < s.next

lemma layoutBounded_initial : LayoutBounded {} := by
  constructor <;> intro w j hj
  · simpa using hj
  · simpa using hj

lemma layoutBounded_step (workers : ℕ) (s : Layout) (i : Instruction)
    (hs : LayoutBounded s) (hi : i.Legal workers s) : LayoutBounded (i.layout s) := by
  have point (w j : ℕ) (hj : j ∈ s.points w) : j < s.next + 1 := (hs.points w j hj).trans_le (by omega)
  have vector (w j : ℕ) (hj : j ∈ s.vectors w) : j < s.next + 1 := (hs.vectors w j hj).trans_le (by omega)
  have upd (f : ℕ → Finset ℕ) (hf : ∀ w j, j ∈ f w → j < s.next) (w a : ℕ)
      (ha : a ≤ s.next) : ∀ u j, j ∈ Function.update f w (insert a (f w)) u → j < s.next + 1 := by
    intro u j hj
    by_cases hu : u = w
    · subst u
      simp only [Function.update_self, Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · omega
      · exact (hf w j hj).trans_le (by omega)
    · rw [Function.update_of_ne hu] at hj
      exact (hf u j hj).trans_le (by omega)
  cases i with
  | query w x => exact ⟨point, upd s.vectors hs.vectors w s.next le_rfl⟩
  | mix w ts => exact ⟨point, upd s.vectors hs.vectors w s.next le_rfl⟩
  | difference w x y => exact ⟨point, upd s.vectors hs.vectors w s.next le_rfl⟩
  | lmo w v => exact ⟨point, upd s.vectors hs.vectors w s.next le_rfl⟩
  | sharp w v => exact ⟨point, upd s.vectors hs.vectors w s.next le_rfl⟩
  | move w x v η => exact ⟨upd s.points hs.points w s.next le_rfl, vector⟩
  | sendPoint w u x => exact ⟨upd s.points hs.points u x (hs.points w x hi.2.2).le, vector⟩
  | sendVector w u v => exact ⟨point, upd s.vectors hs.vectors u v (hs.vectors w v hi.2.2).le⟩

lemma layoutBounded_fold (workers : ℕ) (s : Layout) (code : List Instruction)
    (hs : LayoutBounded s) (hc : LegalFrom workers s code) :
    LayoutBounded (code.foldl (fun s i => i.layout s) s) := by
  induction code generalizing s with
  | nil => exact hs
  | cons i rest ih => exact ih (i.layout s) (layoutBounded_step workers s i hs hc.1) hc.2

lemma codeValid_register_bound (workers : ℕ) (t : Tuning) (s : CodeState)
    (hs : CodeValid workers t s) :
    (∀ w j, j ∈ (codeLayout t s).points w → j < s.next) ∧
      ∀ w j, j ∈ (codeLayout t s).vectors w → j < s.next := by
  have hh := layoutBounded_fold workers {} (codeInstructions t s) layoutBounded_initial hs.2
  rw [hs.1]
  exact ⟨hh.points, hh.vectors⟩

end LongTails.Proofs.BirchNonEuclideanConstruction
