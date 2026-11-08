import LongTails.Algorithms.BirchNonEuclideanFamilies

namespace LongTails.Proofs.BirchNonEuclideanFamilies

open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies

lemma instruction_tuning_cost (i : InstructionTemplate) (s t : Tuning) :
    (i.instantiate s).oracleCost = (i.instantiate t).oracleCost ∧
      (i.instantiate s).lmoCost = (i.instantiate t).lmoCost ∧
      (i.instantiate s).messageCost = (i.instantiate t).messageCost := by
  cases i <;> exact ⟨rfl, rfl, rfl⟩

lemma template_tuning_oracleCalls (a : ProgramTemplate) (s t : Tuning) :
    (a.instantiate s).oracleCalls = (a.instantiate t).oracleCalls := by
  unfold Program.oracleCalls ProgramTemplate.instantiate
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (instruction_tuning_cost i s t).1

lemma template_tuning_lmoCalls (a : ProgramTemplate) (s t : Tuning) :
    (a.instantiate s).lmoCalls = (a.instantiate t).lmoCalls := by
  unfold Program.lmoCalls ProgramTemplate.instantiate
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (instruction_tuning_cost i s t).2.1

lemma template_tuning_messages (a : ProgramTemplate) (s t : Tuning) :
    (a.instantiate s).messages = (a.instantiate t).messages := by
  unfold Program.messages ProgramTemplate.instantiate
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (instruction_tuning_cost i s t).2.2

lemma family_tuning_cost (f : ProtocolFamily) (K B : ℕ) (s t : Tuning) :
    (f.instantiate K B s).oracleCalls = (f.instantiate K B t).oracleCalls ∧
      (f.instantiate K B s).lmoCalls = (f.instantiate K B t).lmoCalls ∧
      (f.instantiate K B s).messages = (f.instantiate K B t).messages :=
  ⟨template_tuning_oracleCalls _ s t, template_tuning_lmoCalls _ s t,
    template_tuning_messages _ s t⟩

lemma state_forIn_cons {σ α β : Type} (step : α → β → StateM σ β)
    (x : α) (xs : List α) (b : β) (s : σ) :
    (forIn (x :: xs) b (fun i b => ForInStep.yield <$> step i b) : StateM σ β) s =
      (forIn xs (step x b s).1 (fun i b => ForInStep.yield <$> step i b) : StateM σ β)
        (step x b s).2 := by
  rw [List.forIn_cons]
  rfl

lemma state_forIn_cost {σ α β : Type} (cost : σ → ℕ)
    (step : α → β → StateM σ β) (c : ℕ)
    (hc : ∀ i b s, cost (step i b s).2 = cost s + c)
    (xs : List α) (b : β) (s : σ) :
    cost ((forIn xs b (fun i b => ForInStep.yield <$> step i b) : StateM σ β) s).2 =
      cost s + xs.length * c := by
  induction xs generalizing b s with
  | nil =>
      simp only [List.forIn_nil, List.length_nil, zero_mul, Nat.add_zero]
      rfl
  | cons x xs ih =>
      rw [state_forIn_cons, ih, hc]
      simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

noncomputable def codeCalls (s : CodeState) : ℕ :=
  ((s.instructions.map (InstructionTemplate.instantiate (canonicalTuning 0 1))).map
    Instruction.oracleCost).sum

lemma emit_calls (i : InstructionTemplate) (s : CodeState) :
    codeCalls ((emit i).run s).2 = codeCalls s +
      (i.instantiate (canonicalTuning 0 1)).oracleCost := by
  change (((s.instructions ++ [i]).map _).map _).sum = _
  simp [codeCalls]

noncomputable def batchQueryStep (worker point B : ℕ) (_ : ℕ)
    (terms : List (Coefficient × ℕ)) : StateM CodeState (List (Coefficient × ℕ)) := do
  let q ← emit (.query worker point)
  return terms ++ [(.constant (1 / (B : ℝ)), q)]

lemma batchQueryStep_calls (worker point B i : ℕ) (terms : List (Coefficient × ℕ))
    (s : CodeState) : codeCalls (batchQueryStep worker point B i terms s).2 = codeCalls s + 1 := by
  change codeCalls ((emit (.query worker point)).run s).2 = _
  exact emit_calls (.query worker point) s

lemma localBatch_run (worker point B : ℕ) (s : CodeState) :
    (localBatch worker point B).run s =
      let z := (forIn (List.range B) []
        (fun i terms => ForInStep.yield <$> batchQueryStep worker point B i terms) :
          StateM CodeState (List (Coefficient × ℕ))) s
      (emit (.mix worker z.1)).run z.2 := rfl

lemma localBatch_calls (worker point B : ℕ) (s : CodeState) :
    codeCalls ((localBatch worker point B).run s).2 = codeCalls s + B := by
  rw [localBatch_run]
  dsimp only
  rw [emit_calls]
  simp only [InstructionTemplate.instantiate, Instruction.oracleCost, Nat.add_zero]
  simpa only [List.length_range, Nat.mul_one] using
    state_forIn_cost codeCalls (batchQueryStep worker point B) 1
      (batchQueryStep_calls worker point B) (List.range B) [] s

lemma state_bind_apply {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f) s = f (x s).1 (x s).2 := rfl

lemma state_pure_apply {σ α : Type} (x : α) (s : σ) : (pure x : StateM σ α) s = (x, s) := rfl

lemma emit_apply (i : InstructionTemplate) (s : CodeState) :
    emit i s = (s.next, { instructions := s.instructions ++ [i], next := s.next + 1 }) := rfl

noncomputable def momentumStep (worker H round h : ℕ) (state : ℕ × ℕ) :
    StateM CodeState (ℕ × ℕ) := do
  let q ← emit (.query worker state.1)
  let alpha := Coefficient.momentum (round * H + h)
  let m ← emit (.mix worker [(alpha, q), (.add (.constant 1) (.neg alpha), state.2)])
  let d ← emit (.sharp worker m)
  let x ← emit (.move worker state.1 d (.mul (.constant (1 / (H : ℝ))) (.step round)))
  return (x, m)

lemma momentumStep_calls (worker H round h : ℕ) (state : ℕ × ℕ) (s : CodeState) :
    codeCalls (momentumStep worker H round h state s).2 = codeCalls s + 1 := by
  simp only [momentumStep, state_bind_apply, emit_apply, state_pure_apply]
  simp [codeCalls, InstructionTemplate.instantiate, Instruction.oracleCost]

lemma localMomentum_run (worker x m H round : ℕ) (s : CodeState) :
    (localMomentum worker x m H round).run s =
      (forIn (List.range H) (x, m)
        (fun h state => ForInStep.yield <$> momentumStep worker H round h state) :
          StateM CodeState (ℕ × ℕ)) s := rfl

lemma localMomentum_calls (worker x m H round : ℕ) (s : CodeState) :
    codeCalls ((localMomentum worker x m H round).run s).2 = codeCalls s + H := by
  rw [localMomentum_run]
  simpa only [List.length_range, Nat.mul_one] using
    state_forIn_cost codeCalls (momentumStep worker H round) 1
      (momentumStep_calls worker H round) (List.range H) (x, m) s

noncomputable def deltaStep (H : ℕ) (dispatch worker : ℕ → ℕ) (k : ℕ)
    (state : (ℕ → ℕ) × (ℕ → ℕ)) : StateM CodeState ((ℕ → ℕ) × (ℕ → ℕ)) := do
  let src := dispatch k
  let w := worker k
  let _ ← emit (.sendPoint 0 w (state.1 src))
  let _ ← emit (.sendVector 0 w (state.2 src))
  let packet ← localMomentum w (state.1 src) (state.2 src) H k
  let dx ← emit (.difference w packet.1 (state.1 src))
  let dm ← emit (.mix w [(.constant 1, packet.2), (.constant (-1), state.2 src)])
  let _ ← emit (.sendVector w 0 dx)
  let _ ← emit (.sendVector w 0 dm)
  let x ← emit (.move 0 (state.1 k) dx (.constant 1))
  let m ← emit (.mix 0 [(.constant 1, state.2 k), (.constant 1, dm)])
  return (Function.update state.1 (k + 1) x, Function.update state.2 (k + 1) m)

lemma deltaStep_calls (H : ℕ) (dispatch worker : ℕ → ℕ) (k : ℕ)
    (state : (ℕ → ℕ) × (ℕ → ℕ)) (s : CodeState) :
    codeCalls (deltaStep H dispatch worker k state s).2 = codeCalls s + H := by
  have h := localMomentum_calls (worker k) (state.1 (dispatch k)) (state.2 (dispatch k)) H k
    { instructions := s.instructions ++ [.sendPoint 0 (worker k) (state.1 (dispatch k)),
        .sendVector 0 (worker k) (state.2 (dispatch k))], next := s.next + 1 + 1 }
  simp only [deltaStep, state_bind_apply, emit_apply, state_pure_apply]
  simpa [codeCalls, StateT.run, InstructionTemplate.instantiate, Instruction.oracleCost] using h

lemma deltaCode_run (H : ℕ) (dispatch worker : ℕ → ℕ) (K B : ℕ) (s : CodeState) :
    (deltaCode H dispatch worker K B).run s =
      let init := (localBatch 0 0 B).run s
      let z := (forIn (List.range K) ((fun _ => 0), (fun _ => init.1))
        (fun k state => ForInStep.yield <$> deltaStep H dispatch worker k state) :
          StateM CodeState ((ℕ → ℕ) × (ℕ → ℕ))) init.2
      (z.1.1, z.2) := rfl

lemma deltaCode_calls (H : ℕ) (dispatch worker : ℕ → ℕ) (K B : ℕ) (s : CodeState) :
    codeCalls ((deltaCode H dispatch worker K B).run s).2 = codeCalls s + B + K * H := by
  rw [deltaCode_run]
  dsimp only
  rw [state_forIn_cost codeCalls _ H (deltaStep_calls H dispatch worker)]
  rw [localBatch_calls]
  simp

lemma deltaFamily_calls (H : ℕ) (dispatch worker : ℕ → ℕ) (K B : ℕ) (t : Tuning) :
    ((deltaMomentumFamily H dispatch worker).instantiate K B t).oracleCalls = B + K * H := by
  rw [(family_tuning_cost _ K B t (canonicalTuning 0 1)).1]
  change codeCalls ((deltaCode H dispatch worker K B).run {}).2 = _
  rw [deltaCode_calls]
  simp [codeCalls]

noncomputable def collectedStep (worker : ℕ → ℕ) (round point B h : ℕ)
    (terms : List (Coefficient × ℕ)) : StateM CodeState (List (Coefficient × ℕ)) := do
  let w := worker (round * B + h)
  let _ ← emit (.sendPoint 0 w point)
  let q ← emit (.query w point)
  let _ ← emit (.sendVector w 0 q)
  return terms ++ [(.constant (1 / (B : ℝ)), q)]

lemma collectedStep_calls (worker : ℕ → ℕ) (round point B h : ℕ)
    (terms : List (Coefficient × ℕ)) (s : CodeState) :
    codeCalls (collectedStep worker round point B h terms s).2 = codeCalls s + 1 := by
  simp only [collectedStep, state_bind_apply, emit_apply, state_pure_apply]
  simp [codeCalls, InstructionTemplate.instantiate, Instruction.oracleCost]

lemma collectedBatch_run (worker : ℕ → ℕ) (round point B : ℕ) (s : CodeState) :
    (collectedBatch worker round point B).run s =
      let z := (forIn (List.range B) []
        (fun h terms => ForInStep.yield <$> collectedStep worker round point B h terms) :
          StateM CodeState (List (Coefficient × ℕ))) s
      (emit (.mix 0 z.1)).run z.2 := rfl

lemma collectedBatch_calls (worker : ℕ → ℕ) (round point B : ℕ) (s : CodeState) :
    codeCalls ((collectedBatch worker round point B).run s).2 = codeCalls s + B := by
  rw [collectedBatch_run]
  dsimp only
  rw [emit_calls]
  simp only [InstructionTemplate.instantiate, Instruction.oracleCost, Nat.add_zero]
  simpa only [List.length_range, Nat.mul_one] using
    state_forIn_cost codeCalls (collectedStep worker round point B) 1
      (collectedStep_calls worker round point B) (List.range B) [] s

noncomputable def batchStep (worker : ℕ → ℕ) (B k : ℕ) (points : ℕ → ℕ) :
    StateM CodeState (ℕ → ℕ) := do
  let g ← collectedBatch worker k (points k) B
  let d ← emit (.sharp 0 g)
  let x ← emit (.move 0 (points k) d (.step k))
  return Function.update points (k + 1) x

lemma batchStep_calls (worker : ℕ → ℕ) (B k : ℕ) (points : ℕ → ℕ) (s : CodeState) :
    codeCalls (batchStep worker B k points s).2 = codeCalls s + B := by
  have h := collectedBatch_calls worker k (points k) B s
  simp only [batchStep, state_bind_apply, emit_apply, state_pure_apply]
  simpa [codeCalls, StateT.run, InstructionTemplate.instantiate, Instruction.oracleCost] using h

lemma batchCode_run (worker : ℕ → ℕ) (K B : ℕ) (s : CodeState) :
    (batchCode worker K B).run s =
      (forIn (List.range K) (fun _ => 0)
        (fun k points => ForInStep.yield <$> batchStep worker B k points) :
          StateM CodeState (ℕ → ℕ)) s := rfl

lemma batchCode_calls (worker : ℕ → ℕ) (K B : ℕ) (s : CodeState) :
    codeCalls ((batchCode worker K B).run s).2 = codeCalls s + K * B := by
  rw [batchCode_run]
  simpa only [List.length_range] using
    state_forIn_cost codeCalls (batchStep worker B) B
      (batchStep_calls worker B) (List.range K) (fun _ => 0) s

lemma minibatchFamily_calls (worker : ℕ → ℕ) (K B : ℕ) (t : Tuning) :
    ((minibatchFamily worker).instantiate K B t).oracleCalls = K * B := by
  rw [(family_tuning_cost _ K B t (canonicalTuning 0 1)).1]
  change codeCalls ((batchCode worker K B).run {}).2 = _
  rw [batchCode_calls]
  simp [codeCalls]

noncomputable def sharedPacketStep (workers H k point momentum i : ℕ)
    (terms : List (Coefficient × ℕ) × List (Coefficient × ℕ)) :
    StateM CodeState (List (Coefficient × ℕ) × List (Coefficient × ℕ)) := do
  let w := i + 1
  let _ ← emit (.sendPoint 0 w point)
  let _ ← emit (.sendVector 0 w momentum)
  let packet ← localMomentum w point momentum H k
  let dx ← emit (.difference w packet.1 point)
  let _ ← emit (.sendVector w 0 dx)
  let _ ← emit (.sendVector w 0 packet.2)
  let c := Coefficient.constant (1 / (workers : ℝ))
  return (terms.1 ++ [(c, dx)], terms.2 ++ [(c, packet.2)])

lemma sharedPacketStep_calls (workers H k point momentum i : ℕ)
    (terms : List (Coefficient × ℕ) × List (Coefficient × ℕ)) (s : CodeState) :
    codeCalls (sharedPacketStep workers H k point momentum i terms s).2 = codeCalls s + H := by
  have h := localMomentum_calls (i + 1) point momentum H k
    { instructions := s.instructions ++ [.sendPoint 0 (i + 1) point,
        .sendVector 0 (i + 1) momentum], next := s.next + 1 + 1 }
  simp only [sharedPacketStep, state_bind_apply, emit_apply, state_pure_apply]
  simpa [codeCalls, StateT.run, InstructionTemplate.instantiate, Instruction.oracleCost] using h

noncomputable def sharedRoundStep (workers H k : ℕ) (state : (ℕ → ℕ) × ℕ) :
    StateM CodeState ((ℕ → ℕ) × ℕ) := do
  let terms ← forIn (List.range workers) ([], [])
    (fun i ts => ForInStep.yield <$> sharedPacketStep workers H k (state.1 k) state.2 i ts)
  let dx ← emit (.mix 0 terms.1)
  let x ← emit (.move 0 (state.1 k) dx (.constant 1))
  let m ← emit (.mix 0 terms.2)
  return (Function.update state.1 (k + 1) x, m)

lemma sharedRoundStep_calls (workers H k : ℕ) (state : (ℕ → ℕ) × ℕ) (s : CodeState) :
    codeCalls (sharedRoundStep workers H k state s).2 = codeCalls s + workers * H := by
  have h := state_forIn_cost codeCalls (sharedPacketStep workers H k (state.1 k) state.2) H
    (sharedPacketStep_calls workers H k (state.1 k) state.2) (List.range workers) ([], []) s
  simp only [sharedRoundStep, state_bind_apply, emit_apply, state_pure_apply]
  simpa [codeCalls, InstructionTemplate.instantiate, Instruction.oracleCost] using h

lemma sharedCode_run (workers H K B : ℕ) (s : CodeState) :
    (sharedCode workers H K B).run s =
      let init := (localBatch 0 0 (workers * B)).run s
      let z := (forIn (List.range K) ((fun _ => 0), init.1)
        (fun k state => ForInStep.yield <$> sharedRoundStep workers H k state) :
          StateM CodeState ((ℕ → ℕ) × ℕ)) init.2
      (z.1.1, z.2) := rfl

lemma sharedCode_calls (workers H K B : ℕ) (s : CodeState) :
    codeCalls ((sharedCode workers H K B).run s).2 = codeCalls s + workers * B + K * (workers * H) := by
  rw [sharedCode_run]
  dsimp only
  rw [state_forIn_cost codeCalls _ (workers * H) (sharedRoundStep_calls workers H)]
  rw [localBatch_calls]
  simp

lemma sharedFamily_calls (workers H K B : ℕ) (t : Tuning) :
    ((sharedMomentumFamily workers H).instantiate K B t).oracleCalls =
      workers * B + K * (workers * H) := by
  rw [(family_tuning_cost _ K B t (canonicalTuning 0 1)).1]
  change codeCalls ((sharedCode workers H K B).run {}).2 = _
  rw [sharedCode_calls]
  simp [codeCalls]

end LongTails.Proofs.BirchNonEuclideanFamilies
