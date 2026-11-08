import LongTails.Proofs.BirchNonEuclideanEventLabels
import LongTails.Proofs.BirchNonEuclideanCertificate
import LongTails.Algorithms.BirchNonEuclideanTrajectories

namespace LongTails.Proofs.BirchNonEuclideanReplay

open OracleTemplate.Rennala (Point)
open LongTails.Setups.UscgConstant (dualNorm)
open LongTails.Setups.BirchNonEuclidean
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanEvents
open LongTails.Algorithms.BirchNonEuclideanTrajectories
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanExecution
open LongTails.Proofs.BirchNonEuclideanCausality
open LongTails.Proofs.BirchNonEuclideanSymbolic

noncomputable def codeMemory (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (s : CodeState) : Memory p.d :=
  interpret p lmo response (codeInstructions t s) (initialMemory p)

lemma codeMemory_next (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (s : CodeState) :
    (codeMemory p lmo response t s).next = 1 + s.instructions.length := by
  simp [codeMemory, interpret_next, codeInstructions, initialMemory]

lemma codeMemory_replies (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (s : CodeState) :
    (codeMemory p lmo response t s).replies = codeCalls s := by
  simp only [codeMemory, interpret_replies, initialMemory, zero_add, queryCount, codeInstructions,
    codeCalls, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (instruction_tuning_cost i t (canonicalTuning 0 1)).1

lemma codeMemory_emit_query (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (s : CodeState) (w x : ℕ) :
    codeMemory p lmo response t (emit (.query w x) s).2 =
      perform p lmo (codeMemory p lmo response t s) (.query w x)
        (response (codeCalls s) ((codeMemory p lmo response t s).points x)) := by
  simp only [codeMemory, codeInstructions_emit, interpret_append, InstructionTemplate.instantiate, interpret]
  rw [← codeMemory, codeMemory_replies]

lemma codeMemory_emit_quiet (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (s : CodeState) (i : InstructionTemplate)
    (hi : (i.instantiate t).oracleCost = 0) :
    codeMemory p lmo response t (emit i s).2 =
      perform p lmo (codeMemory p lmo response t s) (i.instantiate t) 0 := by
  simp only [codeMemory, codeInstructions_emit, interpret_append]
  cases i <;> first | rfl | simp [InstructionTemplate.instantiate, Instruction.oracleCost] at hi

lemma codeMemory_old (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning) (s s' : CodeState)
    (he : CodeExtends s s') (j : ℕ) (hj : j < (codeMemory p lmo response t s).next) :
    (codeMemory p lmo response t s').points j = (codeMemory p lmo response t s).points j ∧
      (codeMemory p lmo response t s').vectors j = (codeMemory p lmo response t s).vectors j := by
  obtain ⟨tail, htail⟩ := he
  have hh : codeInstructions t s' = codeInstructions t s ++ tail.map (InstructionTemplate.instantiate t) := by
    simp [codeInstructions, htail]
  simp only [codeMemory, hh, interpret_append]
  exact ⟨LongTails.Proofs.BirchNonEuclideanCertificate.interpret_old_point p lmo response _ _ j hj,
    interpret_old_vector p lmo response _ _ j hj⟩

lemma momentumStep_memory (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning)
    (w H round h : ℕ) (state : ℕ × ℕ) (s : CodeState)
    (hn : s.next = 1 + s.instructions.length) (hm : state.2 < s.next) :
    let z := momentumStep w H round h state s
    let old := codeMemory p lmo response t s
    let new := codeMemory p lmo response t z.2
    let α := t.momentum (round * H + h)
    let v := α • response (codeCalls s) (old.points state.1) + (1 - α) • old.vectors state.2
    new.vectors z.1.2 = v ∧
      new.points z.1.1 = old.points state.1 + (1 / (H : ℝ) * t.step round) •
        (dualNorm p.N v • lmo v) := by
  have hn' : s.next = (codeMemory p lmo response t s).next := by rw [codeMemory_next, hn]
  have hm0 : state.2 ≠ (codeMemory p lmo response t s).next := by omega
  dsimp only
  simp only [momentumStep, state_bind_apply, state_pure_apply]
  rw [codeMemory_emit_quiet p lmo response t _ (.move _ _ _ _) rfl,
    codeMemory_emit_quiet p lmo response t _ (.sharp _ _) rfl,
    codeMemory_emit_quiet p lmo response t _ (.mix _ _) rfl,
    codeMemory_emit_query]
  simp [InstructionTemplate.instantiate, Coefficient.eval, perform, storeVector,
    emit_apply, hn', hm0, Nat.add_assoc, sub_eq_add_neg]

lemma localPrefix_calls (w H round n : ℕ) (state : ℕ × ℕ) (s : CodeState) :
    codeCalls (localPrefix w H round n state s).2 = codeCalls s + n := by
  induction n with
  | zero => simp [localPrefix_zero]
  | succ n ih =>
      rw [localPrefix_succ]
      dsimp only
      rw [momentumStep_calls, ih]
      omega

lemma localPrefix_memory (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (η : ℝ) (B : ℕ)
    (w H round n : ℕ) (state : ℕ × ℕ) (s : CodeState)
    (hn : s.next = 1 + s.instructions.length) (hm : state.2 < s.next) :
    let t := canonicalTuning η B
    let z := localPrefix w H round n state s
    let old := codeMemory p lmo response t s
    let new := codeMemory p lmo response t z.2
    (new.points z.1.1, new.vectors z.1.2) =
      localValues p lmo (fun h => response (codeCalls s + h)) η B H
        (old.points state.1, old.vectors state.2) n := by
  dsimp only
  induction n with
  | zero => rfl
  | succ n ih =>
      let z := localPrefix w H round n state s
      have hz : z.2.next = 1 + z.2.instructions.length := by
        have hh := localPrefix_aligned w H round n state s (canonicalTuning η B)
          (by rw [codeSymbolic_next, hn])
        rw [codeSymbolic_next] at hh
        exact hh
      have hh := momentumStep_memory p lmo response (canonicalTuning η B) w H round n z.1 z.2 hz
        (localPrefix_momentum_lt w H round n state s hm)
      dsimp only [canonicalTuning] at hh
      rw [localPrefix_succ, localValues]
      have hx := congrArg Prod.fst ih
      have hv := congrArg Prod.snd ih
      change (codeMemory p lmo response (canonicalTuning η B) z.2).points z.1.1 = _ at hx
      change (codeMemory p lmo response (canonicalTuning η B) z.2).vectors z.1.2 = _ at hv
      dsimp only [z, canonicalTuning] at hh hx hv ⊢
      apply Prod.ext
      · dsimp only
        rw [hh.2, hx, hv, localPrefix_calls]
      · dsimp only
        rw [hh.1, hx, hv, localPrefix_calls]

lemma localValues_congr (p : Params) (lmo : Point p.d → Point p.d)
    (response response' : ℕ → Point p.d → Point p.d) (η : ℝ) (B H n : ℕ)
    (start : Point p.d × Point p.d) (hr : ∀ h < n, ∀ x, response h x = response' h x) :
    localValues p lmo response η B H start n = localValues p lmo response' η B H start n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [localValues, localValues, ih (fun h hh => hr h (by omega)), hr n (by omega)]

lemma returnCode_memory (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning)
    (w x0 v0 x v : ℕ) (s : CodeState) (hn : s.next = 1 + s.instructions.length)
    (hv0 : v0 < s.next) (hv : v < s.next) :
    let z := returnCode w x0 v0 x v s
    let old := codeMemory p lmo response t s
    let new := codeMemory p lmo response t z.2
    new.vectors z.1.1 = old.points x - old.points x0 ∧
      new.vectors z.1.2 = old.vectors v - old.vectors v0 := by
  have hn' : s.next = (codeMemory p lmo response t s).next := by rw [codeMemory_next, hn]
  have hv0' : v0 ≠ (codeMemory p lmo response t s).next := by omega
  have hv' : v ≠ (codeMemory p lmo response t s).next := by omega
  dsimp only [returnCode, state_bind_apply, state_pure_apply]
  rw [codeMemory_emit_quiet p lmo response t _ (.sendVector _ _ _) rfl,
    codeMemory_emit_quiet p lmo response t _ (.sendVector _ _ _) rfl,
    codeMemory_emit_quiet p lmo response t _ (.mix _ _) rfl,
    codeMemory_emit_quiet p lmo response t _ (.difference _ _ _) rfl]
  simp [InstructionTemplate.instantiate, Coefficient.eval, perform, storeVector,
    emit_apply, hn', hv0', hv', Nat.add_assoc, sub_eq_add_neg]

lemma commitCode_memory {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning)
    (k dx dm : ℕ) (regs : Registers m) (s : CodeState) (hn : s.next = 1 + s.instructions.length) :
    let z := commitCode k dx dm regs s
    let old := codeMemory p lmo response t s
    let new := codeMemory p lmo response t z.2
    new.points (z.1.points (k + 1)) = old.points (regs.points k) + old.vectors dx ∧
      new.vectors (z.1.momenta (k + 1)) = old.vectors (regs.momenta k) + old.vectors dm := by
  have hn' : s.next = (codeMemory p lmo response t s).next := by rw [codeMemory_next, hn]
  dsimp only [commitCode, state_bind_apply, state_pure_apply]
  rw [codeMemory_emit_quiet p lmo response t _ (.mix _ _) rfl,
    codeMemory_emit_quiet p lmo response t _ (.move _ _ _ _) rfl]
  simp [InstructionTemplate.instantiate, Coefficient.eval, perform, storeVector, emit_apply, hn']

lemma relaunchCode_memory {m : ℕ} (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (t : Tuning)
    (w : Fin m) (k : ℕ) (regs : Registers m) (s : CodeState) :
    let z := relaunchCode w k regs s
    let old := codeMemory p lmo response t s
    let new := codeMemory p lmo response t z.2
    new.points = old.points ∧ new.vectors = old.vectors ∧ new.replies = old.replies := by
  dsimp only [relaunchCode, state_bind_apply, state_pure_apply]
  rw [codeMemory_emit_quiet p lmo response t _ (.sendVector _ _ _) rfl,
    codeMemory_emit_quiet p lmo response t _ (.sendPoint _ _ _) rfl]
  exact ⟨rfl, rfl, rfl⟩

end LongTails.Proofs.BirchNonEuclideanReplay
