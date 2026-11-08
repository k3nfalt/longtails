import LongTails.Proofs.BirchNonEuclideanRennalaCapture
import LongTails.Proofs.BirchNonEuclideanShared

namespace LongTails.Proofs.BirchNonEuclideanRennalaRecords

open LongTails.Setups.BirchNonEuclidean hiding State LegalFrom
open LongTails.Algorithms.BirchNonEuclideanFamilies
open LongTails.Algorithms.BirchNonEuclideanRennala
open LongTails.Proofs.BirchNonEuclideanFamilies
open LongTails.Proofs.BirchNonEuclideanConstruction
open LongTails.Proofs.BirchNonEuclideanCoefficients
open LongTails.Proofs.BirchNonEuclideanRennalaCosts
open LongTails.Proofs.BirchNonEuclideanRennalaLegality
open LongTails.Proofs.BirchNonEuclideanShared (termSum mix_symbolic)
open LongTails.Proofs.BirchNonEuclideanEvents (state_map_apply)

lemma commitCode_extends {m : ℕ} (k : ℕ) (terms : List (Coefficient × ℕ)) (regs : Registers m) :
    BuildExtends (commitCode k terms regs) := by
  unfold commitCode
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro mean
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro d
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro x
  exact buildExtends_pure _

lemma relaunchCode_extends {m : ℕ} (w : Fin m) (k : ℕ) (regs : Registers m) :
    BuildExtends (relaunchCode w k regs) := by
  unfold relaunchCode
  apply buildExtends_bind _ _ (buildExtends_emit _)
  intro _
  exact buildExtends_pure _

lemma replyCode_extends {m : ℕ} (K B : ℕ) (w : Fin m) (pub : State m) (regs : Registers m) :
    BuildExtends (replyCode K B w pub regs) := by
  intro s
  simp only [replyCode, state_bind_apply]
  split_ifs <;> simp only [commitCode, relaunchCode, state_bind_apply, state_pure_apply,
    emit_apply, CodeExtends, List.append_assoc]
  all_goals exact ⟨_, rfl⟩

lemma eventCode_extends {m : ℕ} (K B : ℕ) (e : Event m) (state : State m × Registers m) :
    BuildExtends (eventCode K B e state) := by
  cases e with
  | query w => intro s; exact codeExtends_emit s (.query (w.val + 1) (state.2.point w))
  | reply w => intro s; exact replyCode_extends K B w state.1 state.2 s

lemma replyCode_reply {m : ℕ} (K B : ℕ) (w : Fin m) (pub : State m) (regs : Registers m) (s : CodeState) :
    (replyCode K B w pub regs s).1.reply = regs.reply := by
  simp only [replyCode, state_bind_apply]
  split_ifs <;> simp only [commitCode, relaunchCode, state_bind_apply, state_pure_apply]

lemma replyCode_terms {m : ℕ} (K B : ℕ) (w : Fin m) (pub : State m) (regs : Registers m) (s : CodeState) :
    (replyCode K B w pub regs s).1.terms =
      if pub.round < K ∧ fresh pub w then
        if commits B pub w then [] else regs.terms ++ [(.constant (1 / (B : ℝ)), regs.reply w)]
      else regs.terms := by
  simp only [replyCode, state_bind_apply]
  split_ifs <;> simp_all [commitCode, relaunchCode, state_bind_apply, state_pure_apply, state_map_apply]

lemma commitCode_registers {m : ℕ} (k : ℕ) (terms : List (Coefficient × ℕ)) (regs : Registers m) (s : CodeState) :
    (commitCode k terms regs s).1 = { regs with
      points := Function.update regs.points (k + 1) (s.next + 2)
      sharps := Function.update regs.sharps k (s.next + 1)
      owner := Function.update regs.owner (s.next + 1) k
      terms := [] } ∧ (commitCode k terms regs s).2.next = s.next + 3 := by
  simp only [commitCode, state_bind_apply, state_pure_apply, emit_apply]
  constructor <;> trivial

lemma query_symbolic (w x : ℕ) (s : CodeState) (t : Tuning) (hn : s.next = (codeSymbolic t s).next) :
    let old := codeSymbolic t s
    let new := codeSymbolic t (emit (.query w x) s).2
    new.vectors s.next = (Finsupp.single s.next 1, 0) ∧
      new.queryPoints s.next = old.points x ∧ new.queries = insert s.next old.queries ∧
      new.sharps = old.sharps ∧ new.units = old.units ∧ new.points = old.points := by
  dsimp only
  rw [codeSymbolic_emit]
  simp only [InstructionTemplate.instantiate, symbolicPerform, symbolicStore, ← hn, Function.update_self]
  trivial

lemma relaunchCode_symbolic {m : ℕ} (w : Fin m) (k : ℕ) (regs : Registers m) (s : CodeState) (t : Tuning) :
    codeSymbolic t (relaunchCode w k regs s).2 =
      { codeSymbolic t s with next := (codeSymbolic t s).next + 1 } := by
  simp only [relaunchCode, state_bind_apply, state_pure_apply, codeSymbolic_emit]
  rfl

lemma commitCode_symbolic {m : ℕ} (k : ℕ) (terms : List (Coefficient × ℕ)) (regs : Registers m)
    (s : CodeState) (η : ℝ) (B : ℕ) (hn : s.next = (codeSymbolic (canonicalTuning η B) s).next) :
    let t := canonicalTuning η B
    let old := codeSymbolic t s
    let new := codeSymbolic t (commitCode k terms regs s).2
    new.points (s.next + 2) = old.points (regs.points k) +
      η • ((0, Finsupp.single (s.next + 1) 1) : LinearValue) ∧
    new.sharpInputs (s.next + 1) = termSum t s terms ∧ new.queries = old.queries ∧
      new.sharps = insert (s.next + 1) old.sharps ∧ new.units = old.units := by
  let t := canonicalTuning η B
  let s1 := (emit (.mix 0 terms) s).2
  have hm := mix_symbolic 0 terms s t hn
  change (codeSymbolic t s1).vectors s.next = termSum t s terms at hm
  have hnext : (codeSymbolic t s1).next = s.next + 1 := by
    rw [codeSymbolic_emit]
    change (codeSymbolic t s).next + 1 = _
    rw [← hn]
  have hpoints : (codeSymbolic t s1).points = (codeSymbolic t s).points := by
    rw [codeSymbolic_emit]
    rfl
  have hq : (codeSymbolic t s1).queries = (codeSymbolic t s).queries := by rw [codeSymbolic_emit]; rfl
  have hsh : (codeSymbolic t s1).sharps = (codeSymbolic t s).sharps := by rw [codeSymbolic_emit]; rfl
  have hu : (codeSymbolic t s1).units = (codeSymbolic t s).units := by rw [codeSymbolic_emit]; rfl
  have he : codeSymbolic t (commitCode k terms regs s).2 =
      symbolicPerform (symbolicPerform (codeSymbolic t s1) (.sharp 0 s.next))
        (.move 0 (regs.points k) (s.next + 1) η) := by
    simp only [commitCode, state_bind_apply, state_pure_apply]
    rw [codeSymbolic_emit, codeSymbolic_emit]
    rfl
  dsimp only
  rw [he]
  simp only [symbolicPerform, symbolicStore, hnext, show s.next + 1 + 1 = s.next + 2 by omega,
    Function.update_self, hpoints, hm, hq, hsh, hu]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end LongTails.Proofs.BirchNonEuclideanRennalaRecords
