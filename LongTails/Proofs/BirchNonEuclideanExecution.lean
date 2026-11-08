import LongTails.Setups.BirchNonEuclidean
import LongTails.Proofs.SgdExecution

namespace LongTails.Proofs.BirchNonEuclideanExecution

open OracleTemplate.Rennala (Point)
open OracleTemplate
open LongTails.Setups.BirchNonEuclidean

def queryCount (code : List Instruction) : ℕ :=
  (code.map Instruction.oracleCost).sum

lemma perform_next (p : Params) (lmo : Point p.d → Point p.d)
    (s : Memory p.d) (i : Instruction) (reply : Point p.d) :
    (perform p lmo s i reply).next = s.next + 1 := by
  cases i <;> rfl

lemma perform_replies (p : Params) (lmo : Point p.d → Point p.d)
    (s : Memory p.d) (i : Instruction) (reply : Point p.d) :
    (perform p lmo s i reply).replies = s.replies + i.oracleCost := by
  cases i <;> simp [perform, storeVector, Instruction.oracleCost]

lemma symbolic_next (s : SymbolicMemory) (i : Instruction) :
    (symbolicPerform s i).next = s.next + 1 := by
  cases i <;> rfl

lemma runPure_replies (p : Params) (lmo : Point p.d → Point p.d)
    (code : List Instruction) (s : Memory p.d) :
    (runPure p lmo code s).2.replies = s.replies := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih =>
    cases i <;> simp [runPure, ih, perform, storeVector]

lemma runPure_queryCount (p : Params) (lmo : Point p.d → Point p.d)
    (code : List Instruction) (s : Memory p.d) :
    queryCount (runPure p lmo code s).1 = queryCount code := by
  induction code generalizing s with
  | nil => rfl
  | cons i rest ih =>
    cases i with
    | query w x => rfl
    | _ => simpa only [runPure, queryCount, List.map_cons, List.sum_cons,
        Instruction.oracleCost, zero_add] using ih (perform p lmo s _ 0)

lemma runPure_normal (p : Params) (lmo : Point p.d → Point p.d)
    (code : List Instruction) (s : Memory p.d) :
    (runPure p lmo code s).1 = [] ∨
      ∃ w x rest, (runPure p lmo code s).1 = Instruction.query w x :: rest := by
  induction code generalizing s with
  | nil => exact Or.inl rfl
  | cons i rest ih =>
    cases i with
    | query w x => exact Or.inr ⟨w, x, rest, rfl⟩
    | _ => simpa only [runPure] using ih (perform p lmo s _ 0)

lemma runPure_complete (p : Params) (lmo : Point p.d → Point p.d)
    (code : List Instruction) (s : Memory p.d) (h : queryCount code = 0) :
    (runPure p lmo code s).1 = [] := by
  rcases runPure_normal p lmo code s with hnil | ⟨w, x, rest, hcons⟩
  · exact hnil
  · have hc := runPure_queryCount p lmo code s
    rw [hcons, h] at hc
    simp [queryCount, Instruction.oracleCost] at hc

lemma query_update_replies (p : Params) (a : Program) (lmo : Point p.d → Point p.d)
    (s : State p.d) (reply : Point p.d) (w x : ℕ) (rest : List Instruction)
    (h : s.remaining = Instruction.query w x :: rest) :
    ((programAlgorithm p a lmo).update s reply).memory.replies = s.memory.replies + 1 := by
  simp [programAlgorithm, h, runPure_replies, perform, storeVector]

lemma completed_update (p : Params) (a : Program) (lmo : Point p.d → Point p.d)
    (s : State p.d) (reply : Point p.d) (h : s.remaining = []) :
    (programAlgorithm p a lmo).update s reply = s := by
  simp [programAlgorithm, h]

noncomputable def interpret (p : Params) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) : List Instruction → Memory p.d → Memory p.d
  | [], m => m
  | .query w x :: rest, m => interpret p lmo response rest
      (perform p lmo m (.query w x) (response m.replies (m.points x)))
  | i :: rest, m => interpret p lmo response rest (perform p lmo m i 0)

lemma advance_interpret (p : Params) (a : Program) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (code : List Instruction)
    (m : Memory p.d) (selected : ℕ) :
    StochasticGradient.advance
      (fun k s => (programAlgorithm p a lmo).update s
        (response k ((programAlgorithm p a lmo).query s).2))
      (queryCount code) m.replies
      ⟨(runPure p lmo code m).1, (runPure p lmo code m).2, selected⟩ =
        ⟨[], interpret p lmo response code m, selected⟩ := by
  induction code generalizing m with
  | nil => rfl
  | cons i rest ih =>
      cases i with
      | query w x =>
          simpa [queryCount, Instruction.oracleCost, runPure,
            StochasticGradient.advance, programAlgorithm, interpret, perform, storeVector, Nat.one_add]
            using ih (perform p lmo m (.query w x) (response m.replies (m.points x)))
      | mix w terms =>
          simpa only [queryCount, List.map_cons, List.sum_cons, Instruction.oracleCost,
            zero_add, runPure, interpret, perform, storeVector]
            using ih (perform p lmo m (.mix w terms) 0)
      | difference w x y =>
          simpa only [queryCount, List.map_cons, List.sum_cons, Instruction.oracleCost,
            zero_add, runPure, interpret, perform, storeVector]
            using ih (perform p lmo m (.difference w x y) 0)
      | lmo w v =>
          simpa only [queryCount, List.map_cons, List.sum_cons, Instruction.oracleCost,
            zero_add, runPure, interpret, perform, storeVector]
            using ih (perform p lmo m (.lmo w v) 0)
      | sharp w v =>
          simpa only [queryCount, List.map_cons, List.sum_cons, Instruction.oracleCost,
            zero_add, runPure, interpret, perform, storeVector]
            using ih (perform p lmo m (.sharp w v) 0)
      | move w x v eta =>
          simpa only [queryCount, List.map_cons, List.sum_cons, Instruction.oracleCost,
            zero_add, runPure, interpret, perform, storeVector]
            using ih (perform p lmo m (.move w x v eta) 0)
      | sendPoint w u x =>
          simpa only [queryCount, List.map_cons, List.sum_cons, Instruction.oracleCost,
            zero_add, runPure, interpret, perform, storeVector]
            using ih (perform p lmo m (.sendPoint w u x) 0)
      | sendVector w u v =>
          simpa only [queryCount, List.map_cons, List.sum_cons, Instruction.oracleCost,
            zero_add, runPure, interpret, perform, storeVector]
            using ih (perform p lmo m (.sendVector w u v) 0)

lemma execute_interpret {Ω : Type} [MeasurableSpace Ω] (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d) (ξ : ℕ → Ω) (j : Fin (a.outputCount + 1)) :
    execute (OracleTemplate.BirchSgd.gradientOracle P g) (programAlgorithm p a lmo)
      (fun _ => a.oracleCalls) j ξ =
        (interpret p lmo (fun k x => g x (ξ k)) a.instructions (initialMemory p)).points
          (a.outputPoint j) := by
  erw [StochasticGradient.execute_advance]
  have h := advance_interpret p a lmo (fun k x => g x (ξ k)) a.instructions
    (initialMemory p) (a.outputPoint j)
  simpa only [programAlgorithm, Program.oracleCalls, queryCount, initialMemory] using
    congrArg (fun s : State p.d => s.memory.points s.selected) h
lemma advance_add {S : Type*} (step : ℕ → S → S) (n r call : ℕ) (s : S) :
    StochasticGradient.advance step (n + r) call s =
      StochasticGradient.advance step r (call + n) (StochasticGradient.advance step n call s) := by
  induction n generalizing call s with
  | zero => simp [StochasticGradient.advance]
  | succ n ih =>
      simpa [StochasticGradient.advance, Nat.succ_add, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using ih (call + 1) (step call s)

lemma advance_completed (p : Params) (a : Program) (lmo : Point p.d → Point p.d)
    (response : ℕ → Point p.d → Point p.d) (K call : ℕ) (s : State p.d)
    (h : s.remaining = []) :
    StochasticGradient.advance
      (fun k s => (programAlgorithm p a lmo).update s
        (response k ((programAlgorithm p a lmo).query s).2)) K call s = s := by
  induction K generalizing call with
  | zero => rfl
  | succ K ih =>
      simpa [StochasticGradient.advance, programAlgorithm, h] using ih (call + 1)

lemma execute_surplus {Ω : Type} [MeasurableSpace Ω] (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d) (ξ : ℕ → Ω) (j : Fin (a.outputCount + 1)) (extra : ℕ) :
    execute (OracleTemplate.BirchSgd.gradientOracle P g) (programAlgorithm p a lmo)
      (fun _ => a.oracleCalls + extra) j ξ =
    execute (OracleTemplate.BirchSgd.gradientOracle P g) (programAlgorithm p a lmo)
      (fun _ => a.oracleCalls) j ξ := by
  erw [StochasticGradient.execute_advance, StochasticGradient.execute_advance]
  rw [advance_add]
  have hc := advance_interpret p a lmo (fun k x => g x (ξ k)) a.instructions
    (initialMemory p) (a.outputPoint j)
  change StochasticGradient.advance _ a.oracleCalls 0 ((programAlgorithm p a lmo).initial j) = _ at hc
  rw [hc]
  erw [advance_completed p a lmo (fun k x => g x (ξ k)) extra (0 + a.oracleCalls) _ rfl]

lemma iid_reindex {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {samples : ℕ → Ξ → Ω} {mu : MeasureTheory.Measure Ω} {P : MeasureTheory.Measure Ξ}
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID samples mu P)
    (index : ℕ → ℕ) (hinj : Function.Injective index) :
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k => samples (index k)) mu P :=
  ⟨fun k => h.measurable (index k), ProbabilityTheory.iIndepFun.precomp hinj h.independent,
    fun k => h.marginal (index k)⟩

end LongTails.Proofs.BirchNonEuclideanExecution
