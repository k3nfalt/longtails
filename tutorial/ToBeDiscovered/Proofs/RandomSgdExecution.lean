import tutorial.ToBeDiscovered.Algorithms.RandomSgd
import LongTails.Proofs.Execution

namespace OracleTemplate.StochasticNonconvex

open LongTails.Setups.StochasticSmoothNonconvex

def advance {S : Type*} (step : ℕ → S → S) : ℕ → ℕ → S → S
  | 0, _, s => s
  | K + 1, call, s => advance step K (call + 1) (step call s)

lemma execute_advance {Q R A : Type*} (O : Oracle Q R) (method : Algorithm Q R A)
    (K : ℕ) (seed : method.Seed) (ξ : (k : ℕ) → O.Seed k)
    (response : ℕ → (Fin 1 × Q) → R)
    (h : ∀ history query, O.answer history query (ξ history.length) = response history.length query) :
    execute O method (fun _ => K) seed ξ =
      method.output (advance (fun k s => method.update s (response k (method.query s)))
        K 0 (method.initial seed)) := by
  rw [execute_indexed_of_answer O method K seed ξ response h]
  congr 1
  generalize method.initial seed = s
  generalize (0 : ℕ) = call
  induction K generalizing s call with
  | zero => rfl
  | succ K ih =>
    rw [Function.iterate_succ_apply]
    exact ih _ _

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma advance_frozen (g : E → Ω → E) (η : ℝ) (ξ : ℕ → Ω)
    (K call : ℕ) (x z : E) :
    (advance (fun k s => update η s (g s.2.1 (ξ k))) K call (0, x, z)).2.2 = z := by
  induction K generalizing call x with
  | zero => rfl
  | succ K ih =>
    simpa only [advance, update, Nat.zero_sub, Nat.zero_ne_one, ite_false] using
      ih (call + 1) (x - η • g x (ξ call))

lemma advance_selected (g : E → Ω → E) (η : ℝ) (ξ : ℕ → Ω)
    (K call : ℕ) (x z : E) (i : Fin K) :
    (advance (fun k s => update η s (g s.2.1 (ξ k))) K call (i.val + 1, x, z)).2.2 =
      selected g η K x (fun j => ξ (call + j.val)) i := by
  induction K generalizing call x z with
  | zero => exact Fin.elim0 i
  | succ K ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [advance, update, selected] using
        advance_frozen g η ξ K (call + 1) (x - η • g x (ξ call)) x
    · simp only [advance, update, Fin.val_succ, Nat.add_sub_cancel, selected, Fin.cases_succ]
      have hn : j.val + 1 + 1 ≠ 1 := by omega
      simp only [hn, ite_false]
      simpa [update, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (call + 1) (x - η • g x (ξ call)) z j

lemma execute_randomSgd [MeasurableSpace Ω] (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : E → Ω → E) (η : ℝ) (N : ℕ) [NeZero N] (x0 : E) (i : Fin N) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω
              law := P
              answer := fun _ (_, x) seed => g x seed }
      (randomSgd η N x0) (fun _ => N) i ξ =
        selected g η N x0 (fun j => ξ j.val) i := by
  erw [execute_advance _ _ _ _ _ (fun k q => g q.2 (ξ k)) (fun _ _ => rfl)]
  simpa [randomSgd] using advance_selected g η ξ N 0 x0 x0 i

end OracleTemplate.StochasticNonconvex
