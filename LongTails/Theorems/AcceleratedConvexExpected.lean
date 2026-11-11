import LongTails.Setups.SmoothAndConvexExpected
import LongTails.Proofs.Execution
import LongTails.Proofs.AcceleratedConvex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace OracleTemplate.Gradient.AcceleratedConvexExpected

open LongTails.Setups.SmoothAndConvexExpected
open MeasureTheory

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => max 1 ⌈Real.sqrt (2 * q.L * q.R ^ 2 / q.ε)⌉₊

theorem result :
    Convergence LongTails.Setups.SmoothAndConvexExpected.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => accelerated (q.L, q.x0), ?_, fun _ _ => trivial⟩
  intro q hp K hK f oracle h
  rcases hp with ⟨hL, hR, hε, _, _⟩
  rcases h with ⟨hc, hg, hlip, xstar, hmin, hdist⟩
  let seed0 := (Classical.choice oracle.law.nonempty) 0
  let g := fun x => oracle.answer [] (0, x) seed0
  have hanswer : ∀ k x seed, oracle.answer k (0, x) seed = g x :=
    fun k x seed => (hg k seed x).unique (hg [] seed0 x)
  have haccuracy := accelerated_accuracy f g q.L q.R q.ε q.x0 xstar
    hL hR.le hε hc (hg [] seed0) (hlip [] seed0) hdist K hK
  have hout : (fun w : (accelerated (q.L, q.x0)).Seed × ((k : ℕ) → oracle.Seed k) =>
      f (execute oracle (accelerated (q.L, q.x0)) (fun _ => K) w.1 w.2) - f xstar) =
      fun _ => f (execute { answer := fun _ query _ => g query.2 }
        (accelerated (q.L, q.x0)) (fun _ => K) ()) - f xstar := by
    funext ⟨⟨⟩, seed⟩
    rw [execute_eq_of_answer_eq oracle g hanswer]
  refine ⟨xstar, hmin, ?_, ?_⟩
  · change Integrable (fun w : (accelerated (q.L, q.x0)).Seed × ((k : ℕ) → oracle.Seed k) => f (execute oracle (accelerated (q.L, q.x0))
        (fun _ => K) w.1 w.2) - f xstar) _
    rw [hout]
    exact integrable_const _
  · change (∫ w : (accelerated (q.L, q.x0)).Seed × ((k : ℕ) → oracle.Seed k), f (execute oracle (accelerated (q.L, q.x0))
        (fun _ => K) w.1 w.2) - f xstar
        ∂(((accelerated (q.L, q.x0)).law : Measure (accelerated (q.L, q.x0)).Seed).prod (oracle.law : Measure ((k : ℕ) → oracle.Seed k)))) ≤ q.ε
    rw [hout, integral_const]
    have hmass : (((accelerated (q.L, q.x0)).law : Measure (accelerated (q.L, q.x0)).Seed).prod
        (oracle.law : Measure ((k : ℕ) → oracle.Seed k))).real Set.univ = 1 := probReal_univ
    rw [hmass, one_smul]
    exact haccuracy

end OracleTemplate.Gradient.AcceleratedConvexExpected
