import LongTails.Setups.SmoothAndConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.AcceleratedConvex

namespace OracleTemplate.Gradient.AcceleratedConvex

open LongTails.Setups.SmoothAndConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => max 1 ⌈Real.sqrt (2 * q.L * q.R ^ 2 / q.ε)⌉₊

theorem result :
    Convergence LongTails.Setups.SmoothAndConvex.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => accelerated (q.L, q.x0), ?_, fun _ _ => trivial⟩
  intro q hp K hK f oracle h
  rcases hp with ⟨hL, hR, hε⟩
  rcases h with ⟨hc, hg, hlip, xstar, hmin, hdist⟩
  let seed0 := (Classical.choice oracle.law.nonempty) 0
  let g := fun x => oracle.answer [] (0, x) seed0
  have hanswer : ∀ k x seed, oracle.answer k (0, x) seed = g x :=
    fun k x seed => (hg k seed x).unique (hg [] seed0 x)
  have haccuracy := accelerated_accuracy f g q.L q.R q.ε q.x0 xstar
    hL hR hε hc (hg [] seed0) (hlip [] seed0) hdist K hK
  refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
  rintro ⟨⟨⟩, seed⟩
  change f (execute oracle (accelerated (q.L, q.x0)) (fun _ => K) () seed) - f xstar ≤ q.ε
  erw [execute_eq_of_answer_eq oracle g hanswer]
  exact haccuracy

end OracleTemplate.Gradient.AcceleratedConvex
