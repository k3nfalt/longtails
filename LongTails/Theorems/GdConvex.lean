import LongTails.Setups.SmoothAndConvex
import LongTails.Proofs.GdConvex

namespace OracleTemplate.Gradient.GdConvex

open LongTails.Setups.SmoothAndConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => max 1 ⌈q.L * q.R ^ 2 / (2 * q.ε)⌉₊

theorem result :
    Convergence LongTails.Setups.SmoothAndConvex.spec budget := by
  refine ⟨fun q => gd (q.L, q.x0), ?_, fun _ _ => trivial⟩
  intro q hp f oracle h
  rcases hp with ⟨hL, hR, hε⟩
  rcases h with ⟨hc, hg, hlip, xstar, hmin, hdist⟩
  let seed0 := (Classical.choice oracle.law.nonempty) 0
  let g := fun x => oracle.answer [] (0, x) seed0
  have hanswer : ∀ k x seed, oracle.answer k (0, x) seed = g x :=
    fun k x seed => (hg k seed x).unique (hg [] seed0 x)
  have haccuracy := gd_accuracy f g q.L q.R q.ε q.x0 xstar
    hL hR hε hc (hg [] seed0) (hlip [] seed0) hdist (budget q 0) le_rfl
  refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
  rintro ⟨⟨⟩, seed⟩
  change f (execute oracle (gd (q.L, q.x0)) (fun _ => budget q 0) () seed) - f xstar ≤ q.ε
  erw [execute_eq_of_answer_eq oracle g hanswer]
  exact haccuracy

end OracleTemplate.Gradient.GdConvex
