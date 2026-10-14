import LongTails.Setups.SmoothPL
import LongTails.Proofs.Execution
import LongTails.Proofs.GdPL

namespace OracleTemplate.PLGradient

open LongTails.Setups.SmoothPL

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(p.L / p.μ) * Real.log (1 + p.Δ / p.ε)⌉₊

theorem result : Convergence LongTails.Setups.SmoothPL.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => Gradient.gd (p.L, p.x0), ?_, fun _ _ => trivial⟩
  rintro p ⟨hμ, hμL, hΔ, hε⟩
  intro K hK
  rintro f oracle ⟨ho, hg, hlip, xstar, hmin, hgap, hpl⟩
  have hanswer : ∀ k x seed, oracle.answer k (0, x) seed = gradient f x :=
    fun k x seed => (ho k seed x).unique (hg x)
  have ha := gd_accuracy f p.L p.μ p.Δ p.ε p.x0 xstar hμ hμL hΔ hε hgap hg hlip hpl K hK
  refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
  · rintro ⟨⟨⟩, seed⟩
    change f (execute oracle (Gradient.gd (p.L, p.x0)) (fun _ => (K)) () seed) - f xstar ≤ p.ε
    erw [execute_eq_of_answer_eq oracle (gradient f) hanswer]
    exact ha

end OracleTemplate.PLGradient
