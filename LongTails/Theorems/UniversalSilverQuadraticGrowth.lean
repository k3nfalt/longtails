import LongTails.Setups.SmoothConvexQuadraticGrowth
import LongTails.Proofs.UniversalSilverRate

namespace LongTails.Theorems.UniversalSilverQuadraticGrowth

open OracleTemplate LongTails.Setups.SmoothConvexQuadraticGrowth
open LongTails.Algorithms.UniversalSilver LongTails.Proofs.UniversalSilverSchedule
open LongTails.Proofs.UniversalSilverConvergence LongTails.Proofs.UniversalSilverRate

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈2 * (1 + 2 * p.L / p.μ) ^ (Real.log 2 / Real.log (1 + Real.sqrt 2)) * (Real.logb 2 (1 + p.L * p.R ^ 2 / p.ε) + 1) * (Real.logb 2 (1 + 2 * p.L / p.μ) + Real.logb 2 (Real.logb 2 (1 + p.L * p.R ^ 2 / p.ε) + 1) + 3)⌉₊

theorem result : Convergence LongTails.Setups.SmoothConvexQuadraticGrowth.spec budget := by
  refine ⟨fun p => method p, ?_, ?_⟩
  · intro p hp f O hO
    change Params at p
    change (p.E → ℝ) at f
    change Oracle p.E p.E 1 at O
    obtain ⟨hc, hg, hlip, ⟨xstar, hmin, hR⟩, hqg⟩ := hO
    let seed0 := (Classical.choice O.law.nonempty) 0
    let G : p.E → p.E := fun x => O.answer [] (0, x) seed0
    have hanswer : ∀ k x seed, O.answer k (0, x) seed = G x :=
      fun k x seed => (hg k seed x).unique (hg [] seed0 x)
    have hG : ∀ x, HasGradientAt f (G x) x := fun x => hg [] seed0 x
    have hGlip : ∀ x y, ‖G x - G y‖ ≤ p.L * ‖x - y‖ := fun x y => hlip [] seed0 x y
    refine ⟨xstar, hmin, Filter.Eventually.of_forall ?_⟩
    intro ω
    change f (execute O (method p.toPublic) (budget p) ω.1 ω.2) - f xstar ≤ p.ε
    have hK := budget_ge p hp
    set K := budget p 0
    have hb : budget p = fun _ => K := by funext i; fin_cases i; rfl
    rw [hb, execute_eq_of_answer_eq O G hanswer]
    erw [execute_iterate]
    have hit := iterate_method (G := G) (L := p.L) p.x0 K K (lt_blocks_length K).le
    change f ((fun s : ℕ × p.E => (s.1 + 1, s.2 - (stepsize s.1 / p.L) • G s.2))^[K]
      (0, p.x0)).2 - f xstar ≤ p.ε
    rw [hit]
    exact accuracy p hp hc hG hGlip hmin hR hqg K hK
  · intro p hp
    exact ⟨fun t => stepsize t / p.L, fun t => div_pos (stepsize_positive t) hp.1, rfl⟩

end LongTails.Theorems.UniversalSilverQuadraticGrowth
