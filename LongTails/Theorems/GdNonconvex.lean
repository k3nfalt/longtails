import LongTails.Setups.SmoothNonconvex
import LongTails.Proofs.Execution
import LongTails.Proofs.GdNonconvex

open MeasureTheory

namespace OracleTemplate.NonconvexGradient

open LongTails.Setups.SmoothNonconvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => max 1 ⌈2 * p.L * p.Δ / p.ε ^ 2⌉₊

theorem result :
    Convergence LongTails.Setups.SmoothNonconvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => gdBest (p.L, p.Δ, p.ε, p.x0), ?_, fun _ _ => trivial⟩
  rintro p ⟨hL, hΔ, hε⟩

  rintro f oracle ⟨ho, hg, hlip, lower, hb, hgap⟩
  have hanswer : ∀ k x seed, oracle.answer k (0, x) seed = gradient f x :=
    fun k x seed => (ho k seed x).unique (hg x)
  let K := max 1 ⌈2 * p.L * p.Δ / p.ε ^ 2⌉₊
  let result := execute { answer := fun _ (_, x) _ => gradient f x } (gdBest (p.L, p.Δ, p.ε, p.x0)) (fun _ => K)
  have ha := bestGradient_accuracy f p.L p.Δ p.ε p.x0 hL hε hg hlip lower hb hgap
  have he : ∀ seed : (gdBest (p.L, p.Δ, p.ε, p.x0)).Seed × ((k : ℕ) → oracle.Seed k),
      execute oracle (gdBest (p.L, p.Δ, p.ε, p.x0)) (fun _ => K) seed.1 seed.2 = result := by
    rintro ⟨⟨⟩, ξ⟩
    exact execute_eq_of_answer_eq oracle (gradient f) hanswer _ _ _ _
  have hout : (fun seed : (gdBest (p.L, p.Δ, p.ε, p.x0)).Seed × ((k : ℕ) → oracle.Seed k) =>
      (execute oracle (gdBest (p.L, p.Δ, p.ε, p.x0)) (fun _ => K) seed.1 seed.2)) =
      (fun _ => result) := funext (fun seed => (he seed))
  change spec.successful p f (fun seed : (gdBest (p.L, p.Δ, p.ε, p.x0)).Seed × ((k : ℕ) → oracle.Seed k) =>
    (execute oracle (gdBest (p.L, p.Δ, p.ε, p.x0)) (fun _ => K) seed.1 seed.2)) _
  rw [hout]
  dsimp only [spec, ProbabilityMeasure.coe_mk]
  exact ⟨measurable_const, integrable_const _, by simpa only [integral_const, probReal_univ, one_smul] using ha⟩


end OracleTemplate.NonconvexGradient
