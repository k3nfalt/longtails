import LongTails.Setups.StochasticConvexQuadratic
import LongTails.Proofs.Execution
import LongTails.Proofs.ChebyshevConvergence
import LongTails.Proofs.ChebyshevExecution

open MeasureTheory

namespace OracleTemplate.StochasticConvexQuadratic

open LongTails.Setups.StochasticConvexQuadratic

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 3 + ⌈4 * Real.sqrt (q.L * q.R ^ 2 / q.ε) + 65536 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊

theorem result : Convergence LongTails.Setups.StochasticConvexQuadratic.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun q => BatchedChebyshev.tuned q.L q.R q.σ q.ε q.x0, ?_,
    fun q hp => BatchedChebyshev.tuned_allowed q hp.1⟩
  rintro q hp

  rintro f O ⟨had, A, u, c, hquad⟩
  rcases hp with ⟨hL, hR, hσ, hε⟩
  rcases had with ⟨g, p, rfl, hc, hg, hlip, ⟨xstar, hmin, hdist⟩, ho⟩
  let T := if q.L * q.R ^ 2 / 2 ≤ q.ε then 0 else ⌈Real.sqrt (q.L * q.R ^ 2 / q.ε)⌉₊
  let M := ⌈65536 * q.σ ^ 2 * q.R ^ 2 / q.ε ^ 2⌉₊
  let K := budget q 0
  let P := Measure.infinitePi (fun _ : ℕ => (p : Measure q.Ω))
  let output := fun ξ : ℕ → q.Ω => BatchedChebyshev.run q.L T M g T 1 q.x0 ξ
  have hcalls : BatchedChebyshev.calls T M T 1 ≤ K := by
    by_cases hcoarse : q.L * q.R ^ 2 / 2 ≤ q.ε
    · simp only [T, ite_eq_left hcoarse, BatchedChebyshev.calls, Nat.zero_le]
    · exact (BatchedChebyshev.calls_le T M).trans (by
        simpa only [T, ite_eq_right hcoarse, M, K, budget] using
          BatchedChebyshev.rounded_calls_budget q.L q.R q.σ q.ε)
  have hf := BatchedChebyshev.quadratic_recenter A u xstar c hquad hmin
  have ha := BatchedChebyshev.tuned_expected_accuracy A xstar q.x0 hL hR hε hdist hf hlip ho
  have hout : Measurable output :=
    (BatchedChebyshev.run_measurable ho.measurable q.L T M T 1).comp
      (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun ξ => f (output ξ) - f xstar) P := ha.1
  have he : (∫ ξ, f (output ξ) - f xstar ∂P) ≤ q.ε := ha.2
  let result := fun seed : Unit × (ℕ → q.Ω) => (execute
      { Seed := fun _ => q.Ω
        law := ⟨P, inferInstance⟩
        answer := fun _ (_, x) ω => g x ω }
      (BatchedChebyshev.algorithm q.L T M q.x0) (fun _ => K) seed.1 seed.2)
  change Measurable result ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧
    Integrable (fun seed => f (result seed) - f xstar) ((Measure.dirac ()).prod P) ∧
    (∫ seed, f (result seed) - f xstar ∂(Measure.dirac ()).prod P) ≤ q.ε
  have hexec : result = fun seed => output seed.2 := by
    funext ⟨⟨⟩, ξ⟩
    exact (BatchedChebyshev.execute_algorithm p g q.L T M q.x0 K hcalls ξ)
  rw [hexec]
  refine ⟨hout.comp measurable_snd, xstar, hmin, ?_, ?_⟩
  · exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := P)).integrable_comp_of_integrable hi
  · rw [integral_fun_snd (fun ξ : ℕ → q.Ω => f (output ξ) - f xstar)]
    simpa using he

end OracleTemplate.StochasticConvexQuadratic
