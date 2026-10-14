import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.StochasticGeneralizedConvergence
import LongTails.Proofs.StochasticGeneralizedOutput

open MeasureTheory

namespace OracleTemplate.StochasticGeneralized

open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => if p.Δ ≤ p.ε then 0 else 2*⌈16384*(1+Real.sqrt (p.L0*p.R^2/p.ε)+min ((⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*p.Δ/p.ε)) (Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ)))⌉₊+⌈1073741824*p.σ^2*p.R^2*Real.log (Real.exp 1/p.δ)/p.ε^2⌉₊

theorem result : Convergence LongTails.Setups.StochasticGeneralizedSmoothAndConvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O hadm
  rcases hadm with ⟨g, μ, P, hIID, rfl, hc, hg, hdiff, hH, ⟨u, hmin, hdist, hgap⟩, ho⟩
  by_cases hεΔ : p.Δ ≤ p.ε
  · refine ⟨measurable_execute_output p P ho.measurable (budget p 0), u, hmin, ?_⟩
    have hempty : {w : Unit × (ℕ → p.Ω) |
        p.ε < f (execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (algorithm p) (fun _ => (budget p 0)) w.1 w.2)-f u} = ∅ := by
      ext w
      rcases w with ⟨⟨⟩, ξ⟩
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      erw [execute_trivial p P g ξ hεΔ (budget p 0)]
      exact not_lt_of_ge (hgap.trans hεΔ)
    change ((Measure.dirac ()).prod (P : Measure (ℕ → p.Ω)))
      {w : Unit × (ℕ → p.Ω) | p.ε < f (execute
        { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (algorithm p) (fun _ => (budget p 0)) w.1 w.2)-f u} ≤ ENNReal.ofReal p.δ
    rw [hempty, measure_empty]
    exact bot_le
  · let N := ⌈16384*(1+Real.sqrt (p.L0*p.R^2/p.ε)+min ((⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*p.Δ/p.ε)) (Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ)))⌉₊
    have hN : 16384*(1+Real.sqrt (p.L0*p.R^2/p.ε)+
        min ((⌈(p.L1*p.R)^(2/3 : ℝ)⌉₊ : ℝ)*Real.log (4+4*p.Δ/p.ε)) (Real.log (4+4*p.Δ/p.ε)+(p.L1*p.R*Real.log (4+4*p.Δ/p.ε))^(2/3 : ℝ))) ≤ N := Nat.le_ceil _
    have hK : 2*N+⌈1073741824*p.σ^2*p.R^2*Real.log (Real.exp 1/p.δ)/p.ε^2⌉₊ ≤ budget p 0 := by simp only [budget, ite_eq_right hεΔ]; exact le_rfl
    refine ⟨measurable_execute_output p P ho.measurable (budget p 0), u, hmin, ?_⟩
    exact execution_high_probability p hp hc hg hdiff hH u hmin hdist hgap μ P hIID ho N (budget p 0) hN hK

end OracleTemplate.StochasticGeneralized
