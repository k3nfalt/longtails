import LongTails.Setups.StochasticConstrainedGeneralizedMonotone
import LongTails.Proofs.ProjectedClippedPublic
import LongTails.Proofs.ProjectedClippedBudget
import LongTails.Proofs.Execution

namespace OracleTemplate.StochasticConstrainedGeneralizedMonotone

open LongTails.Setups.StochasticConstrainedGeneralizedMonotone
open ProjectedClippedExtragradient

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈2 ^ 128 * ((q.L0 + q.L1 * q.G) * (1 + q.L1 * q.R) ^ 2 * q.R / q.ε + (1 + q.L1 * q.R) ^ 4 + q.σ ^ 2 / q.ε ^ 2) * (1 + Real.log (2 + (q.L0 + q.L1 * q.G + q.L1 * q.ε) * (1 + q.L1 * q.R) * q.R / q.ε)) ^ 3 * (1 + Real.log ((2 + (q.L0 + q.L1 * q.G + q.L1 * q.ε) * (1 + q.L1 * q.R) * q.R / q.ε) / q.δ))⌉₊

theorem result : Convergence LongTails.Setups.StochasticConstrainedGeneralizedMonotone.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun q => budget q 0)
  refine ⟨fun q => algorithm ⟨q.L0, q.L1, q.R, q.G, q.σ, q.ε, q.δ⟩ q.x0,
    ?_, fun _ _ => trivial⟩
  rintro q ⟨h0, h1, hR, hG, hσ, hε, hδ, hδ1⟩
  rintro I O ⟨g, p, P, proj, hIID, rfl, hproj, hX, hx0, hc, hm, hlip,
    ⟨xstar, hstar, hvi, hd, hGs⟩, hg⟩
  let t : Tuning := ⟨q.L0, q.L1, q.R, q.G, q.σ, q.ε, q.δ⟩
  have hP : ConstrainedMonotone.Proj I.X proj :=
    ⟨fun z => (hproj z).1, fun z => (hproj z).2⟩
  have hF : GeneralizedMonotone.Hyp I.F t.L0 t.L1 := ⟨h0, h1, hc, hm, hlip⟩
  have hn : ConstrainedMonotone.Normal I.X xstar (-I.F xstar) := by
    intro w hw
    simpa only [inner_neg_left, neg_nonpos] using hvi w hw
  have hK : runCalls t 0 (stageCount t) ≤ budget q 0 := by
    apply (Nat.cast_le (α := ℝ)).mp
    exact (total_calls_bound t h0 h1 hR hG hε hδ hδ1).trans (Nat.le_ceil _)
  exact execution_success hP hX t hF hR hε hδ hx0 hstar hn hGs hd p P hIID hg
    (budget q 0) hK

end OracleTemplate.StochasticConstrainedGeneralizedMonotone
