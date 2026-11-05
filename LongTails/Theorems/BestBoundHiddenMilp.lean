import LongTails.Setups.HiddenMixedIntegerLinear
import LongTails.Proofs.BestBoundBranchAndBound

namespace OracleTemplate.HiddenMixedIntegerLinear

open LongTails.Setups.HiddenMixedIntegerLinear

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun P _ => min (2 * ∏ j, (P.hi j - P.lo j + 1).toNat - 1) (1 + 4 * P.p * (goodPoints P).card)

theorem result : Convergence LongTails.Setups.HiddenMixedIntegerLinear.spec budget :=
  ⟨bestBoundBranchAndBound, fun P hv _ O hO ω =>
      hv.elim (fun h => bestBound_solves P h.1 h.2 O hO ω.1 ω.2)
          fun h => bestBound_solves_infeasible P h O hO ω.1 ω.2 _, fun _ _ => trivial⟩

end OracleTemplate.HiddenMixedIntegerLinear
