import LongTails.Setups.BoundedMixedIntegerLinear
import LongTails.Proofs.LpBranchAndBound

namespace OracleTemplate.BoundedMixedIntegerLinear

open LongTails.Setups.BoundedMixedIntegerLinear

def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun P _ => 2 * ∏ j, (P.hi j - P.lo j + 1).toNat - 1

theorem result : Convergence LongTails.Setups.BoundedMixedIntegerLinear.spec budget :=
  convergence_of_public_budget (S := spec) (fun P => 2 * ∏ j, (P.hi j - P.lo j + 1).toNat - 1)
    ⟨lpBranchAndBound, fun P _ _ O hO ω => lpBranchAndBound_solves P O hO ω.1 ω.2,
      fun _ _ => trivial⟩

end OracleTemplate.BoundedMixedIntegerLinear
