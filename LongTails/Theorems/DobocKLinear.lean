import LongTails.Setups.DobocK
import LongTails.Proofs.DobocKConvergence

namespace OracleTemplate.DobocKLinear

open LongTails.Setups.DobocK OracleTemplate.DobocK

def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.k

theorem result : Convergence LongTails.Setups.DobocK.spec budget := by
  refine ⟨fun q => dobocK q, ?_, fun _ _ => rfl⟩
  rintro p ⟨hnet, hlam, hη, hK, hm, hmM, hL, hstep⟩ f O ⟨hA1, hA2, hO, hT⟩
  obtain ⟨xstar, hmin⟩ := penalty_exists_minimizer p f hnet hlam hm hA1
  obtain ⟨h0, h1, hrate⟩ :=
    theorem2 p f hnet hlam hη hK hm hmM hL hA1 hA2 hstep xstar hmin (hT xstar hmin)
  refine ⟨xstar, hmin, h0, h1, Filter.Eventually.of_forall ?_⟩
  rintro ⟨seed, ξ⟩
  have hexec := execute_dobocK p.toPublic f O hO p.k seed ξ
  change penalty p.toPublic f (execute O (dobocK p.toPublic) (fun _ => p.k) seed ξ) -
    penalty p.toPublic f xstar ≤ _
  rw [hexec]
  exact hrate p.k

end OracleTemplate.DobocKLinear
