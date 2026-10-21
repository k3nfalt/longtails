import outputs.Setups.MuonThirdOrder
import outputs.Proofs.MuonThirdOrder

namespace OracleTemplate.MuonThirdOrder

open Muon SimplifiedMuon outputs.Setups.MuonThirdOrder

noncomputable def budget : (let S := outputs.Setups.MuonThirdOrder.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.T

theorem result : Convergence outputs.Setups.MuonThirdOrder.spec budget := by
  refine ⟨fun q => simplifiedMuon q, ?_, fun _ _ => rfl⟩
  intro p hp f O hO
  obtain ⟨hf, hb, hans⟩ := hO
  dsimp only
  intro ω
  have hexe := execute_simplified (publicInput p) O (gradient f) hans ω.1 ω.2
  have key := guarantee p hp f hf hb
  have e : (execute O (simplifiedMuon (publicInput p)) (budget p) ω.1 ω.2) =
      fun j : Fin (p.T + 1) => SimplifiedMuon.trajectory (publicInput p) (gradient f) j := hexe
  exact (congrArg (Guarantee p f) e).mpr key

end OracleTemplate.MuonThirdOrder
