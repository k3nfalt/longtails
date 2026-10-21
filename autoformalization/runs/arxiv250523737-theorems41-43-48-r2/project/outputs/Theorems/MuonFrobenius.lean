import outputs.Setups.MuonFrobenius
import outputs.Proofs.MuonGuarantees

open MeasureTheory

namespace OracleTemplate.MuonFrobenius

open Muon outputs.Setups.MuonFrobenius

noncomputable def budget : (let S := outputs.Setups.MuonFrobenius.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.T * p.B

theorem result : Convergence outputs.Setups.MuonFrobenius.spec budget := by
  refine ⟨fun q => muon q, ?_, fun _ _ => rfl⟩
  intro p hp f O hO
  obtain ⟨hf, hb, Ω, mΩ, μ, P, g, hiid, ho, rfl⟩ := hO
  let := mΩ
  have hB : 1 ≤ (publicInput p).B := hp.2.2.2.2.2.2.2.1
  have hexe : (fun z : Unit × (ℕ → Ω) => execute (sampleOracle P g) (muon (publicInput p)) (budget p) z.1 z.2) =
      fun z (j : Fin (p.T + 1)) => (trajectory (publicInput p) g z.2 j).2.1 :=
    funext fun z => execute_muon (publicInput p) hB P g z.1 z.2
  have hmap : ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω))).map Prod.snd =
      (P : Measure (ℕ → Ω)) := by
    rw [Measure.map_snd_prod]; simp
  change Guarantee p f (fun z : Unit × (ℕ → Ω) => execute (sampleOracle P g) (muon (publicInput p))
    (budget p) z.1 z.2) ((Measure.dirac () : Measure Unit).prod (P : Measure (ℕ → Ω)))
  have key := guarantee p hp f hf hb μ P g hiid ho _ Prod.snd measurable_snd hmap
  rw [← hexe] at key
  exact key

end OracleTemplate.MuonFrobenius
