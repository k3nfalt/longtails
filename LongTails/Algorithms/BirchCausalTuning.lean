import LongTails.Algorithms.BirchCausalPhysical

namespace LongTails.Algorithms.BirchCausalTuning

open LongTails.Algorithms.BirchNonEuclideanPhysical

noncomputable def batchSize (H : ℕ) (κ σ ε : ℝ) : ℕ := max (4 * H) ⌈32 * κ * σ ^ 2 / ε⌉₊

noncomputable def drift (H B : ℕ) : ℝ :=
  ((B : ℝ) + 2 * H * (packetCutoff H B + 1) + 1) / H

noncomputable def stepSize (H B : ℕ) (L : ℝ) : ℝ := 1 / (4 * L * drift H B)

noncomputable def horizon (H B : ℕ) (L Δ ε : ℝ) : ℕ := max 1 ⌈48 * L * Δ * drift H B / ε⌉₊

noncomputable def program {m : ℕ} (p : LongTails.Setups.BirchNonEuclidean.Params) (H : ℕ)
    (word : ℕ → ℕ → ℕ → Fin m) (recipe : ℕ → ℕ → Packet m → LongTails.Algorithms.BirchCausalPackets.PacketExpr) :
    LongTails.Setups.BirchNonEuclidean.Program :=
  let B := batchSize H p.κ p.σ p.ε
  let K := horizon H B p.L p.Δ p.ε
  let η := stepSize H B p.L
  (LongTails.Algorithms.BirchNonEuclideanFamilies.makeTemplate K
    (LongTails.Algorithms.BirchCausalPhysical.physicalGraphCode H K B (word K B) (recipe K B))).instantiate
    (LongTails.Setups.BirchNonEuclidean.canonicalTuning η B)

noncomputable def output {Ω : Type} [MeasurableSpace Ω] {m : ℕ}
    (p : LongTails.Setups.BirchNonEuclidean.Params) (H : ℕ)
    (word : ℕ → ℕ → ℕ → Fin m) (recipe : ℕ → ℕ → Packet m → LongTails.Algorithms.BirchCausalPackets.PacketExpr)
    (lmo : OracleTemplate.Rennala.Point p.d → OracleTemplate.Rennala.Point p.d)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : OracleTemplate.Rennala.Point p.d → Ω → OracleTemplate.Rennala.Point p.d) (Q : ℕ)
    (z : Fin ((program p H word recipe).outputCount + 1) × (ℕ → Ω)) : OracleTemplate.Rennala.Point p.d :=
  OracleTemplate.execute (OracleTemplate.BirchSgd.gradientOracle P g)
    (LongTails.Setups.BirchNonEuclidean.programAlgorithm p (program p H word recipe) lmo) (fun _ => Q) z.1 z.2

end LongTails.Algorithms.BirchCausalTuning
