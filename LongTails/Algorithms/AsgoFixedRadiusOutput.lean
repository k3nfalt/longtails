import LongTails.Setups.AsgoFixedRadius

open MeasureTheory OracleTemplate OracleTemplate.Muon

namespace LongTails.Algorithms.AsgoFixedRadiusOutput

open LongTails.Setups.AsgoFixedRadius

noncomputable section

def output (p : LongTails.Setups.AsgoFixedRadius.Public) {Ξ : Type*} (g : Mat p.m p.n → Ξ → Mat p.m p.n)
    (s : ℕ → Ξ) (T : ℕ) : Mat p.m p.n :=
  if T = 0 then p.W0 else
    (1 / (T : ℝ)) • ∑ t ∈ Finset.range T, Core.point p g s t

def sourceOracle {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : Core.Problem m n) (P : ProbabilityMeasure Ω) (ξ : ℕ → Ω → I.Sample) :
    Oracle (Mat m n) (Mat m n) where
  Seed := fun _ => I.Sample
  law := P.map (fun ω j => ξ j ω)
  answer := fun _ query sample => I.g query.2 sample

end

end LongTails.Algorithms.AsgoFixedRadiusOutput
