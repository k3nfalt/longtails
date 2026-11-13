import LongTails.Setups.BirchNonIID
namespace LongTails.Setups.BirchAveragingDiscovery

open OracleTemplate
open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonIID

/-- Public local horizon together with the unchanged non-IID parameters. -/
structure Parameters (workers : ℕ) where
  base : Params workers
  localSteps : ℕ

/-- The explicitly studied zero-noise, population-Hessian-similarity subclass.
The worker index n represents n+1 workers, so every positive worker count is covered. -/
noncomputable def spec (n : ℕ) : Setup where
  numOracles := n + 1
  Params := Parameters (n + 1)
  Public := Parameters (n + 1)
  Instance p := Instance (n + 1) p.base.d
  Query p := Point p.base.d
  Reply p := Point p.base.d
  Output p := Point p.base.d
  publicInput p := p
  valid p := Valid p.base ∧ 0 < p.localSteps ∧ (∀ i, p.base.σ i = 0) ∧
    (p.base.similarity = .secondOrder ∨ p.base.similarity = .firstAndSecondOrder)
  admissible p I O := Admissible p.base I O
  successful p I output P := (LongTails.Setups.BirchNonIID.spec (n + 1)).successful p.base I output P

end LongTails.Setups.BirchAveragingDiscovery
