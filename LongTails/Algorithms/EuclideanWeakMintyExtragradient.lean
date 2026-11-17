import LongTails.Setups.EuclideanWeakMinty
import LongTails.Algorithms.NonEuclideanExtragradient

namespace LongTails.Algorithms.EuclideanWeakMintyExtragradient

open OracleTemplate LongTails.Setups.EuclideanWeakMinty

noncomputable abbrev mirrorData (p : Params) : LongTails.Setups.NonEuclideanWeakMinty.Public where
  E := EuclideanSpace ℝ (Fin p.d)
  L := p.L
  ρ := p.ρ
  μ := 1
  h := fun x => ‖x‖ ^ 2 / 2
  x0 := p.x0

noncomputable def algorithm (p : Params) :
    Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d)) where
  Seed := (NonEuclideanExtragradient.algorithm (mirrorData p)).Seed
  law := (NonEuclideanExtragradient.algorithm (mirrorData p)).law
  State := NonEuclideanExtragradient.State (mirrorData p)
  initial := (NonEuclideanExtragradient.algorithm (mirrorData p)).initial
  query := (NonEuclideanExtragradient.algorithm (mirrorData p)).query
  update := fun s v => NonEuclideanExtragradient.step (mirrorData p) s (innerSL ℝ v)
  output := NonEuclideanExtragradient.output (mirrorData p)

end LongTails.Algorithms.EuclideanWeakMintyExtragradient
