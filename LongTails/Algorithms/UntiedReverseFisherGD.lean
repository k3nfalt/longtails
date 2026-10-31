import LongTails.Setups.UntiedGaussianReverseFisher
import LongTails.Algorithms.SymmetricReverseFisherGD

open MeasureTheory OracleTemplate WithLp

namespace LongTails.Algorithms.UntiedReverseFisherGD

open LongTails.Setups.UntiedGaussianReverseFisher

def tiedParams (p : Params) : LongTails.Setups.SymmetricGaussianReverseFisher.Params :=
  ⟨p.dimension, 0, 0, 1, 1⟩

noncomputable def direction (p : Params) (seed : Fin p.dimension → ℝ) : Space p :=
  LongTails.Algorithms.SymmetricReverseFisherGD.initial (tiedParams p) seed

noncomputable def initial (p : Params) (seed : Fin p.dimension → ℝ) : Means p :=
  toLp 2 ![direction p seed, -direction p seed]

noncomputable def step : ℝ := 1 / 32

noncomputable def algorithm (p : Params) : Algorithm (Means p) (Means p) (Means p) where
  Seed := Fin p.dimension → ℝ
  law := ⟨Measure.pi (fun _ =>
    (LongTails.Algorithms.SymmetricReverseFisherGD.coordinateLaw : Measure ℝ)), inferInstance⟩
  State := Means p
  initial := initial p
  query θ := (0, θ)
  update θ reply := θ - step • reply
  output θ := θ

noncomputable def output (p : Params) (oracle : Oracle (Means p) (Means p)) (K : ℕ)
    (seed : Fin p.dimension → ℝ) (oracleSeed : (k : ℕ) → oracle.Seed k) : Means p :=
  execute oracle (algorithm p) (fun _ => K) seed oracleSeed

end LongTails.Algorithms.UntiedReverseFisherGD
