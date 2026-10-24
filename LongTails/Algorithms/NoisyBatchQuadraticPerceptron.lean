import LongTails.Setups.NoisyBatchQuadraticPerceptron

namespace LongTails.Algorithms.NoisyBatchQuadraticPerceptron

open OracleTemplate LongTails.Setups.NoisyBatchQuadraticPerceptron

noncomputable def algorithm (P : Public) (η : ℝ) :
    Algorithm (Query P) (Reply P.dimension) (Weights P.dimension) where
  Seed := P.noise.Ω
  law := P.noise.law
  State := ScanState P
  initial := initial P
  query s := (0, s.cursor, s.point)
  update := scanUpdate P η
  output := ScanState.point

noncomputable def output (P : Public)
    (oracle : Oracle (Query P) (Reply P.dimension)) (η : ℝ) (K : ℕ)
    (ω : P.noise.Ω) (ξ : (k : ℕ) → oracle.Seed k) : Weights P.dimension :=
  execute oracle (algorithm P η) (fun _ => K) ω ξ

end LongTails.Algorithms.NoisyBatchQuadraticPerceptron
