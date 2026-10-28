import LongTails.Template
import outputs.Proofs.FreyaModel

open scoped ENNReal

namespace outputs.Algorithms.FreyaInputs

open outputs.Proofs.FreyaModel

structure Base where
  d : ℕ
  m : ℕ
  Lminus : ℝ
  Lpm : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : Space d

structure Serial extends Base where
  S : ℕ
  ρ : ℝ

structure Workers extends Base where
  n : ℕ

structure Family extends Workers where
  S : ℕ
  ρ : ℝ

structure Optimized extends Workers where
  τ : Fin n → ℝ≥0∞

structure Simple extends Workers

structure Raw where
  d : ℕ
  m : ℕ
  n : ℕ
  x0 : Space d
  η : ℝ
  S : ℕ
  ρ : ℝ
  K : ℕ
  «prefix» : Bool

structure SerialRaw where
  d : ℕ
  m : ℕ
  x0 : Space d
  η : ℝ
  S : ℕ
  ρ : ℝ
  K : ℕ

end outputs.Algorithms.FreyaInputs
