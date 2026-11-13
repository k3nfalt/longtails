import LongTails.Algorithms.Batched
import LongTails.Algorithms.RobustGradientEstimator
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OracleTemplate.SublevelRobustGradient

open RobustGradient

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def plainStep (η : ℝ) (x0 : E) : Algorithm E E E where
  State := E
  initial _ := x0
  query x := (0, x)
  update x v := x - η • v
  output x := x

noncomputable def blockMean (m b : ℕ) (r : Fin (m * b) → E) (i : Fin m) : E :=
  (1 / (b : ℝ)) • ∑ l : Fin b, r (finProdFinEquiv (i, l))

noncomputable def robustCenter {n : ℕ} (hn : 0 < n) (B : ℝ) (v : Fin n → E) : E := by
  classical
  exact if ∃ i, n < 2 * (neighbors B v i).card then pilotCenter B v else v ⟨0, hn⟩

noncomputable def aggregate {m b : ℕ} (hm : 0 < m) (B : ℝ) (r : Fin (m * b) → E) : E :=
  robustCenter hm B (blockMean m b r)

noncomputable def rate (L τ α ε : ℝ) : ℝ :=
  32 * α / (7 * (2 - α)) * L * τ ^ (2 / α) * (ε / 4) ^ (-(2 - α) / α)

noncomputable def steps (L τ α ε : ℝ) : ℕ := ⌈rate L τ α ε⌉₊ + 1

noncomputable def subbatches (L τ α Δ ε : ℝ) : ℕ :=
  6 + ⌈Real.logb 2 (32 * (rate L τ α ε + 2) * Δ / ε)⌉₊

noncomputable def noise (L τ α σ ε : ℝ) : ℝ :=
  19 * α / (2 - α) * τ ^ (2 / α) * σ ^ 2 * ε ^ (-(2 / α)) + 2 * σ ^ 2 / (L * ε)

noncomputable def subsize (L τ α σ Δ ε : ℝ) : ℕ :=
  1 + ⌈(1152 + 16 * subbatches L τ α Δ ε) * noise L τ α σ ε⌉₊

noncomputable def radius (L τ α ε : ℝ) : ℝ :=
  2 * Real.sqrt (L * ε / (8 * steps L τ α ε))

lemma subbatches_pos (L τ α Δ ε : ℝ) : 0 < subbatches L τ α Δ ε := by
  unfold subbatches; omega

lemma subsize_pos (L τ α σ Δ ε : ℝ) : 0 < subsize L τ α σ Δ ε := by
  unfold subsize; omega

noncomputable def method (L τ α σ Δ ε : ℝ) (x0 : E) : Algorithm E E E :=
  batched (Q := E) (V := E) (W := E) (U := E)
    (Nat.mul_pos (subbatches_pos L τ α Δ ε) (subsize_pos L τ α σ Δ ε))
    (plainStep (1 / L) x0) (fun x _ => x)
    (fun _ r => aggregate (m := subbatches L τ α Δ ε) (b := subsize L τ α σ Δ ε)
      (subbatches_pos L τ α Δ ε) (radius L τ α ε) r) (0 : E)

end OracleTemplate.SublevelRobustGradient
