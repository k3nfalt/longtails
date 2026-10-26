import LongTails.Template
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Nat.Log

namespace OracleTemplate.RecursiveAnchorKm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def anchorKmUpdate (S : ℕ) (lam Λ α : ℕ → ℝ) (N : ℕ → ℕ) (s : ℕ × ℕ × E × E)
    (r : E) : ℕ × ℕ × E × E :=
  if S < s.1 then s
  else if s.2.1 + 1 < N s.1 then
    (s.1, s.2.1 + 1, (1 - α s.1) • s.2.2.1 + (α s.1 / (1 + Λ s.1)) • (r + s.2.2.2), s.2.2.2)
  else
    (s.1 + 1, 0, (1 - α s.1) • s.2.2.1 + (α s.1 / (1 + Λ s.1)) • (r + s.2.2.2),
      s.2.2.2 + lam (s.1 + 1) • ((1 - α s.1) • s.2.2.1 + (α s.1 / (1 + Λ s.1)) • (r + s.2.2.2)))

noncomputable def recursiveAnchorKm (S : ℕ) (lam Λ α : ℕ → ℝ) (N : ℕ → ℕ) (x0 : E) :
    Algorithm E E E where
  State := ℕ × ℕ × E × E
  initial _ := (0, 0, x0, lam 0 • x0)
  query s := (0, s.2.2.1)
  update s r := anchorKmUpdate S lam Λ α N s r
  output s := s.2.2.1

noncomputable def lastStage (D ε : ℝ) : ℕ := Nat.clog 2 ⌈4 * D / ε⌉₊

noncomputable def anchorWeight (D ε : ℝ) (t : ℕ) : ℝ := 2 ^ t * (ε / (4 * D))

noncomputable def totalWeight (D ε : ℝ) (u : ℕ) : ℝ := (2 ^ (u + 1) - 1) * (ε / (4 * D))

noncomputable def stageTarget (D ε : ℝ) (u : ℕ) : ℝ :=
  if u < lastStage D ε then ε / (6 * (lastStage D ε + 1) * anchorWeight D ε (u + 1))
  else ε / (4 * (lastStage D ε + 1))

noncomputable def stageStep (K σ D ε : ℝ) (u : ℕ) : ℝ :=
  stageTarget D ε u ^ 2 * totalWeight D ε u * (1 + totalWeight D ε u) /
    (stageTarget D ε u ^ 2 * totalWeight D ε u * (1 + totalWeight D ε u) + 2 * K * σ ^ 2)

noncomputable def stageLength (K σ D ε : ℝ) (u : ℕ) : ℕ :=
  (if u = 0 then 2 * lastStage D ε + 7 else 5) *
    ⌈(1 + totalWeight D ε u) / totalWeight D ε u +
      2 * K * σ ^ 2 / (stageTarget D ε u * totalWeight D ε u) ^ 2⌉₊

noncomputable def tunedAnchorKm (K σ D ε : ℝ) (x0 : E) : Algorithm E E E :=
  recursiveAnchorKm (lastStage D ε) (anchorWeight D ε) (totalWeight D ε) (stageStep K σ D ε)
    (stageLength K σ D ε) x0

end OracleTemplate.RecursiveAnchorKm
