import LongTails.Setups.UscgHighProbability

namespace LongTails.Algorithms.UscgSharpConfidence

def mass (α : ℝ) (t : ℕ) : ℝ := 1 - (1 - α) ^ t

noncomputable def correctedWeight (α : ℝ) (t : ℕ) : ℝ := α / mass α t

noncomputable def algorithm (p : LongTails.Setups.UscgHighProbability.Public)
    (α η : ℝ) :=
  LongTails.Setups.UscgHighProbability.method p (correctedWeight α) (fun _ => η)

noncomputable def inverseMemory (p : LongTails.Setups.UscgHighProbability.Public) : ℝ :=
  2 + 65536 * p.ζ ^ 2 * p.σ ^ 2 / p.ε ^ 2

noncomputable def horizon (p : LongTails.Setups.UscgHighProbability.Public) : ℕ :=
  if 2 * p.L * p.Δ ≤ p.ε ^ 2 then 1 else
    ⌈4096 * (2 + 65536 * p.ζ ^ 2 * p.σ ^ 2 / p.ε ^ 2) *
      (1 + p.L * p.Δ / p.ε ^ 2 + Real.sqrt (p.L * p.Δ / p.ε ^ 2) *
        (1 + Real.log (1 / p.δ)))⌉₊

noncomputable def chosenMemory (p : LongTails.Setups.UscgHighProbability.Public) : ℝ :=
  if 2 * p.L * p.Δ ≤ p.ε ^ 2 then 1 / 2 else 1 / inverseMemory p

noncomputable def chosenStep (p : LongTails.Setups.UscgHighProbability.Public) : ℝ :=
  if 2 * p.L * p.Δ ≤ p.ε ^ 2 then 1 else 4 * p.Δ / (p.ε * horizon p)

noncomputable def configured (p : LongTails.Setups.UscgHighProbability.Public) :=
  algorithm p (chosenMemory p) (chosenStep p)

end LongTails.Algorithms.UscgSharpConfidence
