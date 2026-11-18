import LongTails.Setups.StronglyConvexDueling

open OracleTemplate

namespace LongTails.Setups.FlatTransferDueling

structure Params where
  d : ℕ
  [nonzero : NeZero d]
  j : ℕ
  ε : ℝ

attribute [instance] Params.nonzero

noncomputable def model (p : Params) : StronglyConvexDueling.Params where
  d := p.d
  μ := 1/2
  L := 2
  G := 4
  r := 1
  c := (2 * (p.j : ℝ) + 1) / 8
  M := (2 * (p.j : ℝ) + 1) / 4
  k := 2 * p.j
  ε := p.ε

noncomputable abbrev spec : Setup :=
  { StronglyConvexDueling.spec with
    Params := Params
    publicInput := model
    valid := fun p => 0 < p.ε ∧ p.ε ≤ 1/64
    admissible := fun p => StronglyConvexDueling.spec.admissible (model p)
    successful := fun p => StronglyConvexDueling.spec.successful (model p) }

end LongTails.Setups.FlatTransferDueling
