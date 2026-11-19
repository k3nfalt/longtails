import LongTails.Setups.TerminalClippingConvex

open MeasureTheory OracleTemplate

namespace LongTails.Setups.DistanceGrowingSubgradient

abbrev Public := TerminalClippingConvex.Public

def withSamples (p : Public) (Ω : Type) [MeasurableSpace Ω] : TerminalClippingConvex.Params :=
  { p with Ω := Ω }

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance := TerminalClippingConvex.Instance
  Query := TerminalClippingConvex.Query
  Reply p := TerminalClippingConvex.Vector p.d
  Output p := TerminalClippingConvex.Vector p.d
  publicInput := id
  valid p := 0 ≤ p.B ∧ 0 ≤ p.G ∧ 0 < p.δ ∧ p.δ < 1 ∧ 0 < p.R ∧ 0 < p.ε
  admissible p I O := ∃ (Ω : Type) (m : MeasurableSpace Ω),
    TerminalClippingConvex.spec.admissible (@withSamples p Ω m) I O
  successful p := TerminalClippingConvex.spec.successful (withSamples p Unit)

end LongTails.Setups.DistanceGrowingSubgradient
