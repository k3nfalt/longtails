import LongTails.Setups.FiniteDimensionalWeakMinty
import LongTails.Algorithms.CovarianceSoftCut

noncomputable section

namespace LongTails.Algorithms.DimensionAdaptiveMinty

open OracleTemplate LongTails.Setups.FiniteDimensionalWeakMinty

abbrev E (p : Params) := EuclideanSpace ℝ (Fin p.d)

abbrev geometry (p : Params) : LongTails.Setups.CovarianceBoundedConvex.Params where
  d := p.d
  Ω := Unit
  L := 4 / Real.sqrt p.d
  R := p.R
  σ := 0
  ε := p.ε

def margin (p : Params) : ℝ := p.ε / (16 * p.L)

def localized (p : Params) : Prop := (p.d : ℝ) ≤ (p.L * p.R / p.ε)^2

instance (p : Params) : Decidable (localized p) := inferInstanceAs (Decidable (_ ≤ _))

structure Round (p : Params) where
  x : E p
  cuts : List (E p × E p)
  done : Bool

def center (p : Params) (cuts : List (E p × E p)) : E p :=
  CovarianceSoftCut.centroid (geometry p) (margin p) (2 / margin p) cuts

def start (p : Params) : Round p := ⟨if localized p then center p [] else 0, [], false⟩

def output (p : Params) (r : Round p) : E p := p.x0 + r.x

def look (p : Params) (r : Round p) (g : E p) : E p :=
  output p r - (1 / (2*p.L)) • g

def advance (p : Params) (r : Round p) (g h : E p) : Round p :=
  if r.done || decide (‖g‖ ≤ p.ε) then { r with done := true }
  else
    let u := ‖h‖⁻¹ • h
    if localized p then
      let cuts := r.cuts ++ [(u, r.x)]
      ⟨center p cuts, cuts, false⟩
    else ⟨r.x - margin p • u, [], false⟩

def algorithm (p : Params) : Algorithm (E p) (E p) (E p) where
  State := Round p × Option (E p)
  initial _ := (start p, none)
  query := fun (r,g) => (0, g.elim (output p r) (look p r))
  update := fun (r,g) v => match g with
    | none => (r, some v)
    | some w => (advance p r w v, none)
  output := fun (r,_) => output p r

end LongTails.Algorithms.DimensionAdaptiveMinty
