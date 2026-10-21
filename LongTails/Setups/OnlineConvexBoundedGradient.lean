import LongTails.TemplateOnline
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Compactness.Compact

namespace LongTails.Setups.OnlineConvexBoundedGradient

open OracleTemplate

structure Params where
  d : ℕ
  K : Set (EuclideanSpace ℝ (Fin d))
  x0 : K
  D : ℝ
  G : ℝ

structure Public extends Params where
  T : Horizon

abbrev spec : OnlineSetup where
  Params := Params
  Public := Public
  Instance p := ℕ → EuclideanSpace ℝ (Fin p.d) → ℝ
  Query p := p.K
  Reply p := EuclideanSpace ℝ (Fin p.d)
  Output _ := Unit
  publicInput p T := { toParams := p, T := T }
  valid p T := Convex ℝ p.K ∧ IsCompact p.K ∧ 0 < T ∧ 0 < p.D ∧ 0 < p.G ∧
    ∀ x ∈ p.K, ∀ y ∈ p.K, ‖x - y‖ ≤ p.D
  admissible p _ losses oracle :=
    (∀ t, ConvexOn ℝ p.K (losses t) ∧
      ∀ x ∈ p.K, HasGradientAt (losses t) (gradient (losses t) x) x ∧
        ‖gradient (losses t) x‖ ≤ p.G) ∧
    ∀ t query seed,
      oracle.answer t query seed = gradient (losses t) query.2
  successful p T losses result _ bound :=
    ∀ ω, let trace := (result ω).2
      ∀ u : p.K,
        (trace.zipIdx.map fun xt => losses xt.2 xt.1.1.2).sum -
          ∑ t ∈ Finset.range T, losses t u.val ≤ bound

end LongTails.Setups.OnlineConvexBoundedGradient
