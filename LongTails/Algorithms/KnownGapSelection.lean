import LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension
import LongTails.Algorithms.DampedGeneralizedAccelerated
import LongTails.Algorithms.RadiusFreeSherpa

namespace OracleTemplate.KnownGapSelection

open LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension

variable {E : Type*}

noncomputable def combine (c : Prop) [Decidable c] (A B : Algorithm E E E) : Algorithm E E E where
  State := A.State ⊕ B.State
  initial _ := if c then Sum.inl (A.initial (Classical.choice A.law.nonempty))
    else Sum.inr (B.initial (Classical.choice B.law.nonempty))
  query
    | Sum.inl s => A.query s
    | Sum.inr s => B.query s
  update
    | Sum.inl s, r => Sum.inl (A.update s r)
    | Sum.inr s, r => Sum.inr (B.update s r)
  output
    | Sum.inl s => A.output s
    | Sum.inr s => B.output s

noncomputable abbrev toRadiusOnly (p : Params) : LongTails.Setups.RadiusOnlyGeneralizedSmoothConvex.Params :=
  { E := EuclideanSpace ℝ (Fin p.d), L0 := p.L0, L1 := p.L1, x0 := p.x0, R := p.R, ε := p.ε }

noncomputable def gapTrials (p : Params) : ℕ :=
  ⌈4096 * (1 + Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + (⌈(p.L1 * p.R) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * p.Δ / p.ε))⌉₊

noncomputable def radiusSteps (p : Params) : ℕ :=
  ⌈64 * Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + 32768 * (1 + p.L1 * p.R) * Real.log (2 + p.L1 * p.R)⌉₊

noncomputable def algorithm (p : Params) :
    Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) :=
  combine (2 * gapTrials p ≤ radiusSteps p)
    (GeneralizedAccelerated.algorithm p.toGeneralized.toPublic)
    (RadiusFreeSherpa.algorithm (toRadiusOnly p).toPublic)

end OracleTemplate.KnownGapSelection
