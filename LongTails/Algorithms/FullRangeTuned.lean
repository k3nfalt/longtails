import LongTails.Algorithms.FullRangeProgram
import LongTails.Algorithms.SmoothBanachAnchoring
import LongTails.Setups.FullRangeCohypomonotoneInclusion
import LongTails.Proofs.FullRangeEstimator

namespace LongTails.Algorithms.FullRangeTuned

open OracleTemplate
open LongTails.Algorithms.FullRangeMlmc LongTails.Algorithms.FullRangeProgram
open LongTails.Setups.StochasticCohypomonotoneInclusion (Params)

variable (q : Params)

noncomputable def tau : ℝ := 1 - q.ρ * q.L
noncomputable def eta : ℝ := (q.ρ + 1 / q.L) / 2
noncomputable def gamma0 : ℝ := tau q / 8
noncomputable def epsT : ℝ := tau q * eta q * q.ε / 128
noncomputable def radius : ℝ := 2 * q.R + 2 * epsT q

noncomputable def anchorLevels : ℕ := Nat.clog 2 (⌈16 * q.R / epsT q⌉₊ + 1)
noncomputable def stages : ℕ := anchorLevels q + 1

noncomputable def top : ℕ := Nat.clog 2 ⌈104857600 * (stages q : ℝ) ^ 2 * q.σ ^ 2 / q.ε ^ 2 + 1⌉₊

noncomputable def driftConst : ℝ := eta q ^ 2 * q.σ ^ 2 / 4

noncomputable def sigmaT : ℝ :=
  Real.sqrt (epsT q ^ 2 + tau q ^ 2 * ((24 * top q + 4) * driftConst q))

noncomputable def theta : ℝ :=
  min (epsT q ^ 2 / (12800 * (stages q : ℝ) ^ 2 * (9 * radius q ^ 2)))
    (min (epsT q ^ 2 / ((2 : ℝ) ^ (top q + 5) * (9 * radius q ^ 2)))
      (tau q ^ 2 * q.ε ^ 2 / (1152 * q.L ^ 2 * (9 * radius q ^ 2))))

noncomputable def n0 : ℕ := ⌈16 / tau q ^ 2 * (Real.log (1 / theta q) + 8)⌉₊ + 1

noncomputable def batch : ℕ := ⌈576 * q.σ ^ 2 / q.ε ^ 2⌉₊ + 1

noncomputable def failureProb : ℝ :=
  q.ε * tau q * eta q / (8 * (q.ε * tau q * eta q + 3 * radius q))

abbrev thetaType : Type := Fin (top q + 1) × (ℕ → q.Ω)

noncomputable def anchorParams : LongTails.Setups.StochasticSmoothBanachFixedPoint.Params where
  E := q.E
  linearE := InnerProductSpace.toNormedSpace
  completeE := FiniteDimensional.complete ℝ q.E
  countableE := inferInstance
  Ω := thetaType q
  measurableΩ := inferInstance
  x0 := q.x0
  C := 1
  R := q.R
  σ := sigmaT q
  ε := epsT q

noncomputable def calls : ℕ := stages q * LongTails.Algorithms.SmoothBanachAnchoring.innerSteps (anchorParams q)

noncomputable def seedLimit : ℕ :=
  2 * n0 q * (2 * calls q * (top q + 1) + 2 ^ top q * (⌈Real.log (1 / failureProb q)⌉₊ + 1))

noncomputable def totalCalls : ℕ := seedLimit q + 2 * levelTime (n0 q) (top q) + 2 * batch q + 1

abbrev St (q : Params) := ℕ × ℕ × q.E × q.E

noncomputable def toState (s : St q) :
    LongTails.Algorithms.SmoothBanachAnchoring.State (anchorParams q) :=
  ⟨s.1, s.2.1, s.2.2.1, s.2.2.2⟩

noncomputable def ofState (s : LongTails.Algorithms.SmoothBanachAnchoring.State (anchorParams q)) :
    St q :=
  (s.stage, s.step, s.anchor, s.point)

noncomputable def cfg : Cfg q.E (St q) where
  η := eta q
  γ0 := gamma0 q
  a := tau q
  r := radius q
  n0 := n0 q
  top := top q
  B := batch q
  limit := seedLimit q
  x0 := q.x0
  init := ofState q (LongTails.Algorithms.SmoothBanachAnchoring.initial (anchorParams q))
  point := fun s => s.2.2.2
  update := fun s r => ofState q (LongTails.Algorithms.SmoothBanachAnchoring.update (anchorParams q)
    (toState q s) r)

noncomputable def algorithm : Algorithm (q.E ⊕ (ℝ × q.E)) q.E (q.E × q.E) where
  Seed := Fin (calls q) → Fin (top q + 1)
  law := ⟨MeasureTheory.Measure.pi fun _ => LongTails.Proofs.FullRangeEstimator.levelLaw (top q), inferInstance⟩
  State := Prog (Q q.E) q.E (q.E × q.E)
  initial ℓ := fullProg (cfg q) ℓ
  query := stateQuery q.x0
  update := stateUpdate
  output := stateOutput q.x0

end LongTails.Algorithms.FullRangeTuned
