import LongTails.Setups.RhoSmoothRadiusConvex

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.RhoSmoothThreePhase

open OracleTemplate LongTails.Setups.RhoSmoothRadiusConvex

inductive State (E : Type*) where
  | cut (x : E)
  | descend (x : E) (j : ℕ)
  | accel (y u : E) (Γ : ℝ) (started : Bool)

noncomputable def threshold (p : Params) : ℝ := (p.L0 / p.L1) ^ (1 / p.ρ)

noncomputable def curvature (p : Params) (s : ℝ) : ℝ := p.L0 + p.L1 * s ^ p.ρ

noncomputable def depth (p : Params) : ℝ :=
  threshold p / (4 * curvature p (2 * threshold p))

noncomputable def ratio (p : Params) : ℝ := p.L0 * p.R / threshold p

noncomputable def descentSteps (p : Params) : ℕ :=
  ⌈43 * ratio p + 174763 * ratio p ^ 2⌉₊ + 1

noncomputable def stepSize (p : Params) : ℝ := 1 / (8 * p.L0)

noncomputable def initialWeight (p : Params) : ℝ :=
  min (threshold p ^ 2 / (8192 * p.L0) / p.R ^ 2) (8 * p.L0)

noncomputable def momentum (p : Params) (Γ : ℝ) : ℝ := Real.sqrt (stepSize p * Γ)

noncomputable def gdPoint (p : Params) (x r : p.E) : p.E :=
  x - (1 / (4 * curvature p (2 * ‖r‖))) • r

noncomputable def nextDual (p : Params) (u r : p.E) (Γ : ℝ) (started : Bool) : p.E :=
  if started then u - (momentum p Γ / Γ) • r else u

noncomputable def nextWeight (p : Params) (Γ : ℝ) (started : Bool) : ℝ :=
  if started then Γ / (1 + momentum p Γ) else Γ

noncomputable def accelPoint (p : Params) (y u r : p.E) (Γ : ℝ) : p.E :=
  (1 / (1 + momentum p Γ)) • (y + momentum p Γ • u - stepSize p • r)

noncomputable def step (p : Params) (s : State p.E) (r : p.E) : State p.E := by
  classical
  exact match s with
  | .cut x =>
      if threshold p ≤ ‖r‖ then .cut (x - (depth p / ‖r‖) • r) else .descend x 0
  | .descend x j =>
      if j + 1 < descentSteps p then .descend (gdPoint p x r) (j + 1)
      else .accel (gdPoint p x r) (gdPoint p x r) (initialWeight p) false
  | .accel y u Γ b =>
      .accel (accelPoint p y (nextDual p u r Γ b) r (nextWeight p Γ b))
        (nextDual p u r Γ b) (nextWeight p Γ b) true

def point {E : Type*} (s : State E) : E :=
  match s with
  | .cut x => x
  | .descend x _ => x
  | .accel y _ _ _ => y

noncomputable def algorithm (p : Params) : Algorithm p.E p.E p.E where
  State := State p.E
  initial _ := .cut p.x0
  query := fun s => (0, point s)
  update := step p
  output := point

end LongTails.Algorithms.RhoSmoothThreePhase
