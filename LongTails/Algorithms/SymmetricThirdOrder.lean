import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import LongTails.Algorithms.RobustGradientEstimator
import LongTails.Algorithms.HessianAdaptiveCubic
import LongTails.Algorithms.CompositeCubicAcceleration
import LongTails.Algorithms.SampledQueryPlan

namespace LongTails.Algorithms.SymmetricThirdOrder

open scoped RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def kernel (B : E →L[ℝ] E) (L δ : ℝ) (s : E) : ℝ :=
  (1 / 2 : ℝ) * ⟪s, B s⟫ + 2 * L * ‖s‖ ^ 4 + δ / 2 * ‖s‖ ^ 2

noncomputable def model (f : E → ℝ) (c : E) (B : E →L[ℝ] E) (L δ : ℝ) (s : E) : ℝ :=
  (1 / 2 : ℝ) * (f (c + s) - f (c - s)) + kernel B L δ s

noncomputable def kernelGradient (B : E →L[ℝ] E) (L δ : ℝ) (s : E) : E :=
  B s + (8 * L * ‖s‖ ^ 2 + δ) • s

noncomputable def modelGradient (g : E → E) (c : E) (B : E →L[ℝ] E) (L δ : ℝ) (s : E) : E :=
  (1 / 2 : ℝ) • (g (c + s) + g (c - s)) + kernelGradient B L δ s

noncomputable def kernelHessian (B : E →L[ℝ] E) (L δ : ℝ) (s : E) : E →L[ℝ] E :=
  B + (8 * L * ‖s‖ ^ 2 + δ) • ContinuousLinearMap.id ℝ E +
    (16 * L) • (innerSL ℝ s).smulRight s

noncomputable def modelHessian (H : E → E →L[ℝ] E) (c : E)
    (B : E →L[ℝ] E) (L δ : ℝ) (s : E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) • (H (c + s) - H (c - s)) + kernelHessian B L δ s

noncomputable def symmetricHessian [CompleteSpace E] (A : E →L[ℝ] E) : E →L[ℝ] E :=
  (1 / 2 : ℝ) • (A + ContinuousLinearMap.adjoint A)

noncomputable def lowerRayleigh (A : E →L[ℝ] E) : ℝ :=
  sInf ((fun v : E => ⟪A v, v⟫) '' Metric.closedBall 0 1)

noncomputable def shiftedHessian (A : E →L[ℝ] E) (ε : ℝ) : E →L[ℝ] E :=
  A + max ε (-lowerRayleigh A) • ContinuousLinearMap.id ℝ E

noncomputable def hessianPilot [CompleteSpace E] {k : ℕ}
    (σ : ℝ) (A : Fin k → E →L[ℝ] E) : E →L[ℝ] E :=
  symmetricHessian (OracleTemplate.RobustGradient.pilotCenter (18 * σ) A)

noncomputable def gradientPilot {k m : ℕ} (a : ℝ) (v : Fin k → Fin m → E) : E :=
  OracleTemplate.RobustGradient.pilotCenter (2 * a)
    (fun i => (1 / (m : ℝ)) • ∑ j, v i j)

noncomputable def proxObjective (c y : E) (B : E →L[ℝ] E) (L δ : ℝ) (g v : E) : ℝ :=
  ⟪g, v - y⟫ + 2 * (kernel B L δ (v - c) - ⟪kernelGradient B L δ (y - c), v - y⟫)

noncomputable def proxPoint (C : Set E) (fallback c y : E)
    (B : E →L[ℝ] E) (L δ : ℝ) (g : E) : E :=
  HessianAdaptiveCubic.minimize C fallback (proxObjective c y B L δ g)

noncomputable def cleanupObjective (y : E) (B : E →L[ℝ] E) (δ : ℝ) (g v : E) : ℝ :=
  ⟪g, v - y⟫ + kernel B 0 δ (v - y)

noncomputable def cleanupPoint (C : Set E) (fallback y : E)
    (B : E →L[ℝ] E) (δ : ℝ) (g : E) : E :=
  HessianAdaptiveCubic.minimize C fallback (cleanupObjective y B δ g)

noncomputable def innerIterate (C : Set E) (fallback c : E) (B : E →L[ℝ] E)
    (L δ : ℝ) (G : ℕ → E → E) : ℕ → E
  | 0 => fallback
  | k + 1 => proxPoint C fallback c (innerIterate C fallback c B L δ G k) B L δ
      (G k (innerIterate C fallback c B L δ G k))

noncomputable def projectPoint (C : Set E) (fallback v : E) : E :=
  cleanupPoint C fallback v 0 1 0

structure OuterState (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    extends CompositeCubicAcceleration.State E where
  grid : ℕ

def outerInitial (x0 : E) (M : ℕ) : OuterState E :=
  { weight := 0, point := x0, momentum := x0, grid := M }

noncomputable def outerCenter (δ : ℝ) (s : OuterState E) : E :=
  CompositeCubicAcceleration.center E (δ * 4 ^ s.grid) s.toState

noncomputable def outerAdvance (C : Set E) (fallback : E) (L δ X : ℝ) (M : ℕ)
    (s : OuterState E) (z g : E) : OuterState E :=
  if X ≤ s.weight then s else
  let μ := δ * 4 ^ s.grid
  let a := CompositeCubicAcceleration.trialWeight μ s.weight
  let lam := δ + 8 * L * ‖z - outerCenter δ s‖ ^ 2
  let β := min 1 (μ / lam)
  let A := s.weight + β * a
  { weight := A
    point := A⁻¹ • (((1 - β) * s.weight) • s.point + (β * (s.weight + a)) • z)
    momentum := projectPoint C fallback (s.momentum - (β * a) • g)
    grid := if lam ≤ μ then s.grid - 1 else min M (s.grid + 1) }

abbrev Reply (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  E × (E →L[ℝ] E)

structure Config (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  C : Set E
  x0 : E
  L : ℝ
  δ : ℝ
  σh : ℝ
  tolerance : ℝ
  threshold : ℝ
  groups : ℕ
  batch : ℕ
  innerRounds : ℕ
  gridTop : ℕ

open OracleTemplate

def samplePlan (x : E) : (k : ℕ) → QueryPlan E (Reply E) (Fin k → Reply E) k
  | 0 => .done Fin.elim0
  | k + 1 => .ask x fun first => QueryPlan.map (Fin.cons first) (samplePlan x k)

def groupedPlan (x : E) (m : ℕ) : (k : ℕ) →
    QueryPlan E (Reply E) (Fin k → Fin m → Reply E) (m * k)
  | 0 => .done Fin.elim0
  | k + 1 => QueryPlan.bind (samplePlan x m) fun first =>
      QueryPlan.map (Fin.cons first) (groupedPlan x m k)

noncomputable def gradientPlan (cfg : Config E) (x : E) :
    QueryPlan E (Reply E) E (cfg.batch * cfg.groups) :=
  QueryPlan.map (fun v => gradientPilot cfg.tolerance (fun i j => (v i j).1))
    (groupedPlan x cfg.batch cfg.groups)

noncomputable def hessianPlan [CompleteSpace E] (cfg : Config E) (x : E) :
    QueryPlan E (Reply E) (E →L[ℝ] E) cfg.groups :=
  QueryPlan.map (fun v => hessianPilot cfg.σh (fun i => (v i).2)) (samplePlan x cfg.groups)

noncomputable def meanPlan (m : ℕ) (x : E) : QueryPlan E (Reply E) E m :=
  QueryPlan.map (fun v => (1 / (m : ℝ)) • ∑ i, (v i).1) (samplePlan x m)

noncomputable def modelGradientPlan (cfg : Config E) (c y : E) (B : E →L[ℝ] E) :
    QueryPlan E (Reply E) E (cfg.batch * cfg.groups + cfg.batch * cfg.groups) :=
  QueryPlan.bind (gradientPlan cfg y) fun gp =>
    QueryPlan.map (fun gm => (1 / 2 : ℝ) • (gp + gm) + kernelGradient B cfg.L cfg.δ (y - c))
      (gradientPlan cfg (c - (y - c)))

noncomputable def innerPlan (cfg : Config E) (c : E) (B : E →L[ℝ] E) :
    (J : ℕ) → E → QueryPlan E (Reply E) E ((cfg.batch * cfg.groups + cfg.batch * cfg.groups) * J)
  | 0, y => .done y
  | J + 1, y => QueryPlan.bind (modelGradientPlan cfg c y B) fun qg =>
      innerPlan cfg c B J (proxPoint cfg.C cfg.x0 c y B cfg.L cfg.δ qg)

noncomputable def cleanupPlan [CompleteSpace E] (cfg : Config E) (c y : E) (B : E →L[ℝ] E) :
    QueryPlan E (Reply E) (E × E)
      ((cfg.groups + cfg.groups) + (cfg.batch * cfg.groups + cfg.batch * cfg.groups)) :=
  QueryPlan.bind (modelGradientPlan cfg c y B) fun qg =>
    QueryPlan.bind (hessianPlan cfg y) fun Hp =>
      QueryPlan.map (fun Hm =>
        let Hq := shiftedHessian ((1 / 2 : ℝ) • (Hp - Hm) + kernelHessian B cfg.L cfg.δ (y - c)) 0
        let z := cleanupPoint cfg.C cfg.x0 y Hq cfg.δ qg
        (z, -qg - Hq (z - y) - cfg.δ • (z - y)))
        (hessianPlan cfg (c - (y - c)))

noncomputable def roundPlan [CompleteSpace E] (cfg : Config E) (s : OuterState E) :
    QueryPlan E (Reply E) (OuterState E)
      (cfg.groups * (3 + 2 * cfg.batch * (cfg.innerRounds + 1)) + cfg.batch) := by
  let c := outerCenter cfg.δ s
  let plan := QueryPlan.bind (hessianPlan cfg c) fun H =>
    let B := shiftedHessian H (9 * cfg.σh)
    QueryPlan.bind (innerPlan cfg c B cfg.innerRounds cfg.x0) fun y =>
      QueryPlan.bind (cleanupPlan cfg c y B) fun zn =>
        QueryPlan.map (fun gm => outerAdvance cfg.C cfg.x0 cfg.L cfg.δ cfg.threshold cfg.gridTop
          s zn.1 (gm + zn.2)) (meanPlan cfg.batch zn.1)
  have h : cfg.batch + ((cfg.groups + cfg.groups) + (cfg.batch * cfg.groups + cfg.batch * cfg.groups)) +
      (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds + cfg.groups =
      cfg.groups * (3 + 2 * cfg.batch * (cfg.innerRounds + 1)) + cfg.batch := by ring
  exact h ▸ plan

noncomputable def roundsPlan [CompleteSpace E] (cfg : Config E) :
    (T : ℕ) → OuterState E → QueryPlan E (Reply E) (OuterState E)
      ((cfg.groups * (3 + 2 * cfg.batch * (cfg.innerRounds + 1)) + cfg.batch) * T)
  | 0, s => .done s
  | T + 1, s => QueryPlan.bind (roundPlan cfg s) (roundsPlan cfg T)

def roundCalls (cfg : Config E) : ℕ :=
  cfg.groups * (3 + 2 * cfg.batch * (cfg.innerRounds + 1)) + cfg.batch

noncomputable def sampledState [CompleteSpace E] {Ω : Type*}
    (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω) : ℕ → OuterState E
  | 0 => outerInitial cfg.x0 cfg.gridTop
  | t + 1 => QueryPlan.sampledEval oracle ξ (roundPlan cfg (sampledState cfg oracle ξ t)) (roundCalls cfg * t)

noncomputable def sampledCenter [CompleteSpace E] {Ω : Type*}
    (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω) (t : ℕ) : E :=
  outerCenter cfg.δ (sampledState cfg oracle ξ t)

noncomputable def sampledMatrix [CompleteSpace E] {Ω : Type*}
    (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω) (t : ℕ) : E →L[ℝ] E :=
  shiftedHessian (QueryPlan.sampledEval oracle ξ (hessianPlan cfg (sampledCenter cfg oracle ξ t))
    (roundCalls cfg * t)) (9 * cfg.σh)

noncomputable def sampledInner [CompleteSpace E] {Ω : Type*}
    (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω) (t j : ℕ) : E :=
  QueryPlan.sampledEval oracle ξ
    (innerPlan cfg (sampledCenter cfg oracle ξ t) (sampledMatrix cfg oracle ξ t) j cfg.x0)
    (roundCalls cfg * t + cfg.groups)

noncomputable def sampledCleanup [CompleteSpace E] {Ω : Type*}
    (cfg : Config E) (oracle : E → Ω → Reply E) (ξ : ℕ → Ω) (t : ℕ) : E × E :=
  QueryPlan.sampledEval oracle ξ
    (cleanupPlan cfg (sampledCenter cfg oracle ξ t) (sampledInner cfg oracle ξ t cfg.innerRounds)
      (sampledMatrix cfg oracle ξ t))
    (roundCalls cfg * t + cfg.groups + (cfg.batch * cfg.groups + cfg.batch * cfg.groups) * cfg.innerRounds)

noncomputable def algorithm [CompleteSpace E] (cfg : Config E) (T : ℕ) : Algorithm E (Reply E) E where
  State := Σ k, QueryPlan E (Reply E) E k
  initial _ := ⟨_, QueryPlan.map (fun s => s.point) (roundsPlan cfg T (outerInitial cfg.x0 cfg.gridTop))⟩
  query s := (0, QueryPlan.query cfg.x0 s)
  update := QueryPlan.update
  output := QueryPlan.output cfg.x0

noncomputable def output [CompleteSpace E] (cfg : Config E) (T K : ℕ) (O : Oracle E (Reply E))
    (ξ : (k : ℕ) → O.Seed k) : E := execute O (algorithm cfg T) (fun _ => K) () ξ

noncomputable def iterationCount (L R Δ ε σh : ℝ) : ℕ :=
  ⌈(2 : ℝ) ^ 24 * (1 + Real.sqrt (σh * R ^ 2 / ε) + (L * R ^ 4 / ε) ^ (1 / 5 : ℝ)) *
    (1 + Real.log (2 + Δ / ε + σh * R ^ 2 / ε + L * R ^ 4 / ε)) ^ 2⌉₊

noncomputable def tunedConfig (x0 : E) (L R Δ ε σg σh : ℝ) : Config E :=
  let H := σh * R ^ 2 / ε
  let K := L * R ^ 4 / ε
  let F := Δ / ε
  let G := σg ^ 2 * R ^ 2 / ε ^ 2
  let T := iterationCount L R Δ ε σh
  let d := (T : ℝ) ^ 2 / (2 : ℝ) ^ 24 + 288 * H
  let J := ⌈Real.log (1 + (2 : ℝ) ^ 27 * T * (F + 3 * K + d)) / Real.log (7 / 6)⌉₊ + 1
  { C := Metric.closedBall x0 R
    x0 := x0
    L := L
    δ := (ε / R ^ 2) * d
    σh := σh
    tolerance := (ε / R) * Real.sqrt (d / ((2 : ℝ) ^ 24 * T))
    threshold := 6 * R ^ 2 / ε
    groups := ⌈Real.log (6 * T * (2 * (J : ℝ) + 5)) / Real.log (3 / 2)⌉₊
    batch := ⌈144 * (2 : ℝ) ^ 24 * G * T / d⌉₊ + 1
    innerRounds := J
    gridTop := ⌈Real.log (1 + 32 * K / d) / Real.log 4⌉₊ }

noncomputable def tunedAlgorithm [CompleteSpace E] (x0 : E) (L R Δ ε σg σh : ℝ) :
    OracleTemplate.Algorithm E (Reply E) E :=
  algorithm (tunedConfig x0 L R Δ ε σg σh) (iterationCount L R Δ ε σh)

end LongTails.Algorithms.SymmetricThirdOrder
