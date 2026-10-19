import LongTails.Setups.CompositeLipschitzHessian
import LongTails.Algorithms.QueryPlan
import LongTails.Algorithms.CompositeGuardedSearch
import LongTails.Algorithms.CompositeCubicAcceleration
import LongTails.Algorithms.EnergyHessianReuse
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Algorithms.CompositeLazyCubic

open LongTails.Setups.CompositeLipschitzHessian

noncomputable def cubicCoefficient (p : Params) : ℝ := p.H / (p.m : ℝ) ^ 3

noncomputable def localHessianLip (p : Params) : ℝ := p.H + 4 * cubicCoefficient p

noncomputable def condition (p : Params) : ℝ := (p.m : ℝ) ^ 3 + 4

def depth (p : Params) : ℕ := 2 + Nat.log2 (p.m ^ 3 + 4)

noncomputable def extrapolationFactor (p : Params) : ℝ := 1 + (depth p : ℝ)⁻¹

def innerIterations (p : Params) : ℕ := 32768 * p.m * (depth p + 1)

def searchIterations (p : Params) : ℕ := 128 * (depth p + 1)

def gapIterations (p : Params) : ℕ := 256 * (depth p + 1)

noncomputable def outerCoefficient (p : Params) : ℝ :=
  (cubicCoefficient p) ^ (4 / 7 : ℝ) * p.ε ^ (3 / 7 : ℝ) / p.R ^ (2 / 7 : ℝ)

abbrev Reply (p : Params) := p.E ⊕ (p.E →L[ℝ] p.E)
abbrev Plan (p : Params) (U : Type) (n : ℕ) :=
  OracleTemplate.QueryPlan (Fin 3 × (p.E ⊕ Model p)) (Reply p) U n

def readVector (p : Params) : Reply p → p.E
  | .inl v => v
  | .inr _ => 0

def readHessian (p : Params) : Reply p → (p.E →L[ℝ] p.E)
  | .inl _ => 0
  | .inr B => B

noncomputable def localGradient (p : Params) (center x gradient : p.E) : p.E :=
  gradient + (cubicCoefficient p * ‖x - center‖) • (x - center)

noncomputable def localHessian (p : Params) (center x : p.E) (B : p.E →L[ℝ] p.E) : p.E →L[ℝ] p.E :=
  B + cubicCoefficient p • (‖x - center‖ • ContinuousLinearMap.id ℝ p.E +
    ‖x - center‖⁻¹ • (innerSL ℝ (x - center)).smulRight (x - center))

noncomputable def extrapolatedGradient (p : Params) (center snapshot point : p.E) :
    (n i : ℕ) → Plan p p.E n
  | 0, _ => .done 0
  | n + 1, i =>
    let c := extrapolationFactor p ^ i
    let x := snapshot + c • (point - snapshot)
    .ask (0, .inl x) fun reply =>
      let g := localGradient p center x (readVector p reply)
      (extrapolatedGradient p center snapshot point n (i + 1)).map
        (fun rest => (((1 / 64 : ℝ) ^ i) * c) • g + rest)

structure CubicPoint (p : Params) where
  point : p.E
  residual : p.E

noncomputable def cubicStep (p : Params) (center x : p.E) : Plan p (CubicPoint p) 4 :=
  .ask (0, .inl x) fun reply =>
    let g := localGradient p center x (readVector p reply)
    .ask (1, .inl x) fun reply =>
      let B := localHessian p center x (readHessian p reply)
      let q : Model p := ⟨x, g, B, localHessianLip p, 1⟩
      .ask (2, .inr q) fun reply =>
        let z := readVector p reply
        .ask (0, .inl z) fun reply =>
          let gz := localGradient p center z (readVector p reply)
          .done ⟨z, gz - g - B (z - x) - (localHessianLip p * ‖z - x‖) • (z - x)⟩

noncomputable def regularizerScale (p : Params) : ℝ :=
  ∑ i ∈ Finset.range (depth p + 1), (1 / 64 : ℝ) ^ i * extrapolationFactor p ^ i

def trialCalls (p : Params) : ℕ := (depth p + 1 + 1) + (depth p + 1)

structure SearchTrial (p : Params) where
  query : p.E
  point : p.E
  residual : p.E
  certified : Bool

noncomputable def searchTrial (p : Params) (center snapshot y : p.E)
    (B : p.E →L[ℝ] p.E) : Plan p (SearchTrial p) (trialCalls p) := by
  classical
  let plan := (extrapolatedGradient p center snapshot y (depth p + 1) 0).bind fun gy =>
    OracleTemplate.QueryPlan.ask (2, Sum.inr (⟨y, gy, B, 0, regularizerScale p⟩ : Model p)) fun reply =>
      let z := readVector p reply
      (extrapolatedGradient p center snapshot z (depth p + 1) 0).map fun gz =>
        let d := z - y
        (⟨y, z, B (y - z), decide (inner ℝ (gz - gy) d ≤ inner ℝ d (B d) / 2)⟩ : SearchTrial p)
  exact plan

structure SearchState (p : Params) where
  bracket : CompositeGuardedSearch.Bracket
  lowerTrial : SearchTrial p

noncomputable def searchRounds (p : Params) (center snapshot x v : p.E)
    (B : p.E →L[ℝ] p.E) : (n : ℕ) → SearchState p →
      Plan p (SearchState p) ((trialCalls p) * n)
  | 0, state => .done state
  | n + 1, state => by
    classical
    let t := state.bracket.midpoint
    let plan := (searchTrial p center snapshot (x + t • (v - x)) B).bind fun trial =>
      let q := inner ℝ trial.residual (v - x)
      let next : SearchState p :=
        ⟨CompositeGuardedSearch.advance state.bracket trial.certified q,
          if trial.certified = true ∧ q ≤ 0 then trial else state.lowerTrial⟩
      searchRounds p center snapshot x v B n next
    exact plan

noncomputable def guardedSearch (p : Params) (center snapshot x v : p.E)
    (B : p.E →L[ℝ] p.E) :
    Plan p (SearchTrial p) ((trialCalls p) * (searchIterations p + 2)) := by
  classical
  let plan := (searchTrial p center snapshot x B).bind fun first =>
    (searchTrial p center snapshot v B).bind fun last =>
      (searchRounds p center snapshot x v B (searchIterations p)
        ⟨⟨0, 1⟩, first⟩).map fun state =>
        if 0 ≤ inner ℝ first.residual (v - x) then first
        else if last.certified = true ∧ inner ℝ last.residual (v - x) ≤ 0 then last
        else state.lowerTrial
  exact plan

noncomputable def acceleratedRounds (p : Params) (center snapshot : p.E)
    (B : p.E →L[ℝ] p.E) : (n k : ℕ) → CompositeGuardedSearch.AccelerationState p.E →
      Plan p (CompositeGuardedSearch.AccelerationState p.E)
        (((trialCalls p) * (searchIterations p + 2)) * n)
  | 0, _, state => .done state
  | n + 1, k, state =>
    (guardedSearch p center snapshot state.point state.momentum B).bind fun trial =>
      acceleratedRounds p center snapshot B n (k + 1)
        (CompositeGuardedSearch.acceleratedAdvance B k state trial.point trial.residual)

noncomputable def snapshotMetric (p : Params) (center snapshot : p.E) (Δ : ℝ)
    (B : p.E →L[ℝ] p.E) : p.E →L[ℝ] p.E :=
  (32 * ((depth p : ℝ) + 1)) • localHessian p center snapshot B +
    (4096 * ((depth p : ℝ) + 1) ^ 2 * localHessianLip p *
      (Δ / localHessianLip p) ^ (1 / 3 : ℝ)) • ContinuousLinearMap.id ℝ p.E

def gapEpochCalls (p : Params) : ℕ :=
  (trialCalls p) * (searchIterations p + 2) * innerIterations p + 1

noncomputable def gapEpoch (p : Params) (center snapshot : p.E) (Δ : ℝ) :
    Plan p p.E (gapEpochCalls p) :=
  .ask (1, .inl snapshot) fun reply =>
    let B := snapshotMetric p center snapshot Δ (readHessian p reply)
    (acceleratedRounds p center snapshot B (innerIterations p) 0 ⟨snapshot, snapshot⟩).map
      (fun state => state.point)

noncomputable def gapRounds (p : Params) (center : p.E) : (n : ℕ) → p.E → ℝ →
    Plan p p.E (gapEpochCalls p * n)
  | 0, point, _ => .done point
  | n + 1, point, Δ => (gapEpoch p center point Δ).bind fun next =>
      gapRounds p center n next (3 * Δ / 4)

noncomputable def padGradients (p : Params) {U : Type} (value : U) : (n : ℕ) → Plan p U n
  | 0 => .done value
  | n + 1 => .ask (0, .inl p.x0) fun _ => padGradients p value n

def cubicSolveCalls (p : Params) : ℕ := (4 + gapEpochCalls p * gapIterations p) + 4 + 4

noncomputable def cubicSolve (p : Params) (center : p.E) :
    Plan p (CubicPoint p) (cubicSolveCalls p) := by
  classical
  let plan := (cubicStep p center center).bind fun first =>
    (cubicStep p center first.point).bind fun second =>
      if second.residual = 0 then
        padGradients p second (4 + gapEpochCalls p * gapIterations p)
      else
        let Δ := 2 * ‖second.residual‖ * Real.sqrt (‖second.residual‖ / cubicCoefficient p)
        (gapRounds p center (gapIterations p) second.point Δ).bind fun point =>
          cubicStep p center point
  exact plan

noncomputable def scaledGap (p : Params) : ℝ := p.H * p.R ^ 3 / ((p.m : ℝ) ^ 3 * p.ε)

noncomputable def outerIterations (p : Params) : ℕ :=
  16 * (3 + Nat.log2 (2 + ⌈scaledGap p ^ (4 / 7 : ℝ)⌉₊)) * (1 + ⌈scaledGap p ^ (2 / 7 : ℝ)⌉₊)

noncomputable def outerRounds (p : Params) : (n : ℕ) → CompositeCubicAcceleration.State p.E →
    Plan p p.E (cubicSolveCalls p * n)
  | 0, state => .done state.point
  | n + 1, state => by
    classical
    let center := CompositeCubicAcceleration.center p.E (outerCoefficient p) state
    exact (cubicSolve p center).bind fun result =>
      if result.point = center then padGradients p result.point (cubicSolveCalls p * n)
      else
        let d := result.point - center
        let g := result.residual - (cubicCoefficient p * ‖d‖) • d
        outerRounds p n (CompositeCubicAcceleration.advance p.E
          (outerCoefficient p) (cubicCoefficient p) state result.point g)

noncomputable def plan (p : Params) : Plan p p.E (cubicSolveCalls p * outerIterations p) :=
  outerRounds p (outerIterations p) ⟨0, p.x0, p.x0⟩

noncomputable def algorithm (p : Params) : OracleTemplate.Algorithm (p.E ⊕ Model p) (Reply p) p.E 3 :=
  EnergyHessianReuse.channelAlgorithm (0, .inl p.x0) p.x0 (plan p)

end LongTails.Algorithms.CompositeLazyCubic
