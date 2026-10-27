import LongTails.Algorithms.CoarseGeneralizedWarmstart
import LongTails.Algorithms.RobustGeneralizedAccelerated

namespace OracleTemplate.CoarseGeneralized

open LongTails.Setups.FiniteVarianceGeneralizedSmoothAndConvex

noncomputable section

def coarseTolerance (p : Params) : ℝ := p.σ + p.L0 * p.R

def warmCurvature (p : Params) : ℝ := p.L0 + 2 ^ 20 * p.L1 ^ 2 * p.R * coarseTolerance p

def warmTuning (p : Params) : Tuning :=
  { L := warmCurvature p
    L1 := p.L1
    ζ := coarseTolerance p
    rounds := 4096 * ⌈p.L1 * p.R⌉₊
    depth := ⌈Real.log (2 ^ 20 * (1 + p.L1 * p.R) ^ 2) / Real.log 2⌉₊ + 1 }

open Classical in
def warmCalls (p : Params) : ℕ :=
  if p.L1 * p.R < 1 then 0 else (warmTuning p).rounds * ((warmTuning p).depth + 2)

def warmGroups (p : Params) : ℕ :=
  ⌈Real.log (4 * (1 + warmCalls p) / p.δ) / Real.log 2⌉₊ + 1

def warmBatch (p : Params) : ℕ := warmGroups p * 576

def warmCost (p : Params) : ℕ := warmCalls p * warmBatch p

def warmEstimate (p : Params) (v : ℕ → p.E) : p.E :=
  RobustGradient.pilotCenter (2 * coarseTolerance p)
    (fun i : Fin (warmGroups p) => RobustGeneralized.meanBlock (i * 576) 576 v)

noncomputable def coarseNext (p : Params) (oracle : p.E → p.Ω → p.E) (n : ℕ)
    (s : Search p.E) (ξ : Fin n → p.Ω) : Search p.E :=
  searchUpdate (warmTuning p) s
    (warmEstimate p (RobustGeneralized.sampleReplies oracle (searchPoint s) ξ))

open Classical in
def warmPoint (p : Params) (oracle : p.E → p.Ω → p.E) (ξ : ℕ → p.Ω) : p.E :=
  if p.L1 * p.R < 1 then p.x0 else
    warmOutput (StochasticGeneralized.blockTrace (fun _ => warmBatch p) (coarseNext p oracle)
      ((warmAlgorithm (warmTuning p) p.x0).initial ()) ξ (warmCalls p)).1

def restartGap (p : Params) : ℝ := 2 ^ 35 * p.R ^ 2 * ((1 + p.L1 * p.R) * p.L0 + p.L1 * p.σ)

def restartParams (p : Params) (x : p.E) : Params :=
  { p with x0 := x, Δ := restartGap p, δ := p.δ / 2 }

inductive CombinedState (E : Type*) where
  | warm (s : Search E) (blocks received : ℕ) (replies : ℕ → E)
  | final (start : E) (s : RobustGeneralized.State E)

def startFinal (p : Params) (x : p.E) : CombinedState p.E :=
  .final x ((RobustGeneralized.algorithm (restartParams p x)).initial ())

open Classical in
def algorithm (p : Params) : Algorithm p.E p.E p.E where
  State := CombinedState p.E
  initial _ :=
    if p.L1 * p.R < 1 then startFinal p p.x0
    else .warm ((warmAlgorithm (warmTuning p) p.x0).initial ()) 0 0 (fun _ => 0)
  query s := match s with
    | .warm s _ _ _ => (0, searchPoint s)
    | .final x s => (RobustGeneralized.algorithm (restartParams p x)).query s
  update s reply := match s with
    | .warm s blocks received replies =>
        let replies' := Function.update replies received reply
        if received + 1 < warmBatch p then .warm s blocks (received + 1) replies'
        else
          let s' := searchUpdate (warmTuning p) s (warmEstimate p replies')
          if blocks + 1 < warmCalls p then .warm s' (blocks + 1) 0 (fun _ => 0)
          else startFinal p (warmOutput s')
    | .final x s => .final x ((RobustGeneralized.algorithm (restartParams p x)).update s reply)
  output s := match s with
    | .warm s _ _ _ => warmOutput s
    | .final x s => (RobustGeneralized.algorithm (restartParams p x)).output s

end

end OracleTemplate.CoarseGeneralized
