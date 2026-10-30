import LongTails.Algorithms.MultiplicativeRobustEstimator
import LongTails.Algorithms.ProjectedClippedExtragradient

namespace LongTails.Algorithms.GapNoisePastExtragradient

open OracleTemplate

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure StageConfig where
  curvature : ℝ
  scale : ℝ
  radius : ℝ
  regularization : ℝ
  anchor : E
  center : E

structure StageState (E : Type*) where
  base : E
  previousQuery : E
  previousReply : E
  pilotDenominator : ℝ
  previousStep : ℝ
  total : E
  active : Bool

noncomputable def regularizedReply (c : StageConfig (E := E)) (x raw : E) : E :=
  raw + c.regularization • (x - c.anchor)

noncomputable def pilotDenominator (c : StageConfig (E := E)) (estimate : E) : ℝ :=
  c.scale + 2 * c.curvature * (‖estimate‖ + c.scale / c.curvature)

noncomputable def nextStep (state : StageState E) : ℝ :=
  min (2 * state.previousStep) (1 / (16384 * state.pilotDenominator))

noncomputable def clippedReply (c : StageConfig (E := E)) (η : ℝ) (reply : E) : E :=
  clip (1 / (1024 * c.curvature * η)) reply

noncomputable def initialWithDenominator (c : StageConfig (E := E)) (denominator : ℝ) (raw : E) : StageState E :=
  let η := 1 / (16384 * denominator)
  { base := c.center
    previousQuery := c.center
    previousReply := clippedReply c η (regularizedReply c c.center raw)
    pilotDenominator := denominator
    previousStep := η
    total := 0
    active := true }

noncomputable def initialState (c : StageConfig (E := E)) (pilot raw : E) : StageState E :=
  initialWithDenominator c (pilotDenominator c pilot) raw

noncomputable def predictor (proj : E → E) (state : StageState E) : E :=
  proj (state.base - nextStep state • state.previousReply)

noncomputable def permitted (c : StageConfig (E := E)) (state : StageState E) (x : E) : Prop :=
  state.active = true ∧ ‖state.base - c.center‖ ≤ 64 * c.radius ∧ ‖x - c.center‖ ≤ 64 * c.radius

noncomputable def updatedState (c : StageConfig (E := E)) (state : StageState E)
    (x pilot raw nextBase : E) : StageState E :=
  { base := nextBase
    previousQuery := x
    previousReply := clippedReply c (nextStep state) (regularizedReply c x raw)
    pilotDenominator := pilotDenominator c pilot
    previousStep := nextStep state
    total := state.total + x
    active := true }

noncomputable def advance (proj : E → E) (c : StageConfig (E := E))
    (state : StageState E) (x pilot raw : E) : StageState E := by
  classical
  exact if permitted c state x then
    updatedState c state x pilot raw
      (proj (state.base - nextStep state • clippedReply c (nextStep state) (regularizedReply c x raw)))
  else { state with active := false }

noncomputable def trialOutput (c : StageConfig (E := E)) (steps : ℕ) (state : StageState E) : E :=
  if state.active then (1 / (steps : ℝ)) • state.total else c.center

noncomputable def pilotPlan (c : StageConfig (E := E)) (x : E) (batch groups : ℕ) :
    QueryPlan (Fin 2 × E) E E (batch * (groups + 1)) :=
  QueryPlan.map (fun values : List E => MultiplicativeRobustEstimator.medoid
      (fun i : Fin (groups + 1) => values[i.val]?.getD 0))
    (QueryPlan.traverse (groups + 1) fun _ =>
      QueryPlan.map (regularizedReply c x) (ProjectedClippedExtragradient.meanPlan batch x))

noncomputable def initialPlan (c : StageConfig (E := E)) (batch pilotBatch groups : ℕ) :
    QueryPlan (Fin 2 × E) E (StageState E) (batch + pilotBatch * (groups + 1)) :=
  QueryPlan.bind (pilotPlan c c.center pilotBatch groups) fun pilot =>
    QueryPlan.map (initialState c pilot) (ProjectedClippedExtragradient.meanPlan batch c.center)

noncomputable def idlePlan (center : E) (state : StageState E) :
    (calls : ℕ) → QueryPlan (Fin 2 × E) E (StageState E) calls
  | 0 => .done state
  | calls + 1 => .ask (1, center) fun _ => idlePlan center state calls

noncomputable def stepPlan (c : StageConfig (E := E)) (batch pilotBatch groups : ℕ)
    (state : StageState E) :
    QueryPlan (Fin 2 × E) E (StageState E) (((1 + batch) + pilotBatch * (groups + 1)) + 1) := by
  classical
  exact .ask (1, state.base - nextStep state • state.previousReply) fun x =>
    if permitted c state x then
      QueryPlan.bind (pilotPlan c x pilotBatch groups) fun pilot =>
        QueryPlan.bind (ProjectedClippedExtragradient.meanPlan batch x) fun raw =>
          .ask (1, state.base - nextStep state •
            clippedReply c (nextStep state) (regularizedReply c x raw)) fun y =>
              .done (updatedState c state x pilot raw y)
    else idlePlan c.center { state with active := false } ((1 + batch) + pilotBatch * (groups + 1))

noncomputable def repeatPlan {calls : ℕ}
    (step : StageState E → QueryPlan (Fin 2 × E) E (StageState E) calls) :
    (steps : ℕ) → StageState E → QueryPlan (Fin 2 × E) E (StageState E) (calls * steps)
  | 0, state => .done state
  | steps + 1, state => QueryPlan.bind (step state) (repeatPlan step steps)

noncomputable def trialPlan (c : StageConfig (E := E)) (batch pilotBatch groups steps : ℕ) :
    QueryPlan (Fin 2 × E) E E
      (((1 + batch + pilotBatch * (groups + 1)) + 1) * steps + (batch + pilotBatch * (groups + 1))) :=
  QueryPlan.bind (initialPlan c batch pilotBatch groups) fun state =>
    QueryPlan.map (trialOutput c steps) (repeatPlan (stepPlan c batch pilotBatch groups) steps state)

noncomputable def trialAlgorithm (c : StageConfig (E := E)) (batch pilotBatch groups steps : ℕ) :
    Algorithm E E E 2 :=
  LongTails.Algorithms.EnergyHessianReuse.channelAlgorithm (0, c.center) c.center
    (trialPlan c batch pilotBatch groups steps)

noncomputable def executedTrial (c : StageConfig (E := E)) (batch pilotBatch groups steps : ℕ)
    (oracle : Oracle E E 2) (budget : Fin 2 → ℕ) (ξ : (k : ℕ) → oracle.Seed k) : E :=
  execute oracle (trialAlgorithm c batch pilotBatch groups steps) budget () ξ

structure Tuning extends ProjectedClippedExtragradient.Tuning where
  v : ℝ

noncomputable def effectiveCurvature (t : Tuning) : ℝ :=
  t.L1 + t.L0 / (t.G + t.L0 * t.R)

noncomputable def geometry (t : Tuning) : ProjectedClippedExtragradient.Tuning :=
  ⟨t.L0, effectiveCurvature t, t.R, t.G, t.σ, t.ε, t.δ⟩

noncomputable def stages (t : Tuning) : ℕ := ProjectedClippedExtragradient.stageCount (geometry t)

noncomputable def stageScale (t : Tuning) (s : ℕ) : ℝ :=
  2 ^ 40 * ProjectedClippedExtragradient.localScale (geometry t) s

noncomputable def stageShift (t : Tuning) (s : ℕ) : ℝ :=
  ProjectedClippedExtragradient.radius (geometry t) s / (2 ^ 100 * stages t * t.R * (1 + effectiveCurvature t * t.R))

noncomputable def stageSteps (t : Tuning) (s : ℕ) : ℕ :=
  ⌈2 ^ 48 * stageScale t s / ProjectedClippedExtragradient.regularization (geometry t) s⌉₊

noncomputable def stageBatch (t : Tuning) (s : ℕ) : ℕ :=
  max 1 ⌈2 ^ 120 * (1 + effectiveCurvature t * ProjectedClippedExtragradient.radius (geometry t) s) * (t.σ ^ 2 / (ProjectedClippedExtragradient.regularization (geometry t) s * stageScale t s * ProjectedClippedExtragradient.radius (geometry t) s ^ 2) + t.v / (stageScale t s * stageShift t s))⌉₊

noncomputable def pilotBatch (t : Tuning) (s : ℕ) : ℕ :=
  max 1 ⌈2 ^ 40 * (t.σ ^ 2 * effectiveCurvature t ^ 2 / stageScale t s ^ 2 + t.v * t.R * effectiveCurvature t / stageScale t s)⌉₊

noncomputable def pilotGroups (t : Tuning) (s : ℕ) : ℕ :=
  ⌈Real.log (4096 * ((stageSteps t s : ℝ) + 1)) / Real.log 2⌉₊ + 1

noncomputable def outerGroups (t : Tuning) : ℕ :=
  ⌈Real.log (2 * stages t / t.δ) / Real.log 2⌉₊ + 1

noncomputable def stageConfig (t : Tuning) (s : ℕ) (anchor center : E) : StageConfig (E := E) :=
  ⟨effectiveCurvature t, stageScale t s, ProjectedClippedExtragradient.radius (geometry t) s,
    ProjectedClippedExtragradient.regularization (geometry t) s, anchor, center⟩

noncomputable def trialCalls (t : Tuning) (s : ℕ) : ℕ :=
  ((1 + stageBatch t s + pilotBatch t s * (pilotGroups t s + 1)) + 1) * stageSteps t s + (stageBatch t s + pilotBatch t s * (pilotGroups t s + 1))

noncomputable def stageCalls (t : Tuning) (s : ℕ) : ℕ := trialCalls t s * (outerGroups t + 1)

noncomputable def stagePlan (t : Tuning) (s : ℕ) (anchor center : E) :
    QueryPlan (Fin 2 × E) E E (stageCalls t s) :=
  QueryPlan.map (fun values : List E => MultiplicativeRobustEstimator.medoid
      (fun i : Fin (outerGroups t + 1) => values[i.val]?.getD center))
    (QueryPlan.traverse (outerGroups t + 1) fun _ =>
      trialPlan (stageConfig t s anchor center) (stageBatch t s) (pilotBatch t s)
        (pilotGroups t s) (stageSteps t s))

noncomputable def finalBatch (t : Tuning) : ℕ :=
  max 1 ⌈2 ^ 60 * (t.σ ^ 2 / t.ε ^ 2 + t.v * t.R / t.ε)⌉₊

noncomputable def finalCalls (t : Tuning) : ℕ := 1 + finalBatch t * (outerGroups t + 1)

noncomputable def finalPlan (t : Tuning) (anchor x : E) :
    QueryPlan (Fin 2 × E) E E (finalCalls t) :=
  QueryPlan.bind (QueryPlan.traverse (outerGroups t + 1) fun _ =>
    ProjectedClippedExtragradient.meanPlan (finalBatch t) x) fun values =>
      let estimate := MultiplicativeRobustEstimator.medoid
        (fun i : Fin (outerGroups t + 1) => values[i.val]?.getD 0)
      .ask (1, x - ProjectedClippedExtragradient.finalStepSize (geometry t) •
        ClippedExtragradient.regularizedReply
          (ProjectedClippedExtragradient.regularization (geometry t) (stages t - 1)) anchor x estimate)
        fun y => .done y

noncomputable def runCalls (t : Tuning) : ℕ → ℕ → ℕ
  | _, 0 => finalCalls t
  | s, n + 1 => runCalls t (s + 1) n + stageCalls t s

noncomputable def runPlan (t : Tuning) : (s n : ℕ) → E → E →
    QueryPlan (Fin 2 × E) E E (runCalls t s n)
  | _, 0, anchor, center => finalPlan t anchor center
  | s, n + 1, anchor, center => QueryPlan.bind (stagePlan t s anchor center) fun w =>
      runPlan t (s + 1) n (if n = 0 then anchor else (1 / 2 : ℝ) • (anchor + w)) w

noncomputable def algorithm (t : Tuning) (x0 : E) : Algorithm E E E 2 :=
  LongTails.Algorithms.EnergyHessianReuse.channelAlgorithm (0, x0) x0 (runPlan t 0 (stages t) x0 x0)

noncomputable def output (t : Tuning) (x0 : E) (oracle : Oracle E E 2)
    (budget : Fin 2 → ℕ) (ξ : (k : ℕ) → oracle.Seed k) : E :=
  execute oracle (algorithm t x0) budget () ξ

end LongTails.Algorithms.GapNoisePastExtragradient
