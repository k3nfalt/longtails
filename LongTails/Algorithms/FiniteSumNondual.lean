import LongTails.Algorithms.FiniteSumNondualProx
import LongTails.Algorithms.NondualSelector
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LongTails.Setups.FiniteSumNondualSmoothConvex

open MeasureTheory Classical

namespace LongTails.Algorithms.FiniteSumNondual

open LongTails.Setups.FiniteSumNondualSmoothConvex
open FiniteSumNondualProx
open OracleTemplate
open OracleTemplate.ComponentEnvelope (Program)

noncomputable def feasiblePoint (p : Params) (x : Point p) : Feasible p :=
  if hx : x ∈ domain p then ⟨x, hx⟩ else ⟨0, by simpa [domain] using p.hR⟩

noncomputable def adaptProgram (p : Params) {U : Type*}
    (program : Program (Fin p.n × Point p) (Point p) U) :
    Program (Fin p.n × Feasible p) (Point p) U :=
  mapQueries (fun q => (q.1, feasiblePoint p q.2)) program

noncomputable def programAlgorithm (p : Params) {Seed : Type} [MeasurableSpace Seed]
    (law : ProbabilityMeasure Seed)
    (plan : Seed → Program (Fin p.n × Point p) (Point p) (Point p)) :
    Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p) where
  Seed := Seed
  law := law
  State := Program (Fin p.n × Feasible p) (Point p) (Feasible p)
  initial seed := (adaptProgram p (plan seed)).map (feasiblePoint p)
  query state := (0, state.query (0, feasiblePoint p 0))
  update := Program.update
  output := Program.output (feasiblePoint p 0)

noncomputable def output (p : Params) {Seed : Type} [MeasurableSpace Seed]
    (law : ProbabilityMeasure Seed)
    (plan : Seed → Program (Fin p.n × Point p) (Point p) (Point p))
    (oracle : Oracle (Fin p.n × Feasible p) (Point p)) (K : ℕ)
    (seed : Seed) (oracleSeed : (k : ℕ) → oracle.Seed k) : Feasible p :=
  execute oracle (programAlgorithm p law plan) (fun _ => K) seed oracleSeed

noncomputable def guardedResult {Q Reply U Sample : Type*}
    (solver : Q → Sample → Reply) (accept : Q → Reply → Prop) :
    (fuel : ℕ) → Program Q Reply U → (Fin fuel → Sample) → Option U
  | _, .done u, _ => some u
  | 0, .ask _ _, _ => none
  | fuel + 1, .ask q next, seed =>
    let reply := solver q (seed 0)
    if accept q reply then guardedResult solver accept fuel (next reply) (fun j => seed j.succ)
    else none

noncomputable def guardedPlan {Q Reply U Sample BaseQ BaseReply : Type*}
    (solver : Q → Sample → Program BaseQ BaseReply Reply) (accept : Q → Reply → Prop)
    (fallback : U) : (fuel : ℕ) → Program Q Reply U → (Fin fuel → Sample) → Program BaseQ BaseReply U
  | _, .done u, _ => .done u
  | 0, .ask _ _, _ => .done fallback
  | fuel + 1, .ask q next, seed => (solver q (seed 0)).bind fun reply =>
    if accept q reply then guardedPlan solver accept fallback fuel (next reply) (fun j => seed j.succ)
    else .done fallback

section Cuts

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

def CutWeights (C : Set E) (w g : Fin m → E) (δ : ℝ) (a : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ a i) ∧ (∑ i, a i) = 1 ∧ ∀ u ∈ C, (∑ i, a i * ⟪g i, w i - u⟫) < δ

noncomputable def cutOutput (C : Set E) (w g : Fin m → E) (δ : ℝ) : E :=
  if h : ∃ a, CutWeights C w g δ a then ∑ i, (Classical.choose h i) • w i else 0

end Cuts

open scoped RealInnerProductSpace

noncomputable def linePoint (p : Params) (z y : Feasible p) (t : ℝ) : Feasible p :=
  feasiblePoint p ((1 - t) • z.val + t • y.val)

structure LineEndpoint (p : Params) where
  time : ℝ
  certificate : Certificate (Point p)

noncomputable def lineSlope (p : Params) (μ : ℝ) (z y : Feasible p) (e : LineEndpoint p) : ℝ :=
  ⟪μ • ((linePoint p z y e.time).val - e.certificate.point), y.val - z.val⟫

noncomputable def bisectPlan (p : Params) (μ : ℝ) (z y : Feasible p) :
    ℕ → LineEndpoint p → LineEndpoint p → Program (Feasible p) (Certificate (Point p)) (LineEndpoint p)
  | 0, lo, _ => .done lo
  | k + 1, lo, hi =>
    let t := (lo.time + hi.time) / 2
    .ask (linePoint p z y t) fun certificate =>
      let mid : LineEndpoint p := ⟨t, certificate⟩
      if lineSlope p μ z y mid ≤ 0 then bisectPlan p μ z y k mid hi
      else bisectPlan p μ z y k lo mid

noncomputable def linePlan (p : Params) (μ : ℝ) (z y : Feasible p) (k : ℕ) :
    Program (Feasible p) (Certificate (Point p)) (LineEndpoint p) :=
  .ask z fun first =>
    let lo : LineEndpoint p := ⟨0, first⟩
    if 0 ≤ lineSlope p μ z y lo then .done lo
    else .ask y fun last =>
      let hi : LineEndpoint p := ⟨1, last⟩
      if lineSlope p μ z y hi ≤ 0 then .done hi
      else bisectPlan p μ z y k lo hi

noncomputable def selectorRadius (p : Params) : ℝ :=
  p.R * Real.sqrt ((p.d : ℝ) / (1 + Nat.log 2 p.d))

noncomputable def selector (p : Params) (C : Set (Point p)) : Feasible p :=
  if hd : p.d = 0 then feasiblePoint p 0 else
    letI : NeZero p.d := ⟨hd⟩
    feasiblePoint p (NondualSelector.center C (selectorRadius p))

structure Trial (p : Params) where
  selector : Feasible p
  center : Feasible p
  certificate : Certificate (Point p)

noncomputable def trialPoint (p : Params) (trial : Trial p) : Feasible p :=
  feasiblePoint p trial.certificate.point

noncomputable def cutBody (p : Params) (δ : ℝ) (history : List (Trial p)) : Set (Point p) :=
  domain p ∩ {u | ∀ trial ∈ history, δ ≤ ⟪trial.certificate.gradient, (trialPoint p trial).val - u⟫}

noncomputable def historyOutput (p : Params) (δ : ℝ) (history : List (Trial p)) : Feasible p :=
  feasiblePoint p (cutOutput (domain p) (fun i => (trialPoint p (history.get i)).val)
    (fun i => (history.get i).certificate.gradient) δ)

noncomputable def lastPoint (p : Params) (base : Feasible p) (history : List (Trial p)) : Feasible p :=
  history.foldl (fun _ trial => trialPoint p trial) base

noncomputable def phasePlan (p : Params) (μ δ : ℝ) (lineFuel : ℕ) :
    ℕ → List (Trial p) → Feasible p → Program (Feasible p) (Certificate (Point p)) (Feasible p)
  | 0, history, base => .done (if (cutBody p δ history).Nonempty then lastPoint p base history else historyOutput p δ history)
  | fuel + 1, history, base =>
    if (cutBody p δ history).Nonempty then
      let z := selector p (cutBody p δ history)
      (linePlan p μ z (lastPoint p base history) lineFuel).bind fun e =>
        let trial : Trial p := ⟨z, linePoint p z (lastPoint p base history) e.time, e.certificate⟩
        phasePlan p μ δ lineFuel fuel (history ++ [trial]) base
    else .done (historyOutput p δ history)

noncomputable def phasesPlan (p : Params) (μ : ℝ) (phaseFuel lineFuel : ℕ) :
    ℕ → Feasible p → Program (Feasible p) (Certificate (Point p)) (Feasible p)
  | 0, y => .done y
  | phases + 1, y => (phasePlan p μ (p.ε / 2 * (2 : ℝ) ^ phases) lineFuel phaseFuel [] y).bind fun next =>
      phasesPlan p μ phaseFuel lineFuel phases next

noncomputable def scale (p : Params) : ℝ := p.L * p.R ^ 2 / p.ε

noncomputable def logSize (p : Params) : ℕ := 1 + Nat.log 2 (2 + p.d + p.n + ⌈scale p⌉₊)

noncomputable def rootSize (p : Params) : ℕ := 1 + ⌈(scale p / p.n) ^ (1 / 3 : ℝ)⌉₊

noncomputable def phaseSize (p : Params) : ℕ := 64 * rootSize p * logSize p

noncomputable def lineFuel (p : Params) : ℕ := 64 * logSize p

noncomputable def epochCount (p : Params) : ℕ := 512 * logSize p

noncomputable def smoothing (p : Params) : ℝ := p.L / p.n

noncomputable def requestCount (p : Params) : ℕ := logSize p * (10 * phaseSize p) * (lineFuel p + 2)

noncomputable def residualTolerance (p : Params) : ℝ :=
  min (p.ε / (128 * phaseSize p * p.R)) (Real.sqrt (smoothing p * p.ε / (32 * phaseSize p)))

def Seeds (p : Params) := Fin (requestCount p) → Fin (epochCount p) → Fin (144 * p.n) → Fin p.n

noncomputable instance (p : Params) : Fintype (Seeds p) := inferInstanceAs (Fintype (_ → _ → _ → _))
instance (p : Params) : Nonempty (Seeds p) := ⟨fun _ _ _ => 0⟩
instance (p : Params) : MeasurableSpace (Seeds p) := ⊤
instance (p : Params) : MeasurableSingletonClass (Seeds p) := ⟨fun _ => trivial⟩

noncomputable def fallbackPlan (p : Params) : Program (Fin p.n × Point p) (Point p) (Feasible p) :=
  (snapshot (0 : Point p) p.n id).map fun cache =>
    feasiblePoint p (step (domain p) 0 (1 / p.L) 0 0 (cacheMean cache))

noncomputable def solverPlan (p : Params) (c : Feasible p)
    (seed : Fin (epochCount p) → Fin (144 * p.n) → Fin p.n) :
    Program (Fin p.n × Point p) (Point p) (Certificate (Point p)) :=
  solvePlan (domain p) p.L (smoothing p) c.val (epochCount p) seed

noncomputable def plan (p : Params) (seed : Seeds p) : Program (Fin p.n × Point p) (Point p) (Point p) :=
  (fallbackPlan p).bind fun base =>
    (guardedPlan (solverPlan p) (fun _ out => ‖out.error‖ ≤ residualTolerance p) base (requestCount p)
      (phasesPlan p (smoothing p) (10 * phaseSize p) (lineFuel p) (logSize p) base) seed).map Subtype.val

noncomputable def algorithm (p : Params) : Algorithm (Fin p.n × Feasible p) (Point p) (Feasible p) :=
  programAlgorithm p ⟨(PMF.uniformOfFintype (Seeds p)).toMeasure, inferInstance⟩ (plan p)

noncomputable def runOutput (p : Params) (oracle : Oracle (Fin p.n × Feasible p) (Point p)) (K : ℕ)
    (seed : Seeds p) (oracleSeed : (k : ℕ) → oracle.Seed k) : Feasible p :=
  execute oracle (algorithm p) (fun _ => K) seed oracleSeed

end LongTails.Algorithms.FiniteSumNondual
