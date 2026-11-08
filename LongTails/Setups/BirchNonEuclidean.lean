import LongTails.Setups.BirchSgd
import LongTails.Setups.UscgConstant

open MeasureTheory ProbabilityTheory

namespace LongTails.Setups.BirchNonEuclidean

open OracleTemplate
open OracleTemplate.Rennala (Point Instance)
open OracleTemplate.BirchSgd (gradientOracle)
open LongTails.Setups.UscgConstant (dualNorm IsBallLMO)

inductive Instruction where
  | query (worker point : ℕ)
  | mix (worker : ℕ) (terms : List (ℝ × ℕ))
  | difference (worker left right : ℕ)
  | lmo (worker source : ℕ)
  | sharp (worker source : ℕ)
  | move (worker base direction : ℕ) (step : ℝ)
  | sendPoint (sender receiver source : ℕ)
  | sendVector (sender receiver source : ℕ)

structure Layout where
  next : ℕ := 1
  points : ℕ → Finset ℕ := fun _ => {0}
  vectors : ℕ → Finset ℕ := fun _ => {0}

def Instruction.Legal (workers : ℕ) (s : Layout) : Instruction → Prop
  | .query w x => w < workers ∧ x ∈ s.points w
  | .mix w terms => w < workers ∧ ∀ t ∈ terms, t.2 ∈ s.vectors w
  | .difference w x y => w < workers ∧ x ∈ s.points w ∧ y ∈ s.points w
  | .lmo w v => w < workers ∧ v ∈ s.vectors w
  | .sharp w v => w < workers ∧ v ∈ s.vectors w
  | .move w x v η => w < workers ∧ x ∈ s.points w ∧ v ∈ s.vectors w ∧ 0 ≤ η
  | .sendPoint w u x => w < workers ∧ u < workers ∧ x ∈ s.points w
  | .sendVector w u v => w < workers ∧ u < workers ∧ v ∈ s.vectors w

def Instruction.layout (s : Layout) (i : Instruction) : Layout :=
  match i with
  | .query w _ | .mix w _ | .difference w _ _ | .lmo w _ | .sharp w _ =>
      { s with next := s.next + 1, vectors := Function.update s.vectors w (insert s.next (s.vectors w)) }
  | .move w _ _ _ =>
      { s with next := s.next + 1, points := Function.update s.points w (insert s.next (s.points w)) }
  | .sendPoint _ u x =>
      { s with next := s.next + 1, points := Function.update s.points u (insert x (s.points u)) }
  | .sendVector _ u v =>
      { s with next := s.next + 1, vectors := Function.update s.vectors u (insert v (s.vectors u)) }

def LegalFrom (workers : ℕ) : Layout → List Instruction → Prop
  | _, [] => True
  | s, i :: rest => i.Legal workers s ∧ LegalFrom workers (i.layout s) rest

def finalLayout (instructions : List Instruction) : Layout :=
  instructions.foldl (fun s i => i.layout s) {}

structure Program where
  instructions : List Instruction
  outputWorker : ℕ
  outputCount : ℕ
  outputPoint : Fin (outputCount + 1) → ℕ

def Program.Legal (workers : ℕ) (a : Program) : Prop :=
  LegalFrom workers {} a.instructions ∧ a.outputWorker < workers ∧
    ∀ j, a.outputPoint j ∈ (finalLayout a.instructions).points a.outputWorker

def Instruction.oracleCost : Instruction → ℕ
  | .query _ _ => 1
  | _ => 0

def Instruction.messageCost : Instruction → ℕ
  | .sendPoint _ _ _ | .sendVector _ _ _ => 1
  | _ => 0

def Instruction.lmoCost : Instruction → ℕ
  | .lmo _ _ | .sharp _ _ => 1
  | _ => 0

def Program.oracleCalls (a : Program) : ℕ :=
  (a.instructions.map Instruction.oracleCost).sum

def Program.messages (a : Program) : ℕ :=
  (a.instructions.map Instruction.messageCost).sum

def Program.lmoCalls (a : Program) : ℕ :=
  (a.instructions.map Instruction.lmoCost).sum

structure Tuning where
  step : ℕ → ℝ
  momentum : ℕ → ℝ

def Tuning.Valid (t : Tuning) : Prop :=
  (∀ k, 0 ≤ t.step k) ∧ ∀ k, 0 ≤ t.momentum k ∧ t.momentum k ≤ 1

inductive Coefficient where
  | constant (value : ℝ)
  | step (index : ℕ)
  | momentum (index : ℕ)
  | add (left right : Coefficient)
  | mul (left right : Coefficient)
  | neg (value : Coefficient)

def Coefficient.eval (t : Tuning) : Coefficient → ℝ
  | .constant x => x
  | .step k => t.step k
  | .momentum k => t.momentum k
  | .add x y => x.eval t + y.eval t
  | .mul x y => x.eval t * y.eval t
  | .neg x => -x.eval t

inductive InstructionTemplate where
  | query (worker point : ℕ)
  | mix (worker : ℕ) (terms : List (Coefficient × ℕ))
  | difference (worker left right : ℕ)
  | lmo (worker source : ℕ)
  | sharp (worker source : ℕ)
  | move (worker base direction : ℕ) (step : Coefficient)
  | sendPoint (sender receiver source : ℕ)
  | sendVector (sender receiver source : ℕ)

def InstructionTemplate.instantiate (t : Tuning) : InstructionTemplate → Instruction
  | .query w x => .query w x
  | .mix w terms => .mix w (terms.map (fun c => (c.1.eval t, c.2)))
  | .difference w x y => .difference w x y
  | .lmo w v => .lmo w v
  | .sharp w v => .sharp w v
  | .move w x v c => .move w x v (c.eval t)
  | .sendPoint w u x => .sendPoint w u x
  | .sendVector w u v => .sendVector w u v

structure ProgramTemplate where
  instructions : List InstructionTemplate
  outputWorker : ℕ
  outputCount : ℕ
  outputPoint : Fin (outputCount + 1) → ℕ

def ProgramTemplate.instantiate (a : ProgramTemplate) (t : Tuning) : Program where
  instructions := a.instructions.map (InstructionTemplate.instantiate t)
  outputWorker := a.outputWorker
  outputCount := a.outputCount
  outputPoint := a.outputPoint

structure ProtocolFamily where
  template : ℕ → ℕ → ProgramTemplate

def ProtocolFamily.instantiate (a : ProtocolFamily) (horizon batchSize : ℕ)
    (t : Tuning) : Program :=
  (a.template horizon batchSize).instantiate t

structure DualRegularityWitness {d : ℕ} (N : Seminorm ℝ (Point d)) (κ : ℝ) where
  auxiliary : Seminorm ℝ (Point d)
  smoothness : ℝ
  derivative : Point d → Point d
  definite : ∀ x, auxiliary x = 0 → x = 0
  continuous : Continuous auxiliary
  smoothness_lower : 1 ≤ smoothness
  smoothness_upper : smoothness ≤ κ
  derivative_continuous : Continuous derivative
  differentiable : ∀ x, HasGradientAt (fun y => (1 / 2 : ℝ) * auxiliary y ^ 2)
    (derivative x) x
  smooth : ∀ x y, (1 / 2 : ℝ) * auxiliary (x + y) ^ 2 ≤
    (1 / 2 : ℝ) * auxiliary x ^ 2 + inner ℝ (derivative x) y +
      smoothness / 2 * auxiliary y ^ 2
  lower : ∀ x, dualNorm N x ^ 2 ≤ auxiliary x ^ 2
  upper : ∀ x, auxiliary x ^ 2 ≤ κ / smoothness * dualNorm N x ^ 2

def DualRegular {d : ℕ} (N : Seminorm ℝ (Point d)) (κ : ℝ) : Prop :=
  Nonempty (DualRegularityWitness N κ)

abbrev LinearValue := (ℕ →₀ ℝ) × (ℕ →₀ ℝ)

structure SymbolicMemory where
  next : ℕ := 1
  points : ℕ → LinearValue := fun _ => 0
  vectors : ℕ → LinearValue := fun _ => 0
  queryPoints : ℕ → LinearValue := fun _ => 0
  sharpInputs : ℕ → LinearValue := fun _ => 0
  queries : Finset ℕ := ∅
  sharps : Finset ℕ := ∅
  units : Finset ℕ := ∅

noncomputable def symbolicStore (s : SymbolicMemory) (v : LinearValue) : SymbolicMemory :=
  { s with next := s.next + 1, vectors := Function.update s.vectors s.next v }

noncomputable def symbolicPerform (s : SymbolicMemory) (i : Instruction) : SymbolicMemory :=
  match i with
  | .query _ x =>
      { symbolicStore s (Finsupp.single s.next 1, 0) with
        queryPoints := Function.update s.queryPoints s.next (s.points x)
        queries := insert s.next s.queries }
  | .mix _ terms => symbolicStore s (terms.map (fun t => t.1 • s.vectors t.2)).sum
  | .difference _ x y => symbolicStore s (s.points x - s.points y)
  | .lmo _ v =>
      { symbolicStore s (0, Finsupp.single s.next 1) with
        sharpInputs := Function.update s.sharpInputs s.next (s.vectors v)
        units := insert s.next s.units }
  | .sharp _ v =>
      { symbolicStore s (0, Finsupp.single s.next 1) with
        sharpInputs := Function.update s.sharpInputs s.next (s.vectors v)
        sharps := insert s.next s.sharps }
  | .move _ x v η =>
      { s with
        next := s.next + 1
        points := Function.update s.points s.next (s.points x + η • s.vectors v) }
  | .sendPoint _ _ _ | .sendVector _ _ _ => { s with next := s.next + 1 }

noncomputable def Program.symbolic (a : Program) : SymbolicMemory :=
  a.instructions.foldl symbolicPerform {}

noncomputable def transportCoefficient (a : Program) (main owner : ℕ → ℕ)
    (η : ℝ) (e t : ℕ) : ℝ :=
  ∑ q ∈ a.symbolic.queries, |(a.symbolic.sharpInputs e).1 q| *
    |((a.symbolic.queryPoints q).2 t - (a.symbolic.points (main (owner e))).2 t) / η|

structure ProgramCertificate (a : Program) (K : ℕ) (η D V : ℝ) where
  main : ℕ → ℕ
  owner : ℕ → ℕ
  weight : ℕ → ℝ
  positive_horizon : 0 < K
  sharp_only : a.symbolic.units = ∅
  estimator_linear : ∀ e ∈ a.symbolic.sharps, (a.symbolic.sharpInputs e).2 = 0
  estimator_mass : ∀ e ∈ a.symbolic.sharps,
    ∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs e).1 q = 1
  query_linear : ∀ q ∈ a.symbolic.queries, (a.symbolic.queryPoints q).1 = 0
  main_initial : main 0 = 0
  main_linear : ∀ k, k ≤ K → (a.symbolic.points (main k)).1 = 0
  weight_nonneg : ∀ e ∈ a.symbolic.sharps, 0 ≤ weight e
  owner_lt : ∀ e ∈ a.symbolic.sharps, owner e < K
  partition : ∀ k, k < K → ∑ e ∈ a.symbolic.sharps.filter (fun e => owner e = k), weight e = 1
  chain : ∀ k, k < K → (a.symbolic.points (main (k + 1))).2 =
    (a.symbolic.points (main k)).2 +
      η • ∑ e ∈ a.symbolic.sharps.filter (fun e => owner e = k), weight e • Finsupp.single e 1
  output_count : a.outputCount + 1 = K
  output_indices : ∀ j, a.outputPoint j = main j.val
  transport : ∀ t ∈ a.symbolic.sharps,
    (∑ e ∈ a.symbolic.sharps, weight e *
      (∑ j ∈ a.symbolic.sharps, transportCoefficient a main owner η e j) *
        transportCoefficient a main owner η e t) ≤ D ^ 2 * weight t
  noise : (∑ e ∈ a.symbolic.sharps, weight e *
    ∑ q ∈ a.symbolic.queries, (a.symbolic.sharpInputs e).1 q ^ 2) ≤ (K : ℝ) * V

structure StructuralProfile where
  minimumBatch : ℕ
  driftConstant : ℝ
  driftLinear : ℝ
  noiseLinear : ℝ
  noiseQuadratic : ℝ

def StructuralProfile.Valid (c : StructuralProfile) : Prop :=
  0 < c.minimumBatch ∧ 0 ≤ c.driftConstant ∧ 0 ≤ c.driftLinear ∧
    0 ≤ c.noiseLinear ∧ 0 ≤ c.noiseQuadratic

noncomputable def canonicalTuning (η : ℝ) (B : ℕ) : Tuning where
  step := fun _ => η
  momentum := fun _ => 1 / (B : ℝ)

structure Params where
  d : ℕ
  N : Seminorm ℝ (Point d)
  L : ℝ
  σ : ℝ
  ε : ℝ
  Δ : ℝ
  x0 : Point d
  workers : ℕ
  κ : ℝ
  protocol : ProtocolFamily
  profile : StructuralProfile
  callCount : ℕ → ℕ → ℕ

def Structural (p : Params) : Prop :=
  ∀ K B, 0 < K → p.profile.minimumBatch ≤ B → ∀ η : ℝ, 0 < η →
    let a := p.protocol.instantiate K B (canonicalTuning η B)
    a.Legal p.workers ∧ a.oracleCalls = p.callCount K B ∧
      Nonempty (ProgramCertificate a K η
        (p.profile.driftConstant + p.profile.driftLinear * B)
        (p.profile.noiseLinear / B + p.profile.noiseQuadratic / (B : ℝ) ^ 2))

structure Memory (d : ℕ) where
  next : ℕ
  points : ℕ → Point d
  vectors : ℕ → Point d
  pointSamples : ℕ → Finset ℕ
  vectorSamples : ℕ → Finset ℕ
  replies : ℕ

def initialMemory (p : Params) : Memory p.d :=
  ⟨1, fun _ => p.x0, fun _ => 0, fun _ => ∅, fun _ => ∅, 0⟩

def storeVector {d : ℕ} (s : Memory d) (v : Point d) (deps : Finset ℕ) : Memory d :=
  { s with
    next := s.next + 1
    vectors := Function.update s.vectors s.next v
    vectorSamples := Function.update s.vectorSamples s.next deps }

noncomputable def perform (p : Params) (lmo : Point p.d → Point p.d)
    (s : Memory p.d) (i : Instruction) (reply : Point p.d) : Memory p.d :=
  match i with
  | .query _ x =>
      { storeVector s reply (insert s.replies (s.pointSamples x)) with replies := s.replies + 1 }
  | .mix _ terms => storeVector s
      (terms.map (fun t => t.1 • s.vectors t.2)).sum
      (terms.foldl (fun deps t => deps ∪ s.vectorSamples t.2) ∅)
  | .difference _ x y => storeVector s (s.points x - s.points y)
      (s.pointSamples x ∪ s.pointSamples y)
  | .lmo _ v => storeVector s (lmo (s.vectors v)) (s.vectorSamples v)
  | .sharp _ v => storeVector s (dualNorm p.N (s.vectors v) • lmo (s.vectors v))
      (s.vectorSamples v)
  | .move _ x v η =>
      { s with
        next := s.next + 1
        points := Function.update s.points s.next (s.points x + η • s.vectors v)
        pointSamples := Function.update s.pointSamples s.next (s.pointSamples x ∪ s.vectorSamples v) }
  | .sendPoint _ _ _ | .sendVector _ _ _ => { s with next := s.next + 1 }

noncomputable def runPure (p : Params) (lmo : Point p.d → Point p.d) :
    List Instruction → Memory p.d → List Instruction × Memory p.d
  | [], s => ([], s)
  | (.query w x) :: rest, s => ((.query w x) :: rest, s)
  | i :: rest, s => runPure p lmo rest (perform p lmo s i 0)

structure State (d : ℕ) where
  remaining : List Instruction
  memory : Memory d
  selected : ℕ

noncomputable def programAlgorithm (p : Params) (a : Program)
    (lmo : Point p.d → Point p.d) : Algorithm (Point p.d) (Point p.d) (Point p.d) where
  Seed := Fin (a.outputCount + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (a.outputCount + 1))).toMeasure, inferInstance⟩
  State := State p.d
  initial j :=
    let init := runPure p lmo a.instructions (initialMemory p)
    ⟨init.1, init.2, a.outputPoint j⟩
  query s := (0, match s.remaining with
    | (.query _ x) :: _ => s.memory.points x
    | _ => p.x0)
  update s reply :=
    match s.remaining with
    | (.query w x) :: rest =>
        let next := runPure p lmo rest (perform p lmo s.memory (.query w x) reply)
        ⟨next.1, next.2, s.selected⟩
    | _ => s
  output s := s.memory.points s.selected

structure Objective (p : Params) (I : Instance p.d) : Prop where
  differentiable : ∀ x, HasGradientAt I.f (gradient I.f x) x
  smooth : ∀ x y, dualNorm p.N (gradient I.f x - gradient I.f y) ≤ p.L * p.N (x - y)
  lower : ∀ x, I.lower ≤ I.f x
  gap : I.f p.x0 - I.lower ≤ p.Δ

structure StochasticGradient (p : Params) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Point p.d → ℝ) (g : Point p.d → Ω → Point p.d) : Prop where
  measurable : Measurable (Function.uncurry g)
  integrable : ∀ x, Integrable (g x) μ
  unbiased : ∀ x, ∫ ω, g x ω ∂μ = gradient f x
  variance_integrable : ∀ x, Integrable (fun ω => dualNorm p.N (g x ω - gradient f x) ^ 2) μ
  variance : ∀ x, (∫ ω, dualNorm p.N (g x ω - gradient f x) ^ 2 ∂μ) ≤ p.σ ^ 2

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Instance p.d
  Query p := Point p.d
  Reply p := Point p.d
  Output p := Point p.d
  publicInput p := p
  valid p := (∀ x, p.N x = 0 → x = 0) ∧ Continuous p.N ∧
    0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.ε ∧ 0 ≤ p.Δ ∧ 0 < p.workers ∧ DualRegular p.N p.κ ∧ p.profile.Valid ∧ Structural p
  admissible p I O := Objective p I ∧
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI := m
      ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
        (g : Point p.d → Ω → Point p.d),
        LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
          (fun k (η : ℕ → Ω) => η k) (μ : Measure Ω) (P : Measure (ℕ → Ω)) ∧
        StochasticGradient p (μ : Measure Ω) I.f g ∧ O = gradientOracle P g
  successful p I output P := Measurable output ∧
    Integrable (fun ω => dualNorm p.N (gradient I.f (output ω)) ^ 2) (P : Measure _) ∧
    (∫ ω, dualNorm p.N (gradient I.f (output ω)) ^ 2 ∂(P : Measure _)) ≤ p.ε
  allowedAlgorithm p A := ∃ (horizon batchSize : ℕ) (t : Tuning),
    0 < batchSize ∧ t.Valid ∧ (p.protocol.instantiate horizon batchSize t).Legal p.workers ∧
      ∃ lmo : Point p.d → Point p.d, IsBallLMO p.N 1 lmo ∧
        A = programAlgorithm p (p.protocol.instantiate horizon batchSize t) lmo

end LongTails.Setups.BirchNonEuclidean
