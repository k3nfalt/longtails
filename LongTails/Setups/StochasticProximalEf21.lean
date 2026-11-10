import Mathlib
import LongTails.Template
import LongTails.Setups.StochasticSmoothAndConvex

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

namespace LongTails.Setups.StochasticProximalEf21

open OracleTemplate

structure Public where
  dimension : ℕ
  workers : ℕ
  L : ℝ
  R : ℝ
  σ : ℝ
  δ : ℝ
  ε : ℝ
  H : ℝ
  x0 : EuclideanSpace ℝ (Fin dimension)
  initialLaw : ProbabilityMeasure
    ((Fin workers → EuclideanSpace ℝ (Fin dimension)) ×
      (Fin workers → EuclideanSpace ℝ (Fin dimension)))

abbrev Point (p : Public) := EuclideanSpace ℝ (Fin p.dimension)
abbrev WorkerVectors (p : Public) := Fin p.workers → Point p
abbrev InitialMemories (p : Public) := WorkerVectors p × WorkerVectors p
abbrev Query (p : Public) := Point p × WorkerVectors p
abbrev Reply (p : Public) := Point p × WorkerVectors p
abbrev History (p : Public) := List ((Fin 4 × Query p) × Reply p)
abbrev Output (p : Public) := Point p × (ℕ × (ℕ × ℕ))

abbrev Params := Public

structure Instance (p : Public) where
  f : Fin p.workers → Point p → ℝ
  localL : Fin p.workers → ℝ
  ψ : Point p → EReal
  prox : ℝ → Point p → Point p
  xstar : Point p

noncomputable def smoothObjective {p : Public} (I : Instance p) (x : Point p) : ℝ :=
  (p.workers : ℝ)⁻¹ * ∑ i, I.f i x

noncomputable def objective {p : Public} (I : Instance p) (x : Point p) : EReal :=
  (smoothObjective I x : EReal) + I.ψ x

noncomputable def finiteObjective {p : Public} (I : Instance p) (x : Point p) : ℝ :=
  smoothObjective I x + (I.ψ x).toReal

noncomputable def initialCompressionError (p : Public) : ℝ :=
  (p.workers : ℝ)⁻¹ * ∑ i,
    ∫ z : InitialMemories p, ‖z.2 i - z.1 i‖ ^ 2 ∂(p.initialLaw : Measure _)

noncomputable def initialMomentumError {p : Public} (I : Instance p) : ℝ :=
  (p.workers : ℝ)⁻¹ * ∑ i,
    ∫ z : InitialMemories p, ‖z.1 i - gradient (I.f i) p.x0‖ ^ 2
      ∂(p.initialLaw : Measure _)

noncomputable def initialGap {p : Public} (I : Instance p) : ℝ :=
  finiteObjective I p.x0 - finiteObjective I I.xstar

noncomputable def executionStep (p : Public) : ℝ := p.δ / (1572864 * p.L)
noncomputable def regularization (p : Public) (s : ℕ) : ℝ := 2 * p.L / (2 : ℝ) ^ s
noncomputable def momentum (p : Public) (s : ℕ) : ℝ := regularization p s * executionStep p
noncomputable def finalStage (p : Public) : ℕ := ⌈Real.log (32768 * p.L * p.R ^ 2 / p.ε) / Real.log 2⌉₊
noncomputable def batchSize (p : Public) (s : ℕ) : ℕ := max 1 ⌈executionStep p * p.σ ^ 2 / (regularization p s * p.R ^ 2)⌉₊
noncomputable def stageLength (p : Public) (s : ℕ) : ℕ := if s = 0 then ⌈512 / (regularization p 0 * executionStep p) * Real.log (2 + 2 * p.H / (8192 * regularization p 0 * p.R ^ 2))⌉₊ else ⌈512 * Real.log 16 / (regularization p s * executionStep p)⌉₊

noncomputable def iterationCount (p : Public) : ℕ :=
  ∑ s ∈ Finset.range (finalStage p + 1), stageLength p s

noncomputable def samplesPerWorker (p : Public) : ℕ :=
  ∑ s ∈ Finset.range (finalStage p + 1), batchSize p s * stageLength p s

noncomputable def allWorkerSamples (p : Public) : ℕ := p.workers * samplesPerWorker p
noncomputable def allWorkerMessages (p : Public) : ℕ := p.workers * iterationCount p

structure State (p : Public) where
  stage : ℕ
  iteration : ℕ
  phase : ℕ
  batchDraws : ℕ
  x : Point p
  m : WorkerVectors p
  v : WorkerVectors p
  accumulator : WorkerVectors p
  samples : ℕ
  rounds : ℕ
  proxCalls : ℕ

noncomputable def initialState (p : Public) (seed : InitialMemories p) : State p where
  stage := 0
  iteration := 0
  phase := 0
  batchDraws := 0
  x := p.x0
  m := seed.1
  v := seed.2
  accumulator := 0
  samples := 0
  rounds := 0
  proxCalls := 0

noncomputable def methodQuery (p : Public) (s : State p) : Fin 4 × Query p :=
  if s.stage > finalStage p then
    (3, (s.x, 0))
  else if s.phase = 0 then
    (2, (s.x - executionStep p • ((p.workers : ℝ)⁻¹ • ∑ i, s.v i), 0))
  else if s.phase = 1 then
    (0, (s.x, 0))
  else
    (1, (s.x, fun i => s.m i - s.v i))

noncomputable def methodUpdate (p : Public) (s : State p) (reply : Reply p) : State p :=
  if s.stage > finalStage p then
    s
  else if s.phase = 0 then
    { s with
      x := reply.1
      phase := 1
      batchDraws := 0
      accumulator := 0
      proxCalls := s.proxCalls + 1 }
  else if s.phase = 1 then
    let sums : WorkerVectors p := fun i => s.accumulator i + reply.2 i
    if s.batchDraws + 1 < batchSize p s.stage then
      { s with
        batchDraws := s.batchDraws + 1
        accumulator := sums
        samples := s.samples + 1 }
    else
      { s with
        m := fun i =>
          (1 - momentum p s.stage) • s.m i +
          momentum p s.stage •
            ((batchSize p s.stage : ℝ)⁻¹ • sums i +
              regularization p s.stage • (s.x - p.x0))
        phase := 2
        batchDraws := 0
        accumulator := 0
        samples := s.samples + 1 }
  else
    let compressed : WorkerVectors p := fun i => s.v i + reply.2 i
    if s.iteration + 1 < stageLength p s.stage then
      { s with
        iteration := s.iteration + 1
        phase := 0
        v := compressed
        rounds := s.rounds + 1 }
    else
      { s with
        stage := s.stage + 1
        iteration := 0
        phase := 0
        v := compressed
        rounds := s.rounds + 1 }

noncomputable def methodOutput {p : Public} (s : State p) : Output p :=
  (s.x, (s.samples, (s.rounds, s.proxCalls)))

noncomputable def method (p : Public) : Algorithm (Query p) (Reply p) (Output p) 4 where
  Seed := InitialMemories p
  law := p.initialLaw
  State := State p
  initial := initialState p
  query := methodQuery p
  update := methodUpdate p
  output := methodOutput

structure ProblemAssumptions (p : Public) (I : Instance p) : Prop where
  localNonnegative : ∀ i, 0 ≤ I.localL i
  localConvex : ∀ i, ConvexOn ℝ Set.univ (I.f i)
  localGradient : ∀ i x, HasGradientAt (I.f i) (gradient (I.f i) x) x
  localSmooth : ∀ i x y,
    ‖gradient (I.f i) x - gradient (I.f i) y‖ ≤ I.localL i * ‖x - y‖
  rmsSmoothness : p.L = Real.sqrt ((p.workers : ℝ)⁻¹ * ∑ i, I.localL i ^ 2)
  regularizerNoBottom : ∀ x, I.ψ x ≠ ⊥
  regularizerConvex : Convex ℝ {z : Point p × ℝ | I.ψ z.1 ≤ (z.2 : EReal)}
  regularizerClosed : IsClosed {z : Point p × ℝ | I.ψ z.1 ≤ (z.2 : EReal)}
  initialFinite : I.ψ p.x0 ≠ ⊤
  optimumFinite : I.ψ I.xstar ≠ ⊤
  optimum : ∀ x, objective I I.xstar ≤ objective I x
  distance : ‖p.x0 - I.xstar‖ ≤ p.R
  proximalMeasurable : ∀ τ, 0 < τ → Measurable (I.prox τ)
  proximalFinite : ∀ τ, 0 < τ → ∀ u, I.ψ (I.prox τ u) ≠ ⊤
  proximalMinimizer : ∀ τ, 0 < τ → ∀ u z,
    I.ψ (I.prox τ u) + ((‖I.prox τ u - u‖ ^ 2 / (2 * τ) : ℝ) : EReal) ≤
      I.ψ z + ((‖z - u‖ ^ 2 / (2 * τ) : ℝ) : EReal)
  compressionInitiallyIntegrable : ∀ i,
    Integrable (fun z : InitialMemories p => ‖z.2 i - z.1 i‖ ^ 2)
      (p.initialLaw : Measure _)
  momentumInitiallyIntegrable : ∀ i,
    Integrable (fun z : InitialMemories p => ‖z.1 i - gradient (I.f i) p.x0‖ ^ 2)
      (p.initialLaw : Measure _)
  initializationBound :
    8192 * (initialGap I + p.L * p.R ^ 2 +
      (initialCompressionError p + initialMomentumError I) / p.L) ≤ p.H

abbrev Tape {p : Public} (O : Oracle (Query p) (Reply p) 4) :=
  (k : ℕ) → O.Seed k

abbrev Randomness (p : Public) (O : Oracle (Query p) (Reply p) 4) :=
  InitialMemories p × Tape O

noncomputable def executionMeasure (p : Public)
    (O : Oracle (Query p) (Reply p) 4) : Measure (Randomness p O) :=
  (p.initialLaw : Measure _).prod (O.law : Measure _)

noncomputable def pastSpace (p : Public) (O : Oracle (Query p) (Reply p) 4)
    (k : ℕ) : MeasurableSpace (Randomness p O) :=
  MeasurableSpace.comap
    (fun ω : Randomness p O => (ω.1, fun j : Fin k => ω.2 j.val))
    inferInstance

noncomputable def response {p : Public} (O : Oracle (Query p) (Reply p) 4)
    (h : History p) (request : Fin 4 × Query p) (ξ : Tape O) : Reply p :=
  O.answer h request (ξ h.length)

structure OracleAssumptions (p : Public) (I : Instance p)
    (O : Oracle (Query p) (Reply p) 4) : Prop where
  jointMeasurability :
    Measurable (fun z : (History p × (Fin 4 × Query p)) × Tape O =>
      response O z.1.1 z.1.2 z.2)
  gradientMarginals : ∀ (h : History p) (i : Fin p.workers),
    LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient
      (Point p) (Tape O) (O.law : Measure _) (I.f i)
      (fun x ξ => (response O h (0, (x, 0)) ξ).2 i) p.σ
  conditionalGradient :
    ∀ (k : ℕ) (h : Randomness p O → History p)
      (x : Randomness p O → Point p),
      @Measurable _ _ (pastSpace p O k) inferInstance h →
      @Measurable _ _ (pastSpace p O k) inferInstance x →
      (∀ ω, (h ω).length = k) →
      Integrable (fun ω => ‖x ω‖ ^ 2) (executionMeasure p O) →
      ∀ i,
        Integrable
          (fun ω => (response O (h ω) (0, (x ω, 0)) ω.2).2 i)
          (executionMeasure p O) ∧
        Integrable
          (fun ω => ‖(response O (h ω) (0, (x ω, 0)) ω.2).2 i -
            gradient (I.f i) (x ω)‖ ^ 2)
          (executionMeasure p O) ∧
        (MeasureTheory.condExp (pastSpace p O k) (executionMeasure p O)
          (fun ω => (response O (h ω) (0, (x ω, 0)) ω.2).2 i)
          =ᵐ[executionMeasure p O] fun ω => gradient (I.f i) (x ω)) ∧
        (∀ᵐ ω ∂(executionMeasure p O),
          MeasureTheory.condExp (pastSpace p O k) (executionMeasure p O)
            (fun ω' => ‖(response O (h ω') (0, (x ω', 0)) ω'.2).2 i -
              gradient (I.f i) (x ω')‖ ^ 2) ω ≤ p.σ ^ 2)
  compressionMarginals : ∀ (h : History p) (x : Point p) (z : WorkerVectors p) (i : Fin p.workers),
    Integrable (fun ξ => ‖(response O h (1, (x, z)) ξ).2 i - z i‖ ^ 2)
      (O.law : Measure _) ∧
    (∫ ξ, ‖(response O h (1, (x, z)) ξ).2 i - z i‖ ^ 2
      ∂(O.law : Measure _)) ≤ (1 - p.δ) * ‖z i‖ ^ 2
  conditionalCompression :
    ∀ (k : ℕ) (h : Randomness p O → History p)
      (x : Randomness p O → Point p)
      (z : Randomness p O → WorkerVectors p),
      @Measurable _ _ (pastSpace p O k) inferInstance h →
      @Measurable _ _ (pastSpace p O k) inferInstance x →
      @Measurable _ _ (pastSpace p O k) inferInstance z →
      (∀ ω, (h ω).length = k) →
      (∀ i, Integrable (fun ω => ‖z ω i‖ ^ 2) (executionMeasure p O)) →
      ∀ i,
        Integrable
          (fun ω => ‖(response O (h ω) (1, (x ω, z ω)) ω.2).2 i - z ω i‖ ^ 2)
          (executionMeasure p O) ∧
        (∀ᵐ ω ∂(executionMeasure p O),
          MeasureTheory.condExp (pastSpace p O k) (executionMeasure p O)
            (fun ω' => ‖(response O (h ω') (1, (x ω', z ω')) ω'.2).2 i -
              z ω' i‖ ^ 2) ω ≤ (1 - p.δ) * ‖z ω i‖ ^ 2)
  exactProximal : ∀ (h : History p) (x : Point p) (ξ : O.Seed h.length),
    (O.answer h (2, (x, 0)) ξ).1 = I.prox (executionStep p) x

abbrev spec : Setup where
  numOracles := 4
  Params := Params
  Public := Public
  Instance := Instance
  Query := Query
  Reply := Reply
  Output := Output
  publicInput p := p
  valid q := 0 < q.workers ∧ 0 < q.L ∧ 0 < q.R ∧ 0 ≤ q.σ ∧
    0 < q.δ ∧ q.δ ≤ 1 ∧ 0 < q.ε ∧ q.ε ≤ q.L * q.R ^ 2 ∧ 0 ≤ q.H
  admissible q I O := ProblemAssumptions q I ∧ OracleAssumptions q I O
  successful q I output P :=
    Measurable output ∧
    (∀ᵐ ω ∂(P : Measure _), I.ψ (output ω).1 ≠ ⊤) ∧
    Integrable (fun ω => finiteObjective I (output ω).1 - finiteObjective I I.xstar)
      (P : Measure _) ∧
    (∫ ω, finiteObjective I (output ω).1 - finiteObjective I I.xstar
      ∂(P : Measure _)) ≤ q.ε ∧
    (∀ᵐ ω ∂(P : Measure _),
      (output ω).2.1 = samplesPerWorker q ∧
      (output ω).2.2.1 = iterationCount q ∧
      (output ω).2.2.2 = iterationCount q)
  allowedAlgorithm p A := A = method p

end LongTails.Setups.StochasticProximalEf21
