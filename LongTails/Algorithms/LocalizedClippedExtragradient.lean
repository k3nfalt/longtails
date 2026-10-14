import LongTails.Algorithms.ClippedExtragradient
import LongTails.Algorithms.ContinuizedQuasar
import LongTails.Algorithms.QueryPlan
import LongTails.Algorithms.RobustGradientEstimator
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

open scoped BigOperators

namespace OracleTemplate.ClippedExtragradient

structure Tuning where
  L0 : ℝ
  L1 : ℝ
  R : ℝ
  σ : ℝ
  ε : ℝ
  δ : ℝ

noncomputable def stageCount (p : Tuning) : ℕ :=
  ⌈Real.log (1 + 32 * (p.L0 * p.R / p.ε + p.L1 * p.R)) / Real.log 2⌉₊ + 1

noncomputable def repetitions (p : Tuning) : ℕ :=
  ⌈Real.log ((stageCount p : ℝ) / p.δ) / Real.log 2⌉₊ + 1

noncomputable def regularization (p : Tuning) (s : ℕ) : ℝ :=
  2 ^ s * p.ε / (8 * stageCount p * p.R)

noncomputable def radius (p : Tuning) (s : ℕ) : ℝ := p.R / 2 ^ s

noncomputable def clippingScale (p : Tuning) (s : ℕ) : ℝ :=
  p.L1 + 1 / radius p s

noncomputable def localScale (p : Tuning) (s : ℕ) : ℝ :=
  p.L0 + p.L1 * p.ε + regularization p s *
    (2 + 6 * p.L1 * radius p s + (p.L1 * radius p s) ^ 2)

noncomputable def batchSize (p : Tuning) (s : ℕ) : ℕ :=
  max 1 ⌈2 ^ 20 * p.σ ^ 2 / (regularization p s * localScale p s * radius p s ^ 2)⌉₊

noncomputable def innerSteps (p : Tuning) (s : ℕ) : ℕ :=
  ⌈2 ^ 16 * localScale p s / regularization p s⌉₊

noncomputable def stageCalls (p : Tuning) (s : ℕ) : ℕ :=
  (batchSize p s + batchSize p s) * innerSteps p s * repetitions p

noncomputable def remainingCalls (p : Tuning) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | s, k + 1 => remainingCalls p (s + 1) k + stageCalls p s

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def batchStep {Ω : Type*} (n : ℕ) (b S d r : ℝ)
    (anchor center : E) (g : E → Ω → E) (x : E)
    (samples : (Fin n → Ω) × (Fin n → Ω)) : E :=
  let first := regularizedReply r anchor x ((1 / (n : ℝ)) • ∑ i, g x (samples.1 i))
  let γ := stepSize b S first
  let y := halfStep b S x first
  finishStep d γ center x (regularizedReply r anchor y
    ((1 / (n : ℝ)) • ∑ i, g y (samples.2 i)))

abbrev TrialSamples (p : Tuning) (s : ℕ) (Ω : Type*) :=
  Fin (innerSteps p s) → (Fin (batchSize p s) → Ω) × (Fin (batchSize p s) → Ω)

abbrev StageSamples (p : Tuning) (s : ℕ) (Ω : Type*) :=
  Fin (repetitions p) → TrialSamples p s Ω

noncomputable def trialOutput {Ω : Type*} (p : Tuning) (s : ℕ)
    (anchor center : E) (g : E → Ω → E) (samples : TrialSamples p s Ω) : E :=
  ContinuizedSimilarQuasar.iterateSamples
    (batchStep (batchSize p s) (clippingScale p s) (localScale p s)
      (radius p s) (regularization p s) anchor center g)
    (innerSteps p s) center samples

noncomputable def confidenceOutput {Ω : Type*} (p : Tuning) (s : ℕ)
    (anchor center : E) (g : E → Ω → E) (samples : StageSamples p s Ω) : E :=
  RobustGradient.centeredClip (2 * radius p s) center
    (RobustGradient.pilotCenter (radius p s) (fun i => trialOutput p s anchor center g (samples i)))

def collectPlan (x : E) : (n : ℕ) → QueryPlan E E (Fin n → E) n
  | 0 => .done (fun i => Fin.elim0 i)
  | n + 1 => .ask x (fun value => QueryPlan.map (Fin.cons value) (collectPlan x n))

noncomputable def meanPlan (n : ℕ) (x : E) : QueryPlan E E E n :=
  QueryPlan.map (fun values => (n : ℝ)⁻¹ • ∑ i, values i) (collectPlan x n)

noncomputable def stepPlan (p : Tuning) (s : ℕ) (anchor center x : E) :
    QueryPlan E E E (batchSize p s + batchSize p s) :=
  QueryPlan.bind (meanPlan (batchSize p s) x) (fun first =>
    let g := regularizedReply (regularization p s) anchor x first
    let γ := stepSize (clippingScale p s) (localScale p s) g
    let y := halfStep (clippingScale p s) (localScale p s) x g
    QueryPlan.map (fun second => finishStep (radius p s) γ center x
      (regularizedReply (regularization p s) anchor y second))
      (meanPlan (batchSize p s) y))

noncomputable def innerPlan (p : Tuning) (s : ℕ) (anchor center : E) :
    (n : ℕ) → E → QueryPlan E E E ((batchSize p s + batchSize p s) * n)
  | 0, x => .done x
  | n + 1, x => QueryPlan.bind (stepPlan p s anchor center x)
      (fun y => innerPlan p s anchor center n y)

noncomputable def confidencePlan (p : Tuning) (s : ℕ) (anchor center : E) :
    QueryPlan E E E (stageCalls p s) :=
  QueryPlan.map (fun values => RobustGradient.centeredClip (2 * radius p s) center
    (RobustGradient.pilotCenter (radius p s)
      (fun i : Fin (repetitions p) => values.getD i.val center)))
    (QueryPlan.traverse (repetitions p)
      (fun _ => innerPlan p s anchor center (innerSteps p s) center))

noncomputable def localizedPlan (p : Tuning) : (s n : ℕ) → E → E →
    QueryPlan E E E (remainingCalls p s n)
  | _, 0, _, center => .done center
  | s, n + 1, anchor, center => QueryPlan.bind (confidencePlan p s anchor center)
      (fun next => localizedPlan p (s + 1) n ((1 / 2 : ℝ) • (anchor + next)) next)

noncomputable def localizedClippedExtragradient (p : Tuning) (x0 : E) : Algorithm E E E where
  Seed := Unit
  law := ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
  State := Σ k, QueryPlan E E E k
  initial _ := if 0 < p.R then
    ⟨remainingCalls p 0 (stageCount p), localizedPlan p 0 (stageCount p) x0 x0⟩
    else ⟨0, .done x0⟩
  query := fun s => (0, (QueryPlan.query x0) s)
  update := QueryPlan.update
  output := QueryPlan.output x0

end OracleTemplate.ClippedExtragradient
