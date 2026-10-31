import LongTails.Template
import LongTails.Setups.FreyaPageUniform
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory OracleTemplate
open scoped ENNReal NNReal

namespace LongTails.Setups.FreyaIndependence

open LongTails.Setups.FreyaModel LongTails.Algorithms.FreyaInputs
open LongTails.Algorithms.FreyaRandomness LongTails.Algorithms.FreyaPage

structure BatchSchedule (n : ℕ) where
  duration : Fin n → ℕ → ℝ≥0∞
  priority : ℕ → Fin n → ℕ

instance instMeasurableSpaceBatchSchedule (n : ℕ) : MeasurableSpace (BatchSchedule n) :=
  MeasurableSpace.comap (fun γ => (γ.duration, γ.priority)) inferInstance

def ScheduleRealization (q : Raw) (f : Fin q.m → Space q.d → ℝ)
    (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (seed : Seed q.K) (ω : (k : ℕ) → O.Seed k) (batch : ℕ)
    (γ : BatchSchedule q.n) : Prop :=
  ∀ call, call ≤ eventLimit q →
    let s := trace q O seed ω call
    s.iteration = batch →
      (∀ after i j, batchJobs q O seed ω batch call after i = some j →
        γ.duration i j.id ≤ (jobWork j : ℝ≥0∞) * τ i) ∧
      ∀ r, (query q s).2 = some r → ∃ i j c,
        r.pending i = some j ∧
        replyAt q O seed ω call (query q s) = some (i, j.id, c, jobValue f j) ∧
        r.clock ≤ c ∧ (c : ℝ≥0∞) = (j.started : ℝ≥0∞) + γ.duration i j.id ∧
        ∀ i' j', r.pending i' = some j' →
          (r.clock : ℝ≥0∞) ≤ (j'.started : ℝ≥0∞) + γ.duration i' j'.id ∧
          (c : ℝ≥0∞) ≤ (j'.started : ℝ≥0∞) + γ.duration i' j'.id ∧
          ((c : ℝ≥0∞) = (j'.started : ℝ≥0∞) + γ.duration i' j'.id →
            γ.priority call i < γ.priority call i' ∨
              (γ.priority call i = γ.priority call i' ∧ i.val ≤ i'.val))

def isDifferenceBatch (q : Raw)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1)
    (z : Seed q.K × ((k : ℕ) → O.Seed k)) (batch : ℕ) : Prop :=
  ∃ x y c firstID, invocation q O z.1 z.2 batch = some (false, x, y, c, firstID)

noncomputable def batchScheduleIndependent (q : Raw) (f : Fin q.m → Space q.d → ℝ)
    (τ : Fin q.n → ℝ≥0∞)
    (O : Oracle (Option (Request q.d q.m q.n)) (Reply q.d q.n) 1) : Prop := by
  classical
  let Ω := Seed q.K × ((k : ℕ) → O.Seed k)
  let mΩ : MeasurableSpace Ω := inferInstance
  let P : @Measure Ω mΩ :=
    (seedLaw q.ρ q.K : Measure (Seed q.K)).prod
      (O.law : Measure ((k : ℕ) → O.Seed k))
  exact ∀ batch,
    let H := historyBefore q O batch
    H ≤ mΩ ∧
      (∀ j, Measurable[mΩ] (fun z : Ω => batchLabels q z.1 batch j)) ∧
      ∃ Γ : Ω → BatchSchedule q.n,
        Measurable[mΩ] Γ ∧
        (∀ᵐ z ∂P, ScheduleRealization q f τ O z.1 z.2 batch (Γ z)) ∧
        ∀ U : Set (BatchSchedule q.n), MeasurableSet U →
          ∀ F : Finset ℕ, ∀ labels : ℕ → Option (Fin q.m),
            ∀ᵐ z ∂P, isDifferenceBatch q O z batch →
              (P[fun w =>
                if Γ w ∈ U ∧ (∀ j ∈ F, batchLabels q w.1 batch j = labels j)
                then (1 : ℝ) else 0 | H]) z =
              (P[fun w => if Γ w ∈ U then (1 : ℝ) else 0 | H]) z *
                (P[fun w =>
                  if ∀ j ∈ F, batchLabels q w.1 batch j = labels j
                  then (1 : ℝ) else 0 | H]) z

end LongTails.Setups.FreyaIndependence

open MeasureTheory OracleTemplate
open scoped BigOperators ENNReal NNReal

namespace LongTails.Setups.FreyaPageIterations

open LongTails.Setups.FreyaModel

structure Params where
  d : ℕ
  m : ℕ
  n : ℕ
  Lminus : ℝ
  Lpm : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : Space d
  S : ℕ
  ρ : ℝ
  τ : Fin n → ℝ≥0∞
  Lplus : ℝ
  lower : ℝ

def publicInput (p : Params) : LongTails.Algorithms.FreyaInputs.Family where
  d := p.d
  m := p.m
  Lminus := p.Lminus
  Lpm := p.Lpm
  Δ := p.Δ
  ε := p.ε
  x0 := p.x0
  n := p.n
  S := p.S
  ρ := p.ρ

noncomputable abbrev spec : Setup where
  Params := Params
  Public := LongTails.Algorithms.FreyaInputs.Family
  Instance p := Fin p.m → Space p.d → ℝ
  Query p := Option (Request p.d p.m p.n)
  Reply p := Reply p.d p.n
  Output p := Space p.d
  publicInput := publicInput
  valid p := 0 < p.m ∧ 0 ≤ p.Lminus ∧ 0 ≤ p.Lplus ∧ 0 ≤ p.Lpm ∧
    0 ≤ p.Δ ∧ 0 < p.ε ∧
    0 < p.S ∧ 0 < p.ρ ∧ p.ρ ≤ 1 ∧ 0 < p.n ∧ Monotone p.τ
  admissible p f O :=
    (∀ i, Differentiable ℝ (f i)) ∧
    (∀ x, p.lower ≤ objective f x) ∧
    objective f p.x0 - p.lower ≤ p.Δ ∧
    (∀ x y, ‖gradient (objective f) x - gradient (objective f) y‖ ≤
      p.Lminus * ‖x - y‖) ∧
    (∀ x y, (p.m : ℝ)⁻¹ * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lplus ^ 2 * ‖x - y‖ ^ 2) ∧
    (∀ x y, (p.m : ℝ)⁻¹ * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) -
      ‖gradient (objective f) x - gradient (objective f) y‖ ^ 2 ≤
      p.Lpm ^ 2 * ‖x - y‖ ^ 2) ∧
    PrimitiveService f p.τ O ∧
    LongTails.Setups.FreyaIndependence.batchScheduleIndependent
      (LongTails.Algorithms.FreyaTuning.familyRaw (publicInput p) false) f p.τ O
  successful p f output P :=
    Integrable (fun ω => ‖gradient (objective f) (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient (objective f) (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε
  allowedAlgorithm q A := A = LongTails.Algorithms.FreyaTuning.iterations q

end LongTails.Setups.FreyaPageIterations
