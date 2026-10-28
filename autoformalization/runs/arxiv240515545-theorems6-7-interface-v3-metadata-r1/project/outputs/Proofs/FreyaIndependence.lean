import LongTails.Template
import outputs.Algorithms.FreyaPage
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

open MeasureTheory OracleTemplate
open scoped ENNReal NNReal

namespace outputs.Proofs.FreyaIndependence

open outputs.Proofs.FreyaModel outputs.Algorithms.FreyaInputs
open outputs.Algorithms.FreyaRandomness outputs.Algorithms.FreyaPage

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
        O.answer call (query q s) (ω call) = some (i, j.id, c, jobValue f j) ∧
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

end outputs.Proofs.FreyaIndependence
