import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Basic.ENNReal.Inv

open MeasureTheory OracleTemplate
open scoped BigOperators ENNReal NNReal

namespace outputs.Proofs.FreyaModel

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def objective {d m : ℕ} (f : Fin m → Space d → ℝ) (x : Space d) : ℝ :=
  (m : ℝ)⁻¹ * ∑ i, f i x

structure RegularObjective {d m : ℕ} (f : Fin m → Space d → ℝ)
    (x0 : Space d) (lower Lminus Lplus Lpm Δ : ℝ) : Prop where
  differentiable : ∀ i, Differentiable ℝ (f i)
  lower_bound : ∀ x, lower ≤ objective f x
  smooth : ∀ x y, ‖gradient (objective f) x - gradient (objective f) y‖ ≤
    Lminus * ‖x - y‖
  mean_square : ∀ x y, (m : ℝ)⁻¹ * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
    Lplus ^ 2 * ‖x - y‖ ^ 2
  centered : ∀ x y, (m : ℝ)⁻¹ * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) -
    ‖gradient (objective f) x - gradient (objective f) y‖ ^ 2 ≤ Lpm ^ 2 * ‖x - y‖ ^ 2
  gap : objective f x0 - lower ≤ Δ

def JobKind (d : ℕ) := Space d ⊕ (Space d × Space d)

instance instMeasurableSpaceJobKind (d : ℕ) : MeasurableSpace (JobKind d) :=
  inferInstanceAs (MeasurableSpace (Space d ⊕ (Space d × Space d)))

instance instMeasurableSpaceOption {α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Option α) :=
  MeasurableSpace.comap (fun x => match x with
    | none => Sum.inl ()
    | some a => Sum.inr a) (inferInstance : MeasurableSpace (Unit ⊕ α))

structure Job (d m : ℕ) where
  component : Fin m
  kind : JobKind d
  started : ℝ≥0
  id : ℕ

instance instMeasurableSpaceJob (d m : ℕ) : MeasurableSpace (Job d m) :=
  MeasurableSpace.comap (fun j => (j.component, j.kind, j.started, j.id)) inferInstance

structure Request (d m n : ℕ) where
  clock : ℝ≥0
  pending : Fin n → Option (Job d m)

instance instMeasurableSpaceRequest (d m n : ℕ) : MeasurableSpace (Request d m n) :=
  MeasurableSpace.comap (fun r => (r.clock, r.pending)) inferInstance

def Reply (d n : ℕ) := Option (Fin n × ℕ × ℝ≥0 × Space d)

instance instMeasurableSpaceReply (d n : ℕ) : MeasurableSpace (Reply d n) :=
  inferInstanceAs (MeasurableSpace (Option (Fin n × ℕ × ℝ≥0 × Space d)))

noncomputable def jobValue {d m : ℕ} (f : Fin m → Space d → ℝ) (j : Job d m) :
    Space d :=
  match j.kind with
  | Sum.inl x => gradient (f j.component) x
  | Sum.inr (x, y) => gradient (f j.component) x - gradient (f j.component) y

def jobWork {d m : ℕ} (j : Job d m) : ℕ :=
  match j.kind with
  | Sum.inl _ => 1
  | Sum.inr _ => 2

noncomputable def deadline {d m n : ℕ} (τ : Fin n → ℝ≥0∞) (j : Job d m)
    (i : Fin n) : ℝ≥0∞ :=
  j.started + (jobWork j : ℝ≥0∞) * τ i

def legalRequest {d m n : ℕ} (τ : Fin n → ℝ≥0∞) (r : Request d m n) : Prop :=
  (∃ i j, r.pending i = some j) ∧
    ∀ i j, r.pending i = some j → j.started ≤ r.clock ∧ (r.clock : ℝ≥0∞) ≤ deadline τ j i

def PrimitiveService {d m n : ℕ} (f : Fin m → Space d → ℝ) (τ : Fin n → ℝ≥0∞)
    (O : Oracle (Option (Request d m n)) (Reply d n) 1) : Prop :=
  (∀ k, Measurable (fun z : (Fin 1 × Option (Request d m n)) × O.Seed k =>
    O.answer k z.1 z.2)) ∧
  ∀ᵐ ω ∂(O.law : Measure ((k : ℕ) → O.Seed k)), ∀ k,
    O.answer k (0, none) (ω k) = none ∧
    ∀ r, legalRequest τ r → ∃ i j c,
      r.pending i = some j ∧
      O.answer k (0, some r) (ω k) = some (i, j.id, c, jobValue f j) ∧
      r.clock ≤ c ∧ ∀ i' j', r.pending i' = some j' → (c : ℝ≥0∞) ≤ deadline τ j' i'

def FreshAssignments {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (history : ℕ → MeasurableSpace Ω) (remaining : ℕ → Ω → Finset ℕ)
    (chosen : ℕ → Ω → ℕ) : Prop :=
  ∀ k, history k ≤ ‹MeasurableSpace Ω› ∧ Measurable[history k] (remaining k) ∧
    Measurable (chosen k) ∧ ∀ E, MeasurableSet[history k] E → ∀ j,
      (∫⁻ ω in E, if (remaining k ω).Nonempty ∧ chosen k ω = j
        then (1 : ℝ≥0∞) else 0 ∂(P : Measure Ω)) =
      ∫⁻ ω in E, if j ∈ remaining k ω then ((remaining k ω).card : ℝ≥0∞)⁻¹
        else 0 ∂(P : Measure Ω)

def LiveService {d m n : ℕ} (τ : Fin n → ℝ≥0∞)
    (O : Oracle (Option (Request d m n)) (Reply d n) 1) : Prop :=
  ∀ᵐ ω ∂(O.law : Measure ((k : ℕ) → O.Seed k)), ∀ k r, legalRequest τ r → ∃ i j c v,
    r.pending i = some j ∧ O.answer k (0, some r) (ω k) = some (i, j.id, c, v) ∧
      r.clock ≤ c

noncomputable def equilibriumTime {n : ℕ} (τ : Fin n → ℝ≥0∞) (r : ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ j : Fin n, (r + (j.val + 1 : ℕ)) / ∑ i ∈ Finset.Iic j, (τ i)⁻¹

def largeSample (m n : ℕ) : Prop := (n : ℝ) * Real.log n ≤ m

end outputs.Proofs.FreyaModel
