import LongTails.TemplateDistributed
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Data.List.MinMax

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Setups.DistributedJacobianStrongGrowth

open DistributedTemplate
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex

structure Params where
  d : ℕ
  n : ℕ+
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  root : Fin n
  parent : Fin n → Fin n
  depth : Fin n → ℕ
  h : ℕ
  τ : Time
  l : Time
  β : Time
  L : ℝ
  μ : ℝ
  ρ : ℝ
  M : ℝ
  R : ℝ
  ε : ℝ
  x0 : EuclideanSpace ℝ (Fin d)

attribute [instance] Params.measurableΩ

abbrev Point (p : Params) := EuclideanSpace ℝ (Fin p.d)

structure Problem (p : Params) where
  F : Point p → Point p
  J : Point p → Point p →L[ℝ] Point p
  solution : Point p

structure Sampling (p : Params) where
  Seed : Type
  [measurableSeed : MeasurableSpace Seed]
  law : ProbabilityMeasure Seed
  marginal : ProbabilityMeasure p.Ω
  sample : ℕ → Seed → p.Ω
  iid : IID sample (marginal : Measure _) (law : Measure _)

attribute [instance] Sampling.measurableSeed

structure CommReply (p : Params) where
  source : Fin p.n
  bits : List Bool

structure ComputationState (p : Params) where
  pending : Option (Time × Point p)
  samples : ℕ → p.Ω
  used : ℕ

structure CommunicationState (p : Params) where
  messages : Fin p.n → Fin p.n → Option (Time × List Bool)

def adjacent (p : Params) (source target : Fin p.n) : Prop :=
  source ≠ target ∧ (p.parent source = target ∨ p.parent target = source)

noncomputable def computation (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) :
    ComputationOracle (Point p) (Point p) S.Seed p.n where
  State := ComputationState p
  initial _ seed := ⟨none, fun k => S.sample k seed, 0⟩
  submit _ s time x :=
    match s.pending with
    | some _ => s
    | none => { s with pending := some (time + p.τ, x) }
  answer i s time :=
    match s.pending with
    | none => none
    | some (finish, x) =>
        if finish ≤ time then
          some (g i x (s.samples (p.n * s.used + i.val)),
            { s with pending := none, used := s.used + 1 })
        else none

noncomputable def communication (p : Params) (S : Sampling p) :
    CommunicationOracle (CommReply p) S.Seed p.n := by
  classical
  exact {
    State := CommunicationState p
    initial := fun _ => ⟨fun _ _ => none⟩
    submit := fun s time source query =>
      let (target, bits) := query
      if adjacent p source target then
        match s.messages source target with
        | some _ => s
        | none =>
            let finish := time + p.l + p.β * bits.length
            { s with messages := (Function.update s.messages source
                (Function.update (s.messages source) target (some (finish, bits)))) }
      else s
    answer := fun s time =>
      let messages := (List.finRange p.n).flatMap fun source =>
        (List.finRange p.n).filterMap fun target =>
          (s.messages source target).map fun (finish, bits) => (finish, source, target, bits)
      match List.argmin Prod.fst messages with
      | none => none
      | some (finish, source, target, bits) =>
          if finish ≤ time then
            some ((target, ⟨source, bits⟩),
              { s with messages := (Function.update s.messages source
                  (Function.update (s.messages source) target none)) })
          else none }

noncomputable def system (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) :
    Oracle (Point p) (Point p) (CommReply p) p.n where
  Seed := S.Seed
  law := S.law
  computation := computation p g S
  communication := communication p S

def valid (p : Params) : Prop :=
  0 < p.d ∧ p.parent p.root = p.root ∧ p.depth p.root = 0 ∧
    (∀ i, i ≠ p.root → p.depth (p.parent i) + 1 = p.depth i) ∧
    (∀ i, p.depth i ≤ p.h) ∧ 0 < p.τ ∧
    0 < p.μ ∧ p.μ ≤ p.L ∧ 1 ≤ p.ρ ∧ 0 ≤ p.M ∧ 0 < p.R ∧ 0 < p.ε ∧ Nonempty p.Ω

def problemAssumptions (p : Params) (I : Problem p) : Prop :=
  (∀ x, HasFDerivAt I.F (I.J x) x) ∧
    (∀ x y, ‖I.F x - I.F y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ x y, ‖I.J x - I.J y‖ ≤ p.M * ‖x - y‖) ∧
    I.F I.solution = 0 ∧ ‖p.x0 - I.solution‖ ≤ p.R ∧
    (∀ x, p.μ * ‖x - I.solution‖ ^ 2 ≤ ⟪I.F x, x - I.solution⟫)

def oracleAssumptions (p : Params) (I : Problem p)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p) : Prop :=
  (∀ i, Measurable (Function.uncurry (g i))) ∧
    (∀ i x, Integrable (g i x) (S.marginal : Measure _)) ∧
    (∀ i x, Integrable (fun ω => ‖g i x ω‖ ^ 2) (S.marginal : Measure _)) ∧
    (∀ i x, (∫ ω, g i x ω ∂(S.marginal : Measure _)) = I.F x) ∧
    (∀ i x, (∫ ω, ‖g i x ω‖ ^ 2 ∂(S.marginal : Measure _)) ≤ p.ρ * ‖I.F x‖ ^ 2)

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  numWorkers p := p.n
  Instance := Problem
  ComputeQuery := Point
  ComputeReply := Point
  CommReply := CommReply
  Output := Point
  publicInput := id
  valid := valid
  admissible p I O := problemAssumptions p I ∧
    ∃ (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p),
      O = system p g S ∧ oracleAssumptions p I g S
  successful p I output P := Measurable output ∧
    Integrable (fun ω => ‖output ω - I.solution‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖output ω - I.solution‖ ^ 2 ∂(P : Measure _)) ≤ p.ε ^ 2

end LongTails.Setups.DistributedJacobianStrongGrowth
