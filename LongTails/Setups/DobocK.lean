import LongTails.Algorithms.DobocK
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic

open scoped RealInnerProductSpace

namespace LongTails.Setups.DobocK

open OracleTemplate OracleTemplate.DobocK

structure Params extends OracleTemplate.DobocK.Public where
  m : ℝ
  M : ℝ
  L : ℝ
  k : ℕ

def Network (q : OracleTemplate.DobocK.Public) : Prop :=
  0 < q.n ∧
  (∀ i j, q.W i j = q.W j i) ∧
  (∀ i j, 0 ≤ q.W i j) ∧
  (∀ i, ∑ j, q.W i j = 1) ∧
  (∀ j, ∑ i, q.W i j = 1) ∧
  (∀ i j, i ≠ j → (q.W i j = 0 ↔ ¬ q.G.Adj i j)) ∧
  (∀ i, q.W i i = 1 - ∑ j ∈ q.G.neighborFinset i, q.W i j ∧ 0 < q.W i i)

noncomputable def penalty (q : OracleTemplate.DobocK.Public)
    (f : Fin q.n → EuclideanSpace ℝ (Fin q.dim) → ℝ) (x : Stacked q.n q.dim) : ℝ :=
  ∑ i, f i (x i) + 1 / (2 * q.lam) * ⟪x, x - mix q x⟫

noncomputable def penaltyGradient (q : OracleTemplate.DobocK.Public)
    (f : Fin q.n → EuclideanSpace ℝ (Fin q.dim) → ℝ) (x : Stacked q.n q.dim) : Stacked q.n q.dim :=
  WithLp.toLp 2 (fun i => gradient (f i) (x i) + (1 / q.lam) • (x i - mix q x i))

noncomputable def penaltyHessian (q : OracleTemplate.DobocK.Public)
    (f : Fin q.n → EuclideanSpace ℝ (Fin q.dim) → ℝ) (x v : Stacked q.n q.dim) : Stacked q.n q.dim :=
  WithLp.toLp 2 (fun i => fderiv ℝ (gradient (f i)) (x i) (v i) + (1 / q.lam) • (v i - mix q v i))

noncomputable def wmin (q : OracleTemplate.DobocK.Public) : ℝ := ⨅ i, q.W i i

noncomputable def a (p : Params) : ℝ := p.M + 2 * (1 - wmin p.toPublic) / p.lam

def Assumption1 (q : OracleTemplate.DobocK.Public) (m M : ℝ)
    (f : Fin q.n → EuclideanSpace ℝ (Fin q.dim) → ℝ) : Prop :=
  ∀ i, ContDiff ℝ 2 (f i) ∧
    ∀ x v, m * ‖v‖ ^ 2 ≤ ⟪fderiv ℝ (gradient (f i)) x v, v⟫ ∧
      ⟪fderiv ℝ (gradient (f i)) x v, v⟫ ≤ M * ‖v‖ ^ 2

def Assumption2 (q : OracleTemplate.DobocK.Public) (L : ℝ)
    (f : Fin q.n → EuclideanSpace ℝ (Fin q.dim) → ℝ) : Prop :=
  ∀ i x y, ‖fderiv ℝ (gradient (f i)) x - fderiv ℝ (gradient (f i)) y‖ ≤ L * ‖x - y‖

def StepSizeLemma5 (p : Params) : Prop :=
  p.η < 1 ∧ p.η < 1 / a p ∧ p.η < 2 * p.m / (a p ^ 2 * (p.K : ℝ) ^ 2)

def StepSizeTheorem2 (p : Params) (Δ : ℝ) : Prop :=
  p.η < p.m / (a p ^ 2 * (p.K : ℝ) ^ 2) ∧
    p.η ^ 2 * (a p ^ 4 * (2 * a p) ^ (3 / 2 : ℝ) * (p.K : ℝ) ^ 3 * p.L * Δ ^ (1 / 2 : ℝ)) < 6 * p.m ^ 5

noncomputable def rate (p : Params) (Δ : ℝ) : ℝ :=
  (2 * p.m ^ 2 * p.η - p.m * a p ^ 2 * p.η ^ 2 * (p.K : ℝ) ^ 2) / a p -
    a p ^ 3 * (2 * a p) ^ (3 / 2 : ℝ) * p.η ^ 3 * (p.K : ℝ) ^ 3 * p.L / (6 * p.m ^ 3) * Δ ^ (1 / 2 : ℝ)

abbrev spec : Setup where
  Params := Params
  Public := OracleTemplate.DobocK.Public
  Instance q := Fin q.n → EuclideanSpace ℝ (Fin q.dim) → ℝ
  Query q := Stacked q.n q.dim
  Reply q := LocalReply q.n q.dim
  Output q := Stacked q.n q.dim
  publicInput := Params.toPublic
  valid p := Network p.toPublic ∧ 0 < p.lam ∧ 0 < p.η ∧ 1 ≤ p.K ∧ 0 < p.m ∧ p.m ≤ p.M ∧
    0 ≤ p.L ∧ StepSizeLemma5 p
  admissible p f O :=
    Assumption1 p.toPublic p.m p.M f ∧ Assumption2 p.toPublic p.L f ∧
    (∀ k x seed, O.answer k (0, x) seed = localOracle p.toPublic f x) ∧
    ∀ xstar, IsMinOn (penalty p.toPublic f) Set.univ xstar →
      StepSizeTheorem2 p (penalty p.toPublic f p.x0 - penalty p.toPublic f xstar)
  successful p f output P :=
    ∃ xstar, IsMinOn (penalty p.toPublic f) Set.univ xstar ∧
      0 < rate p (penalty p.toPublic f p.x0 - penalty p.toPublic f xstar) ∧
      rate p (penalty p.toPublic f p.x0 - penalty p.toPublic f xstar) < 1 ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _),
        penalty p.toPublic f (output ω) - penalty p.toPublic f xstar ≤
          (1 - rate p (penalty p.toPublic f p.x0 - penalty p.toPublic f xstar)) ^ p.k *
            (penalty p.toPublic f p.x0 - penalty p.toPublic f xstar)
  allowedAlgorithm q A := A = dobocK q

attribute [local simp] penaltyGradient penaltyHessian

end LongTails.Setups.DobocK
