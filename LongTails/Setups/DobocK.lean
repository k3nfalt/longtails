import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic

namespace OracleTemplate.DobocK

abbrev Stacked (n dim : ℕ) : Type := PiLp 2 (fun _ : Fin n => EuclideanSpace ℝ (Fin dim))

abbrev LocalReply (n dim : ℕ) : Type :=
  Fin n → EuclideanSpace ℝ (Fin dim) × (EuclideanSpace ℝ (Fin dim) →L[ℝ] EuclideanSpace ℝ (Fin dim))

structure Public where
  n : ℕ
  dim : ℕ
  G : SimpleGraph (Fin n)
  [adjDecidable : DecidableRel G.Adj]
  W : Matrix (Fin n) (Fin n) ℝ
  lam : ℝ
  η : ℝ
  K : ℕ
  x0 : Stacked n dim

attribute [instance] Public.adjDecidable

noncomputable def mix (q : Public) (v : Stacked q.n q.dim) : Stacked q.n q.dim :=
  WithLp.toLp 2 (fun i => ∑ j ∈ insert i (q.G.neighborFinset i), q.W i j • v j)

noncomputable def localBase (q : Public) (x : Stacked q.n q.dim) (r : LocalReply q.n q.dim) :
    Stacked q.n q.dim :=
  WithLp.toLp 2 (fun i => q.η • ((r i).1 + (1 / q.lam) • (x i - mix q x i)))

noncomputable def innerStep (q : Public) (x : Stacked q.n q.dim) (r : LocalReply q.n q.dim)
    (g : Stacked q.n q.dim) : Stacked q.n q.dim :=
  WithLp.toLp 2 (fun i => localBase q x r i + (1 - q.η / q.lam) • g i - q.η • (r i).2 (g i)
    + (q.η / q.lam) • mix q g i)

noncomputable def direction (q : Public) (x : Stacked q.n q.dim) (r : LocalReply q.n q.dim) :
    Stacked q.n q.dim :=
  (innerStep q x r)^[q.K - 1] (localBase q x r)

noncomputable def step (q : Public) (x : Stacked q.n q.dim) (r : LocalReply q.n q.dim) :
    Stacked q.n q.dim :=
  x - direction q x r

noncomputable def dobocK (q : Public) :
    Algorithm (Stacked q.n q.dim) (LocalReply q.n q.dim) (Stacked q.n q.dim) 1 where
  State := Stacked q.n q.dim
  initial _ := q.x0
  query x := (0, x)
  update x r := step q x r
  output x := x

noncomputable def localOracle (q : Public) (f : Fin q.n → EuclideanSpace ℝ (Fin q.dim) → ℝ)
    (x : Stacked q.n q.dim) : LocalReply q.n q.dim :=
  fun i => (gradient (f i) (x i), fderiv ℝ (gradient (f i)) (x i))

noncomputable def iterate (q : Public) (f : Fin q.n → EuclideanSpace ℝ (Fin q.dim) → ℝ) (k : ℕ) :
    Stacked q.n q.dim :=
  (fun x => step q x (localOracle q f x))^[k] q.x0

attribute [local simp] mix innerStep direction localOracle iterate

end OracleTemplate.DobocK

namespace OracleTemplate.DobocKTuning

open OracleTemplate OracleTemplate.DobocK

structure Public where
  n : ℕ
  dim : ℕ
  G : SimpleGraph (Fin n)
  [adjDecidable : DecidableRel G.Adj]
  W : Matrix (Fin n) (Fin n) ℝ
  lam : ℝ
  m : ℝ
  M : ℝ
  L : ℝ
  Δ : ℝ
  ε : ℝ
  K : ℕ
  x0 : Stacked n dim

attribute [instance] Public.adjDecidable

noncomputable def curvatureBound (p : Public) : ℝ := p.M + 2 / p.lam

noncomputable def tuningScale (p : Public) : ℝ :=
  1 + curvatureBound p + (curvatureBound p) ^ 2 * (p.K : ℝ) ^ 2 / p.m +
    Real.sqrt ((curvatureBound p) ^ 4 * (2 * curvatureBound p) ^ (3 / 2 : ℝ) *
      (p.K : ℝ) ^ 3 * p.L * Real.sqrt p.Δ / (6 * p.m ^ 5))

noncomputable def stepSize (p : Public) : ℝ := 1 / (2 * tuningScale p)

noncomputable def contraction (p : Public) : ℝ :=
  p.m ^ 2 / (2 * curvatureBound p * tuningScale p)

noncomputable def horizon (p : Public) : ℕ :=
  ⌈2 * curvatureBound p * tuningScale p / p.m ^ 2 *
    Real.log (max 1 (p.Δ / p.ε))⌉₊

noncomputable def sourceInput (p : Public) : OracleTemplate.DobocK.Public where
  n := p.n
  dim := p.dim
  G := p.G
  adjDecidable := p.adjDecidable
  W := p.W
  lam := p.lam
  η := stepSize p
  K := p.K
  x0 := p.x0

noncomputable def algorithm (p : Public) :
    Algorithm (Stacked p.n p.dim) (LocalReply p.n p.dim) (Stacked p.n p.dim) 1 :=
  dobocK (sourceInput p)

end OracleTemplate.DobocKTuning

open scoped RealInnerProductSpace

namespace LongTails.Setups.DobocK

open OracleTemplate OracleTemplate.DobocK

structure Constants extends OracleTemplate.DobocK.Public where
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

noncomputable def a (p : Constants) : ℝ := p.M + 2 * (1 - wmin p.toPublic) / p.lam

def Assumption1 (q : OracleTemplate.DobocK.Public) (m M : ℝ)
    (f : Fin q.n → EuclideanSpace ℝ (Fin q.dim) → ℝ) : Prop :=
  ∀ i, ContDiff ℝ 2 (f i) ∧
    ∀ x v, m * ‖v‖ ^ 2 ≤ ⟪fderiv ℝ (gradient (f i)) x v, v⟫ ∧
      ⟪fderiv ℝ (gradient (f i)) x v, v⟫ ≤ M * ‖v‖ ^ 2

def Assumption2 (q : OracleTemplate.DobocK.Public) (L : ℝ)
    (f : Fin q.n → EuclideanSpace ℝ (Fin q.dim) → ℝ) : Prop :=
  ∀ i x y, ‖fderiv ℝ (gradient (f i)) x - fderiv ℝ (gradient (f i)) y‖ ≤ L * ‖x - y‖

def StepSizeLemma5 (p : Constants) : Prop :=
  p.η < 1 ∧ p.η < 1 / a p ∧ p.η < 2 * p.m / (a p ^ 2 * (p.K : ℝ) ^ 2)

def StepSizeTheorem2 (p : Constants) (Δ : ℝ) : Prop :=
  p.η < p.m / (a p ^ 2 * (p.K : ℝ) ^ 2) ∧
    p.η ^ 2 * (a p ^ 4 * (2 * a p) ^ (3 / 2 : ℝ) * (p.K : ℝ) ^ 3 * p.L * Δ ^ (1 / 2 : ℝ)) < 6 * p.m ^ 5

noncomputable def rate (p : Constants) (Δ : ℝ) : ℝ :=
  (2 * p.m ^ 2 * p.η - p.m * a p ^ 2 * p.η ^ 2 * (p.K : ℝ) ^ 2) / a p -
    a p ^ 3 * (2 * a p) ^ (3 / 2 : ℝ) * p.η ^ 3 * (p.K : ℝ) ^ 3 * p.L / (6 * p.m ^ 3) * Δ ^ (1 / 2 : ℝ)

noncomputable def constants (p : OracleTemplate.DobocKTuning.Public) : Constants where
  toPublic := OracleTemplate.DobocKTuning.sourceInput p
  m := p.m
  M := p.M
  L := p.L
  k := 0

open OracleTemplate.DobocKTuning

structure Params extends OracleTemplate.DobocKTuning.Public where
  xstar : Stacked n dim

noncomputable abbrev spec : Setup where
  Params := Params
  Public := OracleTemplate.DobocKTuning.Public
  Instance q := Fin q.n → EuclideanSpace ℝ (Fin q.dim) → ℝ
  Query q := Stacked q.n q.dim
  Reply q := LocalReply q.n q.dim
  Output q := Stacked q.n q.dim
  publicInput := Params.toPublic
  valid p :=
    Network (sourceInput p.toPublic) ∧ 0 < p.lam ∧ 1 ≤ p.K ∧ 0 < p.m ∧ p.m ≤ p.M ∧
      0 ≤ p.L ∧ 0 ≤ p.Δ ∧ 0 < p.ε
  admissible p f O :=
    Assumption1 (sourceInput p.toPublic) p.m p.M f ∧
      Assumption2 (sourceInput p.toPublic) p.L f ∧
      IsMinOn (penalty (sourceInput p.toPublic) f) Set.univ p.xstar ∧
      penalty (sourceInput p.toPublic) f p.x0 -
        penalty (sourceInput p.toPublic) f p.xstar ≤ p.Δ ∧
      ∀ k x seed, O.answer k (0, x) seed = localOracle (sourceInput p.toPublic) f x
  successful p f output _ :=
    ∀ ω, penalty (sourceInput p.toPublic) f (output ω) -
      penalty (sourceInput p.toPublic) f p.xstar ≤ p.ε
  allowedAlgorithm q A := A = algorithm q

attribute [local simp] penaltyGradient penaltyHessian

end LongTails.Setups.DobocK
