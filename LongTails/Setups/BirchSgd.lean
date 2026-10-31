import LongTails.Template
import LongTails.Setups.RennalaIterations
import Mathlib.Probability.Distributions.Uniform
import LongTails.Setups.StochasticSmoothAndConvex

open MeasureTheory

namespace OracleTemplate.BirchSgd

open OracleTemplate
open OracleTemplate.Rennala (Point)

def EpsStationary {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (f : Point d → ℝ)
    (x : Ω → Point d) (P : Measure Ω) (ε : ℝ) : Prop :=
  Integrable (fun ω => ‖gradient f (x ω)‖ ^ 2) P ∧ (∫ ω, ‖gradient f (x ω)‖ ^ 2 ∂P) ≤ ε

structure Tree where
  base : ℕ → ℕ
  point : ℕ → ℕ
  grad : ℕ → ℕ

def Tree.WellFormed (T : Tree) : Prop :=
  ∀ j, T.base j ≤ j ∧ T.point j ≤ j ∧ T.grad j ≤ j

def Tree.foldHist {α : Type} (T : Tree) (init : α) (step : ℕ → α → α) : ℕ → ℕ → α
  | 0 => fun _ => init
  | k + 1 => fun j =>
      if j ≤ k then T.foldHist init step k j else step k (T.foldHist init step k (T.base k))

def Tree.fold {α : Type} (T : Tree) (init : α) (step : ℕ → α → α) (j : ℕ) : α :=
  T.foldHist init step j j

def Tree.repr (T : Tree) (j : ℕ) : Multiset ℕ :=
  T.fold 0 (fun k M => T.grad k ::ₘ M) j

def Tree.depth (T : Tree) (j : ℕ) : ℕ :=
  T.fold 0 (fun _ n => n + 1) j

def Tree.ancestors (T : Tree) (j : ℕ) : Finset ℕ :=
  T.fold {0} (fun k s => insert (k + 1) s) j

def Tree.dist (T : Tree) (y z : ℕ) : ℕ :=
  max (T.depth y - ((T.ancestors y ∩ T.ancestors z).sup T.depth))
    (T.depth z - ((T.ancestors y ∩ T.ancestors z).sup T.depth))

def Tree.IsMainBranch (T : Tree) (m : ℕ → ℕ) : Prop :=
  m 0 = 0 ∧ ∀ k, 0 < m (k + 1) ∧ T.base (m (k + 1) - 1) = m k

def Tree.auxSample (T : Tree) (m : ℕ → ℕ) (k : ℕ) : ℕ :=
  T.grad (m (k + 1) - 1)

def Tree.auxNode (T : Tree) (m : ℕ → ℕ) (k : ℕ) : ℕ :=
  T.point (T.auxSample m k)

structure Hist (d : ℕ) where
  nodes : ℕ → Point d
  replies : ℕ → Point d

def Hist.step {d : ℕ} (T : Tree) (gamma : ℝ) (k : ℕ) (h : Hist d) (reply : Point d) :
    Hist d :=
  ⟨fun j => if j = k + 1 then
      h.nodes (T.base k) - gamma • (if T.grad k = k then reply else h.replies (T.grad k))
    else h.nodes j,
   fun c => if c = k then reply else h.replies c⟩

def Tree.realize {d : ℕ} {Ω : Type} (T : Tree) (gamma : ℝ) (x0 : Point d)
    (g : Point d → Ω → Point d) (η : ℕ → Ω) : ℕ → Hist d
  | 0 => ⟨fun _ => x0, fun _ => 0⟩
  | k + 1 => (T.realize gamma x0 g η k).step T gamma k
      (g ((T.realize gamma x0 g η k).nodes (T.point k)) (η k))

def Tree.vertex {d : ℕ} {Ω : Type} (T : Tree) (gamma : ℝ) (x0 : Point d)
    (g : Point d → Ω → Point d) (η : ℕ → Ω) (j : ℕ) : Point d :=
  (T.realize gamma x0 g η j).nodes j

def Tree.reply {d : ℕ} {Ω : Type} (T : Tree) (gamma : ℝ) (x0 : Point d)
    (g : Point d → Ω → Point d) (η : ℕ → Ω) (c : ℕ) : Point d :=
  g (T.vertex gamma x0 g η (T.point c)) (η c)

noncomputable def stepSize (L σ ε R : ℝ) : ℝ :=
  min (1 / (2 * L))
    (min (if R = 0 then 1 / (2 * L) else 1 / (2 * R * L))
      (if σ = 0 then 1 / (2 * L) else ε / (4 * σ ^ 2 * L)))

noncomputable def horizon (L σ ε Δ R : ℝ) : ℕ :=
  ⌈4 * (R + 1) * L * Δ / ε + 8 * σ ^ 2 * L * Δ / ε ^ 2⌉₊

structure Public where
  d : ℕ
  gamma : ℝ
  x0 : Point d
  tree : Tree
  branch : ℕ → ℕ
  K : ℕ

structure State (d : ℕ) where
  count : ℕ
  hist : Hist d
  chosen : ℕ

noncomputable def birch (p : Public) : Algorithm (Point p.d) (Point p.d) (Point p.d) where
  Seed := Fin (p.K + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (p.K + 1))).toMeasure, inferInstance⟩
  State := State p.d
  initial i := ⟨0, ⟨fun _ => p.x0, fun _ => 0⟩, i.val⟩
  query s := (0, s.hist.nodes (p.tree.point s.count))
  update s reply := ⟨s.count + 1, s.hist.step p.tree p.gamma s.count reply, s.chosen⟩
  output s := s.hist.nodes (p.branch s.chosen)

noncomputable def gradientOracle {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point d → Ω → Point d) :
    Oracle (Point d) (Point d) where
  Seed := fun _ => Ω
  law := P
  answer := fun _ q seed => g q.2 seed

end OracleTemplate.BirchSgd

open MeasureTheory ProbabilityTheory

namespace LongTails.Setups.BirchSgd

open OracleTemplate OracleTemplate.BirchSgd
open OracleTemplate.Rennala (Instance Point)

def SmoothObjective {d : ℕ} (f : Point d → ℝ) (L : ℝ) : Prop :=
  (∀ x, HasGradientAt f (gradient f x) x) ∧
    ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

def LowerBounded {d : ℕ} (f : Point d → ℝ) (lower : ℝ) : Prop :=
  ∀ x, lower ≤ f x

def ReprContained (T : Tree) (m : ℕ → ℕ) : Prop :=
  ∀ k, T.repr (T.auxNode m k) ≤ T.repr (m k)

def DistanceBounded (T : Tree) (m : ℕ → ℕ) (R : ℝ) : Prop :=
  ∀ k, (T.dist (m k) (T.auxNode m k) : ℝ) ≤ R

def SampleIndependent {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (T : Tree) (m : ℕ → ℕ)
    (gamma : ℝ) (x0 : Point d) (g : Point d → Ω → Point d) (P : Measure (ℕ → Ω)) : Prop :=
  ∀ k, IndepFun (fun η : ℕ → Ω => η (T.auxSample m k))
    (fun η : ℕ → Ω => fun i : Fin k =>
      (T.vertex gamma x0 g η (m (i.val + 1)), T.vertex gamma x0 g η (T.auxNode m (i.val + 1)),
        η (T.auxSample m i.val))) P

structure Params where
  d : ℕ
  L : ℝ
  σ : ℝ
  ε : ℝ
  Δ : ℝ
  R : ℝ
  x0 : Point d
  tree : Tree
  branch : ℕ → ℕ

noncomputable def publicInput (p : Params) : Public where
  d := p.d
  gamma := stepSize p.L p.σ p.ε p.R
  x0 := p.x0
  tree := p.tree
  branch := p.branch
  K := horizon p.L p.σ p.ε p.Δ p.R

noncomputable abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance p := Instance p.d
  Query p := Point p.d
  Reply p := Point p.d
  Output p := Point p.d
  publicInput := publicInput
  valid p := 0 < p.L ∧ 0 ≤ p.σ ∧ 0 < p.ε ∧ 0 ≤ p.Δ ∧ 0 ≤ p.R ∧ p.tree.WellFormed ∧
    p.tree.IsMainBranch p.branch ∧ ReprContained p.tree p.branch ∧
    DistanceBounded p.tree p.branch p.R
  admissible p I O :=
    SmoothObjective I.f p.L ∧ LowerBounded I.f I.lower ∧ I.f p.x0 - I.lower ≤ p.Δ ∧
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI := m
      ∃ (μ : ProbabilityMeasure Ω) (P : ProbabilityMeasure (ℕ → Ω))
        (g : Point p.d → Ω → Point p.d),
        (∀ c, (P : Measure (ℕ → Ω)).map (fun η => η c) = (μ : Measure Ω)) ∧
        LongTails.Setups.StochasticSmoothAndConvex.IsStochasticGradient (Point p.d) Ω
          (μ : Measure Ω) I.f g p.σ ∧
        SampleIndependent p.tree p.branch (stepSize p.L p.σ p.ε p.R) p.x0 g
          (P : Measure (ℕ → Ω)) ∧
        O = gradientOracle P g
  successful p I output P :=
    Measurable output ∧
    Integrable (fun ω => ‖gradient I.f (output ω)‖ ^ 2) (P : Measure _) ∧
    (∫ ω, ‖gradient I.f (output ω)‖ ^ 2 ∂(P : Measure _)) ≤ p.ε
  allowedAlgorithm q A := A = birch q

end LongTails.Setups.BirchSgd
