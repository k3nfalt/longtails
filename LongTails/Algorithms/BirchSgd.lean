import LongTails.Template
import LongTails.Algorithms.RennalaModel
import Mathlib.Probability.Distributions.Uniform

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
