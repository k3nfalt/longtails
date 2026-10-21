import outputs.Algorithms.RennalaSgd
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.BatchIterations

open Rennala

structure Params where
  d : ℕ
  L : ℝ
  v : ℝ
  eps : ℝ
  Delta : ℝ
  x0 : Point d
  extra : ℕ

structure SmoothLower (p : Params) (I : Rennala.Instance p.d) : Prop where
  hasGradient : ∀ x, HasGradientAt I.f (gradient I.f x) x
  lipschitz : ∀ x y, ‖gradient I.f x - gradient I.f y‖ ≤ p.L * ‖x - y‖
  lower : ∀ x, I.lower ≤ I.f x
  gap : I.f p.x0 - I.lower = p.Delta

structure Public where
  d : ℕ
  gamma : ℝ
  S : ℕ
  x0 : Point d
  N : ℕ

structure State (p : Public) where
  count : ℕ
  point : Point p.d
  selected : Point p.d
  index : Fin (p.N + 1)

noncomputable def algorithm (p : Public) : Algorithm (Point p.d) (Point p.d) (Point p.d) where
  Seed := Fin (p.N + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (p.N + 1))).toMeasure, inferInstance⟩
  State := State p
  initial j := ⟨0, p.x0, p.x0, j⟩
  query s := (0, s.point)
  update s reply :=
    let x := s.point - p.gamma • reply
    ⟨s.count + 1, x, if s.count + 1 = s.index.val then x else s.selected, s.index⟩
  output s := s.selected

def blocks {Ω : Type} (S : ℕ) (ξ : ℕ → Ω) : ℕ → Fin S → Ω :=
  fun k i => ξ (k * S + i.val)

noncomputable def oracle (p : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Point p.d → Ω → Point p.d) :
    Oracle (Point p.d) (Point p.d) where
  Seed := fun _ => Fin p.S → Ω
  law := P.map (blocks p.S)
  answer := fun _ (_, x) seed => batchEstimator p.S g x seed

end OracleTemplate.BatchIterations
