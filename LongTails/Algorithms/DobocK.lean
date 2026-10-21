import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

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
