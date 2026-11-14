import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Convex.Basic

open scoped RealInnerProductSpace

namespace LongTails.Setups.CoupledStronglyConcaveMinimax

structure Params where
  nx : ℕ
  ny : ℕ
  constraints : ℕ
  X : Set (EuclideanSpace ℝ (Fin nx))
  Y : Set (EuclideanSpace ℝ (Fin ny))
  x0 : EuclideanSpace ℝ (Fin nx)
  y0 : EuclideanSpace ℝ (Fin ny)
  Lf : ℝ
  LJ : ℝ
  J : ℝ
  Gx : ℝ
  Gy : ℝ
  C : ℝ
  DX : ℝ
  DY : ℝ
  μ : ℝ
  δ : ℝ
  Z : ℝ
  ε : ℝ

abbrev XSpace (p : Params) := EuclideanSpace ℝ (Fin p.nx)
abbrev YSpace (p : Params) := EuclideanSpace ℝ (Fin p.ny)
abbrev Weights (p : Params) := EuclideanSpace ℝ (Fin p.constraints)
abbrev Joint (p : Params) := WithLp 2 (XSpace p × YSpace p)

def domain (p : Params) : Set (Joint p) := {z | z.fst ∈ p.X ∧ z.snd ∈ p.Y}

def Normal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (x n : E) : Prop := ∀ u ∈ S, ⟪n, u - x⟫ ≤ 0

structure Valid (p : Params) : Prop where
  compactX : IsCompact p.X
  compactY : IsCompact p.Y
  convexX : Convex ℝ p.X
  convexY : Convex ℝ p.Y
  startX : p.x0 ∈ p.X
  startY : p.y0 ∈ p.Y
  diameterX : ∀ x ∈ p.X, ∀ x' ∈ p.X, ‖x - x'‖ ≤ p.DX
  diameterY : ∀ y ∈ p.Y, ∀ y' ∈ p.Y, ‖y - y'‖ ≤ p.DY
  Lf_nonneg : 0 ≤ p.Lf
  LJ_nonneg : 0 ≤ p.LJ
  J_nonneg : 0 ≤ p.J
  Gx_nonneg : 0 ≤ p.Gx
  Gy_nonneg : 0 ≤ p.Gy
  C_nonneg : 0 ≤ p.C
  DX_nonneg : 0 ≤ p.DX
  DY_nonneg : 0 ≤ p.DY
  μ_pos : 0 < p.μ
  δ_pos : 0 < p.δ
  Z_pos : 0 < p.Z
  ε_pos : 0 < p.ε

structure Instance (p : Params) where
  f : Joint p → ℝ
  c : Joint p → Weights p
  g : Joint p → Joint p
  jac : Joint p → (Joint p →L[ℝ] Weights p)

structure Assumptions (p : Params) (I : Instance p) : Prop where
  gradient : ∀ z ∈ domain p, HasGradientAt I.f (I.g z) z
  derivative : ∀ z ∈ domain p, HasFDerivAt I.c (I.jac z) z
  gradient_lipschitz : ∀ z ∈ domain p, ∀ w ∈ domain p,
    ‖I.g z - I.g w‖ ≤ p.Lf * ‖z - w‖
  jacobian_lipschitz : ∀ z ∈ domain p, ∀ w ∈ domain p,
    ‖I.jac z - I.jac w‖ ≤ p.LJ * ‖z - w‖
  jacobian_bound : ∀ z ∈ domain p, ‖I.jac z‖ ≤ p.J
  gradientX_bound : ∀ z ∈ domain p, ‖(I.g z).fst‖ ≤ p.Gx
  gradientY_bound : ∀ z ∈ domain p, ‖(I.g z).snd‖ ≤ p.Gy
  constraint_bound : ∀ z ∈ domain p, ‖I.c z‖ ≤ p.C
  convex_constraints : ∀ x ∈ p.X, ∀ i,
    ConvexOn ℝ p.Y (fun y => I.c (WithLp.toLp 2 (x, y)) i)
  strongly_concave : ∀ x ∈ p.X, ∀ y ∈ p.Y, ∀ y' ∈ p.Y,
    I.f (WithLp.toLp 2 (x, y')) ≤ I.f (WithLp.toLp 2 (x, y)) +
      ⟪(I.g (WithLp.toLp 2 (x, y))).snd, y' - y⟫ - p.μ / 2 * ‖y' - y‖ ^ 2
  qualification : ∀ z ∈ domain p, ∃ d : YSpace p, ‖d‖ ≤ p.Z ∧
    (∀ n, Normal p.Y z.snd n → ⟪n, d⟫ ≤ 0) ∧
    ∀ i, 0 < I.c z i → (I.jac z (WithLp.toLp 2 (0, d))) i ≤ -p.δ

structure Reply (p : Params) where
  value : ℝ
  gradient : Joint p
  constraints : Weights p
  jacobian : Joint p →L[ℝ] Weights p

structure Output (p : Params) where
  x : XSpace p
  y : YSpace p
  multiplier : Weights p

noncomputable def exactReply (p : Params) (I : Instance p) (z : Joint p) : Reply p :=
  ⟨I.f z, I.g z, I.c z, I.jac z⟩

noncomputable def KKT (p : Params) (I : Instance p) (o : Output p) : Prop :=
  let z := WithLp.toLp 2 (o.x, o.y)
  let g := I.g z - (I.jac z).adjoint o.multiplier
  o.x ∈ p.X ∧ o.y ∈ p.Y ∧ (∀ i, 0 ≤ o.multiplier i) ∧
    ‖WithLp.toLp 2 (fun i => max (I.c z i) 0)‖ ≤ p.ε ∧
    (∑ i, |o.multiplier i * I.c z i|) ≤ p.ε ∧
    ∃ nx ny, Normal p.X o.x nx ∧ Normal p.Y o.y ny ∧
      ‖g.fst + nx‖ ≤ p.ε ∧ ‖g.snd - ny‖ ≤ p.ε

abbrev spec : OracleTemplate.Setup where
  Params := Params
  Public := Params
  Instance := Instance
  Query := Joint
  Reply := Reply
  Output := Output
  publicInput := id
  valid := Valid
  admissible p I oracle := Assumptions p I ∧
    ∀ history seed z, z ∈ domain p → oracle.answer history (0, z) seed = exactReply p I z
  successful p I output law := ∀ᵐ ω ∂(law : MeasureTheory.Measure _), KKT p I (output ω)

end LongTails.Setups.CoupledStronglyConcaveMinimax
