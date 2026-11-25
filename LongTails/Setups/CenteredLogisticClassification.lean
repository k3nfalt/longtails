import LongTails.Setups.ClusteredConvolutionalPerceptron
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Sigmoid

open OracleTemplate
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Setups.CenteredLogisticClassification

open TwoSampleQuadraticPerceptron (Features)
open ManySampleConvolutionalPerceptron (Space Reply)

structure Params where
  d : ℕ
  n : ℕ+

abbrev Data (p : Params) := Fin p.n → Features p.d
abbrev Query (p : Params) := Fin p.n × Space p.d

structure Geometry (p : Params) (D : Data p) where
  R : ℝ
  ε : ℝ
  level : ℝ
  axis : Features p.d
  h : Fin p.n → Features p.d
  y : Fin p.n → ℝ
  scale_pos : 0 < R
  radius_pos : 0 < ε
  radius_le : ε ≤ 1 / 32
  axis_unit : ‖axis‖ = 1
  labels : ∀ i, |y i| = 1
  mean_bound : ‖𝔼 i, y i • (level • axis + h i)‖ ≤ ε
  normalized : level ^ 2 + (𝔼 i, ‖h i‖ ^ 2) = 1
  centered : (𝔼 i, h i) = 0
  radius : ∀ i, ‖h i‖ ≤ ε
  sample_eq : ∀ i, D i = (y i * R) • (level • axis + h i)
  gap : let m := 𝔼 j, y j • (level • axis + h j)
    ∀ i, (9 + 17 * ‖TwoSampleQuadraticPerceptron.shift axis - axis‖) * ε ^ 3 <
      y i * ⟪h i, m - ⟪axis, m⟫ • axis⟫

noncomputable def answer {p : Params} (D : Data p) (q : Query p) : Reply p.d :=
  ⟨TwoSampleQuadraticPerceptron.margin .conv p.d (D q.1) q.2,
   TwoSampleQuadraticPerceptron.direction .conv p.d (D q.1) q.2⟩

noncomputable def initialPoint (d : ℕ) : Space d := ((1, 0), 0)

abbrev Batch (p : Params) := Fin p.n → Reply p.d
abbrev State (p : Params) := ℕ × (Space p.d × Option ℝ) × Batch p

def emptyReply (d : ℕ) : Reply d := ⟨0, 0⟩

noncomputable def batchStep {p : Params} (choose : Batch p → ℝ × ℝ)
    (s : Space p.d × Option ℝ) (b : Batch p) : Space p.d × Option ℝ :=
  let (c, η) := match s.2 with
    | none => choose b
    | some η => (1, η)
  (c • s.1 + η • (𝔼 i, Real.sigmoid (-(c ^ 2 * (b i).margin)) • (c • (b i).direction)), some η)

noncomputable def scanStep {p : Params} (choose : Batch p → ℝ × ℝ) (s : State p)
    (reply : Reply p.d) : State p :=
  let b := Function.update s.2.2 ⟨s.1 % p.n, Nat.mod_lt _ p.n.pos⟩ reply
  if s.1 + 1 < p.n then (s.1 + 1, s.2.1, b)
  else (0, batchStep choose s.2.1 b, fun _ => emptyReply p.d)

def family (p : Params) (A : Algorithm (Query p) (Reply p.d) (Space p.d)) : Prop :=
  ∃ (choose : Batch p → ℝ × ℝ) (state : A.State → State p),
    (∀ b, 0 < (choose b).1 ∧ 0 < (choose b).2) ∧
    (∀ seed, state (A.initial seed) = (0, (initialPoint p.d, none), fun _ => emptyReply p.d)) ∧
    (∀ s, A.query s = (0, (⟨(state s).1 % p.n, Nat.mod_lt _ p.n.pos⟩, (state s).2.1.1))) ∧
    (∀ s r, state (A.update s r) = scanStep choose (state s) r) ∧
    ∀ s, A.output s = (state s).2.1.1

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  Instance := Data
  Query := Query
  Reply p := Reply p.d
  Output p := Space p.d
  publicInput := id
  valid p := 2 ≤ p.d ∧ 2 ≤ (p.n : ℕ)
  admissible p D oracle := Nonempty (Geometry p D) ∧
    ∀ hist query seed, oracle.answer hist query seed = answer D query.2
  successful p D output _ := ∀ ω i, 0 < TwoSampleQuadraticPerceptron.margin .conv p.d (D i) (output ω)
  allowedAlgorithm := family

end LongTails.Setups.CenteredLogisticClassification
