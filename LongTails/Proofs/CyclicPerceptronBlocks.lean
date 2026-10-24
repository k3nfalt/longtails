import LongTails.Setups.CyclicFullWidthPerceptron
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CyclicPerceptronBlocks

open LongTails.Setups.CyclicFullWidthPerceptron

lemma linearPart_update {d : ℕ} (θ : Space d) (q x : Input d) (η : ℝ) :
    linearPart (move θ η (direction q θ)) x =
      ((linearPart θ x).1 + η * (q.1 * x.1 + ⟪q.2, x.2⟫) * θ.b,
        (linearPart θ x).2 + (η * (q.1 * x.1 + ⟪q.2, x.2⟫)) • θ.head) := by
  apply Prod.ext
  · simp only [linearPart, move, direction, inner_add_left, real_inner_smul_left]
    ring
  · simp only [linearPart, move, direction, smul_add, add_apply,
      smul_apply, InnerProductSpace.rankOne_apply]
    module

lemma head_update {d : ℕ} (θ : Space d) (q : Input d) (η : ℝ) :
    ((move θ η (direction q θ)).b, (move θ η (direction q θ)).head) =
      (θ.b + η * (linearPart θ q).1, θ.head + η • (linearPart θ q).2) := rfl

structure Coordinates (d : ℕ) where
  a : ℝ
  B : ℝ
  S : Features d
  X : Features d
  R : Features d
  F : Features d →L[ℝ] Features d

noncomputable def realize {d : ℕ} (η μ : ℝ) (c : Coordinates d) : Space d :=
  ⟨c.a, -(η ^ 2 * μ) • c.R, -(η ^ 2 * μ) • c.X, c.F,
    η ^ 3 * μ ^ 2 * c.B, -(η * μ) • c.S⟩

noncomputable def bias {d : ℕ} (c : Coordinates d) : ℝ := c.a * c.B + ⟪c.X, c.S⟫

lemma reference_margin {d : ℕ} (η μ : ℝ) (c : Coordinates d) :
    margin (1, 0) (realize η μ c) = η ^ 3 * μ ^ 2 * bias c := by
  simp only [margin, linearPart, realize, inner_zero_right, mul_one, add_zero,
    one_smul, map_zero, real_inner_smul_left, real_inner_smul_right, bias]
  rw [real_inner_comm c.S c.X]
  ring

lemma negative_margin {d : ℕ} (η μ ν : ℝ) (c : Coordinates d) (u : Features d) :
    margin (-(1 + ν), -μ • u) (realize η μ c) =
      η * μ ^ 2 * (⟪c.S, c.F u⟫ - η ^ 2 * (1 + ν) * bias c +
        η ^ 4 * μ ^ 2 * c.B * ⟪c.R, u⟫) := by
  simp only [margin, linearPart, realize, real_inner_smul_left, real_inner_smul_right,
    map_smul, inner_add_right, smul_smul, bias]
  rw [real_inner_comm c.S c.X]
  ring

noncomputable def pairedCoordinates {d : ℕ} (negativeFirst : Bool) (α μ β : ℝ)
    (c : Coordinates d) (u : Features d) : Coordinates d :=
  let ν := β * α * μ ^ 2
  let Λ := 1 - α * (1 + ν)
  ⟨Λ * c.a - α ^ 2 * ν * μ ^ 2 * c.B +
      (if negativeFirst then α ^ 2 * μ ^ 2 * ⟪c.R, u⟫ else 0),
    Λ * c.B - β * c.a + ⟪c.R, u⟫,
    Λ • c.S - (α * ν) • c.X + c.F u,
    Λ • c.X - ν • c.S + (if negativeFirst then c.F u else 0),
    c.R + (α * μ ^ 2 * c.B) • u + (if negativeFirst then 0 else c.a • u),
    c.F + (α * μ ^ 2) • InnerProductSpace.rankOne ℝ
      (c.S + (if negativeFirst then 0 else α • c.X)) u⟩

lemma positive_negative_coordinates {d : ℕ} (η μ β : ℝ) (c : Coordinates d)
    (u : Features d) :
    let θ := realize η μ c
    let q : Input d := (-(1 + β * η ^ 2 * μ ^ 2), -μ • u)
    let θ' := move θ η (direction (1, 0) θ)
    move θ' η (direction q θ') = realize η μ (pairedCoordinates false (η ^ 2) μ β c u) := by
  dsimp only
  apply Space.ext
  all_goals simp [move, direction, linearPart, realize, pairedCoordinates,
    real_inner_smul_left, real_inner_smul_right]
  all_goals first | (solve | ring) | (solve | module)

lemma negative_positive_coordinates {d : ℕ} (η μ β : ℝ) (c : Coordinates d)
    (u : Features d) :
    let θ := realize η μ c
    let q : Input d := (-(1 + β * η ^ 2 * μ ^ 2), -μ • u)
    let θ' := move θ η (direction q θ)
    move θ' η (direction (1, 0) θ') = realize η μ (pairedCoordinates true (η ^ 2) μ β c u) := by
  dsimp only
  apply Space.ext
  all_goals simp [move, direction, linearPart, realize, pairedCoordinates,
    real_inner_smul_left, real_inner_smul_right]
  all_goals first | (solve | ring) | (solve | module)

end LongTails.Proofs.CyclicPerceptronBlocks
