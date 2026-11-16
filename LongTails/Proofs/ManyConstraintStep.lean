import LongTails.Proofs.ManyConstraintFinite
import LongTails.Proofs.ManyConstraintStochastic
import LongTails.Proofs.ManyConstraintBall

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintStep

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintPenalty
  LongTails.Proofs.ManyConstraintFinite LongTails.Proofs.ManyConstraintStochastic
  LongTails.Proofs.ManyConstraintCoupling LongTails.Proofs.ManyConstraintBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {m : ℕ} [NeZero m]

noncomputable def Fsm (law : Measure Ξ) (loss : Ξ → E → ℝ) (β : ℝ) (P : Fin m → E → E)
    (x : E) : ℝ :=
  objective law loss x + hpen β P x

noncomputable def Fgrad (law : Measure Ξ) (grad : Ξ → E → E) (β : ℝ) (P : Fin m → E → E)
    (x : E) : E :=
  meanGrad law grad x + hgrad β P x

noncomputable def Phi (law : Measure Ξ) (loss : Ξ → E → ℝ) (β : ℝ) (P : Fin m → E → E)
    (μ : ℝ) (x0 x : E) : ℝ :=
  Fsm law loss β P x + reg μ x0 x

variable {law : Measure Ξ} {loss : Ξ → E → ℝ} {grad : Ξ → E → E} {L σ : ℝ} {xs : E}
  {K : Fin m → Set E} {P : Fin m → E → E}

lemma pointwise_step (h : Regular law loss grad L σ xs) (hP : ∀ j z, IsProj (K j) z (P j z))
    {β μ ρ τ α : ℝ} {x0 : E} (hL : 0 < L) (hβ : 0 < β) (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (hα : 0 < α) (hτ : 0 < τ) (hτh : τ ≤ 1 / 2) (htune : 3 * α * (L + β) * τ ≤ 1)
    {s y z u v : E} (hs : s ∈ closedBall x0 ρ) (hy : y ∈ closedBall x0 ρ)
    (hu : u ∈ closedBall x0 ρ) :
    let x := mix τ s y z
    let ynext := proxBall μ x0 ρ (1 / (3 * (L + β))) x v
    let znext := proxBall μ x0 ρ α z v
    let G := Fgrad law grad β P x
    Phi law loss β P μ x0 ynext + τ / (2 * α) * (1 + α * μ) * ‖znext - u‖ ^ 2 ≤
      (1 / 2 - τ) * Phi law loss β P μ x0 y + 1 / 2 * Phi law loss β P μ x0 s +
      τ * Phi law loss β P μ x0 u + τ / (2 * α) * ‖z - u‖ ^ 2 +
      τ * ⟪G - v, z - u⟫ + ‖G - v‖ ^ 2 / (4 * (L + β)) -
      τ * ((1 / (2 * L)) * ∫ ξ, ‖grad ξ u - grad ξ x‖ ^ 2 ∂law) -
      1 / 2 * (Fsm law loss β P s - Fsm law loss β P x - ⟪G, s - x⟫) := by
  intro x ynext znext G
  have hLt : 0 < L + β := by linarith
  have hK : Convex ℝ (closedBall x0 ρ) := convex_closedBall x0 ρ
  have hψ := reg_strong μ x0 (closedBall x0 ρ) hK
  have hmodel : Fsm law loss β P ynext ≤ Fsm law loss β P x + ⟪G, ynext - x⟫ +
      (L + β) / 2 * ‖ynext - x‖ ^ 2 := by
    have h1 := h.model x ynext
    have h2 := hpen_upper hP hβ.le x ynext
    simp only [Fsm, G, Fgrad, inner_add_left]
    nlinarith [h1, h2]
  have hsupp (w : E) : ⟪G, w - x⟫ + (1 / (2 * L)) * ∫ ξ, ‖grad ξ w - grad ξ x‖ ^ 2 ∂law ≤
      Fsm law loss β P w - Fsm law loss β P x := by
    have h1 := h.support hL x w
    have h2 := hpen_support hP hβ.le x w
    simp only [Fsm, G, Fgrad, inner_add_left]
    linarith
  have hnn (w : E) : 0 ≤ (1 / (2 * L)) * ∫ ξ, ‖grad ξ w - grad ξ x‖ ^ 2 ∂law := by
    have : 0 ≤ ∫ ξ, ‖grad ξ w - grad ξ x‖ ^ 2 ∂law := integral_nonneg fun _ => sq_nonneg _
    positivity
  have hsy : ⟪G, y - x⟫ ≤ Fsm law loss β P y - Fsm law loss β P x := by
    linarith [hsupp y, hnn y]
  have hsu : ⟪G, u - x⟫ ≤ Fsm law loss β P u - Fsm law loss β P x -
      (1 / (2 * L)) * ∫ ξ, ‖grad ξ u - grad ξ x‖ ^ 2 ∂law := by
    linarith [hsupp u]
  have hc := coupling_on (K := closedBall x0 ρ) (f := Fsm law loss β P) (ψ := reg μ x0)
    hLt hμ hα hτ hτh htune hψ hs hy hu (proxBall_mem hρ z v) hmodel
    (proxBall_min (by positivity) hμ hρ x v) (proxBall_min hα hμ hρ z v) hsy hsu
  simp only [Phi]
  linarith [hc]

end LongTails.Proofs.ManyConstraintStep
