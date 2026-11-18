import LongTails.Proofs.KnownGapChainPrefix
import LongTails.Proofs.AdaptivePolynomialLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.KnownGapPartialOracle

open FiniteSumNondualLowerComponents GeneralizedSmoothChainPrefix KnownGapSmoothedChain
open KnownGapChainPrefix AdaptivePolynomialLocalization

noncomputable def partialField {d m : ℕ}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε h : ℝ) (n : ℕ) (a B : ℝ)
    (π : Fin m ↪ Fin d) (r : ℕ) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if 4 * B ≤ ‖x‖ then a • x else
    let v := (coordinateMap π).adjoint
      (truncate r (smoothField φ L₀ L₁ ε h (truncate r (coordinateMap π x))))
    v + AdaptivePolynomialHinge.mixing n
      ((wall a B x - smoothObjective φ L₀ L₁ ε h (truncate r (coordinateMap π x))) / (a * B ^ 2)) •
        (a • x - v)

lemma partialField_prefix {d m : ℕ}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε h : ℝ) (n : ℕ) (a B : ℝ)
    (π ρ : Fin m ↪ Fin d) (r : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (hp : ∀ i, i.val ≤ r → π i = ρ i) :
    partialField φ L₀ L₁ ε h n a B π r x = partialField φ L₀ L₁ ε h n a B ρ r x := by
  unfold partialField
  rw [truncate_prefix π ρ r hp x, adjoint_truncate_prefix π ρ r hp]

lemma partialField_eq {d m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε h : ℝ) (n : ℕ) (a B : ℝ)
    (h0 : 0 < L₀) (h1 : 0 < L₁) (hε : 0 < ε) (hh : 0 < h)
    (hδ : φ.rOut ≤ threshold L₁ h)
    (π : Fin m ↪ Fin d) (r : Fin m) (x : EuclideanSpace ℝ (Fin d))
    (hfar : 4 * B ≤ ‖x‖ →
      field (fun y => smoothObjective φ L₀ L₁ ε h (coordinateMap π y))
        (fun y => (coordinateMap π).adjoint (smoothField φ L₀ L₁ ε h (coordinateMap π y)))
        n a B (a * B ^ 2) x = a • x)
    (hsmall : ‖x‖ < 4 * B → ∀ i, r ≤ i → |x (π i)| ≤ threshold L₁ h) :
    partialField φ L₀ L₁ ε h n a B π r.val x =
      field (fun y => smoothObjective φ L₀ L₁ ε h (coordinateMap π y))
        (fun y => (coordinateMap π).adjoint (smoothField φ L₀ L₁ ε h (coordinateMap π y)))
        n a B (a * B ^ 2) x := by
  unfold partialField
  split_ifs with hx
  · exact (hfar hx).symm
  · have hcoords : ∀ i, r ≤ i → |coordinateMap π x i| ≤ threshold L₁ h :=
      hsmall (lt_of_not_ge hx)
    rw [truncated_objective_eq hm φ L₀ L₁ ε h h0 h1 hε hh hδ r _ hcoords,
      truncated_field_eq hm φ L₀ L₁ ε h h0 h1 hε hh hδ r _ hcoords]
    rfl

end LongTails.Proofs.KnownGapPartialOracle
