import LongTails.Proofs.GeneralizedSmoothChainPrefix
import LongTails.Proofs.GeneralizedSmoothLocalization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.GeneralizedSmoothPartialOracle

open FiniteSumNondualLowerComponents GeneralizedSmoothChainPrefix GeneralizedSmoothSmoothedChain
open GeneralizedSmoothShieldCalculus GeneralizedSmoothShieldGeometry

noncomputable def partialField {d m : ℕ}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε a S : ℝ)
    (π : Fin m ↪ Fin d) (r : ℕ) (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if 24 * S / a ≤ ‖x‖ then a • x else
    a • x + CompactSmoothMaximum.slope
      ((smoothObjective φ L₀ L₁ ε (truncate r (coordinateMap π x)) -
        wall a (16 * S / a) x + 64 * S ^ 2 / a) / (2 * (64 * S ^ 2 / a))) •
      ((coordinateMap π).adjoint (truncate r (smoothField φ L₀ L₁ ε (truncate r (coordinateMap π x)))) - a • x)

lemma partialField_prefix {d m : ℕ}
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε a S : ℝ)
    (π ρ : Fin m ↪ Fin d) (r : ℕ) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ i, i.val ≤ r → π i = ρ i) :
    partialField φ L₀ L₁ ε a S π r x = partialField φ L₀ L₁ ε a S ρ r x := by
  unfold partialField
  rw [truncate_prefix π ρ r h x, adjoint_truncate_prefix π ρ r h]

lemma partialField_eq {d m : ℕ} (hm : 0 < m)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m))) (L₀ L₁ ε a S : ℝ)
    (h0 : 0 < L₀) (h1 : 0 < L₁) (hε : 0 < ε) (ha : 0 < a) (hS : 0 < S)
    (hδ : φ.rOut ≤ 1 / (16 * L₁ * Real.sqrt m))
    (π : Fin m ↪ Fin d) (r : Fin m) (x : EuclideanSpace ℝ (Fin d))
    (hupper : smoothObjective φ L₀ L₁ ε (coordinateMap π x) ≤ S * ‖x‖ + S ^ 2 / a)
    (hsmall : ‖x‖ < 24 * S / a → ∀ i, r ≤ i → |x (π i)| ≤ 1 / (16 * L₁ * Real.sqrt m)) :
    partialField φ L₀ L₁ ε a S π r.val x =
      field (fun y => smoothObjective φ L₀ L₁ ε (coordinateMap π y))
        (fun y => (coordinateMap π).adjoint (smoothField φ L₀ L₁ ε (coordinateMap π y)))
        a (16 * S / a) (64 * S ^ 2 / a) x := by
  unfold partialField
  split_ifs with hx
  · have hs := exterior_separation (fun y => smoothObjective φ L₀ L₁ ε (coordinateMap π y))
      a S ha hS x hx hupper
    have hmix := (mixing_left (fun y => smoothObjective φ L₀ L₁ ε (coordinateMap π y))
      a (16 * S / a) (64 * S ^ 2 / a) (by positivity) x hs).1
    rw [field, hmix, zero_smul, add_zero]
  · have hcoords : ∀ i, r ≤ i → |coordinateMap π x i| ≤ 1 / (16 * L₁ * Real.sqrt m) :=
      hsmall (lt_of_not_ge hx)
    rw [truncated_objective_eq hm φ L₀ L₁ ε h0 h1 hε hδ r _ hcoords,
      truncated_field_eq hm φ L₀ L₁ ε h0 h1 hε hδ r _ hcoords]
    rfl

end LongTails.Proofs.GeneralizedSmoothPartialOracle
