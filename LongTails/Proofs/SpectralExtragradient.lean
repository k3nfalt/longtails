import LongTails.Proofs.SpectralMirrorGeometry
import LongTails.Proofs.NonEuclideanExtragradientStep

namespace LongTails.Proofs.SpectralExtragradient

open LongTails.Setups.NonEuclideanWeakMinty
open LongTails.Algorithms.NonEuclideanExtragradient
open LongTails.Proofs.NonEuclideanExtragradientStep
open LongTails.Proofs.SpectralMirrorGeometry

abbrev Space (m n : ℕ) := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)

noncomputable def data (m n : ℕ) (L ρ : ℝ) (X0 : Space m n) : Public where
  E := Space m n
  L := L
  ρ := ρ
  μ := 1
  h := energy (EuclideanSpace.basisFun (Fin n) ℝ)
  x0 := X0

noncomputable def nuclearNorm {m n : ℕ} (G : Space m n) : ℝ :=
  ‖pairing (EuclideanSpace.basisFun (Fin n) ℝ) G‖

lemma data_valid {m n : ℕ} {L ρ : ℝ} (X0 : Space m n)
    (hL : 0 < L) (hρ : 0 ≤ ρ) (hρL : ρ ≤ 1 / (20 * L)) :
    (data m n L ρ X0).Valid := by
  refine ⟨hL, hρ, hρL, by norm_num [data], ?_, ?_⟩
  · intro X
    exact (energy_hasFDerivAt _ X).differentiableAt
  · intro X Y
    exact energy_strongly_convex _ X Y

lemma data_bregman_bound {m n : ℕ} (L ρ : ℝ) (X0 X Y : Space m n) :
    (data m n L ρ X0).bregman Y X ≤ (min m n : ℝ) * ‖Y - X‖ ^ 2 / 2 := by
  change energy _ Y - energy _ X - fderiv ℝ (energy _) X (Y - X) ≤ _
  rw [energy_bregman]
  simpa only [Fintype.card_fin, min_comm] using
    energy_upper_min (EuclideanSpace.basisFun (Fin n) ℝ)
      (EuclideanSpace.basisFun (Fin m) ℝ) (Y - X)

lemma spectral_direction {m n : ℕ} (L ρ : ℝ) (X0 G : Space m n) :
    let g := pairing (EuclideanSpace.basisFun (Fin n) ℝ) G
    let V := LongTails.Algorithms.PowerDualAveraging.direction g
    ‖V‖ ≤ nuclearNorm G ∧
      Matrix.trace ((coordinates (EuclideanSpace.basisFun (Fin n) ℝ)
        (EuclideanSpace.basisFun (Fin m) ℝ) G).transpose *
        coordinates (EuclideanSpace.basisFun (Fin n) ℝ)
          (EuclideanSpace.basisFun (Fin m) ℝ) V) = nuclearNorm G ^ 2 := by
  have hh := direction_spec (data m n L ρ X0)
    (pairing (EuclideanSpace.basisFun (Fin n) ℝ) G)
  exact ⟨hh.1, by rw [← pairing_trace]; exact hh.2⟩

lemma spectral_mirror {m n : ℕ} {L ρ : ℝ} (X0 X G : Space m n)
    (hL : 0 < L) (hρ : 0 ≤ ρ) (hρL : ρ ≤ 1 / (20 * L)) :
    mirror (data m n L ρ X0) X (pairing (EuclideanSpace.basisFun (Fin n) ℝ) G) =
      X - (1 / (10 * L)) • G := by
  apply quadratic_mirror_minimizer (EuclideanSpace.basisFun (Fin n) ℝ)
  intro Y
  have hh := mirror_spec (data m n L ρ X0) (data_valid X0 hL hρ hρL) X
    (pairing (EuclideanSpace.basisFun (Fin n) ℝ) G) Y
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let Z : Space m n := mirror (data m n L ρ X0) X (pairing b G)
  change (1 / (10 * L)) * pairing b G Z +
    (energy b Z - energy b X - fderiv ℝ (energy b) X (Z - X)) ≤
    (1 / (10 * L)) * pairing b G Y +
    (energy b Y - energy b X - fderiv ℝ (energy b) X (Y - X)) at hh
  rw [(energy_hasFDerivAt b X).fderiv] at hh
  simpa only [add_sub_assoc] using hh

end LongTails.Proofs.SpectralExtragradient
