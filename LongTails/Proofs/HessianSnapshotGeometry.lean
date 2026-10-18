import LongTails.Algorithms.HessianSnapshot
import LongTails.Proofs.TemporalSpectralResponse

namespace LongTails.Proofs.HessianSnapshotGeometry

open scoped RealInnerProductSpace
open LongTails.Algorithms.HessianSnapshot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma coordinates_exist (B : E →L[ℝ] E) (hB : B.toLinearMap.IsSymmetric)
    {β : ℝ} (hβ : 0 < β) (hpos : ∀ x, β * ‖x‖ ^ 2 ≤ ⟪B x, x⟫) :
    ∃ S : E ≃L[ℝ] E, ∀ x, ‖S x‖ ^ 2 = ⟪B x, x⟫ := by
  obtain ⟨A, hA⟩ := OracleTemplate.TemporalDiscrepancy.spectral_factorization B hB
    (fun x => (mul_nonneg hβ.le (sq_nonneg _)).trans (hpos x))
  have hn (x : E) : ‖A x‖ ^ 2 = ⟪B x, x⟫ := by
    rw [← hA]
    simp only [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
  have hi : Function.Injective A := by
    intro x y hxy
    have hp := hpos (x - y)
    rw [← hn, map_sub, hxy, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hp
    have hs := nonpos_of_mul_nonpos_right hp hβ
    have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y), sq_nonneg ‖x - y‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  have hb : Function.Bijective (A : E →ₗ[ℝ] E) :=
    ⟨hi, LinearMap.surjective_of_injective hi⟩
  let S := (LinearEquiv.ofBijective (A : E →ₗ[ℝ] E) hb).toContinuousLinearEquiv
  exact ⟨S, hn⟩

lemma coordinates_spec (B : E →L[ℝ] E) (hB : B.toLinearMap.IsSymmetric)
    {β : ℝ} (hβ : 0 < β) (hpos : ∀ x, β * ‖x‖ ^ 2 ≤ ⟪B x, x⟫) (x : E) :
    ‖coordinates B x‖ ^ 2 = ⟪B x, x⟫ := by
  unfold coordinates
  rw [dite_eq_left (coordinates_exist B hB hβ hpos)]
  exact Classical.choose_spec (coordinates_exist B hB hβ hpos) x

end LongTails.Proofs.HessianSnapshotGeometry
