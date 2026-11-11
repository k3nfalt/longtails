import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic

namespace LongTails.Proofs.MirrorGeneralizedGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma prox_stationary {ψ : E → ℝ} {dψ : E → E →L[ℝ] ℝ}
    (hdψ : ∀ x, HasFDerivAt ψ (dψ x) x) (z w : E) (v : E →L[ℝ] ℝ)
    (hmin : ∀ u, v w + ψ w - dψ z w ≤ v u + ψ u - dψ z u) :
    v + dψ w - dψ z = 0 := by
  have hd := ((v.hasFDerivAt.add (hdψ w)).sub (dψ z).hasFDerivAt)
  have hm : IsMinOn (fun u => v u + ψ u - dψ z u) Set.univ w :=
    fun u _ => hmin u
  exact (hm.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero hd

lemma prox_three_point {ψ : E → ℝ} {dψ : E → E →L[ℝ] ℝ}
    (hdψ : ∀ x, HasFDerivAt ψ (dψ x) x) (z w u : E) (v : E →L[ℝ] ℝ)
    (hmin : ∀ y, v w + ψ w - dψ z w ≤ v y + ψ y - dψ z y) :
    v (w - u) = (ψ u - ψ z - dψ z (u - z)) -
      (ψ u - ψ w - dψ w (u - w)) - (ψ w - ψ z - dψ z (w - z)) := by
  have h := congrArg (fun q : E →L[ℝ] ℝ => q (w - u))
    (prox_stationary hdψ z w v hmin)
  simp only [sub_apply, add_apply, zero_apply, map_sub] at h ⊢
  linarith

lemma prox_displacement {ψ : E → ℝ} {dψ : E → E →L[ℝ] ℝ}
    (hdψ : ∀ x, HasFDerivAt ψ (dψ x) x)
    (hstrong : ∀ x y, ‖y - x‖ ^ 2 / 2 ≤ ψ y - ψ x - dψ x (y - x))
    (z w : E) (v : E →L[ℝ] ℝ)
    (hmin : ∀ u, v w + ψ w - dψ z w ≤ v u + ψ u - dψ z u) :
    ‖w - z‖ ≤ ‖v‖ := by
  have h := prox_three_point hdψ z w z v hmin
  have h1 := hstrong z w
  have h2 := hstrong w z
  have hb := v.le_opNorm (z - w)
  have hl := le_abs_self (v (z - w))
  rw [norm_sub_rev z w] at hb h2
  simp only [sub_self, map_zero, map_sub] at h
  simp only [map_sub] at h1 h2 hb hl
  rw [Real.norm_eq_abs] at hb
  nlinarith [norm_nonneg (w - z), norm_nonneg v]

end LongTails.Proofs.MirrorGeneralizedGeometry
