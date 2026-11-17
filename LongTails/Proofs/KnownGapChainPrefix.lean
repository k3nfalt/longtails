import LongTails.Proofs.GeneralizedSmoothChainPrefix
import LongTails.Proofs.KnownGapSmoothedChain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.KnownGapChainPrefix

open FiniteSumNondualLowerComponents GeneralizedSmoothCoordinateEmbedding
open GeneralizedSmoothChainPrefix KnownGapSmoothedChain

section

variable {m : ℕ} (hm : 0 < m) (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
  (L₀ L₁ ε h : ℝ) (h0 : 0 < L₀) (h1 : 0 < L₁) (hε : 0 < ε) (hh : 0 < h)
  (hδ : φ.rOut ≤ threshold L₁ h)

include hm h0 h1 hε hh hδ

lemma truncated_objective_eq (r : Fin m) (x : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, r ≤ i → |x i| ≤ threshold L₁ h) :
    smoothObjective φ L₀ L₁ ε h (truncate r.val x) = smoothObjective φ L₀ L₁ ε h x := by
  symm
  apply smoothObjective_prefix_eq hm φ L₀ L₁ ε h h0 h1 hε hh hδ r x (truncate r.val x)
  · intro i hi
    simp only [truncate, WithLp.ofLp_toLp, show i.val ≤ r.val from hi, ↓reduceIte]
  · exact (abs_le.mp (hx r le_rfl)).1
  · intro i hi
    exact (abs_le.mp (hx i hi.le)).2
  · intro i hi
    simp only [truncate, WithLp.ofLp_toLp, show ¬ i.val ≤ r.val from by omega, ↓reduceIte]
    exact (threshold_pos L₁ h h1 hh).le

lemma truncated_field_eq (r : Fin m) (x : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, r ≤ i → |x i| ≤ threshold L₁ h) :
    truncate r.val (smoothField φ L₀ L₁ ε h (truncate r.val x)) = smoothField φ L₀ L₁ ε h x := by
  have he : smoothField φ L₀ L₁ ε h x = smoothField φ L₀ L₁ ε h (truncate r.val x) := by
    apply smoothField_prefix_eq hm φ L₀ L₁ ε h h0 h1 hε hh hδ r x (truncate r.val x)
    · intro i hi
      simp only [truncate, WithLp.ofLp_toLp, show i.val ≤ r.val from hi, ↓reduceIte]
    · exact (abs_le.mp (hx r le_rfl)).1
    · intro i hi
      exact (abs_le.mp (hx i hi.le)).2
    · intro i hi
      simp only [truncate, WithLp.ofLp_toLp, show ¬ i.val ≤ r.val from by omega, ↓reduceIte]
      exact (threshold_pos L₁ h h1 hh).le
  rw [← he]
  apply truncate_eq_self
  intro i hi
  exact smoothField_tail_zero hm φ L₀ L₁ ε h h0 h1 hε hh hδ r i hi x
    (abs_le.mp (hx r le_rfl)).1 (abs_le.mp (hx i (by omega))).2

end

end LongTails.Proofs.KnownGapChainPrefix
