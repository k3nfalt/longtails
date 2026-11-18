import LongTails.Proofs.GeneralizedSmoothChainPrefix
import LongTails.Proofs.TailEntropySmoothedChain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.TailEntropyChainPrefix

open FiniteSumNondualLowerComponents GeneralizedSmoothCoordinateEmbedding
open GeneralizedSmoothChainPrefix TailEntropySmoothedChain

section

variable {m : ℕ} (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)))
  (L₀ L₁ ε h : ℝ) (h0 : 0 < L₀) (h1 : 0 < L₁) (hε : 0 < ε) (hh : 0 < h) (hh1 : h ≤ 1)
  (hδ : φ.rOut ≤ threshold L₁)

include h0 h1 hε hh hh1 hδ

lemma truncated_objective_eq (r : Fin m) (x : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, r ≤ i → |x i| ≤ threshold L₁) :
    smoothObjective φ L₀ L₁ ε h (truncate r.val x) = smoothObjective φ L₀ L₁ ε h x := by
  symm
  apply smoothObjective_prefix_eq φ L₀ L₁ ε h h0 h1 hε hh hh1 hδ r x (truncate r.val x)
  · intro i hi
    simp only [truncate, WithLp.ofLp_toLp, show i.val ≤ r.val from hi, ↓reduceIte]
  · exact (abs_le.mp (hx r le_rfl)).1
  · intro i hi
    exact (abs_le.mp (hx i hi.le)).2
  · intro i hi
    simp only [truncate, WithLp.ofLp_toLp, show ¬ i.val ≤ r.val from by omega, ↓reduceIte]
    exact (threshold_pos L₁ h1).le

lemma truncated_field_eq (r : Fin m) (x : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, r ≤ i → |x i| ≤ threshold L₁) :
    truncate r.val (smoothField φ L₀ L₁ ε h (truncate r.val x)) = smoothField φ L₀ L₁ ε h x := by
  have he : smoothField φ L₀ L₁ ε h x = smoothField φ L₀ L₁ ε h (truncate r.val x) := by
    apply smoothField_prefix_eq φ L₀ L₁ ε h h0 h1 hε hh hh1 hδ r x (truncate r.val x)
    · intro i hi
      simp only [truncate, WithLp.ofLp_toLp, show i.val ≤ r.val from hi, ↓reduceIte]
    · exact (abs_le.mp (hx r le_rfl)).1
    · intro i hi
      exact (abs_le.mp (hx i hi.le)).2
    · intro i hi
      simp only [truncate, WithLp.ofLp_toLp, show ¬ i.val ≤ r.val from by omega, ↓reduceIte]
      exact (threshold_pos L₁ h1).le
  rw [← he]
  apply truncate_eq_self
  intro i hi
  exact smoothField_tail_zero φ L₀ L₁ ε h h0 h1 hε hh hh1 hδ r x
    (abs_le.mp (hx r le_rfl)).1 (fun l hl => (abs_le.mp (hx l hl.le)).2) i hi

end

end LongTails.Proofs.TailEntropyChainPrefix
