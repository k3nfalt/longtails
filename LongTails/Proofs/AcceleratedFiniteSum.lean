import LongTails.Proofs.SvrgConvex

open Set

namespace OracleTemplate.FiniteSum

open LongTails.Setups.FiniteSumSmoothAndConvex

variable {n : ℕ} [NeZero n] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [NeZero n] in
lemma objective_convex {f : Fin n → E → ℝ}
    (hc : ∀ i, ConvexOn ℝ Set.univ (f i)) : ConvexOn ℝ Set.univ (objective f) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    (hc i).2 hx hy ha hb hab)
  simp only [smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  simpa [objective, smul_eq_mul, mul_add, mul_left_comm] using
    mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Nat.cast_nonneg n))

lemma fullGradient_lipschitz {g : Fin n × E → E} {L : ℝ}
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖fullGradient g x - fullGradient g y‖ ≤ L * ‖x - y‖ := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  calc
    _ = (n : ℝ)⁻¹ * ‖∑ i, (g (i, x) - g (i, y))‖ := by
      simp [fullGradient, ← smul_sub, ← Finset.sum_sub_distrib, norm_smul]
    _ ≤ (n : ℝ)⁻¹ * ∑ i, ‖g (i, x) - g (i, y)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (n : ℝ)⁻¹ * ∑ _ : Fin n, L * ‖x - y‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hlip i x y)) (by positivity)
    _ = _ := by simp [hn]

end OracleTemplate.FiniteSum
