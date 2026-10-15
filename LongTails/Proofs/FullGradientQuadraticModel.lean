import LongTails.Proofs.QuadraticFiniteSumModel

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.FullGradientAccelerated

open LongTails.Setups.QuadraticFiniteSum

variable {p : Params} (f : Instance p)

noncomputable def averageGradient (x : p.E) : p.E :=
  (p.n : ℝ)⁻¹ • ∑ i, (f.A i x + f.b i)

lemma objective_hasGradientAt (hs : ∀ i, (f.A i).toLinearMap.IsSymmetric) (x : p.E) :
    HasGradientAt (objective f) (averageGradient f x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (QuadraticFiniteSum.component_hasGradientAt f i (hs i) x).hasFDerivAt)).const_smul
      ((p.n : ℝ)⁻¹)
  convert hd using 1
  · rfl
  · simp [averageGradient, map_smul, map_sum]

lemma objective_gradient (hs : ∀ i, (f.A i).toLinearMap.IsSymmetric) (x : p.E) :
    gradient (objective f) x = averageGradient f x :=
  (objective_hasGradientAt f hs x).gradient

lemma objective_expansion (hs : ∀ i, (f.A i).toLinearMap.IsSymmetric) (x y : p.E) :
    objective f y - objective f x =
      ⟪averageGradient f x, y - x⟫ +
        (p.n : ℝ)⁻¹ * (∑ i, ⟪y - x, f.A i (y - x)⟫) / 2 := by
  unfold objective averageGradient
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [QuadraticFiniteSum.component_gap f _ (hs _)]
  rw [Finset.sum_add_distrib, ← sum_inner, inner_smul_left, ← Finset.sum_div]
  simp only [RCLike.conj_to_real]
  ring

lemma quadratic_upper (hA : ∀ i, ‖f.A i‖ ≤ p.L) (v : p.E) :
    (p.n : ℝ)⁻¹ * (∑ i, ⟪v, f.A i v⟫) ≤ p.L * ‖v‖ ^ 2 := by
  have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p.n
  have hsum : (∑ i, ⟪v, f.A i v⟫) ≤ (p.n : ℝ) * (p.L * ‖v‖ ^ 2) := by
    calc
      _ ≤ ∑ _i : Fin p.n, p.L * ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          _ ≤ ‖v‖ * ‖f.A i v‖ := real_inner_le_norm _ _
          _ ≤ ‖v‖ * (p.L * ‖v‖) := mul_le_mul_of_nonneg_left
            (((f.A i).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))) (norm_nonneg _)
          _ = _ := by ring
      _ = _ := by simp
  have hh := mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr (Nat.cast_nonneg p.n : (0 : ℝ) ≤ _))
  simpa only [← mul_assoc, inv_mul_cancel₀ hn, one_mul] using hh

lemma objective_smooth (hs : ∀ i, (f.A i).toLinearMap.IsSymmetric)
    (hA : ∀ i, ‖f.A i‖ ≤ p.L) (x y : p.E) :
    objective f y ≤ objective f x + ⟪gradient (objective f) x, y - x⟫ +
      p.L / 2 * ‖y - x‖ ^ 2 := by
  rw [objective_gradient f hs]
  have he := objective_expansion f hs x y
  have hb := quadratic_upper f hA (y - x)
  linarith

lemma objective_strong (hs : ∀ i, (f.A i).toLinearMap.IsSymmetric)
    (hp : ∀ x, p.μ * ‖x‖ ^ 2 ≤ (p.n : ℝ)⁻¹ * ∑ i, ⟪x, f.A i x⟫)
    (x y : p.E) :
    objective f x + ⟪gradient (objective f) x, y - x⟫ +
      p.μ / 2 * ‖y - x‖ ^ 2 ≤ objective f y := by
  rw [objective_gradient f hs]
  have he := objective_expansion f hs x y
  have hb := hp (y - x)
  linarith

end OracleTemplate.FullGradientAccelerated
