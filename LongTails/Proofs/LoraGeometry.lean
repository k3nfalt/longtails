import LongTails.Algorithms.LoraGd
import LongTails.Proofs.LoraLocalInterpolation

namespace LongTails.Proofs.LoraGeometry

open LongTails.Algorithms.LoraGd
open scoped RealInnerProductSpace

noncomputable def leftPart {m n r : ℕ} (x : Factors m n r) : MatrixSpace m r :=
  WithLp.toLp 2 fun ik => x (Sum.inl ik)

noncomputable def rightPart {m n r : ℕ} (x : Factors m n r) : MatrixSpace r n :=
  WithLp.toLp 2 fun kj => x (Sum.inr kj)

noncomputable def multiply {m n r : ℕ} (B : MatrixSpace m r) (A : MatrixSpace r n) :
    MatrixSpace m n :=
  WithLp.toLp 2 fun ij => ∑ k, B (ij.1, k) * A (k, ij.2)

lemma factor_norm_sq {m n r : ℕ} (x : Factors m n r) :
    ‖x‖ ^ 2 = ‖leftPart x‖ ^ 2 + ‖rightPart x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type,
    leftPart, rightPart]

lemma multiply_norm_sq {m n r : ℕ} (B : MatrixSpace m r) (A : MatrixSpace r n) :
    ‖multiply B A‖ ^ 2 ≤ ‖B‖ ^ 2 * ‖A‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type,
    multiply]
  calc
    (∑ i, ∑ j, (∑ k, B (i, k) * A (k, j)) ^ 2) ≤
        ∑ i, ∑ j, (∑ k, B (i, k) ^ 2) * (∑ k, A (k, j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = (∑ i, ∑ k, B (i, k) ^ 2) * (∑ j, ∑ k, A (k, j) ^ 2) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ = (∑ i, ∑ k, B (i, k) ^ 2) * (∑ k, ∑ j, A (k, j) ^ 2) := by
      rw [Finset.sum_comm (f := fun j k => A (k, j) ^ 2)]

lemma multiply_norm {m n r : ℕ} (B : MatrixSpace m r) (A : MatrixSpace r n) :
    ‖multiply B A‖ ≤ ‖B‖ * ‖A‖ := by
  have h := multiply_norm_sq B A
  nlinarith [norm_nonneg (multiply B A), mul_nonneg (norm_nonneg B) (norm_nonneg A)]

lemma product_norm {m n r : ℕ} (x : Factors m n r) :
    ‖product x‖ ≤ ‖x‖ ^ 2 / 2 := by
  have he : product x = multiply (leftPart x) (rightPart x) := rfl
  rw [he]
  have hm := multiply_norm (leftPart x) (rightPart x)
  have hs := factor_norm_sq x
  nlinarith [sq_nonneg (‖leftPart x‖ - ‖rightPart x‖)]

lemma product_remainder {m n r : ℕ} (u v : Factors m n r) :
    product u - product v - linearization v (u - v) = product (u - v) := by
  ext ij
  simp only [product, linearization, PiLp.sub_apply, PiLp.toLp_apply,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma linearization_sub {m n r : ℕ} (u v h : Factors m n r) :
    linearization u h - linearization v h = linearization (u - v) h := by
  ext ij
  simp only [linearization, PiLp.sub_apply, PiLp.toLp_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma linearization_multiply {m n r : ℕ} (x h : Factors m n r) :
    linearization x h = multiply (leftPart h) (rightPart x) +
      multiply (leftPart x) (rightPart h) := by
  ext ij
  simp only [linearization, multiply, leftPart, rightPart, PiLp.toLp_apply,
    PiLp.add_apply, Finset.sum_add_distrib]

lemma linearization_norm {m n r : ℕ} (x h : Factors m n r) :
    ‖linearization x h‖ ≤ ‖x‖ * ‖h‖ := by
  have hb := multiply_norm (leftPart h) (rightPart x)
  have ha := multiply_norm (leftPart x) (rightPart h)
  have hsx := factor_norm_sq x
  have hsh := factor_norm_sq h
  have hcs : (‖leftPart h‖ * ‖rightPart x‖ + ‖leftPart x‖ * ‖rightPart h‖) ^ 2 ≤
      (‖x‖ * ‖h‖) ^ 2 := by
    rw [mul_pow, hsx, hsh]
    nlinarith [sq_nonneg (‖leftPart h‖ * ‖leftPart x‖ - ‖rightPart h‖ * ‖rightPart x‖)]
  have hnon : 0 ≤ ‖leftPart h‖ * ‖rightPart x‖ + ‖leftPart x‖ * ‖rightPart h‖ := by positivity
  have hbound : ‖leftPart h‖ * ‖rightPart x‖ + ‖leftPart x‖ * ‖rightPart h‖ ≤
      ‖x‖ * ‖h‖ := by
    nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg h)]
  rw [linearization_multiply]
  exact (norm_add_le _ _).trans ((add_le_add hb ha).trans hbound)

noncomputable def derivative {m n r : ℕ} (x : Factors m n r) :
    Factors m n r →L[ℝ] MatrixSpace m n :=
  LinearMap.mkContinuous
    { toFun := linearization x
      map_add' := by
        intro a b
        ext ij
        simp only [linearization, PiLp.add_apply, PiLp.toLp_apply,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      map_smul' := by
        intro c a
        ext ij
        simp only [linearization, PiLp.smul_apply, PiLp.toLp_apply,
          RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring }
    ‖x‖ (linearization_norm x)

lemma derivative_apply {m n r : ℕ} (x h : Factors m n r) :
    derivative x h = linearization x h := rfl

lemma derivative_sub {m n r : ℕ} (u v : Factors m n r) :
    derivative u - derivative v = derivative (u - v) := by
  apply ContinuousLinearMap.ext
  intro h
  exact linearization_sub u v h

lemma derivative_norm {m n r : ℕ} (x : Factors m n r) :
    ‖derivative x‖ ≤ ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (linearization_norm x)

lemma derivative_difference_norm {m n r : ℕ} (u v : Factors m n r) :
    ‖derivative u - derivative v‖ ≤ ‖u - v‖ := by
  rw [derivative_sub]
  exact derivative_norm _

lemma remainder_norm {m n r : ℕ} (u v : Factors m n r) :
    ‖product u - product v - derivative v (u - v)‖ ≤ ‖u - v‖ ^ 2 / 2 := by
  rw [derivative_apply, product_remainder]
  exact product_norm _

lemma derivative_local_bound {m n r : ℕ} (x v : Factors m n r) {R a : ℝ}
    (hv : ∀ h, ‖linearization v h‖ ≤ R * ‖h‖) (hR : 0 ≤ R)
    (hx : ‖x - v‖ ≤ a) : ‖derivative x‖ ≤ R + a := by
  have hb : ‖derivative v‖ ≤ R := ContinuousLinearMap.opNorm_le_bound _ hR hv
  calc
    ‖derivative x‖ ≤ ‖derivative v‖ + ‖derivative x - derivative v‖ :=
      calc
        ‖derivative x‖ = ‖derivative v + (derivative x - derivative v)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    _ ≤ R + a := add_le_add hb ((derivative_difference_norm x v).trans hx)

lemma product_local_bound {m n r : ℕ} (x v : Factors m n r) {R : ℝ}
    (hv : ∀ h, ‖linearization v h‖ ≤ R * ‖h‖) :
    ‖product x - product v‖ ≤ R * ‖x - v‖ + ‖x - v‖ ^ 2 / 2 := by
  have he : product x - product v = linearization v (x - v) + product (x - v) := by
    have h := product_remainder x v
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add (hv _) (product_norm _))

lemma pullback_inner {m n r : ℕ} (x h : Factors m n r) (G : MatrixSpace m n) :
    ⟪pullback x G, h⟫ = ⟪G, linearization x h⟫ := by
  simp only [PiLp.inner_apply, Real.inner_apply, pullback, linearization,
    Fintype.sum_sum_type, Fintype.sum_prod_type,
    Sum.elim_inl, Sum.elim_inr, Finset.sum_mul, Finset.mul_sum,
    mul_add, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  · conv_lhs =>
      arg 2
      ext k
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring

lemma pullback_adjoint {m n r : ℕ} (x : Factors m n r) (G : MatrixSpace m n) :
    pullback x G = (derivative x).adjoint G := by
  apply ext_inner_right ℝ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact pullback_inner x h G

lemma product_hasFDerivAt {m n r : ℕ} (x : Factors m n r) :
    HasFDerivAt product (derivative x) x := by
  rw [hasFDerivAt_iff_tendsto]
  have ht : Filter.Tendsto (fun y : Factors m n r => ‖y - x‖ / 2)
      (nhds x) (nhds 0) := by
    simpa using ((continuous_id.sub (continuous_const : Continuous (fun _ : Factors m n r => x))).norm.div_const 2).tendsto x
  apply squeeze_zero (fun y => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (fun y => ?_) ht
  calc
    ‖y - x‖⁻¹ * ‖product y - product x - derivative x (y - x)‖ ≤
        ‖y - x‖⁻¹ * (‖y - x‖ ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (remainder_norm y x) (inv_nonneg.mpr (norm_nonneg _))
    _ ≤ ‖y - x‖ / 2 := by
      by_cases hz : ‖y - x‖ = 0
      · simp [hz]
      · field_simp
        nlinarith

lemma objective_hasGradientAt {m n r : ℕ} {f : MatrixSpace m n → ℝ}
    (x : Factors m n r) (G : MatrixSpace m n)
    (hf : HasGradientAt f G (product x)) :
    HasGradientAt (fun y => f (product y)) (pullback x G) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := hf.hasFDerivAt.comp x (product_hasFDerivAt x)
  convert hh using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro h
    exact pullback_inner x h G

lemma linearization_repair {m n r : ℕ} (x z : Factors m n r) :
    linearization x (x - z) = product x - product z + product (x - z) := by
  ext ij
  simp only [linearization, product, PiLp.sub_apply, PiLp.add_apply, PiLp.toLp_apply,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

end LongTails.Proofs.LoraGeometry
