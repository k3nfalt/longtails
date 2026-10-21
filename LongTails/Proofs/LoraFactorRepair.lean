import LongTails.Proofs.LoraMatrix

namespace LongTails.Proofs.LoraFactorRepair

open LongTails.Algorithms.LoraGd LongTails.Proofs.LoraGeometry LongTails.Proofs.LoraMatrix

lemma lower_injective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] F) {s : ℝ}
    (hs : 0 < s) (hB : ∀ v, s * ‖v‖ ≤ ‖B v‖) : Function.Injective B := by
  intro u v huv
  have hh := hB (u - v)
  rw [map_sub, huv, sub_self, norm_zero] at hh
  have hz : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

lemma projected_lower {m r : ℕ}
    (B B₀ : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin m))
    {s : ℝ} (hB₀ : ∀ v, s * ‖v‖ ≤ ‖B₀ v‖)
    (hclose : ∀ v, ‖B v - B₀ v‖ ≤ (s / 2) * ‖v‖) :
    ∀ v, (s / 2) * ‖v‖ ≤ ‖B₀.toLinearMap.range.starProjection (B v)‖ := by
  intro v
  let U := B₀.toLinearMap.range
  have hfix : U.starProjection (B₀ v) = B₀ v :=
    U.starProjection_eq_self_iff.mpr ⟨v, rfl⟩
  have herr : ‖U.starProjection (B v) - B₀ v‖ ≤ (s / 2) * ‖v‖ := by
    rw [← hfix, ← map_sub]
    exact (U.norm_starProjection_apply_le _).trans (hclose v)
  have hb := hB₀ v
  have hn := norm_sub_le (U.starProjection (B v)) (U.starProjection (B v) - B₀ v)
  rw [sub_sub_cancel] at hn
  change (s / 2) * ‖v‖ ≤ ‖U.starProjection (B v)‖
  linarith

lemma projected_range {m r : ℕ}
    (B B₀ : EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin m))
    {s : ℝ} (hs : 0 < s) (hB₀ : ∀ v, s * ‖v‖ ≤ ‖B₀ v‖)
    (hclose : ∀ v, ‖B v - B₀ v‖ ≤ (s / 2) * ‖v‖) :
    (B₀.toLinearMap.range.starProjection.comp B).toLinearMap.range =
      B₀.toLinearMap.range := by
  have hi₀ := lower_injective B₀ hs hB₀
  have hi := lower_injective (B₀.toLinearMap.range.starProjection.comp B)
    (half_pos hs) (projected_lower B B₀ hB₀ hclose)
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨v, rfl⟩
    exact B₀.toLinearMap.range.starProjection_apply_mem _
  · rw [LinearMap.finrank_range_of_inj hi, LinearMap.finrank_range_of_inj hi₀]

lemma matrix_repair {m n r : ℕ} (B B₀ : MatrixSpace m r) (A A₀ : MatrixSpace r n)
    {s : ℝ} (hs : 0 < s)
    (hB₀ : ∀ v, s * ‖v‖ ≤ ‖action B₀ v‖)
    (hA₀ : ∀ v, s * ‖v‖ ≤ ‖action (transpose A₀) v‖)
    (hBclose : ‖B - B₀‖ ≤ s / 2) (hAclose : ‖A - A₀‖ ≤ s / 2) :
    ∃ Bhat : MatrixSpace m r, ∃ Ahat : MatrixSpace r n,
      multiply Bhat Ahat = multiply B₀ A₀ ∧
      (s / 2) * ‖B - Bhat‖ ≤ ‖multiply B A - multiply B₀ A₀‖ ∧
      (s / 2) * ‖A - Ahat‖ ≤ ‖multiply B A - multiply B₀ A₀‖ := by
  let U := (actionMap B₀).toLinearMap.range
  let P := U.starProjection
  let Q := Uᗮ.starProjection
  let Bhat := leftApply P B
  have hc : ∀ v, ‖actionMap B v - actionMap B₀ v‖ ≤ (s / 2) * ‖v‖ := by
    intro v
    change ‖action B v - action B₀ v‖ ≤ _
    rw [← action_sub]
    exact (action_norm _ _).trans (mul_le_mul_of_nonneg_right hBclose (norm_nonneg _))
  have hBlow : ∀ v, (s / 2) * ‖v‖ ≤ ‖action Bhat v‖ := by
    intro v
    rw [action_leftApply]
    exact projected_lower (actionMap B) (actionMap B₀) hB₀ hc v
  have hmap : actionMap Bhat = P.comp (actionMap B) := by
    apply ContinuousLinearMap.ext
    intro v
    exact action_leftApply P B v
  have hrange : (actionMap Bhat).toLinearMap.range = U := by
    rw [hmap]
    exact projected_range (actionMap B) (actionMap B₀) hs hB₀ hc
  obtain ⟨Ahat, hprod⟩ := exists_multiply_eq Bhat (multiply B₀ A₀) (by
    intro j
    rw [hrange, multiply_column]
    exact ⟨column A₀ j, rfl⟩)
  have hPfix : leftApply P (multiply B₀ A₀) = multiply B₀ A₀ := by
    rw [leftApply_multiply]
    change multiply (leftApply (actionMap B₀).toLinearMap.range.starProjection B₀) A₀ = _
    rw [leftApply_projection_fixed]
  have hQfix : leftApply Q (multiply B₀ A₀) = 0 := by
    rw [leftApply_projection_complement, hPfix, sub_self]
  have hBdiff : B - Bhat = leftApply Q B := (leftApply_projection_complement U B).symm
  have hAdiff : multiply Bhat (A - Ahat) =
      leftApply P (multiply B A - multiply B₀ A₀) := by
    rw [multiply_sub_right, hprod, leftApply_sub, hPfix, leftApply_multiply]
  have hAlow : ∀ v, (s / 2) * ‖v‖ ≤ ‖action (transpose A) v‖ := by
    apply lower_perturbation _ _ hA₀
    rw [← transpose_sub, transpose_norm]
    exact hAclose
  refine ⟨Bhat, Ahat, hprod, ?_, ?_⟩
  · calc
      (s / 2) * ‖B - Bhat‖ ≤ ‖multiply (B - Bhat) A‖ :=
        multiply_lower_right _ _ (le_of_lt (half_pos hs)) hAlow
      _ = ‖leftApply Q (multiply B A - multiply B₀ A₀)‖ := by
        rw [hBdiff, ← leftApply_multiply, leftApply_sub, hQfix, sub_zero]
      _ ≤ ‖multiply B A - multiply B₀ A₀‖ := by
        simpa only [one_mul] using leftApply_norm Q (multiply B A - multiply B₀ A₀)
          zero_le_one (fun v => by simpa only [one_mul] using Uᗮ.norm_starProjection_apply_le v)
  · calc
      (s / 2) * ‖A - Ahat‖ ≤ ‖multiply Bhat (A - Ahat)‖ :=
        multiply_lower_left _ _ (le_of_lt (half_pos hs)) hBlow
      _ = ‖leftApply P (multiply B A - multiply B₀ A₀)‖ := congrArg norm hAdiff
      _ ≤ ‖multiply B A - multiply B₀ A₀‖ := by
        simpa only [one_mul] using leftApply_norm P (multiply B A - multiply B₀ A₀)
          zero_le_one (fun v => by simpa only [one_mul] using U.norm_starProjection_apply_le v)

noncomputable def combine {m n r : ℕ} (B : MatrixSpace m r) (A : MatrixSpace r n) :
    Factors m n r := WithLp.toLp 2 (Sum.elim (fun ik => B ik) (fun kj => A kj))

lemma leftPart_combine {m n r : ℕ} (B : MatrixSpace m r) (A : MatrixSpace r n) :
    leftPart (combine B A) = B := by ext ik; rfl

lemma rightPart_combine {m n r : ℕ} (B : MatrixSpace m r) (A : MatrixSpace r n) :
    rightPart (combine B A) = A := by ext kj; rfl

lemma leftPart_norm {m n r : ℕ} (x : Factors m n r) : ‖leftPart x‖ ≤ ‖x‖ := by
  have hh := factor_norm_sq x
  nlinarith [norm_nonneg x, norm_nonneg (leftPart x), sq_nonneg ‖rightPart x‖]

lemma rightPart_norm {m n r : ℕ} (x : Factors m n r) : ‖rightPart x‖ ≤ ‖x‖ := by
  have hh := factor_norm_sq x
  nlinarith [norm_nonneg x, norm_nonneg (rightPart x), sq_nonneg ‖leftPart x‖]

lemma factor_repair {m n r : ℕ} (x v : Factors m n r) {s : ℝ} (hs : 0 < s)
    (hB : ∀ w, s * ‖w‖ ≤ ‖leftAction v w‖)
    (hA : ∀ w, s * ‖w‖ ≤ ‖rightTransposeAction v w‖)
    (hclose : ‖x - v‖ ≤ s / 2) :
    ∃ z : Factors m n r, product z = product v ∧
      s ^ 2 * ‖x - z‖ ^ 2 ≤ 8 * ‖product x - product v‖ ^ 2 := by
  have hbclose : ‖leftPart x - leftPart v‖ ≤ s / 2 :=
    (leftPart_norm (x - v)).trans hclose
  have haclose : ‖rightPart x - rightPart v‖ ≤ s / 2 :=
    (rightPart_norm (x - v)).trans hclose
  obtain ⟨Bhat, Ahat, hp, hb, ha⟩ := matrix_repair (leftPart x) (leftPart v)
    (rightPart x) (rightPart v) hs hB hA hbclose haclose
  refine ⟨combine Bhat Ahat, hp, ?_⟩
  have hb2 := pow_le_pow_left₀ (mul_nonneg (le_of_lt (half_pos hs)) (norm_nonneg _)) hb 2
  have ha2 := pow_le_pow_left₀ (mul_nonneg (le_of_lt (half_pos hs)) (norm_nonneg _)) ha 2
  rw [factor_norm_sq]
  change s ^ 2 * (‖leftPart x - Bhat‖ ^ 2 + ‖rightPart x - Ahat‖ ^ 2) ≤ _
  change (s / 2 * ‖leftPart x - Bhat‖) ^ 2 ≤ ‖product x - product v‖ ^ 2 at hb2
  change (s / 2 * ‖rightPart x - Ahat‖) ^ 2 ≤ ‖product x - product v‖ ^ 2 at ha2
  nlinarith

end LongTails.Proofs.LoraFactorRepair
