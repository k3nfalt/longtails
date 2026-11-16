import LongTails.Proofs.AsgoFixedRadiusMatrix

open Matrix Finset
open scoped BigOperators

namespace OracleTemplate.AsgoFixedRadius

open LongTails.Setups.AsgoFixedRadius

lemma combined_metric_posDef {m : ℕ} (L V : Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (hL : L.PosDef) (hV : V.PosDef) (hc : 0 < c) :
    (L + c • V).PosDef := by
  open Matrix in
  open scoped BigOperators in
  (
    exact hL.add (hV.smul hc)
  )

lemma combined_metric_control {m n : ℕ} (L V : Matrix (Fin m) (Fin m) ℝ)
    (grad noise : ℕ → Muon.Mat m n) (R : ℝ) (T M : ℕ)
    (hL : L.PosDef) (hV : V.PosDef) (hR : 0 < R) (hT : 0 < T) (hM : 0 < M) :
    let c := Real.sqrt ((T : ℝ) / M) / (2 * R)
    let a := 3 * R / 2
    a * (Core.matrixRoot (∑ t ∈ range T, Core.gram (grad t + noise t))).trace ≤
      (∑ t ∈ range T, Core.weightedQuadratic (L⁻¹) (grad t)) / 2 +
      (∑ t ∈ range T, Core.weightedQuadratic (V⁻¹) (noise t)) / (2 * c) +
      a ^ 2 * L.trace + a ^ 2 * c * V.trace := by
  open Matrix in
  open scoped BigOperators in
  (
    classical
    let c := Real.sqrt ((T : ℝ) / M) / (2*R)
    let a := 3*R/2
    let A := L+c•V
    let Q := ∑ t ∈ range T, Core.gram (grad t+noise t)
    have hc : 0<c := div_pos (Real.sqrt_pos.2 (div_pos (Nat.cast_pos.2 hT) (Nat.cast_pos.2 hM))) (by positivity)
    have hA : A.PosDef := combined_metric_posDef L V c hL hV hc
    have hAi := (inverse_posDef A hA).1.posSemidef
    have hQ : Q.PosSemidef := Matrix.posSemidef_sum _ (fun t _ => by
      delta Core.gram
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose (Muon.toMatrix (grad t+noise t)))
    have hLA : Core.loewner L A := by
      delta Core.loewner
      simpa only [A,add_sub_cancel_left] using hV.posSemidef.smul hc.le
    have hVA : Core.loewner (c•V) A := by
      delta Core.loewner
      simpa only [A,add_sub_cancel_right] using hL.posSemidef
    have hInv : (c•V)⁻¹ = c⁻¹•V⁻¹ := by
      let := invertibleOfNonzero hc.ne'
      rw [Matrix.inv_smul V c ((Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit), invOf_eq_inv]
    have hpair : ∀ X Y : Muon.Mat m n,
        Core.weightedQuadratic A⁻¹ (X+Y) ≤ 2*Core.weightedQuadratic A⁻¹ X+2*Core.weightedQuadratic A⁻¹ Y := by
      intro X Y
      have hh := quadratic_nonneg A⁻¹ (X-Y) hAi
      change 0 ≤ ((Muon.toMatrix X-Muon.toMatrix Y)ᵀ*A⁻¹*(Muon.toMatrix X-Muon.toMatrix Y)).trace at hh
      change ((Muon.toMatrix X+Muon.toMatrix Y)ᵀ*A⁻¹*(Muon.toMatrix X+Muon.toMatrix Y)).trace ≤ _
      delta Core.weightedQuadratic
      simp only [Matrix.transpose_sub, Matrix.transpose_add,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
        Matrix.trace_sub, Matrix.trace_add] at hh ⊢
      linarith
    have hpoint : ∀ t, Core.weightedQuadratic A⁻¹ (grad t+noise t) ≤
        2*Core.weightedQuadratic L⁻¹ (grad t)+(2*c⁻¹)*Core.weightedQuadratic V⁻¹ (noise t) := by
      intro t
      have h1 := inverse_quadratic_order A L (grad t) hA hL hLA
      have h2 := inverse_quadratic_order A (c•V) (noise t) hA (hV.smul hc) hVA
      rw [hInv] at h2
      delta Core.weightedQuadratic at h2
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,smul_eq_mul] at h2
      have hp := hpair (grad t) (noise t)
      change Core.weightedQuadratic A⁻¹ (noise t) ≤
        c⁻¹ * Core.weightedQuadratic V⁻¹ (noise t) at h2
      linarith
    have hsum := Finset.sum_le_sum (s := range T) (fun t _ => hpoint t)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have ht : (A⁻¹*Q).trace = ∑ t ∈ range T, Core.weightedQuadratic A⁻¹ (grad t+noise t) := by
      dsimp only [Q]
      rw [Matrix.mul_sum, Matrix.trace_sum]
      apply Finset.sum_congr rfl
      intro t _
      delta Core.gram Core.weightedQuadratic
      rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    have htr : A.trace=L.trace+c*V.trace := by
      simp only [A,Matrix.trace_add,Matrix.trace_smul,smul_eq_mul]
    have hy := weighted_trace_young A Q a hA hQ
    rw [ht,htr] at hy
    change a*(Core.matrixRoot Q).trace ≤
      (∑ t ∈ range T, Core.weightedQuadratic L⁻¹ (grad t))/2+
      (∑ t ∈ range T, Core.weightedQuadratic V⁻¹ (noise t))/(2*c)+a^2*L.trace+a^2*c*V.trace
    norm_num only [div_eq_mul_inv, _root_.mul_inv_rev] at hy ⊢
    nlinarith
  )

end OracleTemplate.AsgoFixedRadius
