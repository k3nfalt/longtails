import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Proofs.NoisyTwoSamplePerceptronSignal

lemma mixed_pair_norm {δ a b u z : ℝ} (hδ : 0 ≤ δ) (hd : δ ≤ 1 / 56)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : a ≤ 7 / 8 + 7 / 5 * δ) (hb' : b ≤ 7 / 5 * δ) :
    (a * u + b * z) ^ 2 + (b * u + z) ^ 2 ≤
      (1 + δ / 2) ^ 2 * (u ^ 2 + z ^ 2) := by
  have h₁ : a + 4 * b ≤ 1 + δ / 2 := by linarith
  have h₂ : 1 + b / 4 ≤ 1 + δ / 2 := by linarith
  have h₃ : (a * u + b * z) ^ 2 ≤ (a + 4 * b) * (a * u ^ 2 + b / 4 * z ^ 2) := by
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (2 * u - z / 2))]
  have h₄ : (b * u + z) ^ 2 ≤ (1 + b / 4) * (4 * b * u ^ 2 + z ^ 2) := by
    nlinarith [mul_nonneg hb (sq_nonneg (2 * u - z / 2))]
  calc
    _ ≤ (1 + δ / 2) * (a * u ^ 2 + b / 4 * z ^ 2) +
        (1 + δ / 2) * (4 * b * u ^ 2 + z ^ 2) := by
      exact add_le_add (h₃.trans (mul_le_mul_of_nonneg_right h₁ (by positivity)))
        (h₄.trans (mul_le_mul_of_nonneg_right h₂ (by positivity)))
    _ = (1 + δ / 2) * ((a + 4 * b) * u ^ 2 + (1 + b / 4) * z ^ 2) := by ring
    _ ≤ (1 + δ / 2) * ((1 + δ / 2) * u ^ 2 + (1 + δ / 2) * z ^ 2) := by
      gcongr
    _ = _ := by ring

open scoped RealInnerProductSpace in
lemma repeated_move {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (hA : ∀ x y, ⟪A x,y⟫ = ⟪x,A y⟫) (hL : ‖A‖ ≤ 1/2)
    (x y e : E) (hy : y = x + A x + e) (hm : ⟪A y,y⟫ ≤ 0) :
    ‖y‖ ≤ ‖x‖+2*‖e‖ := by
  let v := y-x
  have hv : v = A x+e := by dsimp [v]; rw [hy]; abel
  have hV : y = x+v := by dsimp [v]; abel
  have hvx : A x = v-e := by rw [hv]; abel
  have hAy : A y = v-e+A v := by conv_lhs => rw [hV,map_add,hvx]
  have habs := abs_real_inner_le_norm (A v) v
  have hAv := (A.le_opNorm v).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have hquad : -(‖v‖^2/2) ≤ ⟪A v,v⟫ := by
    nlinarith only [(abs_le.mp habs).1,mul_le_mul_of_nonneg_right hAv (norm_nonneg v)]
  have h₁ : ⟪A v,y⟫ = ‖v‖^2-⟪v,e⟫+⟪A v,v⟫ := by
    rw [hA,hAy,inner_add_right,inner_sub_right,real_inner_self_eq_norm_sq,real_inner_comm v (A v)]
  rw [hAy,inner_add_left,inner_sub_left,h₁] at hm
  have hsq := norm_sub_sq_real y x
  have hid : ‖y‖^2-‖x‖^2 = 2*⟪v,y⟫-‖v‖^2 := by
    dsimp [v]
    rw [inner_sub_left,real_inner_self_eq_norm_sq,real_inner_comm y x]
    linarith
  by_contra! h
  have hdist := norm_add_le x v
  rw [← hV] at hdist
  have h₀ : ‖e‖ ≤ ‖v‖ := by linarith [norm_nonneg e]
  have h₁ := real_inner_le_norm v e
  have h₂ := real_inner_le_norm e y
  have hprod := mul_pos (show 0 < ‖y‖-‖x‖-2*‖e‖ by linarith)
    (show 0 < ‖y‖+‖x‖ by linarith [norm_nonneg e,norm_nonneg x])
  nlinarith only [hprod,hid,hquad,hm,h₁,h₂,mul_le_mul_of_nonneg_left h₀ (norm_nonneg v),
    mul_nonneg (norm_nonneg e) (norm_nonneg x)]

lemma partition_prefix (u : ℕ → ℝ) (T : ℕ) {e : ℝ} (he : 0 ≤ e)
    (hone : ∀ i < T, u (i+1) ≤ 2*u i+e)
    (htwo : ∀ i, i+2 ≤ T → u (i+1) ≤ u i+2*e ∨ u (i+2) ≤ u i+3*e)
    (hpos : ∀ i, 0 ≤ u i) (start n : ℕ) (hT : start+n ≤ T) :
    u (start+n) ≤ 2*u start+4*n*e := by
  induction n using Nat.strong_induction_on generalizing start with
  | h n ih =>
    obtain _|n := n
    · norm_num
      linarith [hpos start]
    obtain _|n := n
    · norm_num
      linarith [hone start (by omega)]
    obtain H|H := htwo start (by omega)
    · have h := ih (n+1) (by omega) (start+1) (by omega)
      rw [show start+1+(n+1) = start+(n+1+1) by omega] at h
      push_cast at h ⊢
      nlinarith only [h,H]
    · have h := ih n (by omega) (start+2) (by omega)
      rw [show start+2+n = start+(n+1+1) by omega] at h
      push_cast
      nlinarith only [h,H,he]

end LongTails.Proofs.NoisyTwoSamplePerceptronSignal
