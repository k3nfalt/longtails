import LongTails.Proofs.NcConcaveTransitions

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveTransitionBounds

open LongTails.Proofs.NcConcaveScalars LongTails.Proofs.NcConcaveTransitions

variable {n : ℕ}

noncomputable def sq1 (v : Fin (n + 1) → ℝ) : ℝ := ∑ j, v j ^ 2

lemma sq1_nonneg (v : Fin (n + 1) → ℝ) : 0 ≤ sq1 v := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sum_castSucc_le (v : Fin (n + 1) → ℝ) : ∑ i : Fin n, v i.castSucc ^ 2 ≤ sq1 v := by
  unfold sq1
  rw [Fin.sum_univ_castSucc]
  linarith [sq_nonneg (v (Fin.last n))]

lemma sum_succ_le (v : Fin (n + 1) → ℝ) : ∑ i : Fin n, v i.succ ^ 2 ≤ sq1 v := by
  unfold sq1
  rw [Fin.sum_univ_succ]
  linarith [sq_nonneg (v 0)]

lemma dq_abs (u v : Fin (n + 1) → ℝ) (i : Fin n) :
    |dq u v i| ≤ 3 / 2 * |v i.castSucc| + 3 / 2 * |v i.succ| := by
  unfold dq
  have h1 := dnu_nonneg (u i.castSucc)
  have h2 := dnu_le (u i.castSucc)
  have h3 := nu_nonneg (u i.succ)
  have h4 := nu_le_one (u i.succ)
  have h5 := nu_nonneg (u i.castSucc)
  have h6 := nu_le_one (u i.castSucc)
  have h7 := dnu_nonneg (u i.succ)
  have h8 := dnu_le (u i.succ)
  have ha : |dnu (u i.castSucc) * v i.castSucc * (1 - nu (u i.succ))| ≤ 3 / 2 * |v i.castSucc| := by
    rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg (by linarith : 0 ≤ 1 - nu (u i.succ))]
    have hv := abs_nonneg (v i.castSucc)
    have hx : dnu (u i.castSucc) * |v i.castSucc| ≤ 3 / 2 * |v i.castSucc| :=
      mul_le_mul_of_nonneg_right h2 hv
    have hy : dnu (u i.castSucc) * |v i.castSucc| * (1 - nu (u i.succ)) ≤
        dnu (u i.castSucc) * |v i.castSucc| * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg h1 hv)
    linarith
  have hb : |nu (u i.castSucc) * (dnu (u i.succ) * v i.succ)| ≤ 3 / 2 * |v i.succ| := by
    rw [abs_mul, abs_mul, abs_of_nonneg h5, abs_of_nonneg h7]
    have hv := abs_nonneg (v i.succ)
    have hx : dnu (u i.succ) * |v i.succ| ≤ 3 / 2 * |v i.succ| := mul_le_mul_of_nonneg_right h8 hv
    have hy : nu (u i.castSucc) * (dnu (u i.succ) * |v i.succ|) ≤ 1 * (dnu (u i.succ) * |v i.succ|) :=
      mul_le_mul_of_nonneg_right h6 (mul_nonneg h7 hv)
    linarith
  calc _ ≤ |dnu (u i.castSucc) * v i.castSucc * (1 - nu (u i.succ))| +
        |nu (u i.castSucc) * (dnu (u i.succ) * v i.succ)| := abs_sub _ _
    _ ≤ _ := add_le_add ha hb

lemma sq2_dq_le (u v : Fin (n + 1) → ℝ) : sq2 (dq u v) ≤ 9 * sq1 v := by
  have hpt (i : Fin n) : dq u v i ^ 2 ≤ 9 / 2 * v i.castSucc ^ 2 + 9 / 2 * v i.succ ^ 2 := by
    have h := dq_abs u v i
    have h0 := abs_nonneg (dq u v i)
    have hsq : dq u v i ^ 2 ≤ (3 / 2 * |v i.castSucc| + 3 / 2 * |v i.succ|) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ h0 h 2
    nlinarith [sq_abs (v i.castSucc), sq_abs (v i.succ),
      sq_nonneg (|v i.castSucc| - |v i.succ|)]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  unfold sq2
  linarith [sum_castSucc_le v, sum_succ_le v]

lemma sq2_drho_le_nine (u v : Fin (n + 1) → ℝ) : sq2 (drho u v) ≤ 9 * sq1 v :=
  (sq2_drho_le u v).trans (sq2_dq_le u v)

lemma dq_add (u v w : Fin (n + 1) → ℝ) (i : Fin n) : dq u (v + w) i = dq u v i + dq u w i := by
  simp only [dq, Pi.add_apply]; ring

lemma dq_smul (u v : Fin (n + 1) → ℝ) (c : ℝ) (i : Fin n) : dq u (c • v) i = c * dq u v i := by
  simp only [dq, Pi.smul_apply, smul_eq_mul]; ring

lemma drho_add (u v w : Fin (n + 1) → ℝ) (i : Fin n) :
    drho u (v + w) i = drho u v i + drho u w i := by
  simp only [drho, dq_add, mul_add, Finset.sum_add_distrib]; ring

lemma drho_smul (u v : Fin (n + 1) → ℝ) (c : ℝ) (i : Fin n) :
    drho u (c • v) i = c * drho u v i := by
  simp only [drho, dq_smul]
  rw [show (∑ j, q u j * (c * dq u v j)) = c * ∑ j, q u j * dq u v j by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
  ring

end LongTails.Proofs.NcConcaveTransitionBounds
