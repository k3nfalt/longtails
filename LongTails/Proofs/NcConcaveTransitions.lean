import LongTails.Proofs.NcConcaveScalars

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveTransitions

open LongTails.Proofs.NcConcaveScalars

variable {n : ℕ}

noncomputable def q (u : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  nu (u i.castSucc) * (1 - nu (u i.succ))

noncomputable def dq (u v : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  dnu (u i.castSucc) * v i.castSucc * (1 - nu (u i.succ)) -
    nu (u i.castSucc) * (dnu (u i.succ) * v i.succ)

noncomputable def sq2 (w : Fin n → ℝ) : ℝ := ∑ i, w i ^ 2

noncomputable def nrm (u : Fin (n + 1) → ℝ) : ℝ := Real.sqrt (1 + sq2 (q u))

noncomputable def rho (u : Fin (n + 1) → ℝ) (i : Fin n) : ℝ := q u i / nrm u

noncomputable def drho (u v : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  dq u v i / nrm u - q u i * (∑ j, q u j * dq u v j) / nrm u ^ 3

lemma sq2_nonneg (w : Fin n → ℝ) : 0 ≤ sq2 w := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma nrm_pos (u : Fin (n + 1) → ℝ) : 0 < nrm u :=
  Real.sqrt_pos.mpr (by linarith [sq2_nonneg (q u)])

lemma nrm_sq (u : Fin (n + 1) → ℝ) : nrm u ^ 2 = 1 + sq2 (q u) :=
  Real.sq_sqrt (by linarith [sq2_nonneg (q u)])

lemma one_le_nrm (u : Fin (n + 1) → ℝ) : 1 ≤ nrm u := by
  rw [nrm, Real.le_sqrt (by norm_num) (by linarith [sq2_nonneg (q u)])]
  linarith [sq2_nonneg (q u)]

lemma q_nonneg (u : Fin (n + 1) → ℝ) (i : Fin n) : 0 ≤ q u i :=
  mul_nonneg (nu_nonneg _) (by linarith [nu_le_one (u i.succ)])

lemma q_le_one (u : Fin (n + 1) → ℝ) (i : Fin n) : q u i ≤ 1 := by
  have h1 := nu_le_one (u i.castSucc)
  have h2 := nu_nonneg (u i.succ)
  have h3 := nu_nonneg (u i.castSucc)
  unfold q
  nlinarith

lemma sq2_rho (u : Fin (n + 1) → ℝ) : sq2 (rho u) = sq2 (q u) / (1 + sq2 (q u)) := by
  unfold rho
  simp only [sq2, div_pow, ← Finset.sum_div, nrm_sq]

lemma sq2_rho_le_one (u : Fin (n + 1) → ℝ) : sq2 (rho u) ≤ 1 := by
  rw [sq2_rho, div_le_one (by linarith [sq2_nonneg (q u)])]
  linarith

lemma rho_nonneg (u : Fin (n + 1) → ℝ) (i : Fin n) : 0 ≤ rho u i :=
  div_nonneg (q_nonneg u i) (nrm_pos u).le

lemma inner_le_sq2 (w z : Fin n → ℝ) : (∑ i, w i * z i) ^ 2 ≤ sq2 w * sq2 z :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma sq2_drho_le (u v : Fin (n + 1) → ℝ) : sq2 (drho u v) ≤ sq2 (dq u v) := by
  have hspos : 0 < nrm u := nrm_pos u
  have hs2 : nrm u ^ 2 = 1 + sq2 (q u) := nrm_sq u
  have hQ : 0 ≤ sq2 (q u) := sq2_nonneg _
  have hD : 0 ≤ sq2 (dq u v) := sq2_nonneg _
  have hpt : ∀ i, drho u v i ^ 2 = dq u v i ^ 2 / nrm u ^ 2 -
      2 * (∑ j, q u j * dq u v j) / nrm u ^ 4 * (q u i * dq u v i) +
      (∑ j, q u j * dq u v j) ^ 2 / nrm u ^ 6 * q u i ^ 2 := by
    intro i; simp only [drho]; field_simp; ring
  have hexp : sq2 (drho u v) = sq2 (dq u v) / nrm u ^ 2 +
      (∑ j, q u j * dq u v j) ^ 2 * (sq2 (q u) - 2 * nrm u ^ 2) / nrm u ^ 6 := by
    unfold sq2
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      ← Finset.mul_sum]
    field_simp
    ring
  rw [hexp]
  have h1 : sq2 (dq u v) / nrm u ^ 2 ≤ sq2 (dq u v) :=
    div_le_self hD (by nlinarith [one_le_nrm u])
  have h2 : (∑ j, q u j * dq u v j) ^ 2 * (sq2 (q u) - 2 * nrm u ^ 2) / nrm u ^ 6 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by nlinarith))
      (by positivity)
  linarith

end LongTails.Proofs.NcConcaveTransitions
