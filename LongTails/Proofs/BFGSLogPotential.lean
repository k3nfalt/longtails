import LongTails.Proofs.BFGSMatrix

open Matrix

namespace LongTails.Proofs.BFGSLogPotential

open LongTails.Setups.LinearPredictorBFGS LongTails.Proofs.BFGSMatrix

variable {d : ℕ}

lemma posDef_symm {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) : Mᵀ = M := by
  have h := hM.isHermitian
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h

lemma posDef_quad_pos {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {v : Fin d → ℝ}
    (hv : v ≠ 0) : 0 < v ⬝ᵥ (M *ᵥ v) := by
  simpa using hM.dotProduct_mulVec_pos hv

lemma posDef_quad_nonneg {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) (v : Fin d → ℝ) :
    0 ≤ v ⬝ᵥ (M *ᵥ v) := by
  simpa using hM.posSemidef.dotProduct_mulVec_nonneg v

lemma inv_mulVec_of_mulVec {N : Matrix (Fin d) (Fin d) ℝ} (hN : IsUnit N.det) {z u : Fin d → ℝ}
    (h : N *ᵥ z = u) : N⁻¹ *ᵥ u = z := by
  rw [← h, mulVec_mulVec, nonsing_inv_mul _ hN, one_mulVec]

lemma det_add_rankOne (N : Matrix (Fin d) (Fin d) ℝ) (hN : IsUnit N.det) (c : ℝ)
    (u : Fin d → ℝ) :
    det (N + c • vecMulVec u u) = det N * (1 + c * (u ⬝ᵥ (N⁻¹ *ᵥ u))) := by
  have hfac : c • vecMulVec u u = replicateCol Unit u * replicateRow Unit (c • u) := by
    ext i j
    simp [vecMulVec, replicateCol, replicateRow, Matrix.mul_apply]
    ring
  have key : (replicateRow Unit (c • u) * N⁻¹ * replicateCol Unit u) () () =
      c * (u ⬝ᵥ (N⁻¹ *ᵥ u)) := by
    simp only [Matrix.mul_apply, replicateRow_apply, replicateCol_apply, Pi.smul_apply,
      smul_eq_mul, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hfac, det_add_replicateCol_mul_replicateRow hN]
  congr 1
  rw [det_unique]
  rw [Matrix.add_apply, Matrix.one_apply_eq]
  exact congrArg (1 + ·) key

structure Scalars (B Q : Matrix (Fin d) (Fin d) ℝ) (s : Fin d → ℝ) where
  w1 : Fin d → ℝ
  w2 : Fin d → ℝ
  hw1 : (B + Q) *ᵥ w1 = B *ᵥ s
  hw2 : (B + Q) *ᵥ w2 = Q *ᵥ s

noncomputable def scalars {B Q : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (hQ : Q.PosDef)
    (s : Fin d → ℝ) : Scalars B Q s :=
  ⟨(B + Q)⁻¹ *ᵥ (B *ᵥ s), (B + Q)⁻¹ *ᵥ (Q *ᵥ s), mulVec_inv_mulVec (hB.add hQ) _,
    mulVec_inv_mulVec (hB.add hQ) _⟩

section Static

variable {B Q : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (hQ : Q.PosDef) {s : Fin d → ℝ}
  (hs : s ≠ 0)

include hB hQ in
lemma w_sum (S : Scalars B Q s) : S.w1 + S.w2 = s := by
  have hM := hB.add hQ
  have hu : IsUnit (B + Q).det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  have h1 : (B + Q) *ᵥ (S.w1 + S.w2) = (B + Q) *ᵥ s := by
    rw [mulVec_add, S.hw1, S.hw2, add_mulVec]
  have := congrArg (fun v => (B + Q)⁻¹ *ᵥ v) h1
  simpa [mulVec_mulVec, nonsing_inv_mul _ hu] using this

include hB hQ in
lemma bw2_eq_qw1 (S : Scalars B Q s) : B *ᵥ S.w2 = Q *ᵥ S.w1 := by
  have h := w_sum hB hQ S
  have e1 : B *ᵥ S.w1 + Q *ᵥ S.w1 = B *ᵥ s := by rw [← add_mulVec, S.hw1]
  have hbs : B *ᵥ s = B *ᵥ S.w1 + B *ᵥ S.w2 := by rw [← mulVec_add, h]
  have e2 : B *ᵥ S.w2 = B *ᵥ s - B *ᵥ S.w1 := by
    rw [hbs]; abel
  rw [e2, ← e1]; abel

include hB hQ in
lemma bprime_eq (S : Scalars B Q s) :
    (B *ᵥ s) ⬝ᵥ S.w2 = S.w1 ⬝ᵥ (Q *ᵥ S.w1) + S.w2 ⬝ᵥ (B *ᵥ S.w2) := by
  have hBt := posDef_symm hB
  have h := w_sum hB hQ S
  have hb := bw2_eq_qw1 hB hQ S
  have hbs : B *ᵥ s = B *ᵥ S.w1 + B *ᵥ S.w2 := by rw [← mulVec_add, h]
  rw [hbs, add_dotProduct, symm_dot hBt S.w1 S.w2, hb, dotProduct_comm (Q *ᵥ S.w1) S.w2]

include hB hQ hs in
lemma bprime_pos (S : Scalars B Q s) : 0 < (B *ᵥ s) ⬝ᵥ S.w2 := by
  rw [bprime_eq hB hQ S]
  have h := w_sum hB hQ S
  have h1 := posDef_quad_nonneg hQ S.w1
  have h2 := posDef_quad_nonneg hB S.w2
  by_cases hw1 : S.w1 = 0
  · have hw2 : S.w2 ≠ 0 := by
      intro hw2; apply hs; rw [← h, hw1, hw2, add_zero]
    have := posDef_quad_pos hB hw2
    linarith
  · have := posDef_quad_pos hQ hw1
    linarith

end Static

lemma cs_posDef {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) (u v : Fin d → ℝ) :
    (u ⬝ᵥ (M *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (M *ᵥ u)) * (v ⬝ᵥ (M *ᵥ v)) := by
  have hMt := posDef_symm hM
  by_cases hv : v = 0
  · subst hv; simp
  have hC := posDef_quad_pos hM hv
  set A := u ⬝ᵥ (M *ᵥ u)
  set Bv := u ⬝ᵥ (M *ᵥ v)
  set C := v ⬝ᵥ (M *ᵥ v)
  have hvu : v ⬝ᵥ (M *ᵥ u) = Bv := by
    simp only [Bv]; rw [← symm_dot hMt, dotProduct_comm]
  have hq := posDef_quad_nonneg hM (C • u - Bv • v)
  have hexp : (C • u - Bv • v) ⬝ᵥ (M *ᵥ (C • u - Bv • v)) = C * (A * C - Bv ^ 2) := by
    simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hvu]
    ring
  rw [hexp] at hq
  have : 0 ≤ A * C - Bv ^ 2 := by
    by_contra hneg
    have := mul_neg_of_pos_of_neg hC (lt_of_not_ge hneg)
    linarith
  linarith

section Static2

variable {B Q : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (hQ : Q.PosDef) {s : Fin d → ℝ}
  (hs : s ≠ 0)

include hB hQ in
lemma dot_beta1 (S : Scalars B Q s) :
    s ⬝ᵥ (B *ᵥ s) = (B *ᵥ s) ⬝ᵥ S.w1 + (B *ᵥ s) ⬝ᵥ S.w2 := by
  have h := w_sum hB hQ S
  calc s ⬝ᵥ (B *ᵥ s) = (S.w1 + S.w2) ⬝ᵥ (B *ᵥ s) := by rw [h]
    _ = _ := by rw [add_dotProduct, dotProduct_comm S.w1, dotProduct_comm S.w2]

include hB hQ in
lemma dot_qw1 (S : Scalars B Q s) : (Q *ᵥ s) ⬝ᵥ S.w1 = (B *ᵥ s) ⬝ᵥ S.w2 := by
  have hMt : (B + Q)ᵀ = B + Q := posDef_symm (hB.add hQ)
  rw [← S.hw2, symm_dot hMt, S.hw1, dotProduct_comm]

include hB hQ in
lemma dot_beta2 (S : Scalars B Q s) :
    s ⬝ᵥ (Q *ᵥ s) = (B *ᵥ s) ⬝ᵥ S.w2 + (Q *ᵥ s) ⬝ᵥ S.w2 := by
  have h := w_sum hB hQ S
  calc s ⬝ᵥ (Q *ᵥ s) = (S.w1 + S.w2) ⬝ᵥ (Q *ᵥ s) := by rw [h]
    _ = _ := by
      rw [add_dotProduct, dotProduct_comm S.w1, dotProduct_comm S.w2, dot_qw1 hB hQ S]

include hB hQ in
lemma dot_cs (S : Scalars B Q s) :
    ((B *ᵥ s) ⬝ᵥ S.w2) ^ 2 ≤ ((B *ᵥ s) ⬝ᵥ S.w1) * ((Q *ᵥ s) ⬝ᵥ S.w2) := by
  have hMt : (B + Q)ᵀ = B + Q := posDef_symm (hB.add hQ)
  have e1 : (B *ᵥ s) ⬝ᵥ S.w2 = S.w1 ⬝ᵥ ((B + Q) *ᵥ S.w2) := by
    rw [← S.hw1, symm_dot hMt]
  have e2 : (B *ᵥ s) ⬝ᵥ S.w1 = S.w1 ⬝ᵥ ((B + Q) *ᵥ S.w1) := by
    rw [← S.hw1, dotProduct_comm]
  have e3 : (Q *ᵥ s) ⬝ᵥ S.w2 = S.w2 ⬝ᵥ ((B + Q) *ᵥ S.w2) := by
    rw [← S.hw2, dotProduct_comm]
  rw [e1, e2, e3]
  exact cs_posDef (hB.add hQ) _ _

include hB hQ hs in
lemma dot_a_pos (S : Scalars B Q s) : 0 < (B *ᵥ s) ⬝ᵥ S.w1 := by
  have hMt : (B + Q)ᵀ = B + Q := posDef_symm (hB.add hQ)
  have e2 : (B *ᵥ s) ⬝ᵥ S.w1 = S.w1 ⬝ᵥ ((B + Q) *ᵥ S.w1) := by
    rw [← S.hw1, dotProduct_comm]
  rw [e2]
  apply posDef_quad_pos (hB.add hQ)
  intro h0
  have hb : B *ᵥ s = 0 := by rw [← S.hw1, h0, mulVec_zero]
  have := posDef_quad_pos hB hs
  rw [hb, dotProduct_zero] at this
  exact lt_irrefl _ this

include hB hQ hs in
lemma dot_c_pos (S : Scalars B Q s) : 0 < (Q *ᵥ s) ⬝ᵥ S.w2 := by
  have e3 : (Q *ᵥ s) ⬝ᵥ S.w2 = S.w2 ⬝ᵥ ((B + Q) *ᵥ S.w2) := by
    rw [← S.hw2, dotProduct_comm]
  rw [e3]
  apply posDef_quad_pos (hB.add hQ)
  intro h0
  have hb : Q *ᵥ s = 0 := by rw [← S.hw2, h0, mulVec_zero]
  have := posDef_quad_pos hQ hs
  rw [hb, dotProduct_zero] at this
  exact lt_irrefl _ this

lemma bfgs_add_Q (B Q : Matrix (Fin d) (Fin d) ℝ) (s : Fin d → ℝ) :
    bfgsUpdate B s (Q *ᵥ s) + Q =
      ((B + Q) + (-(s ⬝ᵥ (B *ᵥ s))⁻¹) • vecMulVec (B *ᵥ s) (B *ᵥ s)) +
        ((Q *ᵥ s) ⬝ᵥ s)⁻¹ • vecMulVec (Q *ᵥ s) (Q *ᵥ s) := by
  rw [bfgsUpdate, neg_smul]; abel

include hB in
lemma M1_mulVec (Q : Matrix (Fin d) (Fin d) ℝ) (hs : s ≠ 0) :
    ((B + Q) + (-(s ⬝ᵥ (B *ᵥ s))⁻¹) • vecMulVec (B *ᵥ s) (B *ᵥ s)) *ᵥ s = Q *ᵥ s := by
  have hBt := posDef_symm hB
  have hpos := posDef_quad_pos hB hs
  rw [add_mulVec, smul_mulVec, vecMulVec_mulVec', add_mulVec, smul_smul,
    dotProduct_comm (B *ᵥ s) s]
  rw [show -(s ⬝ᵥ (B *ᵥ s))⁻¹ * (s ⬝ᵥ (B *ᵥ s)) = -1 by field_simp]
  rw [neg_one_smul]; abel

include hB hQ hs in
lemma det_static (S : Scalars B Q s) :
    det (bfgsUpdate B s (Q *ᵥ s) + Q) =
      2 * det (B + Q) * (((B *ᵥ s) ⬝ᵥ S.w2) / (s ⬝ᵥ (B *ᵥ s))) := by
  have hM := hB.add hQ
  have huM : IsUnit (B + Q).det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  have hβ1 := posDef_quad_pos hB hs
  have hβ2 := posDef_quad_pos hQ hs
  have hbp := bprime_pos hB hQ hs S
  have hdetM : 0 < det (B + Q) := hM.det_pos
  set M1 := (B + Q) + (-(s ⬝ᵥ (B *ᵥ s))⁻¹) • vecMulVec (B *ᵥ s) (B *ᵥ s) with hM1
  have hw1 : (B + Q)⁻¹ *ᵥ (B *ᵥ s) = S.w1 := inv_mulVec_of_mulVec huM S.hw1
  have hdet1 : det M1 = det (B + Q) * (((B *ᵥ s) ⬝ᵥ S.w2) / (s ⬝ᵥ (B *ᵥ s))) := by
    rw [hM1, det_add_rankOne _ huM, hw1, dot_beta1 hB hQ S]
    congr 1
    have : (B *ᵥ s) ⬝ᵥ S.w1 + (B *ᵥ s) ⬝ᵥ S.w2 ≠ 0 := by
      rw [← dot_beta1 hB hQ S]; exact hβ1.ne'
    field_simp
    ring
  have hdet1pos : 0 < det M1 := by
    rw [hdet1]; positivity
  have huM1 : IsUnit M1.det := isUnit_iff_ne_zero.mpr hdet1pos.ne'
  have hM1s : M1 *ᵥ s = Q *ᵥ s := M1_mulVec hB Q hs
  have hinv : M1⁻¹ *ᵥ (Q *ᵥ s) = s := inv_mulVec_of_mulVec huM1 hM1s
  have hqs : (Q *ᵥ s) ⬝ᵥ s = s ⬝ᵥ (Q *ᵥ s) := dotProduct_comm _ _
  rw [bfgs_add_Q, ← hM1, det_add_rankOne _ huM1, hinv, hdet1, hqs]
  rw [inv_mul_cancel₀ hβ2.ne']
  ring

lemma coef_ids (a bp c e : ℝ) (hbp : bp ≠ 0) (h2 : bp + c ≠ 0) (h1 : a + bp ≠ 0) :
    let α2 := ((bp + c) - e * (a + bp)) / (2 * (bp + c))
    let α1 := α2 + e * (a + bp) / bp
    α1 + (-(a + bp)⁻¹) * (α1 * a + α2 * bp) = e ∧
      α2 + (bp + c)⁻¹ * (α1 * bp + α2 * c) = 1 := by
  intro α2 α1
  constructor
  · simp only [α1, α2]; field_simp; ring
  · simp only [α1, α2]; field_simp; ring

include hB hQ hs in
lemma pi_static (S : Scalars B Q s) (e : ℝ) :
    let a := (B *ᵥ s) ⬝ᵥ S.w1
    let bp := (B *ᵥ s) ⬝ᵥ S.w2
    let c := (Q *ᵥ s) ⬝ᵥ S.w2
    let α2 := ((bp + c) - e * (a + bp)) / (2 * (bp + c))
    let α1 := α2 + e * (a + bp) / bp
    (e • (B *ᵥ s) + Q *ᵥ s) ⬝ᵥ ((bfgsUpdate B s (Q *ᵥ s) + Q)⁻¹ *ᵥ (e • (B *ᵥ s) + Q *ᵥ s)) =
      e * (α1 * a + α2 * bp) + (α1 * bp + α2 * c) := by
  intro a bp c α2 α1
  have hM := hB.add hQ
  have huM : IsUnit (B + Q).det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  have hβ1 := posDef_quad_pos hB hs
  have hβ2 := posDef_quad_pos hQ hs
  have hbp : 0 < bp := bprime_pos hB hQ hs S
  have ha : 0 < a := dot_a_pos hB hQ hs S
  have hc : 0 < c := dot_c_pos hB hQ hs S
  have e1 : s ⬝ᵥ (B *ᵥ s) = a + bp := dot_beta1 hB hQ S
  have e2 : (Q *ᵥ s) ⬝ᵥ s = bp + c := by rw [dotProduct_comm]; exact dot_beta2 hB hQ S
  have eq1 : (Q *ᵥ s) ⬝ᵥ S.w1 = bp := dot_qw1 hB hQ S
  have hdet := det_static hB hQ hs S
  have hdetpos : 0 < det (bfgsUpdate B s (Q *ᵥ s) + Q) := by
    rw [hdet]; have := hM.det_pos; positivity
  have huP : IsUnit (bfgsUpdate B s (Q *ᵥ s) + Q).det := isUnit_iff_ne_zero.mpr hdetpos.ne'
  set x := α1 • S.w1 + α2 • S.w2 with hx
  have hbx : (B *ᵥ s) ⬝ᵥ x = α1 * a + α2 * bp := by
    rw [hx, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hqx : (Q *ᵥ s) ⬝ᵥ x = α1 * bp + α2 * c := by
    rw [hx, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, eq1]
  have hMx : (B + Q) *ᵥ x = α1 • (B *ᵥ s) + α2 • (Q *ᵥ s) := by
    rw [hx, mulVec_add, mulVec_smul, mulVec_smul, S.hw1, S.hw2]
  obtain ⟨c1, c2⟩ := coef_ids a bp c e hbp.ne' (by linarith) (by linarith)
  have hPx : (bfgsUpdate B s (Q *ᵥ s) + Q) *ᵥ x = e • (B *ᵥ s) + Q *ᵥ s := by
    rw [bfgs_add_Q, add_mulVec, add_mulVec, smul_mulVec, smul_mulVec, vecMulVec_mulVec',
      vecMulVec_mulVec', hMx, hbx, hqx, smul_smul, smul_smul, e1, e2]
    have : (α1 • (B *ᵥ s) + α2 • (Q *ᵥ s) + (-(a + bp)⁻¹ * (α1 * a + α2 * bp)) • (B *ᵥ s) +
        ((bp + c)⁻¹ * (α1 * bp + α2 * c)) • (Q *ᵥ s)) =
        (α1 + (-(a + bp)⁻¹) * (α1 * a + α2 * bp)) • (B *ᵥ s) +
          (α2 + (bp + c)⁻¹ * (α1 * bp + α2 * c)) • (Q *ᵥ s) := by module
    rw [this, c1, c2, one_smul]
  rw [inv_mulVec_of_mulVec huP hPx, add_dotProduct, smul_dotProduct, hbx, hqx, smul_eq_mul]

include hB hQ in
lemma pi_static_old (S : Scalars B Q s) (e : ℝ) :
    (e • (B *ᵥ s)) ⬝ᵥ ((B + Q)⁻¹ *ᵥ (e • (B *ᵥ s))) = e ^ 2 * ((B *ᵥ s) ⬝ᵥ S.w1) := by
  have hM := hB.add hQ
  have huM : IsUnit (B + Q).det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  have h : (B + Q) *ᵥ (e • S.w1) = e • (B *ᵥ s) := by rw [mulVec_smul, S.hw1]
  rw [inv_mulVec_of_mulVec huM h, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

end Static2

end LongTails.Proofs.BFGSLogPotential
