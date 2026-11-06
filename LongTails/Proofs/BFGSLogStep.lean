import LongTails.Proofs.BFGSLogDet
import LongTails.Proofs.BFGSLogScalar

open Matrix

namespace LongTails.Proofs.BFGSLogStep

open LongTails.Setups.LinearPredictorBFGS LongTails.Proofs.BFGSMatrix
open LongTails.Proofs.BFGSLogPotential LongTails.Proofs.BFGSLogDet LongTails.Proofs.BFGSLogScalar

variable {d : ℕ}

noncomputable def Psi (B Q : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  2 * Real.log (det (B + Q)) - Real.log (det B) - Real.log (det Q)

noncomputable def pit (B Q : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) : ℝ :=
  g ⬝ᵥ ((B + Q)⁻¹ *ᵥ g)

noncomputable def U (k : ℕ) (B Q : Matrix (Fin d) (Fin d) ℝ) (g : Fin d → ℝ) : ℝ :=
  k * Psi B Q + Real.log (pit B Q g)

lemma pit_pos {B Q : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (hQ : Q.PosDef) {g : Fin d → ℝ}
    (hg : g ≠ 0) : 0 < pit B Q g := by
  have hM := hB.add hQ
  have hu : IsUnit (B + Q).det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  have hw : (B + Q)⁻¹ *ᵥ g ≠ 0 := by
    intro h0
    apply hg
    rw [← mulVec_inv_mulVec hM g, h0, mulVec_zero]
  have := posDef_quad_pos hM hw
  rw [mulVec_inv_mulVec hM g, dotProduct_comm] at this
  exact this

lemma step_identity (a bp c e : ℝ) (ha : 0 < a) (hbp : 0 < bp) (hc : 0 < c) (he : e < 0) :
    let α2 := ((bp + c) - e * (a + bp)) / (2 * (bp + c))
    let α1 := α2 + e * (a + bp) / bp
    let t := bp / (a + bp)
    let p := bp / (bp + c)
    let ν := ((bp + c) / (-(e * (a + bp))) - 1) ^ 2
    (e * (α1 * a + α2 * bp) + (α1 * bp + α2 * c)) * (t * (1 - t)) =
      (e ^ 2 * a) * (1 - t - p * (1 - ν / 2)) := by
  intro α2 α1 t p ν
  have h1 : a + bp ≠ 0 := by linarith
  have h2 : bp + c ≠ 0 := by linarith
  have h0 : e ≠ 0 := he.ne
  have h4 : bp ≠ 0 := hbp.ne'
  have h3 : -(e * (a + bp)) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero h0 h1)
  simp only [α1, α2, t, p, ν]
  field_simp
  ring

lemma tp_bounds (a bp c : ℝ) (ha : 0 < a) (hbp : 0 < bp) (hc : 0 < c) (hcs : bp ^ 2 ≤ a * c) :
    0 < bp / (a + bp) ∧ bp / (a + bp) < 1 ∧ 0 < bp / (bp + c) ∧
      bp / (bp + c) ≤ 1 - bp / (a + bp) := by
  refine ⟨by positivity, (div_lt_one (by linarith)).mpr (by linarith), by positivity, ?_⟩
  have hA : 0 < a + bp := by linarith
  have hC : 0 < bp + c := by linarith
  rw [div_le_iff₀ hC]
  have : (1 - bp / (a + bp)) = a / (a + bp) := by field_simp; ring
  rw [this, div_mul_eq_mul_div, le_div_iff₀ hA]
  nlinarith

lemma Psi_eq_log {B Q : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (hQ : Q.PosDef) :
    Psi B Q = Real.log (det (B + Q) ^ 2 / (det B * det Q)) := by
  have h1 := (hB.add hQ).det_pos
  have h2 := hB.det_pos
  have h3 := hQ.det_pos
  rw [Psi, Real.log_div (by positivity) (by positivity), Real.log_mul h2.ne' h3.ne',
    Real.log_pow]
  push_cast; ring

section Step

variable {B Q : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (hQ : Q.PosDef) {s : Fin d → ℝ}
  (hs : s ≠ 0)

include hB hQ hs in
lemma U_step (e : ℝ) (he : e < 0) (k : ℕ) (hgp : e • (B *ᵥ s) + Q *ᵥ s ≠ 0) :
    let S := scalars hB hQ s
    let a := (B *ᵥ s) ⬝ᵥ S.w1
    let bp := (B *ᵥ s) ⬝ᵥ S.w2
    let c := (Q *ᵥ s) ⬝ᵥ S.w2
    let t := bp / (a + bp)
    let p := bp / (bp + c)
    let ν := ((s ⬝ᵥ (Q *ᵥ s)) / (-((e • (B *ᵥ s)) ⬝ᵥ s)) - 1) ^ 2
    0 < t ∧ t < 1 ∧ 0 < p ∧ p ≤ 1 - t ∧ 0 < 1 - t - p * (1 - ν / 2) ∧
    U k (bfgsUpdate B s (Q *ᵥ s)) Q (e • (B *ᵥ s) + Q *ᵥ s) =
      U k B Q (e • (B *ᵥ s)) + Real.log ((4 * t * p) ^ k * (1 - t - p * (1 - ν / 2)) /
        (t * (1 - t))) := by
  intro S a bp c t p ν
  have ha : 0 < a := dot_a_pos hB hQ hs S
  have hbp : 0 < bp := bprime_pos hB hQ hs S
  have hc : 0 < c := dot_c_pos hB hQ hs S
  have hcs : bp ^ 2 ≤ a * c := dot_cs hB hQ S
  obtain ⟨ht0, ht1, hp0, hp1⟩ := tp_bounds a bp c ha hbp hc hcs
  have e1 : s ⬝ᵥ (B *ᵥ s) = a + bp := dot_beta1 hB hQ S
  have e2 : s ⬝ᵥ (Q *ᵥ s) = bp + c := dot_beta2 hB hQ S
  have hβ2 : 0 < (Q *ᵥ s) ⬝ᵥ s := by rw [dotProduct_comm, e2]; linarith
  have hBp : (bfgsUpdate B s (Q *ᵥ s)).PosDef := upd_posDef hB hs hβ2
  have hdetBp : det (bfgsUpdate B s (Q *ᵥ s)) = det B * ((bp + c) / (a + bp)) := by
    rw [upd_det hB hs hβ2, dotProduct_comm, e2, e1]
  have hdetP : det (bfgsUpdate B s (Q *ᵥ s) + Q) = 2 * det (B + Q) * t := by
    rw [det_static hB hQ hs S, e1]
  have hpitP : pit (bfgsUpdate B s (Q *ᵥ s)) Q (e • (B *ᵥ s) + Q *ᵥ s) =
      e * ((((bp + c) - e * (a + bp)) / (2 * (bp + c)) + e * (a + bp) / bp) * a +
        ((bp + c) - e * (a + bp)) / (2 * (bp + c)) * bp) +
      ((((bp + c) - e * (a + bp)) / (2 * (bp + c)) + e * (a + bp) / bp) * bp +
        ((bp + c) - e * (a + bp)) / (2 * (bp + c)) * c) := pi_static hB hQ hs S e
  have hpit : pit B Q (e • (B *ᵥ s)) = e ^ 2 * a := pi_static_old hB hQ S e
  have hgs : (e • (B *ᵥ s)) ⬝ᵥ s = e * (a + bp) := by
    rw [smul_dotProduct, smul_eq_mul, dotProduct_comm, e1]
  have hν : ν = ((bp + c) / (-(e * (a + bp))) - 1) ^ 2 := by
    simp only [ν]; rw [e2, hgs]
  have hid := step_identity a bp c e ha hbp hc he
  simp only at hid
  rw [← hpitP, ← hpit, ← hν] at hid
  have hpit0 : 0 < pit B Q (e • (B *ᵥ s)) := by
    rw [hpit]
    have he2 : 0 < e ^ 2 := by nlinarith [mul_pos_of_neg_of_neg he he]
    exact mul_pos he2 ha
  have hpitP0 : 0 < pit (bfgsUpdate B s (Q *ᵥ s)) Q (e • (B *ᵥ s) + Q *ᵥ s) :=
    pit_pos hBp hQ hgp
  have hratio : pit (bfgsUpdate B s (Q *ᵥ s)) Q (e • (B *ᵥ s) + Q *ᵥ s) /
      pit B Q (e • (B *ᵥ s)) = (1 - t - p * (1 - ν / 2)) / (t * (1 - t)) := by
    have htt : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
    rw [div_eq_div_iff hpit0.ne' htt.ne']
    linarith [hid]
  have hPsi : Psi (bfgsUpdate B s (Q *ᵥ s)) Q = Psi B Q + Real.log (4 * t * p) := by
    rw [Psi_eq_log hBp hQ, Psi_eq_log hB hQ, hdetP, hdetBp]
    have h1 := (hB.add hQ).det_pos
    have h2 := hB.det_pos
    have h3 := hQ.det_pos
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    simp only [t, p]
    field_simp
    ring
  have hrpos : 0 < (1 - t - p * (1 - ν / 2)) / (t * (1 - t)) := by
    rw [← hratio]; positivity
  have htt : 0 < t * (1 - t) := mul_pos ht0 (by linarith)
  have hX : 0 < 1 - t - p * (1 - ν / 2) := by
    have := mul_pos hrpos htt
    rwa [div_mul_cancel₀ _ htt.ne'] at this
  refine ⟨ht0, ht1, hp0, hp1, hX, ?_⟩
  have h4 : 0 < 4 * t * p := by positivity
  have hR : Real.log ((4 * t * p) ^ k * (1 - t - p * (1 - ν / 2)) / (t * (1 - t))) =
      k * Real.log (4 * t * p) + (Real.log (pit (bfgsUpdate B s (Q *ᵥ s)) Q
        (e • (B *ᵥ s) + Q *ᵥ s)) - Real.log (pit B Q (e • (B *ᵥ s)))) := by
    rw [mul_div_assoc, Real.log_mul (pow_pos h4 k).ne' hrpos.ne', Real.log_pow, ← hratio,
      Real.log_div hpitP0.ne' hpit0.ne']
  unfold U
  rw [hPsi, hR]
  ring

include hB hQ hs in
lemma U_step_contract (e : ℝ) (he : e < 0) (k : ℕ) (hk : 2 ≤ k) (νb : ℝ)
    (hν : ((s ⬝ᵥ (Q *ᵥ s)) / (-((e • (B *ᵥ s)) ⬝ᵥ s)) - 1) ^ 2 ≤ νb)
    (hνb : 2 ≤ νb * (k + 1)) (hgp : e • (B *ᵥ s) + Q *ᵥ s ≠ 0) :
    U k (bfgsUpdate B s (Q *ᵥ s)) Q (e • (B *ᵥ s) + Q *ᵥ s) ≤
      U k B Q (e • (B *ᵥ s)) + Real.log (νb * (1 + 1 / (2 * k - 1))) := by
  have h := U_step hB hQ hs e he k hgp
  dsimp only at h
  obtain ⟨ht0, ht1, hp0, hp1, hX, heq⟩ := h
  rw [heq]
  have hcore := core_bound _ _ _ νb k hk ht0 ht1 hp0 hp1 hν hνb
  have htt := mul_pos ht0 (sub_pos.mpr ht1)
  have hle := (div_le_iff₀ htt).mpr hcore
  have hpos : 0 < (4 * ((B *ᵥ s) ⬝ᵥ (scalars hB hQ s).w2 / ((B *ᵥ s) ⬝ᵥ (scalars hB hQ s).w1 +
      (B *ᵥ s) ⬝ᵥ (scalars hB hQ s).w2)) * ((B *ᵥ s) ⬝ᵥ (scalars hB hQ s).w2 /
      ((B *ᵥ s) ⬝ᵥ (scalars hB hQ s).w2 + (Q *ᵥ s) ⬝ᵥ (scalars hB hQ s).w2))) :=
    mul_pos (mul_pos (by norm_num) ht0) hp0
  have hpos2 := div_pos (mul_pos (pow_pos hpos k) hX) htt
  linarith [Real.log_le_log hpos2 hle]

include hB hQ hs in
lemma U_step_any (e : ℝ) (he : e < 0) (k : ℕ) (hk : 1 ≤ k) (hgp : e • (B *ᵥ s) + Q *ᵥ s ≠ 0) :
    U k (bfgsUpdate B s (Q *ᵥ s)) Q (e • (B *ᵥ s) + Q *ᵥ s) ≤
      U k B Q (e • (B *ᵥ s)) + Real.log (4 * (1 +
        ((s ⬝ᵥ (Q *ᵥ s)) / (-((e • (B *ᵥ s)) ⬝ᵥ s)) - 1) ^ 2 / 2)) := by
  have h := U_step hB hQ hs e he k hgp
  dsimp only at h
  obtain ⟨ht0, ht1, hp0, hp1, hX, heq⟩ := h
  rw [heq]
  have hcore := core_bound_any _ _ _ k hk ht0 ht1 hp0 hp1 (sq_nonneg
    ((s ⬝ᵥ (Q *ᵥ s)) / (-((e • (B *ᵥ s)) ⬝ᵥ s)) - 1))
  have htt := mul_pos ht0 (sub_pos.mpr ht1)
  have hle := (div_le_iff₀ htt).mpr hcore
  have hpos : 0 < (4 * ((B *ᵥ s) ⬝ᵥ (scalars hB hQ s).w2 / ((B *ᵥ s) ⬝ᵥ (scalars hB hQ s).w1 +
      (B *ᵥ s) ⬝ᵥ (scalars hB hQ s).w2)) * ((B *ᵥ s) ⬝ᵥ (scalars hB hQ s).w2 /
      ((B *ᵥ s) ⬝ᵥ (scalars hB hQ s).w2 + (Q *ᵥ s) ⬝ᵥ (scalars hB hQ s).w2))) :=
    mul_pos (mul_pos (by norm_num) ht0) hp0
  have hpos2 := div_pos (mul_pos (pow_pos hpos k) hX) htt
  linarith [Real.log_le_log hpos2 hle]

end Step

lemma inv_smul_mulVec {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosDef) {c : ℝ} (hc : 0 < c)
    (g : Fin d → ℝ) : (c • M)⁻¹ *ᵥ g = c⁻¹ • (M⁻¹ *ᵥ g) := by
  have hcM : (c • M).PosDef := hM.smul hc
  have hu : IsUnit (c • M).det := (isUnit_iff_isUnit_det _).mp hcM.isUnit
  apply inv_mulVec_of_mulVec hu
  rw [smul_mulVec, mulVec_smul, mulVec_inv_mulVec hM, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

lemma U_switch {B Q Q' : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (hQ : Q.PosDef)
    (hQ' : Q'.PosDef) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (h1 : ∀ v : Fin d → ℝ, v ⬝ᵥ (Q' *ᵥ v) ≤ Real.exp ℓ * (v ⬝ᵥ (Q *ᵥ v)))
    (h2 : ∀ v : Fin d → ℝ, v ⬝ᵥ (Q *ᵥ v) ≤ Real.exp ℓ * (v ⬝ᵥ (Q' *ᵥ v)))
    (k : ℕ) {g : Fin d → ℝ} (hg : g ≠ 0) :
    U k B Q' g ≤ U k B Q g + (3 * k * d + 1) * ℓ := by
  have hE : 1 ≤ Real.exp ℓ := Real.one_le_exp hℓ
  have hEpos : 0 < Real.exp ℓ := Real.exp_pos ℓ
  have hM := hB.add hQ
  have hM' := hB.add hQ'
  have hMt : (Real.exp ℓ • (B + Q))ᵀ = Real.exp ℓ • (B + Q) := by
    rw [transpose_smul, posDef_symm hM]
  have hQt : (Real.exp ℓ • Q')ᵀ = Real.exp ℓ • Q' := by rw [transpose_smul, posDef_symm hQ']
  have hd1 : det (B + Q') ≤ Real.exp ℓ ^ d * det (B + Q) := by
    rw [← det_smul_fin]
    apply det_mono hM' hMt
    intro v
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul, add_mulVec, add_mulVec, dotProduct_add,
      dotProduct_add]
    have := h1 v
    have := posDef_quad_nonneg hB v
    nlinarith
  have hd2 : det Q ≤ Real.exp ℓ ^ d * det Q' := by
    rw [← det_smul_fin]
    exact det_mono hQ hQt (fun v => by rw [smul_mulVec, dotProduct_smul, smul_eq_mul]; exact h2 v)
  have hp : pit B Q' g ≤ Real.exp ℓ * pit B Q g := by
    have hle : LeQ (B + Q) (Real.exp ℓ • (B + Q')) := by
      intro v
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul, add_mulVec, add_mulVec, dotProduct_add,
        dotProduct_add]
      have := h2 v
      have := posDef_quad_nonneg hB v
      nlinarith
    have := inv_anti hM (hM'.smul hEpos) hle g
    rw [inv_smul_mulVec hM' hEpos, dotProduct_smul, smul_eq_mul] at this
    unfold pit
    have hx : 0 ≤ g ⬝ᵥ ((B + Q')⁻¹ *ᵥ g) := by
      have := posDef_quad_nonneg hM'.inv g
      exact this
    calc g ⬝ᵥ ((B + Q')⁻¹ *ᵥ g) = Real.exp ℓ * ((Real.exp ℓ)⁻¹ * g ⬝ᵥ ((B + Q')⁻¹ *ᵥ g)) := by
          field_simp
      _ ≤ Real.exp ℓ * (g ⬝ᵥ ((B + Q)⁻¹ *ᵥ g)) := mul_le_mul_of_nonneg_left this hEpos.le
  have hdM := hM.det_pos
  have hdM' := hM'.det_pos
  have hdQ := hQ.det_pos
  have hdQ' := hQ'.det_pos
  have hpit := pit_pos hB hQ hg
  have hpit' := pit_pos hB hQ' hg
  have l1 : Real.log (det (B + Q')) ≤ d * ℓ + Real.log (det (B + Q)) := by
    have := Real.log_le_log hdM' hd1
    rwa [Real.log_mul (by positivity) hdM.ne', Real.log_pow, Real.log_exp] at this
  have l2 : Real.log (det Q) ≤ d * ℓ + Real.log (det Q') := by
    have := Real.log_le_log hdQ hd2
    rwa [Real.log_mul (by positivity) hdQ'.ne', Real.log_pow, Real.log_exp] at this
  have l3 : Real.log (pit B Q' g) ≤ ℓ + Real.log (pit B Q g) := by
    have := Real.log_le_log hpit' hp
    rwa [Real.log_mul hEpos.ne' hpit.ne', Real.log_exp] at this
  unfold U Psi
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_le_mul_of_nonneg_left l1 hk, mul_le_mul_of_nonneg_left l2 hk]

lemma cs_psd {M : Matrix (Fin d) (Fin d) ℝ} (hMt : Mᵀ = M)
    (hnn : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ (M *ᵥ v)) (u v : Fin d → ℝ) (hC : 0 < v ⬝ᵥ (M *ᵥ v)) :
    (u ⬝ᵥ (M *ᵥ v)) ^ 2 ≤ (u ⬝ᵥ (M *ᵥ u)) * (v ⬝ᵥ (M *ᵥ v)) := by
  set A := u ⬝ᵥ (M *ᵥ u)
  set Bv := u ⬝ᵥ (M *ᵥ v)
  set C := v ⬝ᵥ (M *ᵥ v)
  have hvu : v ⬝ᵥ (M *ᵥ u) = Bv := by
    simp only [Bv]; rw [← symm_dot hMt, dotProduct_comm]
  have hq := hnn (C • u - Bv • v)
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

lemma det_rank_one_lower {N Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.PosDef) (hNt : Nᵀ = N)
    (h4 : ∀ v : Fin d → ℝ, 4 * (v ⬝ᵥ (Q *ᵥ v)) ≤ v ⬝ᵥ (N *ᵥ v)) {z : Fin d → ℝ} (hz : z ≠ 0) :
    4 ^ d * det Q * (z ⬝ᵥ (N *ᵥ z)) ≤ 4 * det N * (z ⬝ᵥ (Q *ᵥ z)) := by
  have hzQ := posDef_quad_pos hQ hz
  have h4Q : ((4 : ℝ) • Q).PosDef := hQ.smul (by norm_num)
  have hdet4 : det ((4 : ℝ) • Q) = 4 ^ d * det Q := det_smul_fin 4 Q
  have hdQ := hQ.det_pos
  set E := N - (4 : ℝ) • Q with hE
  have hEt : Eᵀ = E := by rw [hE, transpose_sub, transpose_smul, hNt, posDef_symm hQ]
  have hEq : ∀ v : Fin d → ℝ, v ⬝ᵥ (E *ᵥ v) = v ⬝ᵥ (N *ᵥ v) - 4 * (v ⬝ᵥ (Q *ᵥ v)) := fun v => by
    rw [hE, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hEnn : ∀ v : Fin d → ℝ, 0 ≤ v ⬝ᵥ (E *ᵥ v) := fun v => by rw [hEq]; linarith [h4 v]
  have hN4 : LeQ ((4 : ℝ) • Q) N := fun v => by
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]; exact h4 v
  have hdN : 4 ^ d * det Q ≤ det N := by rw [← hdet4]; exact det_mono h4Q hNt hN4
  set c := z ⬝ᵥ (E *ᵥ z) with hc
  rcases (hEnn z).eq_or_lt with hc0 | hcpos
  · have : z ⬝ᵥ (N *ᵥ z) = 4 * (z ⬝ᵥ (Q *ᵥ z)) := by
      have := hEq z; linarith
    rw [this]
    nlinarith
  · set f := E *ᵥ z with hf
    have hrank : LeQ ((4 : ℝ) • Q + c⁻¹ • vecMulVec f f) N := by
      intro u
      have hl : u ⬝ᵥ (((4 : ℝ) • Q + c⁻¹ • vecMulVec f f) *ᵥ u) =
          4 * (u ⬝ᵥ (Q *ᵥ u)) + c⁻¹ * (u ⬝ᵥ f) ^ 2 := by
        rw [add_mulVec, smul_mulVec, smul_mulVec, vecMulVec_mulVec', dotProduct_add,
          dotProduct_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          smul_eq_mul, dotProduct_comm f u]
        ring
      have hcs : (u ⬝ᵥ f) ^ 2 ≤ (u ⬝ᵥ (E *ᵥ u)) * c := cs_psd hEt hEnn u z hcpos
      have h2 : c⁻¹ * (u ⬝ᵥ f) ^ 2 ≤ u ⬝ᵥ (E *ᵥ u) := by
        rw [inv_mul_le_iff₀ hcpos]; linarith
      rw [hl]
      have := hEq u
      linarith
    have hpd : ((4 : ℝ) • Q + c⁻¹ • vecMulVec f f).PosDef := by
      have hpsd : (c⁻¹ • vecMulVec f f).PosSemidef := by
        refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
        · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_smul,
            transpose_vecMulVec]
        · simp only [star_trivial, smul_mulVec, vecMulVec_mulVec', dotProduct_smul, smul_eq_mul]
          have : 0 ≤ c⁻¹ := inv_nonneg.mpr hcpos.le
          rw [dotProduct_comm f v, ← sq]
          exact mul_nonneg this (sq_nonneg _)
      exact h4Q.add_posSemidef hpsd
    have hdl := det_mono hpd hNt hrank
    have hu4 : IsUnit ((4 : ℝ) • Q).det := (isUnit_iff_isUnit_det _).mp h4Q.isUnit
    rw [det_add_rankOne _ hu4, hdet4] at hdl
    set w := ((4 : ℝ) • Q)⁻¹ *ᵥ f with hw
    have h4w : ((4 : ℝ) • Q) *ᵥ w = f := mulVec_inv_mulVec h4Q f
    have hzf : z ⬝ᵥ f = c := rfl
    have hcs2 := cs_posDef h4Q z w
    rw [h4w, hzf, dotProduct_comm w f] at hcs2
    have hz4 : z ⬝ᵥ (((4 : ℝ) • Q) *ᵥ z) = 4 * (z ⬝ᵥ (Q *ᵥ z)) := by
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hz4] at hcs2
    have hNz : z ⬝ᵥ (N *ᵥ z) = 4 * (z ⬝ᵥ (Q *ᵥ z)) + c := by
      have := hEq z; linarith
    have hfw0 : 0 ≤ f ⬝ᵥ w := by
      have := posDef_quad_nonneg h4Q w
      rw [h4w, dotProduct_comm] at this; exact this
    have key : c * (z ⬝ᵥ (N *ᵥ z)) ≤ 4 * (z ⬝ᵥ (Q *ᵥ z)) * (c + (f ⬝ᵥ w)) := by
      rw [hNz]; nlinarith
    have hdl' : 4 ^ d * det Q * (1 + c⁻¹ * (f ⬝ᵥ w)) ≤ det N := hdl
    have : 1 + c⁻¹ * (f ⬝ᵥ w) = (c + f ⬝ᵥ w) / c := by
      rw [add_div, div_self hcpos.ne', inv_mul_eq_div]
    rw [this] at hdl'
    have hA : 0 < 4 ^ d * det Q := by positivity
    have := mul_le_mul_of_nonneg_left key hA.le
    have h5 : 4 ^ d * det Q * ((c + f ⬝ᵥ w) / c) * c = 4 ^ d * det Q * (c + f ⬝ᵥ w) := by
      rw [mul_assoc, div_mul_cancel₀ _ hcpos.ne']
    have h6 := mul_le_mul_of_nonneg_right hdl' hcpos.le
    rw [h5] at h6
    nlinarith

lemma U_lower {B Q : Matrix (Fin d) (Fin d) ℝ} (hB : B.PosDef) (hQ : Q.PosDef) (k : ℕ)
    (hk : 1 ≤ k) {g : Fin d → ℝ} (hg : g ≠ 0) :
    ((k : ℝ) * d - 1) * Real.log 4 + Real.log (g ⬝ᵥ (Q⁻¹ *ᵥ g)) ≤ U k B Q g := by
  have hM := hB.add hQ
  have hBt := posDef_symm hB
  have hQt := posDef_symm hQ
  have hMt := posDef_symm hM
  have hBit : (B⁻¹)ᵀ = B⁻¹ := posDef_symm hB.inv
  set M := B + Q with hMdef
  set N := M * B⁻¹ * M with hN
  have hNt : Nᵀ = N := by rw [hN, transpose_mul, transpose_mul, hMt, hBit, Matrix.mul_assoc]
  have hquad : ∀ v : Fin d → ℝ, v ⬝ᵥ (N *ᵥ v) =
      (B *ᵥ v) ⬝ᵥ v + 2 * ((Q *ᵥ v) ⬝ᵥ v) + (Q *ᵥ v) ⬝ᵥ (B⁻¹ *ᵥ (Q *ᵥ v)) := fun v => by
    have hw : B⁻¹ *ᵥ (B *ᵥ v) = v :=
      inv_mulVec_of_mulVec ((isUnit_iff_isUnit_det _).mp hB.isUnit) rfl
    have hsym : (B *ᵥ v) ⬝ᵥ (B⁻¹ *ᵥ (Q *ᵥ v)) = (Q *ᵥ v) ⬝ᵥ v := by
      rw [← symm_dot hBit, hw, dotProduct_comm]
    rw [hN, ← mulVec_mulVec, ← mulVec_mulVec, ← symm_dot hMt, hMdef, add_mulVec, mulVec_add, hw,
      add_dotProduct, dotProduct_add, dotProduct_add, hsym]
    ring
  have hBv : ∀ v : Fin d → ℝ, 0 ≤ (B *ᵥ v) ⬝ᵥ v := fun v => by
    rw [dotProduct_comm]; exact posDef_quad_nonneg hB v
  have hQv : ∀ v : Fin d → ℝ, 0 ≤ (Q *ᵥ v) ⬝ᵥ v := fun v => by
    rw [dotProduct_comm]; exact posDef_quad_nonneg hQ v
  have hQBQ : ∀ v : Fin d → ℝ, 0 ≤ (Q *ᵥ v) ⬝ᵥ (B⁻¹ *ᵥ (Q *ᵥ v)) := fun v =>
    posDef_quad_nonneg hB.inv _
  have h4 : ∀ v : Fin d → ℝ, 4 * (v ⬝ᵥ (Q *ᵥ v)) ≤ v ⬝ᵥ (N *ᵥ v) := fun v => by
    rw [hquad]
    have hw : B⁻¹ *ᵥ (B *ᵥ v) = v :=
      inv_mulVec_of_mulVec ((isUnit_iff_isUnit_det _).mp hB.isUnit) rfl
    have hsym : (B *ᵥ v) ⬝ᵥ (B⁻¹ *ᵥ (Q *ᵥ v)) = (Q *ᵥ v) ⬝ᵥ v := by
      rw [← symm_dot hBit, hw, dotProduct_comm]
    have hnn := posDef_quad_nonneg hB.inv (B *ᵥ v - Q *ᵥ v)
    rw [mulVec_sub, hw, sub_dotProduct, dotProduct_sub, dotProduct_sub, hsym] at hnn
    rw [dotProduct_comm v (Q *ᵥ v)]
    have hcomm : (Q *ᵥ v) ⬝ᵥ v = v ⬝ᵥ (Q *ᵥ v) := dotProduct_comm _ _
    nlinarith
  have hMN : ∀ v : Fin d → ℝ, v ⬝ᵥ (M *ᵥ v) ≤ v ⬝ᵥ (N *ᵥ v) := fun v => by
    rw [hquad, hMdef, add_mulVec, dotProduct_add, dotProduct_comm v (B *ᵥ v),
      dotProduct_comm v (Q *ᵥ v)]
    linarith [hQv v, hQBQ v]
  have hdetN : det N = det M ^ 2 / det B := by
    rw [hN, det_mul, det_mul, det_nonsing_inv]
    have := hB.det_pos
    field_simp
    rw [Ring.inverse_eq_inv']
    field_simp
  set z := Q⁻¹ *ᵥ g with hz
  have hQz : Q *ᵥ z = g := mulVec_inv_mulVec hQ g
  have hz0 : z ≠ 0 := by intro h0; apply hg; rw [← hQz, h0, mulVec_zero]
  have hrank := det_rank_one_lower hQ hNt h4 hz0
  have hzQz : z ⬝ᵥ (Q *ᵥ z) = g ⬝ᵥ z := by rw [hQz, dotProduct_comm]
  have hΛ : 0 < g ⬝ᵥ z := by rw [← hzQz]; exact posDef_quad_pos hQ hz0
  set π := pit B Q g with hπ
  have hπpos : 0 < π := pit_pos hB hQ hg
  have hcsM := cs_posDef hM z (M⁻¹ *ᵥ g)
  rw [mulVec_inv_mulVec hM, dotProduct_comm z g, dotProduct_comm (M⁻¹ *ᵥ g) g] at hcsM
  have hMg : g ⬝ᵥ (M⁻¹ *ᵥ g) = π := rfl
  rw [hMg] at hcsM
  have hzMz := hMN z
  have hzNz : (g ⬝ᵥ z) ^ 2 ≤ z ⬝ᵥ (N *ᵥ z) * π := by
    have := mul_le_mul_of_nonneg_right hzMz hπpos.le
    linarith
  rw [hzQz] at hrank
  have hdN4 : (4 : ℝ) ^ d * det Q ≤ det N := by
    have h4Q : ((4 : ℝ) • Q).PosDef := hQ.smul (by norm_num)
    rw [← det_smul_fin]
    exact det_mono h4Q hNt (fun v => by rw [smul_mulVec, dotProduct_smul, smul_eq_mul]; exact h4 v)
  have hdQ := hQ.det_pos
  have hdNpos : 0 < det N := lt_of_lt_of_le (by positivity) hdN4
  have hPsi : Psi B Q = Real.log (det N) - Real.log (det Q) := by
    rw [Psi, ← hMdef, hdetN, Real.log_div (pow_pos hM.det_pos 2).ne' hB.det_pos.ne',
      Real.log_pow]
    push_cast
    ring
  have hl4 : Real.log 4 ≠ 0 := by positivity
  have hPsi1 : (d : ℝ) * Real.log 4 ≤ Psi B Q := by
    rw [hPsi]
    have := Real.log_le_log (by positivity) hdN4
    rw [Real.log_mul (by positivity) hdQ.ne', Real.log_pow] at this
    linarith
  have hzN0 : 0 < z ⬝ᵥ (N *ᵥ z) := by
    have := posDef_quad_pos hQ hz0
    linarith [h4 z]
  have hPsi2 : (d : ℝ) * Real.log 4 - Real.log 4 + Real.log (g ⬝ᵥ z) - Real.log π ≤ Psi B Q := by
    rw [hPsi]
    have h1 : (4 : ℝ) ^ d * det Q * ((g ⬝ᵥ z) ^ 2 / π) ≤ 4 * det N * (g ⬝ᵥ z) := by
      have : (g ⬝ᵥ z) ^ 2 / π ≤ z ⬝ᵥ (N *ᵥ z) := by rw [div_le_iff₀ hπpos]; linarith
      calc (4 : ℝ) ^ d * det Q * ((g ⬝ᵥ z) ^ 2 / π) ≤ 4 ^ d * det Q * (z ⬝ᵥ (N *ᵥ z)) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ 4 * det N * (g ⬝ᵥ z) := hrank
    have h2 : (4 : ℝ) ^ d * det Q * (g ⬝ᵥ z) ≤ 4 * det N * π := by
      have e : (4 : ℝ) ^ d * det Q * ((g ⬝ᵥ z) ^ 2 / π) =
          (4 ^ d * det Q * (g ⬝ᵥ z)) * ((g ⬝ᵥ z) / π) := by ring
      rw [e] at h1
      have hq : 0 < (g ⬝ᵥ z) / π := div_pos hΛ hπpos
      have := (mul_le_mul_iff_of_pos_right hΛ).mp (by
        calc (4 ^ d * det Q * (g ⬝ᵥ z)) * (g ⬝ᵥ z) = (4 ^ d * det Q * (g ⬝ᵥ z)) *
              ((g ⬝ᵥ z) / π) * π := by field_simp
          _ ≤ 4 * det N * (g ⬝ᵥ z) * π := mul_le_mul_of_nonneg_right h1 hπpos.le
          _ = 4 * det N * π * (g ⬝ᵥ z) := by ring)
      exact this
    have := Real.log_le_log (by positivity) h2
    rw [Real.log_mul (by positivity) hΛ.ne', Real.log_mul (by positivity) hdQ.ne', Real.log_pow,
      Real.log_mul (by positivity) hπpos.ne', Real.log_mul (by norm_num) hdNpos.ne'] at this
    linarith
  unfold U
  rw [← hπ]
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have := mul_le_mul_of_nonneg_left hPsi1 hk1
  nlinarith

end LongTails.Proofs.BFGSLogStep
