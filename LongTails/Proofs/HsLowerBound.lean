import LongTails.Setups.HighDimensionalHessianStableSkewMonotone
import LongTails.Proofs.HsParams
import LongTails.Proofs.HsExecution
import LongTails.Proofs.SharpChainHiding

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HsLowerBound

open LongTails.Setups.HighDimensionalHessianStableSkewMonotone
open LongTails.Proofs.HsProfile LongTails.Proofs.HsChain LongTails.Proofs.HsStability
open LongTails.Proofs.HsInstance LongTails.Proofs.HsBounds LongTails.Proofs.HsParams
open LongTails.Proofs.HsExecution

variable (P : Params)

noncomputable def nb : ℕ := bud (P.M * P.D)

noncomputable def kk : ℕ := 2 * nb P

noncomputable def pp : ℕ := pK (kk P)

noncomputable def sβ : ℝ := P.D / Real.sqrt (KK (kk P))

noncomputable def sα : ℝ := 16 * P.ε * Real.sqrt (KK (kk P) + 1)

noncomputable def toU (x : E P.d) : E P.d := (sβ P)⁻¹ • (x - P.x0)

variable (π : Fin (kk P + 1) ↪ Fin P.d)

noncomputable def hardF (x : E P.d) : E P.d := sα P • FF π (pp P) (toU P x)

noncomputable def hardDF (x : E P.d) : E P.d →L[ℝ] E P.d :=
  (sα P / sβ P) • DFF π (pp P) (toU P x)

noncomputable def hardOracle : Oracle (E P.d) (E P.d ⊕ (E P.d →L[ℝ] E P.d)) 2 where
  answer _ q _ := if q.1 = 0 then Sum.inl (hardF P π q.2) else Sum.inr (hardDF P π q.2)

section Facts

variable {P}

lemma sβ_pos (hD : 0 < P.D) : 0 < sβ P := by
  unfold sβ
  have := KK_pos (kk P)
  positivity

lemma hasFDerivAt_toU (x : E P.d) :
    HasFDerivAt (toU P) ((sβ P)⁻¹ • ContinuousLinearMap.id ℝ (E P.d)) x := by
  have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const P.x0).const_smul (sβ P)⁻¹
  exact h

lemma hasFDerivAt_hardF (x : E P.d) :
    HasFDerivAt (hardF P π) (hardDF P π x) x := by
  have h1 := (hasFDerivAt_Fv (pp P) (pp P) (ca (kk P)) (cl (kk P)) cκ (cC (kk P)) (nn π) cc
    (ch_pos (kk P)) (toU P x) (w2 := cw)).comp x (hasFDerivAt_toU x)
  have h2 := h1.const_smul (sα P)
  have h3 : hardDF P π x = sα P • ((DFv (pp P) (pp P) (ca (kk P)) (ch (kk P)) cw (cl (kk P)) cκ
      (cC (kk P)) (nn π) cc (toU P x)).comp ((sβ P)⁻¹ • ContinuousLinearMap.id ℝ (E P.d))) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [hardDF, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_smul, div_eq_mul_inv]
  rw [h3]
  exact h2

end Facts

section Arith

variable {P}

lemma valid_facts (hv : spec.valid P) :
    0 < P.M ∧ 0 < P.D ∧ 0 < P.ε ∧ 0 ≤ P.Λ ∧ 2 ^ 60 ≤ P.M * P.D ∧
      P.ε * (P.M * P.D) ^ 2 ≤ P.Λ * P.D ∧ 2 ^ 21 * (P.M * P.D) ^ ((10 : ℝ) / 3) ≤ P.d := by
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩ := hv
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

lemma kk_ge (hv : spec.valid P) : 1024 ≤ kk P := by
  have := bud_ge (valid_facts hv).2.2.2.2.1
  unfold kk nb
  omega

lemma pp_le (hv : spec.valid P) : ((pp P : ℕ) : ℝ) + 1 ≤ KK (kk P) := by
  have h := pK_le (kk P) (kk_ge hv)
  unfold KK pp
  exact_mod_cast h

lemma stab_arith (hv : spec.valid P) : cM (kk P) (pp P) * Real.sqrt (KK (kk P)) ≤ P.M * P.D := by
  obtain ⟨hM, hD, _, _, hY, _, _⟩ := valid_facts hv
  set Y := P.M * P.D with hYd
  have hc := cM_le (pp_le hv)
  have hlog := pK_le_log hY
  have hKb := KK_bud_le hY
  have hb3 := bud_cube hY
  have hK := KK_pos (kk P)
  have hL := Lg_ge hY
  set K := KK (kk P) with hKd
  have hKe : K = KK (2 * bud Y) := rfl
  set L := Lg Y
  set pp1 : ℝ := ((pp P : ℕ) : ℝ) + 1
  have hpp : pp1 ≤ 13 * L := by
    have : pp P = pK (2 * bud Y) := rfl
    simp only [pp1, this]
    exact hlog
  have hcM0 : 0 ≤ cM (kk P) (pp P) := by
    unfold cM
    have := (cS_pos (k := kk P) (pp P)).le
    unfold ch cw cκ
    positivity
  have hsq : (cM (kk P) (pp P) * Real.sqrt K) ^ 2 ≤ Y ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK.le]
    have h1 : cM (kk P) (pp P) ^ 2 ≤ (1500 * pp1 * K) ^ 2 :=
      pow_le_pow_left₀ hcM0 hc 2
    have h2 : (1500 * pp1 * K) ^ 2 * K ≤ (19500 * L) ^ 2 * K ^ 3 := by
      have : 1500 * pp1 ≤ 19500 * L := by nlinarith
      have h0 : 0 ≤ 1500 * pp1 := by positivity
      have := pow_le_pow_left₀ h0 this 2
      nlinarith [pow_pos hK 3]
    have h3 : K ^ 3 ≤ 27 * (bud Y : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ hK.le (hKe ▸ hKb) 3
      nlinarith
    have h4 : (bud Y : ℝ) ^ 3 ≤ (Y / (2 ^ 18 * L)) ^ 2 := hb3
    have hL0 : 0 < L := by linarith
    have h5 : (19500 * L) ^ 2 * (27 * (Y / (2 ^ 18 * L)) ^ 2) ≤ Y ^ 2 := by
      rw [div_pow, mul_pow, mul_pow]
      field_simp
      nlinarith [sq_nonneg Y]
    calc cM (kk P) (pp P) ^ 2 * K ≤ (1500 * pp1 * K) ^ 2 * K :=
          mul_le_mul_of_nonneg_right h1 hK.le
      _ ≤ (19500 * L) ^ 2 * K ^ 3 := h2
      _ ≤ (19500 * L) ^ 2 * (27 * (Y / (2 ^ 18 * L)) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
      _ ≤ Y ^ 2 := h5
  have hY0 : 0 ≤ Y := by positivity
  have hl : 0 ≤ cM (kk P) (pp P) * Real.sqrt K := by positivity
  nlinarith [sq_nonneg (cM (kk P) (pp P) * Real.sqrt K - Y), sq_nonneg (cM (kk P) (pp P) * Real.sqrt K + Y)]

lemma QK3_le (hv : spec.valid P) :
    (((pp P : ℕ) : ℝ) + 1) * KK (kk P) ^ 3 ≤ (P.M * P.D) ^ 2 / 2 ^ 32 := by
  obtain ⟨_, _, _, _, hY, _, _⟩ := valid_facts hv
  set Y := P.M * P.D with hYd
  have hKb := KK_bud_le hY
  have hb3 := bud_cube hY
  have hK := KK_pos (kk P)
  have hL := Lg_ge hY
  have hQ : (((pp P : ℕ) : ℝ) + 1) ≤ 13 * Lg Y := pK_le_log hY
  have hQ0 : 0 ≤ (((pp P : ℕ) : ℝ) + 1) := by positivity
  have h1 : KK (kk P) ^ 3 ≤ 27 * (bud Y : ℝ) ^ 3 := by
    have := pow_le_pow_left₀ hK.le hKb 3
    nlinarith
  have hX : Xb Y ^ 2 = Y ^ 2 / (2 ^ 36 * Lg Y ^ 2) := by
    unfold Xb; rw [div_pow, mul_pow]; ring
  have hL0 : 0 < Lg Y := by linarith
  calc (((pp P : ℕ) : ℝ) + 1) * KK (kk P) ^ 3 ≤ (13 * Lg Y) * (27 * (Y ^ 2 / (2 ^ 36 * Lg Y ^ 2))) := by
        apply mul_le_mul hQ _ (by positivity) (by positivity)
        rw [← hX]; linarith
    _ = 351 * Y ^ 2 / (2 ^ 36 * Lg Y) := by field_simp; ring
    _ ≤ Y ^ 2 / 2 ^ 32 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : (0 : ℝ) ≤ Y ^ 2 := sq_nonneg _
        nlinarith

lemma K5_le (hv : spec.valid P) : KK (kk P) ^ 5 ≤ 243 * (P.M * P.D) ^ ((10 : ℝ) / 3) := by
  obtain ⟨_, _, _, _, hY, _, _⟩ := valid_facts hv
  set Y := P.M * P.D
  have hKb := KK_bud_le hY
  have hbl := bud_le hY
  have hXle := Xb_le hY
  have hK := KK_pos (kk P)
  have hY0 : 0 ≤ Y := by linarith [show (0 : ℝ) < 2 ^ 60 by positivity]
  have hX0 : 0 ≤ Xb Y := by linarith [Xb_ge hY, show (0 : ℝ) < 2 ^ 24 by positivity]
  have h1 : KK (kk P) ^ 5 ≤ 243 * (bud Y : ℝ) ^ 5 := by
    have := pow_le_pow_left₀ hK.le hKb 5
    nlinarith
  have h2 : (bud Y : ℝ) ^ 5 ≤ Xb Y ^ ((10 : ℝ) / 3) := by
    have := pow_le_pow_left₀ (Nat.cast_nonneg _) hbl 5
    have e : (Xb Y ^ ((2 : ℝ) / 3)) ^ 5 = Xb Y ^ ((10 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]; norm_num
    linarith
  have h3 : Xb Y ^ ((10 : ℝ) / 3) ≤ Y ^ ((10 : ℝ) / 3) := by
    apply Real.rpow_le_rpow hX0 _ (by norm_num)
    have : Y / 2 ^ 18 ≤ Y := div_le_self hY0 (by norm_num)
    linarith
  nlinarith

end Arith

section Admissible

variable {P}

lemma sα_div_sβ (hv : spec.valid P) :
    sα P / sβ P ≤ 32 * P.ε * KK (kk P) / P.D := by
  obtain ⟨_, hD, hε, _, _, _, _⟩ := valid_facts hv
  have hK := KK_ge (kk P)
  have hs1 : Real.sqrt (KK (kk P) + 1) * Real.sqrt (KK (kk P)) ≤ 2 * KK (kk P) := by
    rw [← Real.sqrt_mul (by linarith)]
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hsK : 0 < Real.sqrt (KK (kk P)) := Real.sqrt_pos.mpr (by linarith)
  unfold sα sβ
  rw [div_div_eq_mul_div, div_le_div_iff₀ hD hD]
  have : 16 * P.ε * Real.sqrt (KK (kk P) + 1) * Real.sqrt (KK (kk P)) ≤
      32 * P.ε * KK (kk P) := by
    have := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ 16 * P.ε by positivity)
    nlinarith
  nlinarith

lemma hard_admissible (hv : spec.valid P) :
    spec.admissible P (hardF P π) (hardOracle P π) := by
  obtain ⟨hM, hD, hε, hΛ, hY, hΛD, _⟩ := valid_facts hv
  have hp2 : 2 ≤ pp P := pK_ge _
  have hp1 : 1 ≤ pp P := by omega
  have hw : (0 : ℝ) < cw := by unfold cw; norm_num
  have hfd : ∀ x, fderiv ℝ (hardF P π) x = hardDF P π x :=
    fun x => (hasFDerivAt_hardF π x).fderiv
  have hβ := sβ_pos hD
  have hα : 0 < sα P := mul_pos (mul_pos (by norm_num) hε)
    (Real.sqrt_pos.mpr (by have := KK_pos (kk P); linarith))
  have hαβ : 0 ≤ sα P / sβ P := by positivity
  refine ⟨fun _ _ _ => by simp [hardOracle], fun _ x _ => ?_,
    fun x => (hasFDerivAt_hardF π x).differentiableAt,
    ⟨0, fun _ => by simp, fun x u v => ?_, fun x v => ?_, fun x y v => ?_⟩, ?_⟩
  · simp [hardOracle, hfd]
  · rw [hfd, sub_zero]
    simp only [hardDF, smul_apply, real_inner_smul_left, real_inner_smul_right]
    rw [DFv_symm]
  · rw [hfd, sub_zero]
    simp only [hardDF, smul_apply, real_inner_smul_left]
    exact mul_nonneg hαβ (DFF_quad_nonneg π (pp P) hp1 _ v)
  · rw [hfd, hfd, sub_zero, sub_zero]
    simp only [hardDF, smul_apply, real_inner_smul_left]
    have hst := FF_stable π (pp P) hp2 (pK_q (kk P)) (toU P x) (toU P y) v
    have hdist : ‖toU P y - toU P x‖ = (sβ P)⁻¹ * ‖y - x‖ := by
      unfold toU
      rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hβ)]
    have hcM : cM (kk P) (pp P) * (sβ P)⁻¹ ≤ (toGeneral P).pub.M := by
      have h1 := stab_arith hv
      change cM (kk P) (pp P) * (sβ P)⁻¹ ≤ P.M
      unfold sβ
      rw [inv_div, mul_div_assoc', div_le_iff₀ hD]
      linarith
    have hexp : Real.exp (cM (kk P) (pp P) * ‖toU P y - toU P x‖) ≤
        Real.exp ((toGeneral P).pub.M * ‖y - x‖) := by
      apply Real.exp_le_exp.mpr
      rw [hdist, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hcM (norm_nonneg _)
    have hq0 := DFF_quad_nonneg π (pp P) hp1 (toU P x) v
    calc sα P / sβ P * ⟪DFF π (pp P) (toU P y) v, v⟫ ≤
        sα P / sβ P * (Real.exp (cM (kk P) (pp P) * ‖toU P y - toU P x‖) *
          ⟪DFF π (pp P) (toU P x) v, v⟫) := mul_le_mul_of_nonneg_left hst hαβ
      _ ≤ sα P / sβ P * (Real.exp ((toGeneral P).pub.M * ‖y - x‖) *
          ⟪DFF π (pp P) (toU P x) v, v⟫) := by
          gcongr
      _ = _ := mul_left_comm _ _ _
  · obtain ⟨xs, hxs⟩ := exists_minimizer (pp P) (pp P) (ca (kk P)) (cl (kk P)) cκ (cC (kk P))
      (nn π) cc hp1 hp1 (ch_pos _) hw (by unfold cl; have := KK_pos (kk P); positivity)
    refine ⟨P.x0 + sβ P • xs, ?_, ?_, fun x _ => ?_⟩
    · have hu : toU P (P.x0 + sβ P • xs) = xs := by
        unfold toU
        rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hβ.ne', one_smul]
      unfold hardF
      rw [hu]
      have := Fv_eq_zero_of_min (pp P) (pp P) (ca (kk P)) (cl (kk P)) cκ (cC (kk P)) (nn π) cc
        (ch_pos _) hw xs hxs
      unfold FF
      rw [this, smul_zero]
    · change ‖P.x0 - (P.x0 + sβ P • xs)‖ ≤ P.D
      rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
      have hn := minimizer_norm π (pp P) hp1 xs hxs
      have hK := KK_pos (kk P)
      have hsK : 0 < Real.sqrt (KK (kk P)) := Real.sqrt_pos.mpr hK
      calc sβ P * ‖xs‖ ≤ sβ P * Real.sqrt (KK (kk P)) := mul_le_mul_of_nonneg_left hn hβ.le
        _ = P.D := by unfold sβ; field_simp
    · change ‖fderiv ℝ (hardF P π) x‖ ≤ P.Λ
      rw [hfd]
      unfold hardDF
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hαβ]
      have hN := DFF_norm_le π (pp P) hp1 (toU P x)
      have hpp := pp_le hv
      have hK := KK_ge (kk P)
      set K := KK (kk P)
      set Q : ℝ := ((pp P : ℕ) : ℝ) + 1
      have hQ1 : 1 ≤ Q := by have : (0 : ℝ) ≤ (pp P : ℕ) := Nat.cast_nonneg _; linarith
      have hΛhat : 5 + 64 * K ^ 2 * Q + 8 * Q * (14 * K + 9) ^ 2 ≤ 4301 * (Q * K ^ 2) := by
        have h1 : (14 * K + 9) ^ 2 ≤ 529 * K ^ 2 := by nlinarith
        have h2 : 1 ≤ Q * K ^ 2 := by nlinarith
        nlinarith
      have hab := sα_div_sβ hv
      have hQK := QK3_le hv
      have hfin : sα P / sβ P * (5 + 64 * K ^ 2 * Q + 8 * Q * (14 * K + 9) ^ 2) ≤ P.Λ := by
        calc sα P / sβ P * (5 + 64 * K ^ 2 * Q + 8 * Q * (14 * K + 9) ^ 2) ≤
            32 * P.ε * K / P.D * (4301 * (Q * K ^ 2)) :=
              mul_le_mul hab hΛhat (by positivity) (by positivity)
          _ = 137632 * P.ε * (Q * K ^ 3) / P.D := by ring
          _ ≤ 137632 * P.ε * ((P.M * P.D) ^ 2 / 2 ^ 32) / P.D := by gcongr
          _ ≤ P.Λ := by
              rw [div_le_iff₀ hD]
              have : 137632 * P.ε * ((P.M * P.D) ^ 2 / 2 ^ 32) ≤ P.ε * (P.M * P.D) ^ 2 := by
                have h0 : 0 ≤ P.ε * (P.M * P.D) ^ 2 := by positivity
                rw [mul_div_assoc', div_le_iff₀ (by positivity)]
                nlinarith
              linarith
      exact (mul_le_mul_of_nonneg_left hN hαβ).trans hfin

end Admissible

section Hiding

variable {P}

noncomputable def full (π : Fin (kk P + 1) ↪ Fin P.d) (u : E P.d) : E P.d × (E P.d →L[ℝ] E P.d) :=
  (sα P • FF π (pp P) u, (sα P / sβ P) • DFF π (pp P) u)

noncomputable def part (π : Fin (kk P + 1) ↪ Fin P.d) (t : ℕ) (u : E P.d) :
    E P.d × (E P.d →L[ℝ] E P.d) :=
  (sα P • Fv (pp P) (pp P) (ca (kk P)) (ch (kk P)) cw (cl (kk P)) cκ (cC (kk P)) (nt π t) (ct t) u,
    (sα P / sβ P) •
      DFv (pp P) (pp P) (ca (kk P)) (ch (kk P)) cw (cl (kk P)) cκ (cC (kk P)) (nt π t) (ct t) u)

lemma nt_prefix {d k : ℕ} (π ρ : Fin (k + 1) ↪ Fin d) (t : ℕ)
    (h : ∀ j : Fin (k + 1), j.val ≤ t → π j = ρ j) : nt π t = nt ρ t := by
  funext j
  unfold nt
  split_ifs with hj
  · unfold nn pv
    rw [h j hj]
    split_ifs with h0
    · rw [h ⟨j.val - 1, by omega⟩ (by simp only; omega)]
    · rfl
  · rfl

lemma part_prefix (π ρ : Fin (kk P + 1) ↪ Fin P.d) (t : ℕ)
    (h : ∀ j : Fin (kk P + 1), j.val ≤ t → π j = ρ j) : part π t = part ρ t := by
  unfold part
  rw [nt_prefix π ρ t h]

lemma full_eq_part (π : Fin (kk P + 1) ↪ Fin P.d) (t : ℕ) (u : E P.d)
    (hu : ‖u‖ ≤ cB (kk P) → ∀ j : Fin (kk P + 1), t ≤ j.val → |u (π j)| ≤ cθ (kk P)) :
    full π u = part π t u := by
  have hp1 : 1 ≤ pp P := by have := pK_ge (kk P); unfold pp; omega
  have hK := KK_pos (kk P)
  unfold full part FF DFF
  by_cases hb : ‖u‖ ≤ cB (kk P)
  · have hah : 0 ≤ ca (kk P) - ch (kk P) := by rw [ca_sub_ch]; positivity
    have hθ : 2 * cθ (kk P) ≤ ca (kk P) - ch (kk P) := by
      rw [ca_sub_ch]; unfold cθ
      rw [show 2 * (1 / (16 * KK (kk P))) = 1 / (8 * KK (kk P)) by field_simp; ring]
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    obtain ⟨h1, h2⟩ := answers_masked π (pp P) (pp P) (ca (kk P)) cw (cl (kk P)) cκ (cC (kk P))
      hp1 (ch_pos _) hah t (cθ (kk P)) hθ u (hu hb)
    rw [h1, h2]
  · push Not at hb
    have hu2 : 4 * KK (kk P) + 4 ≤ ‖u‖ ^ 2 := by
      rw [← cB_sq]
      have : 0 ≤ cB (kk P) := by unfold cB; positivity
      nlinarith
    obtain ⟨hz1, hz2⟩ := zv_far π (pp P) hp1 u hu2 t
    obtain ⟨a1, b1⟩ := answers_far (pp P) hp1 u hz1
    obtain ⟨a2, b2⟩ := answers_far (pp P) hp1 u hz2
    rw [a1, b1, a2, b2]

end Hiding

section Failure

variable {P}

variable (A : Algorithm (E P.d) (E P.d ⊕ (E P.d →L[ℝ] E P.d)) (E P.d) 2)

noncomputable def qry (s : A.State × (Fin 2 → ℕ) × Bool) : E P.d := toU P (A.query s.1).2

noncomputable def outU (s : A.State × (Fin 2 → ℕ) × Bool) : E P.d := toU P (A.output s.1)

noncomputable def upd (s : A.State × (Fin 2 → ℕ) × Bool) (r : E P.d × (E P.d →L[ℝ] E P.d)) :
    A.State × (Fin 2 → ℕ) × Bool :=
  if s.2.2 = true ∨ s.2.1 (A.query s.1).1 = 0 then (s.1, s.2.1, true)
  else (A.update s.1 (if (A.query s.1).1 = 0 then Sum.inl r.1 else Sum.inr r.2),
    Function.update s.2.1 (A.query s.1).1 (s.2.1 (A.query s.1).1 - 1), false)

noncomputable def ansF (π : Fin (kk P + 1) ↪ Fin P.d) (q : Fin 2 × E P.d) :
    E P.d ⊕ (E P.d →L[ℝ] E P.d) :=
  if q.1 = 0 then Sum.inl (hardF P π q.2) else Sum.inr (hardDF P π q.2)

lemma stepTwo_eq (π : Fin (kk P + 1) ↪ Fin P.d) :
    stepTwo A (ansF π) = fun s => upd A s (full π (qry A s)) := by
  funext s
  unfold stepTwo upd ansF qry full hardF hardDF
  split_ifs <;> rfl

lemma bud_sum (b : Fin 2 → ℕ) (hb : ∀ i, b i ≤ nb P) : b 0 + b 1 ≤ kk P := by
  have h0 := hb 0
  have h1 := hb 1
  unfold kk
  omega

lemma loss_ge (hv : spec.valid P) (π : Fin (kk P + 1) ↪ Fin P.d)
    (s : A.State × (Fin 2 → ℕ) × Bool)
    (hs : ‖outU A s‖ ≤ cB (kk P) → |outU A s (π (Fin.last (kk P)))| ≤ cθ (kk P)) :
    2 * P.ε ≤ ‖hardF P π (A.output s.1)‖ := by
  obtain ⟨_, _, hε, _, _, _, _⟩ := valid_facts hv
  have hp1 : 1 ≤ pp P := by have := pK_ge (kk P); unfold pp; omega
  have hg := grad_lower π (pp P) hp1 (outU A s) hs
  have hK := KK_pos (kk P)
  have hs1 : 0 < Real.sqrt (KK (kk P) + 1) := Real.sqrt_pos.mpr (by linarith)
  unfold hardF
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by unfold sα; positivity)]
  change 2 * P.ε ≤ sα P * ‖FF π (pp P) (outU A s)‖
  calc 2 * P.ε = sα P * (1 / (8 * Real.sqrt (KK (kk P) + 1))) := by
        unfold sα; field_simp; ring
    _ ≤ sα P * ‖FF π (pp P) (outU A s)‖ :=
        mul_le_mul_of_nonneg_left hg (by unfold sα; positivity)

lemma size_ok (hv : spec.valid P) :
    4 * (((kk P + 1 : ℕ) : ℝ) ^ 2 * (cB (kk P) ^ 2 / cθ (kk P) ^ 2)) + ((kk P + 1 : ℕ) : ℝ) ≤
      P.d := by
  obtain ⟨_, _, _, _, _, _, hd⟩ := valid_facts hv
  have h5 := K5_le hv
  have hK := KK_ge (kk P)
  have hc : ((kk P + 1 : ℕ) : ℝ) = KK (kk P) := by unfold KK; push_cast; ring
  have hθ : cθ (kk P) ^ 2 = 1 / (256 * KK (kk P) ^ 2) := by
    unfold cθ; rw [div_pow, one_pow, mul_pow]; norm_num
  rw [hc, cB_sq, hθ]
  set K := KK (kk P)
  have e : 4 * (K ^ 2 * ((4 * K + 4) / (1 / (256 * K ^ 2)))) = 1024 * K ^ 4 * (4 * K + 4) := by
    field_simp
    ring
  rw [e]
  have h1 : 1024 * K ^ 4 * (4 * K + 4) + K ≤ 8193 * K ^ 5 := by
    have : K ≤ K ^ 5 := by
      calc K = K ^ 1 := (pow_one K).symm
        _ ≤ K ^ 5 := pow_le_pow_right₀ hK (by norm_num)
    have : K ^ 4 ≤ K ^ 5 := pow_le_pow_right₀ hK (by norm_num)
    nlinarith [pow_pos (show (0 : ℝ) < K by linarith) 4]
  have h2 : 8193 * K ^ 5 ≤ 2 ^ 21 * (P.M * P.D) ^ ((10 : ℝ) / 3) := by
    have : (0 : ℝ) ≤ (P.M * P.D) ^ ((10 : ℝ) / 3) :=
      Real.rpow_nonneg (mul_pos (valid_facts hv).1 (valid_facts hv).2.1).le _
    nlinarith
  linarith

set_option maxHeartbeats 1600000 in
theorem hard_failure (hv : spec.valid P) (b : Fin 2 → ℕ) (hb : ∀ i, b i ≤ nb P) :
    ∃ π : Fin (kk P + 1) ↪ Fin P.d,
      ¬ (Integrable (fun ω : A.Seed × ((k : ℕ) → Unit) =>
            ‖hardF P π (execute (hardOracle P π) A b ω.1 ω.2)‖)
          ((A.law : Measure _).prod (Measure.dirac (fun _ => ())) : Measure _) ∧
        ∫ ω : A.Seed × ((k : ℕ) → Unit), ‖hardF P π (execute (hardOracle P π) A b ω.1 ω.2)‖
          ∂((A.law : Measure _).prod (Measure.dirac (fun _ => ()))) ≤ P.ε) := by
  obtain ⟨_, _, hε, _, _, _, _⟩ := valid_facts hv
  have hK := KK_pos (kk P)
  have hsz := size_ok hv
  have hθ0 : 0 < cθ (kk P) := by unfold cθ; positivity
  have hB0 : 0 ≤ cB (kk P) := by unfold cB; positivity
  set Dw : ℝ := 4 * ((kk P + 1 : ℕ) ^ 2 * (cB (kk P) ^ 2 / cθ (kk P) ^ 2)) with hDwd
  have hDw : 0 < Dw := by
    have : 0 < cB (kk P) := by unfold cB; positivity
    rw [hDwd]
    positivity
  have hsize : 4 * ((kk P + 1 : ℕ) ^ 2 * (cB (kk P) ^ 2 / cθ (kk P) ^ 2)) ≤ Dw :=
    le_of_eq hDwd.symm
  have hDs : Dw + (kk P + 1 : ℕ) ≤ P.d := hsz
  let Pm : ProbabilityMeasure (A.Seed × ((k : ℕ) → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ => ())), inferInstance⟩
  have hpart : ∀ π ρ : Fin (kk P + 1) ↪ Fin P.d, ∀ t : ℕ,
      (∀ j : Fin (kk P + 1), j.val ≤ t → π j = ρ j) → part π t = part ρ t :=
    fun π ρ t h => part_prefix π ρ t h
  have hfull : ∀ (π : Fin (kk P + 1) ↪ Fin P.d) (t : ℕ) (u : E P.d), t < kk P →
      (‖u‖ ≤ cB (kk P) → ∀ j : Fin (kk P + 1), t ≤ j.val → |u (π j)| ≤ cθ (kk P)) →
        full π u = part π t u :=
    fun π t u _ hu => full_eq_part π t u hu
  let loss : (Fin (kk P + 1) ↪ Fin P.d) → A.State × (Fin 2 → ℕ) × Bool → ℝ :=
    fun π s => ‖hardF P π (A.output s.1)‖
  have hnn : ∀ π s, 0 ≤ loss π s := fun _ _ => norm_nonneg _
  have hloss : ∀ (π : Fin (kk P + 1) ↪ Fin P.d) (s : A.State × (Fin 2 → ℕ) × Bool),
      (‖outU A s‖ ≤ cB (kk P) → |outU A s (π (Fin.last (kk P)))| ≤ cθ (kk P)) →
        2 * P.ε ≤ loss π s :=
    fun π s hs => loss_ge A hv π s hs
  let initial : A.Seed × ((k : ℕ) → Unit) → A.State × (Fin 2 → ℕ) × Bool :=
    fun ω => (A.initial ω.1, b, false)
  obtain ⟨π, hπ⟩ := LongTails.Proofs.SharpChainHiding.exists_failure (d := P.d) (k := kk P)
    (cB (kk P)) (cθ (kk P)) Dw P.ε hB0 hθ0 hDw hDs hsize hε full part hpart hfull loss hnn
    (qry A) (outU A) (upd A) hloss initial Pm
  refine ⟨π, ?_⟩
  have hexec : ∀ ω : A.Seed × ((k : ℕ) → Unit),
      execute (hardOracle P π) A b ω.1 ω.2 =
        A.output (((fun s => upd A s (full π (qry A s)))^[kk P]) (A.initial ω.1, b, false)).1 := by
    intro ω
    rw [← stepTwo_eq A π]
    exact execute_two (hardOracle P π) A b ω.1 ω.2 (ansF π) (fun _ _ => rfl) (kk P) (bud_sum b hb)
  exact not_success_congr _ _ _ P.ε
    (fun ω => congrArg (fun z => ‖hardF P π z‖) (hexec ω)) hπ

end Failure

end LongTails.Proofs.HsLowerBound
