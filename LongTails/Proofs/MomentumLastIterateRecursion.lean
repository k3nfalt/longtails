import LongTails.Proofs.MomentumLastIterateWeights

open Finset

namespace OracleTemplate.MomentumConvex

lemma core_step {γ κ G τ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) (hτ : 1 ≤ τ) {Dn Dc Bc Fn Fc ac ap : ℝ}
    (hI : Dn ≤ Bc - 2 * (γ * τ) * ((1 + κ * τ / (τ + 1 + κ)) * ac - κ * τ / (τ + 1 + κ) * ap - Fn) +
      (γ * τ) ^ 2 * G ^ 2)
    (hII : wt γ κ τ * Bc ≤ wt γ κ (τ + 1) * Dc +
      (wt γ κ τ - wt γ κ (τ + 1)) * ((κ * γ * τ) ^ 2 * G ^ 2))
    (hIII : wt γ κ τ * Fn ≤ wt γ κ (τ + 1) * Fc + (wt γ κ τ - wt γ κ (τ + 1)) * ac) :
    wt γ κ τ * Dn + 2 * lam κ (τ - 1) * Fn ≤
      wt γ κ (τ + 1) * Dc + 2 * lam κ τ * Fc + 2 * nu κ τ * ap +
        (2 * γ + 4 * κ ^ 2 * γ / (τ + 1)) * G ^ 2 -
        2 * (lam κ τ + nu κ τ - lam κ (τ - 1)) * ac := by
  have h0 : 0 < τ := by linarith
  have hw : 0 < wt γ κ τ := wt_pos hγ hκ h0
  have hr := rho_eq hγ hκ h0
  have hn := nu_eq hκ h0
  have hl := lam_eq hγ hκ h0
  have hs := sig_eq hγ hκ h0
  have hp := lam_pred_add_rho hκ hτ
  have hG : 0 ≤ G ^ 2 := sq_nonneg G
  have hj := mul_le_mul_of_nonneg_right (jensen_le hγ hκ hτ) hG
  have hno := mul_le_mul_of_nonneg_right (noise_le hγ hκ h0) hG
  have hc : 0 ≤ γ * τ * (τ + 1) / 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left hI hw.le
  have h3 := mul_le_mul_of_nonneg_left hIII hc
  set w := wt γ κ τ
  set w' := wt γ κ (τ + 1)
  set r := rho κ τ
  set n := nu κ τ
  set l := lam κ τ
  set l' := lam κ (τ - 1)
  set s := sig κ τ
  set q := κ * τ / (τ + 1 + κ)
  have e1 : w * (Bc - 2 * (γ * τ) * ((1 + q) * ac - q * ap - Fn) + (γ * τ) ^ 2 * G ^ 2) =
      w * Bc - 2 * r * ac - 2 * n * ac + 2 * n * ap + 2 * r * Fn + w * (γ * τ) ^ 2 * G ^ 2 := by
    rw [← hn, ← hr]; ring
  have e3l : γ * τ * (τ + 1) / 2 * (w * Fn) = s * Fn := by rw [← hs]; ring
  have e3r : γ * τ * (τ + 1) / 2 * (w' * Fc + (w - w') * ac) = l * Fc + (s - l) * ac := by
    rw [← hs, ← hl]; ring
  rw [e1] at h1
  rw [e3l, e3r] at h3
  have e4 : (w - w') * (κ * γ * τ) ^ 2 * G ^ 2 = (w - w') * ((κ * γ * τ) ^ 2 * G ^ 2) := by ring
  rw [e4] at hj
  have hr' : r = s - l' := by linarith
  rw [hr'] at h1
  nlinarith [h1, h3, hII, hj, hno]

lemma potential_bound {γ κ G : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) {T : ℕ} (hT : 1 ≤ T)
    (a D B F : ℕ → ℝ) (ha : ∀ t, 0 ≤ a t) (hD : ∀ t, 0 ≤ D t) (hF0 : F 0 = 0)
    (hI : ∀ t, t < T → D (t + 1) ≤ B t -
      2 * (γ * ((T : ℝ) - t)) * ((1 + κ * ((T : ℝ) - t) / ((T : ℝ) - t + 1 + κ)) * a t -
        κ * ((T : ℝ) - t) / ((T : ℝ) - t + 1 + κ) * a (t - 1) - F (t + 1)) +
      (γ * ((T : ℝ) - t)) ^ 2 * G ^ 2)
    (hII : ∀ t, t < T → wt γ κ ((T : ℝ) - t) * B t ≤ wt γ κ ((T : ℝ) - t + 1) * D t +
      (wt γ κ ((T : ℝ) - t) - wt γ κ ((T : ℝ) - t + 1)) * ((κ * γ * ((T : ℝ) - t)) ^ 2 * G ^ 2))
    (hIII : ∀ t, t < T → wt γ κ ((T : ℝ) - t) * F (t + 1) ≤ wt γ κ ((T : ℝ) - t + 1) * F t +
      (wt γ κ ((T : ℝ) - t) - wt γ κ ((T : ℝ) - t + 1)) * a t) :
    2 * uu κ 1 * a (T - 1) ≤ wt γ κ ((T : ℝ) + 1) * D 0 + 2 * nu κ T * a 0 +
      ∑ t ∈ range T, (2 * γ + 4 * κ ^ 2 * γ / ((T : ℝ) - t + 1)) * G ^ 2 := by
  have key : ∀ t, t < T →
      wt γ κ ((T : ℝ) - t + 1) * D t + 2 * lam κ ((T : ℝ) - t) * F t +
        2 * nu κ ((T : ℝ) - t) * a (t - 1) ≤
      wt γ κ ((T : ℝ) + 1) * D 0 + 2 * nu κ T * a 0 +
        ∑ s ∈ range t, (2 * γ + 4 * κ ^ 2 * γ / ((T : ℝ) - s + 1)) * G ^ 2 := by
    intro t
    induction t with
    | zero =>
      intro _
      simp [hF0]
    | succ t ih =>
      intro ht
      have ht' : t < T := Nat.lt_of_succ_lt ht
      have hτ : (2 : ℝ) ≤ (T : ℝ) - t := by
        have : ((t + 1 + 1 : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
        push_cast at this; linarith
      have hstep := core_step (G := G) hγ hκ (by linarith : (1 : ℝ) ≤ (T : ℝ) - t)
        (hI t ht') (hII t ht') (hIII t ht')
      have hmono := uu_mono hκ hτ
      unfold uu at hmono
      have hcast : ((T : ℝ) - ((t + 1 : ℕ) : ℝ)) = (T : ℝ) - t - 1 := by push_cast; ring
      have hcast' : ((T : ℝ) - ((t + 1 : ℕ) : ℝ)) + 1 = (T : ℝ) - t := by push_cast; ring
      rw [sum_range_succ, hcast', hcast, Nat.add_sub_cancel]
      have hpos : 0 ≤ (lam κ ((T : ℝ) - t) + nu κ ((T : ℝ) - t) - lam κ ((T : ℝ) - t - 1) -
          nu κ ((T : ℝ) - t - 1)) * a t := mul_nonneg (by linarith) (ha t)
      have ih' := ih ht'
      nlinarith [hstep, ih', hpos]
  obtain ⟨m, rfl⟩ : ∃ m, T = m + 1 := ⟨T - 1, by omega⟩
  have hlast := key m (Nat.lt_succ_self m)
  have hc1 : ((m + 1 : ℕ) : ℝ) - (m : ℝ) = 1 := by push_cast; ring
  have hstep := core_step (G := G) hγ hκ (le_refl (1 : ℝ))
    (by simpa [hc1] using hI m (Nat.lt_succ_self m))
    (by simpa [hc1] using hII m (Nat.lt_succ_self m))
    (by simpa [hc1] using hIII m (Nat.lt_succ_self m))
  rw [hc1] at hlast
  have hl0 : lam κ ((1 : ℝ) - 1) = 0 := by simp [lam]
  rw [hl0] at hstep
  have hw : 0 < wt γ κ 1 := wt_pos hγ hκ one_pos
  have hDT := mul_nonneg hw.le (hD (m + 1))
  rw [sum_range_succ, hc1, Nat.add_sub_cancel]
  unfold uu
  have h11 : (1 : ℝ) + 1 = 2 := by norm_num
  rw [h11] at hstep hlast ⊢
  nlinarith [hstep, hlast, hDT]

lemma sum_inv_le_log (T : ℕ) : ∑ j ∈ range T, 1 / ((j : ℝ) + 2) ≤ Real.log ((T : ℝ) + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ]
    have hx : (0 : ℝ) < ((T : ℝ) + 2) / ((T : ℝ) + 1) := by positivity
    have h := Real.one_sub_inv_le_log_of_pos hx
    rw [Real.log_div (by positivity) (by positivity)] at h
    have e : 1 - (((T : ℝ) + 2) / ((T : ℝ) + 1))⁻¹ = 1 / ((T : ℝ) + 2) := by
      field_simp; ring
    rw [e] at h
    push_cast
    have e2 : (T : ℝ) + 1 + 1 = (T : ℝ) + 2 := by ring
    rw [e2]
    linarith

lemma sum_reflect_inv (T : ℕ) :
    ∑ t ∈ range T, 1 / ((T : ℝ) - t + 1) = ∑ j ∈ range T, 1 / ((j : ℝ) + 2) := by
  rw [← sum_range_reflect (fun j : ℕ => 1 / ((j : ℝ) + 2)) T]
  refine sum_congr rfl (fun t ht => ?_)
  have ht' : t < T := mem_range.mp ht
  have h1 : t ≤ T - 1 := by omega
  have h2 : 1 ≤ T := by omega
  rw [Nat.cast_sub h1, Nat.cast_sub h2]
  congr 1
  push_cast
  ring

lemma error_sum_le {γ κ G : ℝ} (hγ : 0 ≤ γ) (T : ℕ) :
    ∑ t ∈ range T, (2 * γ + 4 * κ ^ 2 * γ / ((T : ℝ) - t + 1)) * G ^ 2 ≤
      (2 * γ * T + 4 * κ ^ 2 * γ * Real.log ((T : ℝ) + 1)) * G ^ 2 := by
  have h1 : ∑ t ∈ range T, (2 * γ + 4 * κ ^ 2 * γ / ((T : ℝ) - t + 1)) * G ^ 2 =
      (2 * γ * T + 4 * κ ^ 2 * γ * ∑ t ∈ range T, 1 / ((T : ℝ) - t + 1)) * G ^ 2 := by
    rw [← sum_mul, sum_add_distrib, mul_sum]
    simp only [sum_const, card_range, nsmul_eq_mul]
    congr 2
    · ring
    · refine sum_congr rfl (fun t _ => ?_); ring
  rw [h1, sum_reflect_inv]
  have h2 := sum_inv_le_log T
  have h3 : 0 ≤ 4 * κ ^ 2 * γ := by positivity
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  have h5 : 0 ≤ G ^ 2 := sq_nonneg G
  nlinarith [h4, h5]

lemma final_bound {G R κ γ a a0 D0 Tr : ℝ} (hG : 0 < G) (hR : 0 < R) (hκ : 0 ≤ κ) (hTr : 0 ≤ Tr)
    (hγ : γ = R / (G * (Tr + 1) * Real.sqrt (Tr + 1)))
    (ha : 0 ≤ a) (ha0 : 0 ≤ a0) (ha0' : a0 ≤ G * R) (hD0' : D0 ≤ R ^ 2)
    (h : 2 * uu κ 1 * a ≤ wt γ κ (Tr + 1) * D0 + 2 * nu κ Tr * a0 +
      (2 * γ * Tr + 4 * κ ^ 2 * γ * Real.log (Tr + 1)) * G ^ 2) :
    a ≤ G * R / Real.sqrt (Tr + 1) *
      (4 + 4 * κ / Real.sqrt (Tr + 1) + 4 * κ ^ 2 * Real.log (Tr + 1) / (Tr + 1)) := by
  set M : ℝ := Tr + 1 with hM
  have hMpos : 0 < M := by positivity
  set s := Real.sqrt M with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hMpos
  have hss : s * s = M := Real.mul_self_sqrt hMpos.le
  have hγpos : 0 < γ := by rw [hγ]; positivity
  have hlog : 0 ≤ Real.log M := Real.log_nonneg (by rw [hM]; linarith)
  have hu := uu_one hκ
  have h1 : a ≤ 2 * uu κ 1 * a := by nlinarith
  have h2 : wt γ κ M * D0 ≤ 2 / (γ * M ^ 2) * R ^ 2 := by
    have := wt_top_le hγpos hκ hMpos
    have hw := (wt_pos hγpos hκ hMpos).le
    calc wt γ κ M * D0 ≤ wt γ κ M * R ^ 2 := mul_le_mul_of_nonneg_left hD0' hw
      _ ≤ 2 / (γ * M ^ 2) * R ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg R)
  have h3 : 2 * nu κ Tr * a0 ≤ 2 * (2 * κ / M) * (G * R) := by
    have hn := nu_le hκ hTr
    have hn0 := nu_nonneg hκ hTr
    have : nu κ Tr * a0 ≤ 2 * κ / M * (G * R) :=
      mul_le_mul hn ha0' ha0 (by positivity)
    linarith
  have e1 : 2 / (γ * M ^ 2) * R ^ 2 = G * R / s * 2 := by
    rw [hγ, ← hss]; field_simp
  have e2 : 2 * (2 * κ / M) * (G * R) = G * R / s * (4 * κ / s) := by
    rw [← hss]; field_simp; ring
  have e3 : (2 * γ * Tr + 4 * κ ^ 2 * γ * Real.log M) * G ^ 2 =
      G * R / s * (2 * (Tr / M) + 4 * κ ^ 2 * Real.log M / M) := by
    rw [hγ]; field_simp
  have hTM : Tr / M ≤ 1 := by
    rw [div_le_one hMpos, hM]; linarith
  have hGRs : 0 ≤ G * R / s := by positivity
  have h4 : G * R / s * (2 * (Tr / M) + 4 * κ ^ 2 * Real.log M / M) ≤
      G * R / s * (2 + 4 * κ ^ 2 * Real.log M / M) :=
    mul_le_mul_of_nonneg_left (by linarith) hGRs
  rw [e3] at h
  calc a ≤ 2 * uu κ 1 * a := h1
    _ ≤ G * R / s * 2 + G * R / s * (4 * κ / s) + G * R / s * (2 + 4 * κ ^ 2 * Real.log M / M) := by
        linarith
    _ = G * R / s * (4 + 4 * κ / s + 4 * κ ^ 2 * Real.log M / M) := by ring

lemma kappa_log_le {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 4 * κ ^ 2 * (1 + Real.log (1 + κ)) ≤ M) :
    κ ^ 2 * Real.log M ≤ M := by
  have hl1 : 0 ≤ Real.log (1 + κ) := Real.log_nonneg (by linarith)
  rcases eq_or_lt_of_le hκ with h0 | hpos
  · rw [← h0] at hM ⊢
    simpa using hM
  · have hκ2 : 0 < κ ^ 2 := by positivity
    set θ := M / κ ^ 2 with hθ
    have hMθ : M = θ * κ ^ 2 := by rw [hθ]; field_simp
    have hθ4 : 4 * (1 + Real.log (1 + κ)) ≤ θ := by
      rw [hθ, le_div_iff₀ hκ2]; linarith
    have hθpos : 0 < θ := by linarith
    have hsq : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθpos
    have h1 : Real.log θ ≤ θ / 2 := by
      have h := Real.log_le_sub_one_of_pos hsq
      rw [Real.log_sqrt hθpos.le] at h
      have hss : Real.sqrt θ * Real.sqrt θ = θ := Real.mul_self_sqrt hθpos.le
      nlinarith [sq_nonneg (Real.sqrt θ - 2)]
    have h2 : Real.log κ ≤ Real.log (1 + κ) := Real.log_le_log hpos (by linarith)
    have h3 : Real.log M = Real.log θ + 2 * Real.log κ := by
      rw [hMθ, Real.log_mul hθpos.ne' hκ2.ne', Real.log_pow]; push_cast; ring
    have h4 : Real.log M ≤ θ := by rw [h3]; linarith
    calc κ ^ 2 * Real.log M ≤ κ ^ 2 * θ := mul_le_mul_of_nonneg_left h4 hκ2.le
      _ = M := by rw [hMθ]; ring

lemma budget_bound {G R κ ε M : ℝ} (hG : 0 < G) (hR : 0 < R) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hM1 : 100 * G ^ 2 * R ^ 2 / ε ^ 2 ≤ M) (hM2 : 4 * κ ^ 2 * (1 + Real.log (1 + κ)) ≤ M) :
    G * R / Real.sqrt M * (4 + 4 * κ / Real.sqrt M + 4 * κ ^ 2 * Real.log M / M) ≤ ε := by
  have hA : 0 < 100 * G ^ 2 * R ^ 2 / ε ^ 2 := by positivity
  have hMpos : 0 < M := lt_of_lt_of_le hA hM1
  set s := Real.sqrt M with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hMpos
  have hss : s * s = M := Real.mul_self_sqrt hMpos.le
  have hl1 : 0 ≤ Real.log (1 + κ) := Real.log_nonneg (by linarith)
  have h1 : 10 * G * R / ε ≤ s := by
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    calc (10 * G * R / ε) ^ 2 = 100 * G ^ 2 * R ^ 2 / ε ^ 2 := by ring
      _ ≤ M := hM1
  have h2 : G * R / s ≤ ε / 10 := by
    rw [div_le_iff₀ hspos]
    have := (div_le_iff₀ hε).mp h1
    linarith
  have h3 : 2 * κ ≤ s := by
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg (sq_nonneg κ) hl1]
  have h4 : 4 * κ / s ≤ 2 := by
    rw [div_le_iff₀ hspos]; linarith
  have h5 : 4 * κ ^ 2 * Real.log M / M ≤ 4 := by
    rw [div_le_iff₀ hMpos]
    have := kappa_log_le hκ hM2
    linarith
  have h6 : 0 ≤ 4 * κ / s := by positivity
  have h7 : 0 ≤ G * R / s := by positivity
  have h8 : 4 + 4 * κ / s + 4 * κ ^ 2 * Real.log M / M ≤ 10 := by linarith
  calc G * R / s * (4 + 4 * κ / s + 4 * κ ^ 2 * Real.log M / M) ≤ G * R / s * 10 :=
        mul_le_mul_of_nonneg_left h8 h7
    _ ≤ ε / 10 * 10 := mul_le_mul_of_nonneg_right h2 (by norm_num)
    _ = ε := by ring

end OracleTemplate.MomentumConvex
