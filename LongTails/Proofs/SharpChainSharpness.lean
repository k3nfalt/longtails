import LongTails.Proofs.SharpChainMargins

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.SharpChainSharpness

open MintyChainGeometry SharpChainGeometry SharpChainInstance SharpChainMargins

variable {d k : ℕ}

set_option hygiene false in
local notation "E" => EuclideanSpace ℝ (Fin d)

variable (μ0 D : ℝ) (π : Fin (k + 1) ↪ Fin d)

noncomputable def hardTarget : E := lift π (tgt μ0 D)

lemma hard_nonneg (hμ : 0 ≤ μ0) (u : E) : 0 ≤ hardValue μ0 D π u := by
  refine le_trans ?_ (radialVal_le_hard μ0 D π u)
  unfold radialVal
  exact mul_nonneg (by linarith) (norm_nonneg _)

lemma hardTarget_norm (hμ0 : μ0 ^ 2 < 1) (hD : 0 < D) : ‖hardTarget μ0 D π‖ = D := by
  have h := norm_lift_sq π (tgt μ0 D)
  rw [tgt_norm_sq μ0 D hμ0] at h
  unfold hardTarget
  exact (pow_left_inj₀ (norm_nonneg _) hD.le two_ne_zero).mp h

lemma hard_zero_of (hμ : 0 ≤ μ0) (hμ1 : μ0 ≤ 1 / 2) (hD : 0 < D) (z : E)
    (hz : ∀ j, z (π j) = tgt μ0 D j) (hn : ‖z‖ ≤ 3 * D) : hardValue μ0 D π z = 0 := by
  have hμ0 : μ0 ^ 2 < 1 := by nlinarith
  have hdev : dev μ0 D π z = fun _ => 0 := by
    funext j
    simp [dev, hz j]
  have hl : ‖lift π (fun _ : Fin (k + 1) => (0 : ℝ))‖ = 0 := by
    simpa using norm_lift_sq π (fun _ : Fin (k + 1) => (0 : ℝ))
  apply le_antisymm _ (hard_nonneg μ0 D π hμ z)
  rw [hardValue_eq]
  refine max_le ?_ (max_le ?_ ?_)
  · unfold coneVal
    linarith
  · obtain ⟨m, -, he, -⟩ := best_spec μ0 D π z k le_rfl
    rw [he]
    simp only [chainPiece, chainVal, chainRoot, hdev, hz m]
    have hmask : mask m.val (fun _ : Fin (k + 1) => (0 : ℝ)) = fun _ => 0 := by
      funext j
      simp [mask]
    rw [hmask]
    rw [hl, zero_pow two_ne_zero, zero_add, Real.sqrt_sq (gap_pos μ0 D hμ0 hD m.val).le]
    have hoff : 0 ≤ offset μ0 D k m.val := by
      unfold offset
      have := gap_pos μ0 D hμ0 hD k
      positivity
    unfold tgt tgtN
    split_ifs with hm
    · linarith
    · have hmk : m.val = k := by omega
      rw [hmk] at hoff ⊢
      have := gap_pos μ0 D hμ0 hD k
      nlinarith [mul_le_mul_of_nonneg_right (show μ0 ≤ 1 by linarith) this.le]
  · unfold radialVal
    rw [hdev, hl, mul_zero]

lemma hard_isMin_of (hμ : 0 ≤ μ0) (hμ1 : μ0 ≤ 1 / 2) (hD : 0 < D) (z : E)
    (hz : ∀ j, z (π j) = tgt μ0 D j) (hn : ‖z‖ ≤ 3 * D) :
    IsMinOn (hardValue μ0 D π) Set.univ z := by
  refine isMinOn_univ_iff.mpr fun y => ?_
  rw [hard_zero_of μ0 D π hμ hμ1 hD z hz hn]
  exact hard_nonneg μ0 D π hμ y

lemma hardTarget_apply (j : Fin (k + 1)) : hardTarget μ0 D π (π j) = tgt μ0 D j :=
  lift_apply π _ j

lemma hardTarget_isMin (hμ : 0 ≤ μ0) (hμ1 : μ0 ≤ 1 / 2) (hD : 0 < D) :
    IsMinOn (hardValue μ0 D π) Set.univ (hardTarget μ0 D π) := by
  have hμ0 : μ0 ^ 2 < 1 := by nlinarith
  apply hard_isMin_of μ0 D π hμ hμ1 hD _ (hardTarget_apply μ0 D π)
  rw [hardTarget_norm μ0 D π hμ0 hD]
  linarith

lemma hard_sharp (hμ : 0 < μ0) (hμ1 : μ0 ≤ 1 / 2) (hD : 0 < D) (u : E) :
    ∃ z, IsMinOn (hardValue μ0 D π) Set.univ z ∧
      μ0 / 16 * ‖u - z‖ ≤ hardValue μ0 D π u - hardValue μ0 D π z := by
  have hμ0 : μ0 ^ 2 < 1 := by nlinarith
  set N := ‖lift π (dev μ0 D π u)‖ with hN
  set xs := hardTarget μ0 D π
  set v := u - lift π (dev μ0 D π u) with hv
  set w := v - xs with hw
  have hvj : ∀ j, v (π j) = tgt μ0 D j := by
    intro j
    rw [hv, PiLp.sub_apply, lift_apply]
    simp [dev]
  have hwj : ∀ j, w (π j) = 0 := by
    intro j
    rw [hw, PiLp.sub_apply, hvj, hardTarget_apply, sub_self]
  have horth : ∀ c : ℝ, ⟪xs, c • w⟫ = 0 := by
    intro c
    rw [inner_smul_right]
    change c * ⟪lift π (tgt μ0 D), w⟫ = 0
    rw [inner_lift]
    simp [hwj]
  have hxs : ‖xs‖ = D := hardTarget_norm μ0 D π hμ0 hD
  have hnorm : ∀ c : ℝ, ‖xs + c • w‖ ^ 2 = D ^ 2 + c ^ 2 * ‖w‖ ^ 2 := by
    intro c
    rw [norm_add_sq_real, horth c, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hxs]
    ring
  have hvw : v = xs + (1 : ℝ) • w := by rw [one_smul, hw]; abel
  have huv : ‖u - v‖ = N := by rw [hv, sub_sub_cancel]
  have hR : μ0 / 2 * N ≤ hardValue μ0 D π u := radialVal_le_hard μ0 D π u
  have hC : 3 * ‖u‖ - 9 * D ≤ hardValue μ0 D π u := coneVal_le_hard μ0 D π u
  have hN0 : 0 ≤ N := norm_nonneg _
  have hs8 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have hs8l : (5 : ℝ) / 2 ≤ Real.sqrt 8 := by
    apply Real.le_sqrt_of_sq_le
    norm_num
  have hs8p : 0 ≤ Real.sqrt 8 := Real.sqrt_nonneg _
  by_cases hsmall : ‖w‖ ≤ Real.sqrt 8 * D
  · refine ⟨v, hard_isMin_of μ0 D π hμ.le hμ1 hD v hvj ?_, ?_⟩
    · have h := hnorm 1
      rw [← hvw] at h
      have h2 : ‖v‖ ^ 2 ≤ (3 * D) ^ 2 := by
        rw [h]
        have := pow_le_pow_left₀ (norm_nonneg _) hsmall 2
        rw [mul_pow, hs8] at this
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
    · rw [hard_zero_of μ0 D π hμ.le hμ1 hD v hvj ?_, sub_zero, huv]
      · nlinarith [mul_nonneg hμ.le hN0]
      · have h := hnorm 1
        rw [← hvw] at h
        have h2 : ‖v‖ ^ 2 ≤ (3 * D) ^ 2 := by
          rw [h]
          have := pow_le_pow_left₀ (norm_nonneg _) hsmall 2
          rw [mul_pow, hs8] at this
          nlinarith
        exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
  · have hwpos : 0 < ‖w‖ := lt_of_le_of_lt (by positivity) (not_le.mp hsmall)
    set c := Real.sqrt 8 * D / ‖w‖ with hc
    set z := xs + c • w
    have hzj : ∀ j, z (π j) = tgt μ0 D j := by
      intro j
      simp only [z, xs, PiLp.add_apply, PiLp.smul_apply, hwj, add_zero, hardTarget_apply,
        smul_eq_mul, mul_zero]
    have hzn : ‖z‖ ≤ 3 * D := by
      have h := hnorm c
      have hcw : c ^ 2 * ‖w‖ ^ 2 = 8 * D ^ 2 := by
        rw [hc, div_pow, mul_pow, hs8]
        field_simp
      have h2 : ‖z‖ ^ 2 ≤ (3 * D) ^ 2 := by
        change ‖xs + c • w‖ ^ 2 ≤ _
        rw [h, hcw]
        nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
    refine ⟨z, hard_isMin_of μ0 D π hμ.le hμ1 hD z hzj hzn, ?_⟩
    rw [hard_zero_of μ0 D π hμ.le hμ1 hD z hzj hzn, sub_zero]
    have hvz : v - z = (1 - c) • w := by
      rw [hvw]
      simp only [z, one_smul, sub_smul]
      abel
    have hc1 : c ≤ 1 := by
      rw [hc, div_le_one hwpos]
      exact (not_le.mp hsmall).le
    have hdist : ‖u - z‖ ≤ N + (‖w‖ - Real.sqrt 8 * D) := by
      have e : u - z = (u - v) + (v - z) := by abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [huv, hvz, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc1)]
      have : (1 - c) * ‖w‖ = ‖w‖ - Real.sqrt 8 * D := by
        rw [hc, sub_mul, one_mul, div_mul_cancel₀ _ hwpos.ne']
      linarith
    have hv2 : ‖v‖ ^ 2 = D ^ 2 + ‖w‖ ^ 2 := by
      have h := hnorm 1
      rw [← hvw, one_pow, one_mul] at h
      exact h
    have hcs : D + Real.sqrt 8 * ‖w‖ ≤ 3 * ‖v‖ := by
      have h1 : (D + Real.sqrt 8 * ‖w‖) ^ 2 ≤ (3 * ‖v‖) ^ 2 := by
        rw [mul_pow, hv2]
        nlinarith [sq_nonneg (Real.sqrt 8 * D - ‖w‖)]
      exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h1
    have huvn : ‖v‖ - N ≤ ‖u‖ := by
      have := norm_sub_norm_le v u
      rw [norm_sub_rev v u, huv] at this
      linarith
    have hC' : Real.sqrt 8 * (‖w‖ - Real.sqrt 8 * D) - 3 * N ≤ hardValue μ0 D π u := by
      have e : Real.sqrt 8 * (‖w‖ - Real.sqrt 8 * D) = Real.sqrt 8 * ‖w‖ - 8 * D := by
        rw [mul_sub, ← mul_assoc, ← sq, hs8]
      rw [e]
      linarith
    set s := ‖w‖ - Real.sqrt 8 * D
    have hs0 : 0 ≤ s := by linarith
    have hcomb : (1 - μ0 / 40) * (μ0 / 2 * N) + μ0 / 40 * (Real.sqrt 8 * s - 3 * N) ≤
        hardValue μ0 D π u := by
      nlinarith [mul_le_mul_of_nonneg_left hR (show (0 : ℝ) ≤ 1 - μ0 / 40 by linarith),
        mul_le_mul_of_nonneg_left hC' (show (0 : ℝ) ≤ μ0 / 40 by linarith)]
    have k1 : μ0 / 16 * N ≤ (1 - μ0 / 40) * (μ0 / 2 * N) - μ0 / 40 * (3 * N) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hμ1) (mul_nonneg hμ.le hN0), mul_nonneg hμ.le hN0]
    have k2 : μ0 / 16 * s ≤ μ0 / 40 * (Real.sqrt 8 * s) := by
      have h := mul_le_mul_of_nonneg_right hs8l (mul_nonneg hμ.le hs0)
      linarith only [h]
    have hd16 : μ0 / 16 * ‖u - z‖ ≤ μ0 / 16 * (N + s) :=
      mul_le_mul_of_nonneg_left hdist (by linarith)
    linarith only [hcomb, k1, k2, hd16]

end LongTails.Proofs.SharpChainSharpness
