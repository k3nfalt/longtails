import LongTails.Proofs.UntiedReverseFisherPhases
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.UntiedReverseFisherBranches

open LongTails.Proofs.UntiedReverseFisherDynamics
open LongTails.Proofs.UntiedReverseFisherPhases
open LongTails.Proofs.UntiedReverseFisherRidge
open LongTails.Proofs.SymmetricReverseFisherScalar
open LongTails.Proofs.SymmetricReverseFisherRidge
open LongTails.Proofs.SymmetricReverseFisherCoefficients
open LongTails.Proofs.SymmetricReverseFisherDynamics
open LongTails.Proofs.SymmetricReverseFisherTrajectory
open LongTails.Proofs.SymmetricReverseFisherGeometry

noncomputable def warmIterations (B : ℝ) : ℕ :=
  ⌈512 / 7 * Real.log (1 + B / centreThreshold)⌉₊

noncomputable def positiveIterations (a ε u0 B : ℝ) : ℕ :=
  warmIterations B + postIterations a ε ((29 / 32) ^ warmIterations B * u0)
    (1 / u0 * (16 / 15) ^ warmIterations B)

noncomputable def centreIterations (B ε : ℝ) : ℕ :=
  ⌈512 / 7 * Real.log (1 + 2 * B / Real.sqrt ε)⌉₊

noncomputable def smallIterations (ε : ℝ) : ℕ :=
  ⌈204800 / ε * Real.log (16 / ε)⌉₊

lemma contractionFactor_eq : contractionFactor = 1 - 7 / 512 := by
  unfold contractionFactor stepSize; norm_num

lemma centre_decay {B X : ℝ} (hB : 0 ≤ B) (hX : 0 < X) {k : ℕ}
    (hk : 512 / 7 * Real.log (1 + B / X) ≤ k) : contractionFactor ^ k * B ≤ X := by
  have hZ : 0 < 1 + B / X := by positivity
  have hn : Real.log (1 + B / X) / (7 / 512) ≤ (k : ℝ) := by
    calc Real.log (1 + B / X) / (7 / 512) = 512 / 7 * Real.log (1 + B / X) := by ring
      _ ≤ k := hk
  have h := pow_le_inv_of_log (t := 7 / 512) (by norm_num) (by norm_num) hZ hn
  rw [contractionFactor_eq]
  calc (1 - 7 / 512) ^ k * B ≤ 1 / (1 + B / X) * B := mul_le_mul_of_nonneg_right h hB
    _ = B * X / (X + B) := by field_simp
    _ ≤ X := by rw [div_le_iff₀ (by linarith)]; nlinarith

section Branches

variable {q : SParams} {e : SSpace q} {a : ℝ} {y : ℕ → SSpace q × SSpace q}

theorem centre_final (he : ‖e‖ = 1) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hy : ∀ k, y (k + 1) = pairStep (a • e) (y k)) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε)
    (hw0 : ‖(y 0).1‖ ≤ B) {k : ℕ} (hk : centreIterations B ε ≤ k) :
    ‖(y k).1‖ ^ 2 ≤ ε / 4 := by
  have hs := Real.sqrt_pos.mpr hε
  have h1 := traj_centre ha1 he ha hy k
  have hc0 : 0 ≤ 1 - 7 * stepSize / 16 := by unfold stepSize; norm_num
  have h2 : (1 - 7 * stepSize / 16) ^ k * ‖(y 0).1‖ ≤ (1 - 7 * stepSize / 16) ^ k * B :=
    mul_le_mul_of_nonneg_left hw0 (pow_nonneg hc0 k)
  have h3 := centre_decay (B := B) (X := Real.sqrt ε / 2) hB (by positivity)
    (k := k) (by
      have := Nat.le_ceil (512 / 7 * Real.log (1 + 2 * B / Real.sqrt ε))
      rw [show B / (Real.sqrt ε / 2) = 2 * B / Real.sqrt ε by field_simp]
      exact this.trans (by exact_mod_cast hk))
  unfold contractionFactor at h3
  have h4 : ‖(y k).1‖ ≤ Real.sqrt ε / 2 := by linarith
  have hsq := Real.sq_sqrt hε.le
  nlinarith [mul_le_mul h4 h4 (norm_nonneg _) (by positivity)]

theorem positive_branch (he : ‖e‖ = 1) (ha : 0 < a) (ha1 : a ≤ 1 / 2)
    (hy : ∀ k, y (k + 1) = pairStep (a • e) (y k)) {B u0 ε : ℝ} (hε : 0 < ε) (hu0 : 0 < u0)
    (hu01 : u0 ≤ 1) (hB : 0 ≤ B) (hv0 : ‖(y 0).2‖ = 1) (hw0 : ‖(y 0).1‖ ≤ B)
    (hU0 : u0 ≤ ⟪(y 0).2, e⟫) {k : ℕ} (hk : positiveIterations a ε u0 B ≤ k) :
    ‖(y k).2 - a • e‖ ^ 2 ≤ ε / 4 := by
  set T0 := warmIterations B with hT0
  unfold positiveIterations at hk
  rw [← hT0] at hk
  obtain ⟨i, rfl⟩ : ∃ i, k = T0 + i := ⟨k - T0, by omega⟩
  have hi : postIterations a ε ((29 / 32) ^ T0 * u0) (1 / u0 * (16 / 15) ^ T0) ≤ i := by omega
  set z : ℕ → SSpace q × SSpace q := fun j => y (T0 + j) with hzdef
  have hz : ∀ j, z (j + 1) = pairStep (a • e) (z j) := fun j => by
    simp only [hzdef, show T0 + (j + 1) = T0 + j + 1 by omega]; exact hy _
  have hball := traj_ball he ha.le hy (by rw [hv0]; linarith) T0
  have hθ : 0 < centreThreshold := by unfold centreThreshold; norm_num
  have hW : ∀ j, ‖(z j).1‖ ≤ centreThreshold * contractionFactor ^ j := by
    intro j
    have h1 := traj_centre ha1 he ha.le hy (T0 + j)
    have h2 := centre_decay (B := B) (X := centreThreshold) hB hθ (k := T0)
      (Nat.le_ceil _)
    have hc0 : 0 ≤ contractionFactor := by rw [contractionFactor_eq]; norm_num
    change ‖(y (T0 + j)).1‖ ≤ _
    unfold contractionFactor at *
    rw [pow_add] at h1
    calc ‖(y (T0 + j)).1‖ ≤ (1 - 7 * stepSize / 16) ^ T0 * (1 - 7 * stepSize / 16) ^ j *
          ‖(y 0).1‖ := h1
      _ ≤ (1 - 7 * stepSize / 16) ^ T0 * (1 - 7 * stepSize / 16) ^ j * B :=
          mul_le_mul_of_nonneg_left hw0 (by positivity)
      _ = (1 - 7 * stepSize / 16) ^ T0 * B * (1 - 7 * stepSize / 16) ^ j := by ring
      _ ≤ centreThreshold * (1 - 7 * stepSize / 16) ^ j :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
  have hA4 : ∀ k, 0 ≤ alpha ‖(y k).2‖ ∧ alpha ‖(y k).2‖ ≤ 4 :=
    fun k => ⟨(traj_alpha (y := y) k).1, (traj_alpha (y := y) k).2.2⟩
  have hcrude : ∀ k, 0 ≤ ⟪(y k).2, e⟫ → (1 - 1 / 64 * alpha ‖(y k).2‖ - 1 / 64 * (13 / 2 * a ^ 2)) *
      ⟪(y k).2, e⟫ ≤ ⟪(y (k + 1)).2, e⟫ := by
    intro k hk
    have h := traj_crude he ha.le ha1 hy k hk
    rw [stepSize_half] at h
    exact h
  have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith
  have hc0 : (0 : ℝ) ≤ 13 / 2 * a ^ 2 := by positivity
  have hc2 : 13 / 2 * a ^ 2 ≤ 2 := by nlinarith
  have hU0' : 0 < ⟪(y 0).2, e⟫ := lt_of_lt_of_le hu0 hU0
  have hlow := warm_lower (U := fun k => ⟪(y k).2, e⟫) (A := fun k => alpha ‖(y k).2‖)
    (by norm_num) le_rfl hc0 hc2 hA4 hcrude hU0'.le T0
  have hTnn : ∀ k, 0 ≤ ‖transverse e (y k).2‖ := fun k => norm_nonneg _
  have hTstep : ∀ k, ‖transverse e (y (k + 1)).2‖ =
      (1 - 1 / 64 * alpha ‖(y k).2‖) * ‖transverse e (y k).2‖ := by
    intro k
    have h := traj_transverse he ha.le hy k
    rw [stepSize_half] at h
    exact h
  have hTinit : ‖transverse e (y 0).2‖ ≤ 1 / u0 * ⟪(y 0).2, e⟫ := by
    have h := coordinate_norm e (y 0).2 he
    rw [hv0] at h
    have hT1 : ‖transverse e (y 0).2‖ ≤ 1 := by
      nlinarith [norm_nonneg (transverse e (y 0).2), sq_nonneg ⟪(y 0).2, e⟫]
    have : 1 ≤ 1 / u0 * ⟪(y 0).2, e⟫ := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hu0]; linarith
    linarith
  have hratio := warm_ratio (U := fun k => ⟪(y k).2, e⟫) (T := fun k => ‖transverse e (y k).2‖)
    (A := fun k => alpha ‖(y k).2‖) (by norm_num) le_rfl hc0 hc2 hA4 hcrude hTstep hTnn hU0'
    hTinit (by positivity) T0
  have hu1 : 0 < (29 / 32) ^ T0 * u0 := by positivity
  have hUz : (29 / 32) ^ T0 * u0 ≤ ucoord e z 0 := by
    change (29 / 32) ^ T0 * u0 ≤ ⟪(y (T0 + 0)).2, e⟫
    have : (1 - 6 * (1 / 64 : ℝ)) = 29 / 32 := by norm_num
    rw [this] at hlow
    calc (29 / 32) ^ T0 * u0 ≤ (29 / 32) ^ T0 * ⟪(y 0).2, e⟫ :=
          mul_le_mul_of_nonneg_left hU0 (by positivity)
      _ ≤ _ := hlow
  have hP : 1 ≤ 1 / u0 * (16 / 15) ^ T0 := by
    have h1 : 1 ≤ 1 / u0 := by rw [le_div_iff₀ hu0]; linarith
    have h2 : 1 ≤ (16 / 15 : ℝ) ^ T0 := one_le_pow₀ (by norm_num)
    nlinarith
  have hTz : tcoord e z 0 ≤ 1 / u0 * (16 / 15) ^ T0 * ucoord e z 0 := by
    change ‖transverse e (y (T0 + 0)).2‖ ≤ _ * ⟪(y (T0 + 0)).2, e⟫
    have : (1 / (1 - 4 * (1 / 64 : ℝ))) = 16 / 15 := by norm_num
    rw [this] at hratio
    simpa using hratio
  have h := post_branch he ha ha1 hz (by simpa [hzdef] using hball) hW hu1 hUz hP hTz hε hi
  simpa [hzdef] using h

lemma snd_norm_small (he : ‖e‖ = 1) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (x : SSpace q × SSpace q) :
    ‖(pairStep (a • e) x).2‖ ≤
      (1 - 1 / 64 * alpha ‖x.2‖ + 1 / 64 * (13 / 2 * a ^ 2)) * ‖x.2‖ := by
  have hl := (lambda_bounds (r := ‖x.2‖) (η := 1 / 64) (by norm_num) (by norm_num)).1
  have hd := ridge_difference_crude ha ha1 (a * ⟪x.1, e⟫) (a * ⟪x.2, e⟫)
  have hκ : |a * ⟪x.2, e⟫| ≤ a * ‖x.2‖ := by
    rw [abs_mul, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left (by simpa [he] using abs_real_inner_le_norm x.2 e) ha
  have hγ : stepSize = 1 / 32 := rfl
  have e1 : ⟪x.1 + x.2, a • e⟫ = a * ⟪x.1, e⟫ + a * ⟪x.2, e⟫ := by
    rw [inner_add_left, inner_axis, inner_axis]
  have e2 : ⟪x.1 - x.2, a • e⟫ = a * ⟪x.1, e⟫ - a * ⟪x.2, e⟫ := by
    rw [inner_sub_left, inner_axis, inner_axis]
  simp only [pairStep, norm_axis e he ha, e1, e2]
  rw [hγ]
  calc _ ≤ ‖(1 - 1 / 32 / 2 * alpha ‖x.2‖) • x.2‖ + ‖(1 / 32 / 4 * (ridgeForce a (a * ⟪x.1, e⟫ +
        a * ⟪x.2, e⟫) - ridgeForce a (a * ⟪x.1, e⟫ - a * ⟪x.2, e⟫))) • (a • e)‖ := norm_add_le _ _
    _ = (1 - 1 / 64 * alpha ‖x.2‖) * ‖x.2‖ + 1 / 128 * |ridgeForce a (a * ⟪x.1, e⟫ + a * ⟪x.2, e⟫) -
        ridgeForce a (a * ⟪x.1, e⟫ - a * ⟪x.2, e⟫)| * a := by
      rw [norm_smul, norm_smul, norm_axis e he ha, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), abs_mul]
      norm_num
    _ ≤ _ := by
      have := mul_le_mul_of_nonneg_left (hd.trans (mul_le_mul_of_nonneg_left hκ (by norm_num)))
        (show (0:ℝ) ≤ 1 / 128 * a by positivity)
      nlinarith

lemma small_capped {t t' ε a2 : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) (hε1 : ε ≤ 1) (_ha2 : 0 ≤ a2)
    (haε : a2 ≤ ε / 10 ^ 5)
    (hstep : t' ≤ (1 - 1 / 64 * min t 1 / 120 + 1 / 64 * (20 * a2)) * t) :
    t' ≤ max ((1 - ε / 204800) * t) (ε / 16) := by
  by_cases hbig : ε / 16 ≤ t
  · apply le_max_of_le_left
    have hmin : ε / 16 ≤ min t 1 := le_min hbig (by linarith)
    have : 1 - 1 / 64 * min t 1 / 120 + 1 / 64 * (20 * a2) ≤ 1 - ε / 204800 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this ht]
  · push Not at hbig
    apply le_max_of_le_right
    have ht1 : t ≤ 1 := by linarith
    rw [min_eq_left ht1] at hstep
    by_cases hs : 20 * a2 ≤ t / 120
    · have : 1 - 1 / 64 * t / 120 + 1 / 64 * (20 * a2) ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right this ht]
    · push Not at hs
      have ht2 : t ≤ 2400 * a2 := by linarith
      have : 1 - 1 / 64 * t / 120 + 1 / 64 * (20 * a2) ≤ 1 + 1 / 64 * (20 * a2) := by nlinarith
      have h2 := mul_le_mul_of_nonneg_right this ht
      have h3 : (1 + 1 / 64 * (20 * a2)) * t ≤ (1 + 1 / 64 * (20 * (ε / 10 ^ 5))) * (2400 * (ε / 10 ^ 5)) :=
        mul_le_mul (by nlinarith) (by linarith) ht (by positivity)
      nlinarith

theorem small_branch (he : ‖e‖ = 1) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hy : ∀ k, y (k + 1) = pairStep (a • e) (y k)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (haε : a ^ 2 ≤ ε / 10 ^ 5) (hv0 : ‖(y 0).2‖ = 1) {k : ℕ} (hk : smallIterations ε ≤ k) :
    ‖(y k).2 - a • e‖ ^ 2 ≤ ε / 4 := by
  have hstep : ∀ k, ‖(y (k + 1)).2‖ ^ 2 ≤ max ((1 - ε / 204800) * ‖(y k).2‖ ^ 2) (ε / 16) := by
    intro k
    apply small_capped (sq_nonneg _) hε hε1 (sq_nonneg a) haε
    rw [hy k]
    have h := snd_norm_small he ha ha1 (y k)
    have hA := traj_alpha (y := y) k
    have hl := (lambda_bounds (r := ‖(y k).2‖) (η := 1 / 64) (by norm_num) (by norm_num))
    have hα := alpha_lower (norm_nonneg (y k).2)
    have ha2 : a ^ 2 ≤ 1 / 4 := by nlinarith
    set l := 1 - 1 / 64 * alpha ‖(y k).2‖
    set x := 1 / 64 * (13 / 2 * a ^ 2)
    have hx : 0 ≤ x := by positivity
    have hx1 : x ≤ 1 / 32 := by simp only [x]; nlinarith
    have hsq : (l + x) ^ 2 ≤ l + 3 * x := by nlinarith [hl.1, hl.2]
    have h0 : 0 ≤ (l + x) * ‖(y k).2‖ := by nlinarith [hl.1, norm_nonneg (y k).2]
    have h2 : ‖(pairStep (a • e) (y k)).2‖ ^ 2 ≤ (l + 3 * x) * ‖(y k).2‖ ^ 2 := by
      calc _ ≤ ((l + x) * ‖(y k).2‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = (l + x) ^ 2 * ‖(y k).2‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have h3 : l + 3 * x ≤ 1 - 1 / 64 * min (‖(y k).2‖ ^ 2) 1 / 120 + 1 / 64 * (20 * a ^ 2) := by
      simp only [l, x]
      nlinarith
    exact h2.trans (mul_le_mul_of_nonneg_right h3 (sq_nonneg _))
  have hdecay := capped_decay (fun k => ‖(y k).2‖ ^ 2) (d := 1 - ε / 204800)
    (ell := ε / 16) (by nlinarith) (by nlinarith) (by positivity) hstep k
  have hZ : 0 < 16 / ε := by positivity
  have hn : Real.log (16 / ε) / (ε / 204800) ≤ (k : ℝ) := by
    have := Nat.le_ceil (204800 / ε * Real.log (16 / ε))
    calc Real.log (16 / ε) / (ε / 204800) = 204800 / ε * Real.log (16 / ε) := by field_simp
      _ ≤ _ := this
      _ ≤ k := by exact_mod_cast hk
  have hpow := pow_le_inv_of_log (t := ε / 204800) (by positivity) (by nlinarith) hZ hn
  have hv : ‖(y k).2‖ ^ 2 ≤ ε / 16 := by
    simp only [hv0, one_pow, mul_one] at hdecay
    refine hdecay.trans (max_le ?_ le_rfl)
    calc (1 - ε / 204800) ^ k ≤ 1 / (16 / ε) := hpow
      _ = ε / 16 := by field_simp
  have hae : ‖a • e‖ = a := norm_axis e he ha
  have htri : ‖(y k).2 - a • e‖ ≤ ‖(y k).2‖ + a := by
    have := norm_sub_le (y k).2 (a • e); rw [hae] at this; exact this
  have hn0 := norm_nonneg ((y k).2 - a • e)
  nlinarith [mul_le_mul htri htri hn0 (by positivity), sq_nonneg (‖(y k).2‖ - a)]

end Branches

end LongTails.Proofs.UntiedReverseFisherBranches
