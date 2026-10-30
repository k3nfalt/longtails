import LongTails.Proofs.ScheduleBlockGeneric
import LongTails.Proofs.ScheduleCoordinateBoundsExtra
import Mathlib.Analysis.Complex.ExponentialBounds

namespace OracleTemplate.ScheduleBlock

open Finset

structure ScheduleFacts (η : ℕ → ℝ) (n : ℕ) (L K : ℝ) : Prop where
  hL : 0 < L
  hK : 1 ≤ K
  eta_nonneg : ∀ j, 0 ≤ η j
  eta_pos : ∀ j < n, 0 < η j
  eta_le : ∀ j < n, η j ≤ K / L
  win_le : ∀ lam, 0 ≤ lam → lam ≤ L → ∀ s t, s ≤ t → t ≤ n → |win η lam s t| ≤ K
  pre_le : ∀ lam, 0 ≤ lam → lam ≤ L → ∀ t ≤ n, |pr η lam t| ≤ 1
  fin : ∀ lam, 0 ≤ lam → lam ≤ L → (1 + 2 * lam * ssum η n) * pr η lam n ^ 2 ≤ 1

def wsum (η : ℕ → ℝ) (ξ : ℕ → ℝ) (t : ℕ) : ℝ := ∑ s ∈ range t, η s * |ξ s|

def usum (ξ : ℕ → ℝ) (t : ℕ) : ℝ := ∑ s ∈ range t, |ξ s|

variable {η : ℕ → ℝ} {n : ℕ} {L K : ℝ}

lemma wsum_nonneg (F : ScheduleFacts η n L K) (ξ : ℕ → ℝ) (t : ℕ) : 0 ≤ wsum η ξ t :=
  Finset.sum_nonneg fun s _ => mul_nonneg (F.eta_nonneg s) (abs_nonneg _)

lemma usum_nonneg (ξ : ℕ → ℝ) (t : ℕ) : 0 ≤ usum ξ t :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma ssum_pos (F : ScheduleFacts η n L K) {t : ℕ} (ht1 : 1 ≤ t) (htn : t ≤ n) : 0 < ssum η t := by
  unfold ssum
  calc (0:ℝ) < η 0 := F.eta_pos 0 (by omega)
    _ ≤ ∑ s ∈ range t, η s := Finset.single_le_sum (fun s _ => F.eta_nonneg s)
        (Finset.mem_range.mpr (by omega))

lemma ssum_mono (F : ScheduleFacts η n L K) {t t' : ℕ} (h : t ≤ t') : ssum η t ≤ ssum η t' := by
  unfold ssum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (fun s _ _ => F.eta_nonneg s)

lemma errResp_pos_bound (F : ScheduleFacts η n L K) {lam : ℝ} (h0 : 0 ≤ lam) (hL : lam ≤ L)
    (ξ : ℕ → ℝ) {t : ℕ} (ht : t ≤ n) : |errResp η lam ξ t| ≤ K * wsum η ξ t :=
  errResp_pos_le F.eta_nonneg ξ t fun s hs => F.win_le lam h0 hL (s + 1) t hs ht

lemma lam_errResp_bound (F : ScheduleFacts η n L K) {lam : ℝ} (h0 : 0 ≤ lam) (hL : lam ≤ L)
    (ξ : ℕ → ℝ) {t : ℕ} (ht : t ≤ n) : |lam * errResp η lam ξ t| ≤ 2 * K * usum ξ t :=
  lam_errResp_le ξ t fun s hs => F.win_le lam h0 hL s t hs ht

lemma resp_zero (η : ℕ → ℝ) (t : ℕ) : resp η 0 t = ssum η t := by
  unfold resp ssum win
  simp

lemma pr_zero (η : ℕ → ℝ) (t : ℕ) : pr η 0 t = 1 := by
  unfold pr win
  simp

lemma pr_neg_le_three (F : ScheduleFacts η n L K) {m : ℝ} (hm : 0 ≤ m) (t : ℕ)
    (hmS : m * ssum η t < 1) : pr η (-m) t ≤ 3 := by
  have h := pr_neg_le_exp F.eta_nonneg hm t
  have h2 : Real.exp (m * ssum η t) ≤ Real.exp 1 := Real.exp_le_exp.mpr hmS.le
  have h3 := Real.exp_one_lt_d9
  linarith

lemma neg_U1_at (F : ScheduleFacts η n L K) {m γ : ℝ} (hm : 0 < m) (ξ : ℕ → ℝ) {t : ℕ}
    (ht1 : 1 ≤ t) (htn : t ≤ n) :
    γ * traj η (-m) γ ξ t + -m * traj η (-m) γ ξ t ^ 2 / 2 ≤
      -(traj η (-m) γ ξ t ^ 2 / (21 * ssum η t)) + 1181 * wsum η ξ t ^ 2 / ssum η t +
        16 * m * wsum η ξ t ^ 2 := by
  have hS := ssum_pos F ht1 htn
  obtain ⟨hRS, hRPS⟩ := resp_neg_bounds F.eta_nonneg hm.le t
  have hRP : m * resp η (-m) t = pr η (-m) t - 1 := by
    have := lam_mul_resp η (-m) t; linarith
  have h := neg_coord_U1 (γ := γ) hm hS (wsum_nonneg F ξ t) hRP hRS (by linarith [hRPS])
    (pr_neg_ge F.eta_nonneg hm.le t) (pr_neg_le_three F hm.le t)
    (errResp_neg_le F.eta_nonneg hm.le ξ t)
  rw [traj_eq]
  linarith

lemma neg_U2_at (F : ScheduleFacts η n L K) {m γ : ℝ} (hm : 0 < m) (ξ : ℕ → ℝ) {t : ℕ}
    (ht1 : 1 ≤ t) (htn : t ≤ n) :
    γ * traj η (-m) γ ξ t + -m * traj η (-m) γ ξ t ^ 2 / 2 ≤
      -(ssum η t * γ ^ 2 / 2) + 1188 * wsum η ξ t ^ 2 / ssum η t + 15 * m * wsum η ξ t ^ 2 +
        15 * ssum η t * m ^ 2 * wsum η ξ t ^ 2 := by
  have hS := ssum_pos F ht1 htn
  obtain ⟨hRS, hRPS⟩ := resp_neg_bounds F.eta_nonneg hm.le t
  have hRP : m * resp η (-m) t = pr η (-m) t - 1 := by
    have := lam_mul_resp η (-m) t; linarith
  have h := neg_coord_U2 (γ := γ) hm hS (wsum_nonneg F ξ t) hRP hRS (by linarith [hRPS])
    (pr_neg_ge F.eta_nonneg hm.le t) (pr_neg_le_three F hm.le t)
    (errResp_neg_le F.eta_nonneg hm.le ξ t)
  rw [traj_eq]
  linarith

lemma pos_U5_at (F : ScheduleFacts η n L K) {lam γ : ℝ} (h0 : 0 ≤ lam) (hL : lam ≤ L)
    (ξ : ℕ → ℝ) {t : ℕ} (htn : t ≤ n) :
    γ * traj η lam γ ξ t + lam * traj η lam γ ξ t ^ 2 / 2 ≤
      K * |γ| * wsum η ξ t + L * K ^ 2 * wsum η ξ t ^ 2 / 2 := by
  have hP := F.pre_le lam h0 hL t htn
  have hR := resp_pos_nonneg F.eta_nonneg h0 t hP
  have h := pos_coord_U5 (γ := γ) (δ := errResp η lam ξ t) h0 hR (lam_mul_resp η lam t) hP
  have hδ := errResp_pos_bound F h0 hL ξ htn
  have hw := wsum_nonneg F ξ t
  have hδ2 : errResp η lam ξ t ^ 2 ≤ K ^ 2 * wsum η ξ t ^ 2 := by
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
  have h1 : |γ| * |errResp η lam ξ t| ≤ K * |γ| * wsum η ξ t := by
    have := mul_le_mul_of_nonneg_left hδ (abs_nonneg γ); linarith
  have h2 : lam * errResp η lam ξ t ^ 2 / 2 ≤ L * K ^ 2 * wsum η ξ t ^ 2 / 2 := by
    have := mul_le_mul hL hδ2 (sq_nonneg _) F.hL.le
    linarith
  rw [traj_eq]
  linarith

theorem coord_completed (F : ScheduleFacts η n L K) (hn : 1 ≤ n) {lam γ : ℝ}
    (hlo : -L ≤ lam) (hhi : lam ≤ L) (ξ : ℕ → ℝ) :
    γ * traj η lam γ ξ n + lam * traj η lam γ ξ n ^ 2 / 2 +
        (if 0 ≤ lam then ssum η n * (γ + lam * traj η lam γ ξ n) ^ 2 / 4 else 0) ≤
      (K ^ 2 / 2 + 1181) * wsum η ξ n ^ 2 / ssum η n +
        (L * K ^ 2 / 2 + 16 * L) * wsum η ξ n ^ 2 + 2 * ssum η n * K ^ 2 * usum ξ n ^ 2 := by
  have hS := ssum_pos F hn le_rfl
  have hw := wsum_nonneg F ξ n
  have hu := usum_nonneg ξ n
  have hLp := F.hL
  have t1 : 0 ≤ (K ^ 2 / 2 + 1181) * wsum η ξ n ^ 2 / ssum η n := by positivity
  have t1' : K ^ 2 * wsum η ξ n ^ 2 / (2 * ssum η n) ≤
      (K ^ 2 / 2 + 1181) * wsum η ξ n ^ 2 / ssum η n := by
    rw [div_le_div_iff₀ (by positivity) hS]
    have : 0 ≤ wsum η ξ n ^ 2 * ssum η n := by positivity
    nlinarith
  have t2 : 0 ≤ L * K ^ 2 / 2 * wsum η ξ n ^ 2 := by positivity
  have t3 : 0 ≤ 16 * L * wsum η ξ n ^ 2 := by positivity
  have t4 : 0 ≤ 2 * ssum η n * K ^ 2 * usum ξ n ^ 2 := by positivity
  split_ifs with h0
  · set S := ssum η n
    set P := pr η lam n
    set R := resp η lam n
    set δ := errResp η lam ξ n
    have hRP := lam_mul_resp η lam n
    have hfin : S * P ^ 2 ≤ R * (1 + P) / 2 := by
      rcases h0.lt_or_eq with hpos | hz
      · have hf := F.fin lam h0 hhi
        have : lam * (S * P ^ 2) ≤ lam * (R * (1 + P) / 2) := by
          have e : lam * (R * (1 + P) / 2) = (1 - P) * (1 + P) / 2 := by rw [← hRP]; ring
          rw [e]; nlinarith
        exact le_of_mul_le_mul_left this hpos
      · subst hz
        have e1 : P = 1 := pr_zero η n
        have e2 : R = S := resp_zero η n
        rw [e1, e2]; linarith
    have h := pos_coord_U4 (γ := γ) (δ := δ) hS h0 hRP hfin
    have hmg := model_grad_eq η lam γ ξ n
    have htr := traj_eq η lam γ ξ n
    have hδ := errResp_pos_bound F h0 hhi ξ le_rfl
    have hlδ := lam_errResp_bound F h0 hhi ξ le_rfl
    have hδ2 : δ ^ 2 ≤ K ^ 2 * wsum η ξ n ^ 2 := by
      rw [← mul_pow, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
    have hlδ2 : (lam * δ) ^ 2 ≤ 4 * K ^ 2 * usum ξ n ^ 2 := by
      rw [show 4 * K ^ 2 * usum ξ n ^ 2 = (2 * K * usum ξ n) ^ 2 by ring, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hlδ 2
    have hA : lam * δ ^ 2 ≤ L * (K ^ 2 * wsum η ξ n ^ 2) :=
      mul_le_mul hhi hδ2 (sq_nonneg _) hLp.le
    have hB : δ ^ 2 / S ≤ K ^ 2 * wsum η ξ n ^ 2 / S := div_le_div_of_nonneg_right hδ2 hS.le
    have hC : S * (lam * δ) ^ 2 ≤ S * (4 * K ^ 2 * usum ξ n ^ 2) :=
      mul_le_mul_of_nonneg_left hlδ2 hS.le
    rw [hmg, htr]
    change γ * (-(R * γ) - δ) + lam * (-(R * γ) - δ) ^ 2 / 2 + S * (P * γ - lam * δ) ^ 2 / 4 ≤ _
    change S * (P * γ - lam * δ) ^ 2 ≤
      4 * -(γ * (-(R * γ) - δ) + lam * (-(R * γ) - δ) ^ 2 / 2) + 2 * δ ^ 2 / S + 2 * lam * δ ^ 2 +
        2 * S * (lam * δ) ^ 2 at h
    have e : K ^ 2 * wsum η ξ n ^ 2 / (2 * S) = K ^ 2 * wsum η ξ n ^ 2 / S / 2 := by
      rw [div_div, mul_comm S 2]
    clear_value S P R δ
    have k1 : 2 * δ ^ 2 / S = 2 * (δ ^ 2 / S) := by ring
    have k2 : (K ^ 2 / 2 + 1181) * wsum η ξ n ^ 2 / S =
        K ^ 2 * wsum η ξ n ^ 2 / S / 2 + 1181 * (wsum η ξ n ^ 2 / S) := by ring
    have k3 : K ^ 2 * wsum η ξ n ^ 2 / S = K ^ 2 * (wsum η ξ n ^ 2 / S) := by ring
    have k4 : 0 ≤ wsum η ξ n ^ 2 / S := by positivity
    linarith
  · push Not at h0
    obtain ⟨m, rfl⟩ : ∃ m, lam = -m := ⟨-lam, by ring⟩
    have hm : 0 < m := by linarith
    have h := neg_U1_at F hm ξ hn le_rfl (γ := γ)
    have hq : 0 ≤ traj η (-m) γ ξ n ^ 2 / (21 * ssum η n) := by positivity
    have : 16 * m * wsum η ξ n ^ 2 ≤ 16 * L * wsum η ξ n ^ 2 := by nlinarith
    have : 1181 * wsum η ξ n ^ 2 / ssum η n ≤ (K ^ 2 / 2 + 1181) * wsum η ξ n ^ 2 / ssum η n := by
      apply div_le_div_of_nonneg_right _ hS.le
      have : 0 ≤ K ^ 2 / 2 * wsum η ξ n ^ 2 := by positivity
      nlinarith
    linarith

theorem coord_pred (F : ScheduleFacts η n L K) (hn : 1 ≤ n) {lam γ : ℝ}
    (hlo : -L ≤ lam) (hhi : lam ≤ L) (ξ : ℕ → ℝ) :
    γ * traj η lam γ ξ n + lam * traj η lam γ ξ n ^ 2 / 2 +
        (if lam < 0 then ssum η n * γ ^ 2 / 2 else 0) ≤
      K * |γ| * wsum η ξ n + L * K ^ 2 * wsum η ξ n ^ 2 / 2 + 1188 * wsum η ξ n ^ 2 / ssum η n +
        15 * L * wsum η ξ n ^ 2 + 15 * ssum η n * L ^ 2 * wsum η ξ n ^ 2 := by
  have hS := ssum_pos F hn le_rfl
  have hw := wsum_nonneg F ξ n
  have hLp := F.hL
  have t1 : 0 ≤ K * |γ| * wsum η ξ n := by have := F.hK; positivity
  have t2 : 0 ≤ L * K ^ 2 * wsum η ξ n ^ 2 / 2 := by positivity
  have t3 : 0 ≤ 1188 * wsum η ξ n ^ 2 / ssum η n := by positivity
  have t4 : 0 ≤ 15 * L * wsum η ξ n ^ 2 := by positivity
  have t5 : 0 ≤ 15 * ssum η n * L ^ 2 * wsum η ξ n ^ 2 := by positivity
  split_ifs with h0
  · obtain ⟨m, rfl⟩ : ∃ m, lam = -m := ⟨-lam, by ring⟩
    have hm : 0 < m := by linarith
    have hmL : m ≤ L := by linarith
    have h := neg_U2_at F hm ξ hn le_rfl (γ := γ)
    have : 15 * m * wsum η ξ n ^ 2 ≤ 15 * L * wsum η ξ n ^ 2 := by nlinarith
    have : 15 * ssum η n * m ^ 2 * wsum η ξ n ^ 2 ≤ 15 * ssum η n * L ^ 2 * wsum η ξ n ^ 2 := by
      have : m ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hm.le hmL 2
      have : 0 ≤ 15 * ssum η n * wsum η ξ n ^ 2 := by positivity
      nlinarith
    linarith
  · push Not at h0
    have h := pos_U5_at F h0 hhi ξ le_rfl (γ := γ)
    linarith

theorem coord_exit (F : ScheduleFacts η n L K) {t : ℕ} (ht1 : 1 ≤ t) (htn : t ≤ n) {lam γ : ℝ}
    (hlo : -L ≤ lam) (hhi : lam ≤ L) (ξ : ℕ → ℝ) :
    γ * traj η lam γ ξ t + lam * traj η lam γ ξ t ^ 2 / 2 +
        traj η lam γ ξ t ^ 2 / (21 * ssum η n) ≤
      K * |γ| * wsum η ξ t + 2 * ssum η n * γ ^ 2 / 21 +
        (2 * K ^ 2 / 21 + 1181) * wsum η ξ t ^ 2 / ssum η t +
        (L * K ^ 2 / 2 + 16 * L) * wsum η ξ t ^ 2 := by
  have hSt := ssum_pos F ht1 htn
  have hSS := ssum_mono F htn
  have hS : 0 < ssum η n := lt_of_lt_of_le hSt hSS
  have hw := wsum_nonneg F ξ t
  have hLp := F.hL
  have t1 : 0 ≤ K * |γ| * wsum η ξ t := by have := F.hK; positivity
  have t2 : 0 ≤ 2 * ssum η n * γ ^ 2 / 21 := by positivity
  have t3 : 0 ≤ (2 * K ^ 2 / 21 + 1181) * wsum η ξ t ^ 2 / ssum η t := by positivity
  have t4 : 0 ≤ L * K ^ 2 / 2 * wsum η ξ t ^ 2 := by positivity
  have t5 : 0 ≤ 16 * L * wsum η ξ t ^ 2 := by positivity
  rcases le_or_gt 0 lam with h0 | h0
  · have h := pos_U5_at F h0 hhi ξ htn (γ := γ)
    set St := ssum η t
    set S := ssum η n
    set u := traj η lam γ ξ t
    have hu : |u| ≤ St * |γ| + K * wsum η ξ t := by
      have htr : u = -(resp η lam t * γ) - errResp η lam ξ t := traj_eq η lam γ ξ t
      have hR := resp_pos_bounds F.eta_nonneg (lam := lam) t
        (fun s hs => F.pre_le lam h0 hhi s (le_trans hs htn))
      have hδ := errResp_pos_bound F h0 hhi ξ htn
      rw [htr]
      calc |-(resp η lam t * γ) - errResp η lam ξ t|
          ≤ |resp η lam t * γ| + |errResp η lam ξ t| := by
            rw [show -(resp η lam t * γ) - errResp η lam ξ t =
              -(resp η lam t * γ) + -errResp η lam ξ t by ring]
            refine (abs_add_le _ _).trans ?_
            rw [abs_neg, abs_neg]
        _ ≤ St * |γ| + K * wsum η ξ t := by
            rw [abs_mul]
            exact add_le_add (mul_le_mul_of_nonneg_right hR (abs_nonneg _)) hδ
    have hu2 : u ^ 2 ≤ 2 * St ^ 2 * γ ^ 2 + 2 * K ^ 2 * wsum η ξ t ^ 2 := by
      have h1 : u ^ 2 ≤ (St * |γ| + K * wsum η ξ t) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hu 2
      have h2 : (St * |γ| + K * wsum η ξ t) ^ 2 ≤
          2 * (St * |γ|) ^ 2 + 2 * (K * wsum η ξ t) ^ 2 := by
        nlinarith [sq_nonneg (St * |γ| - K * wsum η ξ t)]
      have e : (St * |γ|) ^ 2 = St ^ 2 * γ ^ 2 := by rw [mul_pow, sq_abs]
      nlinarith
    have hdiv : u ^ 2 / (21 * S) ≤ 2 * S * γ ^ 2 / 21 + 2 * K ^ 2 / 21 * wsum η ξ t ^ 2 / St := by
      have a1 : u ^ 2 / (21 * S) ≤ (2 * St ^ 2 * γ ^ 2 + 2 * K ^ 2 * wsum η ξ t ^ 2) / (21 * S) :=
        div_le_div_of_nonneg_right hu2 (by positivity)
      have a2 : 2 * St ^ 2 * γ ^ 2 / (21 * S) ≤ 2 * S * γ ^ 2 / 21 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : St ^ 2 ≤ S * S := by nlinarith
        have := sq_nonneg γ
        nlinarith
      have a3 : 2 * K ^ 2 * wsum η ξ t ^ 2 / (21 * S) ≤ 2 * K ^ 2 / 21 * wsum η ξ t ^ 2 / St := by
        rw [div_le_div_iff₀ (by positivity) hSt]
        have : 0 ≤ 2 * K ^ 2 * wsum η ξ t ^ 2 := by positivity
        nlinarith
      rw [add_div] at a1
      linarith
    have e : (2 * K ^ 2 / 21 + 1181) * wsum η ξ t ^ 2 / St =
        2 * K ^ 2 / 21 * wsum η ξ t ^ 2 / St + 1181 * wsum η ξ t ^ 2 / St := by ring
    have : 0 ≤ 1181 * wsum η ξ t ^ 2 / St := by positivity
    clear_value St S u
    linarith
  · obtain ⟨m, rfl⟩ : ∃ m, lam = -m := ⟨-lam, by ring⟩
    have hm : 0 < m := by linarith
    have h := neg_U1_at F hm ξ ht1 htn (γ := γ)
    have hq : traj η (-m) γ ξ t ^ 2 / (21 * ssum η n) ≤
        traj η (-m) γ ξ t ^ 2 / (21 * ssum η t) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    have : 16 * m * wsum η ξ t ^ 2 ≤ 16 * L * wsum η ξ t ^ 2 := by nlinarith
    have : 1181 * wsum η ξ t ^ 2 / ssum η t ≤
        (2 * K ^ 2 / 21 + 1181) * wsum η ξ t ^ 2 / ssum η t := by
      apply div_le_div_of_nonneg_right _ hSt.le
      have : 0 ≤ 2 * K ^ 2 / 21 * wsum η ξ t ^ 2 := by positivity
      nlinarith
    linarith

end OracleTemplate.ScheduleBlock
