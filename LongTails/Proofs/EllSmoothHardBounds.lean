import LongTails.Proofs.EllSmoothHard

open scoped BigOperators RealInnerProductSpace Topology

namespace LongTails.Proofs.EllSmoothHardBounds

open LongTails.Proofs.EllSmoothProfiles
open LongTails.Proofs.AbcChainProfiles (pos rr abs_sub_le_sum pos_nonneg pos_of_nonneg pos_of_nonpos)
open LongTails.Proofs.EllSmoothChain LongTails.Proofs.EllSmoothChainHessian
open LongTails.Proofs.EllSmoothHard
open LongTails.Proofs.AbcHardFunction (sel sel_apply sel_norm sel_opNorm sel_adjoint adjoint_norm
  adjoint_congr)

variable (S : Shape) {n d : ℕ}

lemma norm_le_of_sq_le {w : Space d} {B : ℝ} (hB : 0 ≤ B) (h : ‖w‖ ^ 2 ≤ B ^ 2) : ‖w‖ ≤ B :=
  le_of_sq_le_sq h hB

lemma le_norm_of_sq_le {w : Space d} {B : ℝ} (h : B ^ 2 ≤ ‖w‖ ^ 2) : B ≤ ‖w‖ :=
  le_of_sq_le_sq h (norm_nonneg w)

lemma dcut_mul_norm (w : Space d) :
    |dcut S n (‖w‖ ^ 2)| * ‖w‖ ≤ 5 / (6 * rad S n) := by
  have hr := rad_pos S n
  rcases le_total (16 * rad S n ^ 2) (‖w‖ ^ 2) with h | h
  · rw [dcut_of_ge S n h, abs_zero, zero_mul]
    positivity
  · have hw : ‖w‖ ≤ 4 * rad S n :=
      norm_le_of_sq_le (by positivity) (by nlinarith)
    have h1 := dcut_abs S n (‖w‖ ^ 2)
    calc |dcut S n (‖w‖ ^ 2)| * ‖w‖ ≤ 5 / (24 * rad S n ^ 2) * (4 * rad S n) :=
          mul_le_mul h1 hw (norm_nonneg _) (by positivity)
      _ = 5 / (6 * rad S n) := by field_simp; ring

lemma ddcut_mul_sq (w : Space d) :
    |ddcut S n (‖w‖ ^ 2)| * ‖w‖ ^ 2 ≤ 1 / rad S n ^ 2 := by
  have hr := rad_pos S n
  rcases le_total (16 * rad S n ^ 2) (‖w‖ ^ 2) with h | h
  · rw [ddcut_of_ge S n h, abs_zero, zero_mul]
    positivity
  · have h1 := ddcut_abs S n (‖w‖ ^ 2)
    calc |ddcut S n (‖w‖ ^ 2)| * ‖w‖ ^ 2 ≤ 1 / (16 * rad S n ^ 4) * (16 * rad S n ^ 2) :=
          mul_le_mul h1 h (sq_nonneg _) (by positivity)
      _ = 1 / rad S n ^ 2 := by field_simp

lemma bco_near (π : Fin (n + 1) ↪ Fin d) (w : Space d) (h : ‖w‖ ^ 2 ≤ 4 * rad S n ^ 2) :
    bco S π w = 2 * dwall S n (‖w‖ ^ 2) := by
  unfold bco
  rw [dcut_of_le S n h]
  ring

lemma hgrad_near (π : Fin (n + 1) ↪ Fin d) (w : Space d) (h : ‖w‖ ^ 2 ≤ 4 * rad S n ^ 2) :
    hgrad S π w = vfield S π w + (2 * dwall S n (‖w‖ ^ 2)) • w := by
  unfold hgrad
  rw [cut_of_le S n h, bco_near S π w h, one_smul]

lemma hgrad_near_ge (π : Fin (n + 1) ↪ Fin d) (w : Space d) (h : ‖w‖ ^ 2 ≤ 4 * rad S n ^ 2) :
    ‖field S (sel π w)‖ - S.mu / 2000 ≤ ‖hgrad S π w‖ := by
  have h1 : ‖sel π (hgrad S π w)‖ ≤ ‖hgrad S π w‖ := sel_norm π _
  have h2 : sel π (hgrad S π w) =
      field S (sel π w) + (2 * dwall S n (‖w‖ ^ 2)) • sel π w := by
    rw [hgrad_near S π w h, map_add, map_smul, sel_vfield]
  rw [h2] at h1
  have h3 := field_add_smul_ge S (sel π w) (2 * dwall S n (‖w‖ ^ 2))
  have hd0 := dwall_nonneg S n (‖w‖ ^ 2)
  have hd1 := dwall_le S n (‖w‖ ^ 2)
  have ht := S.tEnd_pos
  have hn := n1_pos n
  have h4 : |2 * dwall S n (‖w‖ ^ 2)| * (S.tEnd * ((n : ℝ) + 1)) ≤
      2 * kap S n * (S.tEnd * ((n : ℝ) + 1)) := by
    rw [abs_of_nonneg (by positivity)]
    gcongr
  have h5 := kap_tEnd S n
  linarith

lemma hgrad_near_unfinished (π : Fin (n + 1) ↪ Fin d) (w : Space d)
    (h : ‖w‖ ^ 2 ≤ 4 * rad S n ^ 2) (hu : ∃ k : Fin (n + 1), |sel π w k| < 1) :
    1 / 2 ≤ ‖hgrad S π w‖ := by
  have h1 := hgrad_near_ge S π w h
  have h2 := field_norm_ge_one S (sel π w) hu
  have hmu := S.hmu'
  linarith

lemma chainSel_abs (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    |chain S (sel π w)| ≤ 20 * ((n : ℝ) + 1) := chain_abs S _

lemma hgrad_far (π : Fin (n + 1) ↪ Fin d) (w : Space d) (h : 4 * rad S n ^ 2 ≤ ‖w‖ ^ 2) :
    1 ≤ ‖hgrad S π w‖ := by
  have hr := rad_pos S n
  have hn := n1_ge n
  have hrg := rad_ge' S n
  have hw : 2 * rad S n ≤ ‖w‖ := le_norm_of_sq_le (by nlinarith)
  have hkr := kap_rad S n
  have hk := kap_pos S n
  have hch := chainSel_abs S π w
  have hdc := dcut_abs S n (‖w‖ ^ 2)
  have hb : kap S n ≤ bco S π w := by
    unfold bco
    rw [dwall_of_ge S n h]
    have h1 : |2 * dcut S n (‖w‖ ^ 2) * chain S (sel π w)| ≤ kap S n := by
      rw [abs_mul, abs_mul, abs_two]
      have h2 : 2 * |dcut S n (‖w‖ ^ 2)| * |chain S (sel π w)| ≤
          2 * (5 / (24 * rad S n ^ 2)) * (20 * ((n : ℝ) + 1)) := by
        gcongr
      refine h2.trans ?_
      have e : 2 * (5 / (24 * rad S n ^ 2)) * (20 * ((n : ℝ) + 1)) =
          25 / 3 * ((n : ℝ) + 1) / rad S n ^ 2 := by field_simp; ring
      rw [e, div_le_iff₀ (by positivity)]
      have : kap S n * rad S n ^ 2 = 2 ^ 22 / 52000 * ((n : ℝ) + 1) * rad S n := by
        rw [← hkr]; ring
      rw [this]
      nlinarith
    have := neg_abs_le (2 * dcut S n (‖w‖ ^ 2) * chain S (sel π w))
    linarith
  have hv : ‖cut S n (‖w‖ ^ 2) • vfield S π w‖ ≤ 103 * ((n : ℝ) + 1) := by
    rw [norm_smul, Real.norm_of_nonneg (cut_nonneg S n _)]
    calc cut S n (‖w‖ ^ 2) * ‖vfield S π w‖ ≤ 1 * ‖field S (sel π w)‖ :=
          mul_le_mul (cut_le_one S n _) (vfield_norm S π w) (norm_nonneg _) zero_le_one
      _ ≤ 103 * ((n : ℝ) + 1) := by rw [one_mul]; exact field_norm_le S _
  have hbw : kap S n * (2 * rad S n) ≤ ‖bco S π w • w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hk.le.trans hb)]
    exact mul_le_mul hb hw (by positivity) (hk.le.trans hb)
  have hlow : ‖bco S π w • w‖ - ‖cut S n (‖w‖ ^ 2) • vfield S π w‖ ≤ ‖hgrad S π w‖ := by
    unfold hgrad
    have := norm_sub_norm_le (bco S π w • w) (-(cut S n (‖w‖ ^ 2) • vfield S π w))
    rw [norm_neg, sub_neg_eq_add, add_comm] at this
    exact this
  have hnum : (1 : ℝ) + 103 * ((n : ℝ) + 1) ≤ kap S n * (2 * rad S n) := by
    have : kap S n * (2 * rad S n) = 2 * (2 ^ 22 / 52000 * ((n : ℝ) + 1)) := by
      rw [← hkr]; ring
    rw [this]
    nlinarith
  linarith

lemma min_rpow_double {A g r : ℝ} (hA : 0 ≤ A) (hg : 0 ≤ g) (h : A ≤ 2 * g) (hr0 : 0 ≤ r)
    (hr2 : r ≤ 2) : min 1 (A ^ r) ≤ 4 * min 1 (g ^ r) := by
  have hg0 : 0 ≤ g ^ r := Real.rpow_nonneg hg r
  rcases le_total 1 (g ^ r) with h1 | h1
  · rw [min_eq_left h1]
    exact (min_le_left _ _).trans (by norm_num)
  · rw [min_eq_right h1]
    refine (min_le_right _ _).trans ?_
    calc A ^ r ≤ (2 * g) ^ r := Real.rpow_le_rpow hA h hr0
      _ = 2 ^ r * g ^ r := Real.mul_rpow (by norm_num) hg
      _ ≤ 4 * g ^ r := by
        gcongr
        calc (2 : ℝ) ^ r ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hr2
          _ = 4 := by norm_num

lemma n1_div_rad_sq (n : ℕ) : ((n : ℝ) + 1) / rad S n ^ 2 ≤ 1 / 2 ^ 22 := by
  have hr := rad_pos S n
  have hrg := rad_ge' S n
  have hn := n1_ge n
  have h1 : (1 : ℝ) ≤ rad S n := by linarith
  have h2 : rad S n * 1 ≤ rad S n * rad S n := mul_le_mul_of_nonneg_left h1 hr.le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma far_dcut_term (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    4 * |dcut S n (‖w‖ ^ 2)| * ‖w‖ * ‖field S (sel π w)‖ ≤ 1 := by
  have hr := rad_pos S n
  have hrg := rad_ge' S n
  have hA := field_norm_le S (sel π w)
  have hA0 := norm_nonneg (field S (sel π w))
  have hdm := dcut_mul_norm S w (n := n)
  have h1 : |dcut S n (‖w‖ ^ 2)| * ‖w‖ * ‖field S (sel π w)‖ ≤
      5 / (6 * rad S n) * (103 * ((n : ℝ) + 1)) :=
    mul_le_mul hdm hA hA0 (by positivity)
  have e : 5 / (6 * rad S n) * (103 * ((n : ℝ) + 1)) =
      515 / 6 * (((n : ℝ) + 1) / rad S n) := by ring
  have hq : ((n : ℝ) + 1) / rad S n ≤ 1 / 2 ^ 22 := by
    rw [div_le_div_iff₀ hr (by positivity)]
    linarith
  rw [e] at h1
  linarith

lemma dcut_chain_abs (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    |2 * dcut S n (‖w‖ ^ 2) * chain S (sel π w)| ≤
      25 / 3 * (((n : ℝ) + 1) / rad S n ^ 2) := by
  have hr := rad_pos S n
  have hch := chainSel_abs S π w
  have hdc := dcut_abs S n (‖w‖ ^ 2)
  rw [abs_mul, abs_mul, abs_two]
  have h2 : |dcut S n (‖w‖ ^ 2)| * |chain S (sel π w)| ≤
      5 / (24 * rad S n ^ 2) * (20 * ((n : ℝ) + 1)) :=
    mul_le_mul hdc hch (abs_nonneg _) (by positivity)
  have e : 5 / (24 * rad S n ^ 2) * (20 * ((n : ℝ) + 1)) =
      25 / 6 * (((n : ℝ) + 1) / rad S n ^ 2) := by ring
  rw [e] at h2
  linarith

lemma far_bco_abs (π : Fin (n + 1) ↪ Fin d) (w : Space d) (h : 4 * rad S n ^ 2 ≤ ‖w‖ ^ 2) :
    |bco S π w| ≤ 1 := by
  have hk := kap_pos S n
  have hkle := kap_le S n
  have hmu' := S.hmu'
  have h1 := dcut_chain_abs S π w
  have h2 := n1_div_rad_sq S n
  unfold bco
  rw [dwall_of_ge S n h]
  have h3 : |2 * kap S n| = 2 * kap S n := abs_of_nonneg (by positivity)
  have h4 := abs_add_le (2 * dcut S n (‖w‖ ^ 2) * chain S (sel π w)) (2 * kap S n)
  rw [h3] at h4
  linarith

lemma far_ddcut_term (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    4 * |ddcut S n (‖w‖ ^ 2)| * |chain S (sel π w)| * ‖w‖ ^ 2 ≤ 1 := by
  have hr := rad_pos S n
  have hch := chainSel_abs S π w
  have hdd := ddcut_mul_sq S w (n := n)
  have h2 := n1_div_rad_sq S n
  have h1 : |ddcut S n (‖w‖ ^ 2)| * ‖w‖ ^ 2 * |chain S (sel π w)| ≤
      1 / rad S n ^ 2 * (20 * ((n : ℝ) + 1)) :=
    mul_le_mul hdd hch (abs_nonneg _) (by positivity)
  have e : 1 / rad S n ^ 2 * (20 * ((n : ℝ) + 1)) =
      20 * (((n : ℝ) + 1) / rad S n ^ 2) := by ring
  rw [e] at h1
  linarith

lemma wall_curv_term (w : Space d) (h : ‖w‖ ^ 2 ≤ 4 * rad S n ^ 2) :
    4 * |ddwall S n (‖w‖ ^ 2)| * ‖w‖ ^ 2 ≤ 11 * kap S n := by
  have hk := kap_pos S n
  have hl := lam_pos S n
  have hdd0 := ddwall_nonneg S n (‖w‖ ^ 2)
  have hdd1 := ddwall_le S n (‖w‖ ^ 2)
  rw [abs_of_nonneg hdd0]
  have hq : 0 ≤ kap S n / lam S n := div_nonneg hk.le hl.le
  have h1 : ddwall S n (‖w‖ ^ 2) * ‖w‖ ^ 2 ≤ kap S n / lam S n * (4 * rad S n ^ 2) :=
    mul_le_mul hdd1 h (sq_nonneg _) hq
  have e0 : kap S n / lam S n * lam S n = kap S n := div_mul_cancel₀ _ hl.ne'
  have e1 : 4 * rad S n ^ 2 = 8 / 3 * lam S n := by unfold lam; ring
  rw [e1] at h1
  linarith

lemma hgrad_class_near (π : Fin (n + 1) ↪ Fin d) (w : Space d)
    (h : ‖w‖ ^ 2 ≤ 4 * rad S n ^ 2) :
    ‖fderiv ℝ (hgrad S π) w‖ ≤
      1000 / S.th * min 1 (‖field S (sel π w)‖ ^ (2 - S.th)) + S.mu + 13 * kap S n := by
  have hbase := hgrad_fderiv_le S π w
  have hDf := fderiv_field_bound S (sel π w)
  rw [cut_of_le S n h, dcut_of_le S n h, ddcut_of_le S n h, bco_near S π w h] at hbase
  simp only [one_mul, abs_zero, mul_zero, zero_mul, add_zero, zero_add] at hbase
  have hd0 := dwall_nonneg S n (‖w‖ ^ 2)
  have hd1 := dwall_le S n (‖w‖ ^ 2)
  have hwall := wall_curv_term S w h
  have hb2 : |2 * dwall S n (‖w‖ ^ 2)| = 2 * dwall S n (‖w‖ ^ 2) :=
    abs_of_nonneg (by positivity)
  rw [hb2] at hbase
  linarith

lemma near_scalar {th mu κ A g D : ℝ} (hth : 0 < th) (hth' : th ≤ 1 / 2) (hmu : 0 < mu)
    (hmu' : mu ≤ 1) (hκ : κ ≤ mu / 52000) (hA0 : 0 ≤ A) (hg0 : 0 ≤ g)
    (hge : A - mu / 2000 ≤ g)
    (hD : D ≤ 1000 / th * min 1 (A ^ (2 - th)) + mu + 13 * κ) :
    D ≤ 4000 / th * (min 1 (g ^ (2 - th)) + mu) := by
  have hexp0 : (0 : ℝ) ≤ 2 - th := by linarith
  have hexp2 : 2 - th ≤ 2 := by linarith
  have hinv : (2 : ℝ) ≤ 1 / th := by
    rw [le_div_iff₀ hth]; linarith
  have hc1000 : (0 : ℝ) ≤ 1000 / th := by positivity
  have hmin0 : 0 ≤ min 1 (g ^ (2 - th)) := le_min zero_le_one (Real.rpow_nonneg hg0 _)
  have hI : 1000 / th = 1000 * (1 / th) := by ring
  have hI4 : 4000 / th = 4000 * (1 / th) := by ring
  have hmuI : 2 * mu ≤ 1 / th * mu := mul_le_mul_of_nonneg_right hinv hmu.le
  have hminI : 0 ≤ 1 / th * min 1 (g ^ (2 - th)) := mul_nonneg (by positivity) hmin0
  rcases le_total (mu / 1000) A with hA | hA
  · have hA2 : A ≤ 2 * g := by linarith
    have hm := min_rpow_double hA0 hg0 hA2 hexp0 hexp2
    have h1 := mul_le_mul_of_nonneg_left hm hc1000
    rw [hI] at h1 hD
    rw [hI4]
    linarith
  · have hA1 : A ≤ 1 := by linarith
    have hpow : A ^ (2 - th) ≤ mu / 1000 := by
      rcases eq_or_lt_of_le hA0 with h0 | h0
      · rw [← h0, Real.zero_rpow (by linarith)]
        positivity
      · calc A ^ (2 - th) ≤ A ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_ge h0 hA1 (by linarith)
          _ = A := Real.rpow_one _
          _ ≤ mu / 1000 := hA
    have hmin : min 1 (A ^ (2 - th)) ≤ mu / 1000 := (min_le_right _ _).trans hpow
    have h1 := mul_le_mul_of_nonneg_left hmin hc1000
    rw [hI] at h1 hD
    rw [hI4]
    linarith

lemma hgrad_class_far (π : Fin (n + 1) ↪ Fin d) (w : Space d)
    (h : 4 * rad S n ^ 2 ≤ ‖w‖ ^ 2) :
    ‖fderiv ℝ (hgrad S π) w‖ ≤ 1000 / S.th + 3 := by
  have hbase := hgrad_fderiv_le S π w
  have hDg := fderiv_field_norm_le S (sel π w)
  rw [ddwall_of_ge S n h] at hbase
  simp only [abs_zero, mul_zero, add_zero] at hbase
  have hc1 := cut_le_one S n (‖w‖ ^ 2)
  have t1 : cut S n (‖w‖ ^ 2) * ‖fderiv ℝ (field S) (sel π w)‖ ≤ 1000 / S.th := by
    calc _ ≤ 1 * (1000 / S.th) := mul_le_mul hc1 hDg (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have t2 := far_dcut_term S π w
  have t3 := far_bco_abs S π w h
  have t4 := far_ddcut_term S π w
  linarith

lemma hgrad_class (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    ‖fderiv ℝ (hgrad S π) w‖ ≤
      4000 / S.th * (min 1 (‖hgrad S π w‖ ^ (2 - S.th)) + S.mu) := by
  have hth := S.hth
  have hth' := S.hth'
  have hmu := S.hmu
  rcases le_total (‖w‖ ^ 2) (4 * rad S n ^ 2) with h | h
  · exact near_scalar hth hth' hmu S.hmu' (kap_le S n) (norm_nonneg _) (norm_nonneg _)
      (hgrad_near_ge S π w h) (hgrad_class_near S π w h)
  · have hfar := hgrad_far S π w h
    have hpow : 1 ≤ ‖hgrad S π w‖ ^ (2 - S.th) := Real.one_le_rpow hfar (by linarith)
    rw [min_eq_left hpow]
    have h1 := hgrad_class_far S π w h
    have hinv : (2 : ℝ) ≤ 1 / S.th := by
      rw [le_div_iff₀ hth]; linarith
    have e1 : 1000 / S.th = 1000 * (1 / S.th) := by ring
    have e2 : 4000 / S.th * (1 + S.mu) = 4000 * (1 / S.th) + 4000 * (1 / S.th) * S.mu := by ring
    have hp : 0 ≤ 1 / S.th * S.mu := by positivity
    rw [e1] at h1
    rw [e2]
    linarith

lemma hval_ge (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    -(20 * ((n : ℝ) + 1)) ≤ hval S π w := by
  unfold hval
  have hc0 := cut_nonneg S n (‖w‖ ^ 2)
  have hc1 := cut_le_one S n (‖w‖ ^ 2)
  have hw := wall_nonneg S n (‖w‖ ^ 2)
  have hch := chainSel_abs S π w
  have hn := n1_pos n
  have h1 : |cut S n (‖w‖ ^ 2) * chain S (sel π w)| ≤ 20 * ((n : ℝ) + 1) := by
    rw [abs_mul, abs_of_nonneg hc0]
    calc _ ≤ 1 * (20 * ((n : ℝ) + 1)) := mul_le_mul hc1 hch (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have := neg_abs_le (cut S n (‖w‖ ^ 2) * chain S (sel π w))
  linarith

lemma hval_zero_le (π : Fin (n + 1) ↪ Fin d) : hval S π (0 : Space d) ≤ 0 := by
  unfold hval
  have hr := rad_pos S n
  have h0 : ‖(0 : Space d)‖ ^ 2 ≤ 4 * rad S n ^ 2 := by simp; positivity
  rw [cut_of_le S n h0, one_mul, map_zero]
  have hw : wall S n (‖(0 : Space d)‖ ^ 2) = 0 := by
    unfold wall wallArg
    have harg : ((‖(0 : Space d)‖ ^ 2 - rad S n ^ 2) / lam S n) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (lam_pos S n).le
      simp
      positivity
    have hW : W ((‖(0 : Space d)‖ ^ 2 - rad S n ^ 2) / lam S n) = 0 := by
      unfold W
      rw [rc_of_nonpos harg, rc_of_nonpos (by linarith), rc_of_nonpos (by linarith)]
      ring
    rw [hW, mul_zero]
  rw [hw, add_zero]
  exact chain_zero_le S

end LongTails.Proofs.EllSmoothHardBounds
