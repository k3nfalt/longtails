import LongTails.Proofs.AbcChainProfiles
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Topology
open LongTails.Proofs.AbcChainProfiles

namespace LongTails.Proofs.EllSmoothProfiles

noncomputable def rc (s : ℝ) : ℝ := pos s ^ 3 / 6

lemma rr_hasDerivAt (x : ℝ) : HasDerivAt rr (pos x) x :=
  model_hasDerivAt rr pos (1 / 2) (fun x y => by have := rr_model x y; linarith) x

lemma rr_nonneg (x : ℝ) : 0 ≤ rr x := by unfold rr; positivity

lemma rr_of_nonpos {x : ℝ} (h : x ≤ 0) : rr x = 0 := by simp [rr, pos_of_nonpos h]

lemma rr_of_nonneg {x : ℝ} (h : 0 ≤ x) : rr x = x ^ 2 / 2 := by simp [rr, pos_of_nonneg h]

lemma rc_of_nonpos {x : ℝ} (h : x ≤ 0) : rc x = 0 := by simp [rc, pos_of_nonpos h]

lemma rc_of_nonneg {x : ℝ} (h : 0 ≤ x) : rc x = x ^ 3 / 6 := by simp [rc, pos_of_nonneg h]

lemma rc_hasDerivAt (x : ℝ) : HasDerivAt rc (rr x) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h : rc =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact rc_of_nonpos (le_of_lt hy)
    rw [rr_of_nonpos hx.le]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq h
  · subst hx
    rw [rr_of_nonpos le_rfl]
    apply HasDerivAt.of_isLittleO
    have hb : (fun y => rc y - rc 0 - (y - 0) • (0 : ℝ)) =O[𝓝 (0 : ℝ)] (fun y => ‖y - 0‖ ^ 2) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with y hy
      have hy1 : |y| < 1 := by simpa [Real.dist_eq] using hy
      have hp0 := pos_nonneg y
      have hp1 : pos y ≤ |y| := max_le (le_abs_self y) (abs_nonneg y)
      have hrc : rc 0 = 0 := rc_of_nonpos le_rfl
      simp only [hrc, sub_zero, smul_zero, Real.norm_eq_abs, sq_abs, one_mul]
      rw [abs_of_nonneg (by unfold rc; positivity), abs_of_nonneg (sq_nonneg y)]
      unfold rc
      have h3 : pos y ^ 3 ≤ |y| ^ 3 := pow_le_pow_left₀ hp0 hp1 3
      have h4 : |y| ^ 3 ≤ |y| ^ 2 := by
        have := abs_nonneg y
        nlinarith [sq_nonneg (|y|)]
      nlinarith [sq_abs y]
    exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub (0 : ℝ) (by norm_num : 1 < 2))
  · have h : rc =ᶠ[𝓝 x] fun y => y ^ 3 / 6 := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact rc_of_nonneg (le_of_lt hy)
    have hd : HasDerivAt (fun y : ℝ => y ^ 3 / 6) (rr x) x := by
      have h3 := (hasDerivAt_pow 3 x).div_const 6
      convert h3 using 1
      rw [rr_of_nonneg hx.le]
      ring
    exact hd.congr_of_eventuallyEq h

noncomputable def psi (t : ℝ) : ℝ :=
  216 * (rc (t - 1 / 2) - 3 * rc (t - 2 / 3) + 3 * rc (t - 5 / 6) - rc (t - 1))

noncomputable def dpsi (t : ℝ) : ℝ :=
  216 * (rr (t - 1 / 2) - 3 * rr (t - 2 / 3) + 3 * rr (t - 5 / 6) - rr (t - 1))

noncomputable def ddpsi (t : ℝ) : ℝ :=
  216 * (pos (t - 1 / 2) - 3 * pos (t - 2 / 3) + 3 * pos (t - 5 / 6) - pos (t - 1))

lemma psi_hasDerivAt (t : ℝ) : HasDerivAt psi (dpsi t) t := by
  have h (a : ℝ) : HasDerivAt (fun s => rc (s - a)) (rr (t - a)) t := by
    have := (rc_hasDerivAt (t - a)).comp t ((hasDerivAt_id t).sub_const a)
    simp only [mul_one] at this
    exact this
  have hh := ((((h (1 / 2)).sub ((h (2 / 3)).const_mul 3)).add ((h (5 / 6)).const_mul 3)).sub
    (h 1)).const_mul 216
  exact hh

lemma dpsi_hasDerivAt (t : ℝ) : HasDerivAt dpsi (ddpsi t) t := by
  have h (a : ℝ) : HasDerivAt (fun s => rr (s - a)) (pos (t - a)) t := by
    have := (rr_hasDerivAt (t - a)).comp t ((hasDerivAt_id t).sub_const a)
    simp only [mul_one] at this
    exact this
  have hh := ((((h (1 / 2)).sub ((h (2 / 3)).const_mul 3)).add ((h (5 / 6)).const_mul 3)).sub
    (h 1)).const_mul 216
  exact hh

lemma psi_of_le {t : ℝ} (h : t ≤ 1 / 2) : psi t = 0 := by
  unfold psi
  rw [rc_of_nonpos (by linarith), rc_of_nonpos (by linarith), rc_of_nonpos (by linarith),
    rc_of_nonpos (by linarith)]
  ring

lemma dpsi_of_le {t : ℝ} (h : t ≤ 1 / 2) : dpsi t = 0 := by
  unfold dpsi
  rw [rr_of_nonpos (by linarith), rr_of_nonpos (by linarith), rr_of_nonpos (by linarith),
    rr_of_nonpos (by linarith)]
  ring

lemma ddpsi_of_le {t : ℝ} (h : t ≤ 1 / 2) : ddpsi t = 0 := by
  unfold ddpsi
  rw [pos_of_nonpos (by linarith), pos_of_nonpos (by linarith), pos_of_nonpos (by linarith),
    pos_of_nonpos (by linarith)]
  ring

lemma psi_of_ge {t : ℝ} (h : 1 ≤ t) : psi t = 1 := by
  unfold psi
  rw [rc_of_nonneg (by linarith), rc_of_nonneg (by linarith), rc_of_nonneg (by linarith),
    rc_of_nonneg (by linarith)]
  ring

lemma dpsi_of_ge {t : ℝ} (h : 1 ≤ t) : dpsi t = 0 := by
  unfold dpsi
  rw [rr_of_nonneg (by linarith), rr_of_nonneg (by linarith), rr_of_nonneg (by linarith),
    rr_of_nonneg (by linarith)]
  ring

lemma ddpsi_of_ge {t : ℝ} (h : 1 ≤ t) : ddpsi t = 0 := by
  unfold ddpsi
  rw [pos_of_nonneg (by linarith), pos_of_nonneg (by linarith), pos_of_nonneg (by linarith),
    pos_of_nonneg (by linarith)]
  ring

lemma dpsi_nonneg (t : ℝ) : 0 ≤ dpsi t := by
  rcases le_total t (1 / 2) with h1 | h1
  · rw [dpsi_of_le h1]
  rcases le_total t (2 / 3) with h2 | h2
  · unfold dpsi
    rw [rr_of_nonneg (by linarith), rr_of_nonpos (by linarith), rr_of_nonpos (by linarith),
      rr_of_nonpos (by linarith)]
    nlinarith [sq_nonneg (t - 1 / 2)]
  rcases le_total t (5 / 6) with h3 | h3
  · unfold dpsi
    rw [rr_of_nonneg (by linarith), rr_of_nonneg (by linarith), rr_of_nonpos (by linarith),
      rr_of_nonpos (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr h3)]
  rcases le_total t 1 with h4 | h4
  · unfold dpsi
    rw [rr_of_nonneg (by linarith), rr_of_nonneg (by linarith), rr_of_nonneg (by linarith),
      rr_of_nonpos (by linarith)]
    nlinarith [sq_nonneg (t - 1)]
  · rw [dpsi_of_ge h4]

lemma dpsi_le (t : ℝ) : dpsi t ≤ 5 := by
  rcases le_total t (1 / 2) with h1 | h1
  · rw [dpsi_of_le h1]; norm_num
  rcases le_total t (2 / 3) with h2 | h2
  · unfold dpsi
    rw [rr_of_nonneg (by linarith), rr_of_nonpos (by linarith), rr_of_nonpos (by linarith),
      rr_of_nonpos (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  rcases le_total t (5 / 6) with h3 | h3
  · unfold dpsi
    rw [rr_of_nonneg (by linarith), rr_of_nonneg (by linarith), rr_of_nonpos (by linarith),
      rr_of_nonpos (by linarith)]
    nlinarith [sq_nonneg (t - 3 / 4)]
  rcases le_total t 1 with h4 | h4
  · unfold dpsi
    rw [rr_of_nonneg (by linarith), rr_of_nonneg (by linarith), rr_of_nonneg (by linarith),
      rr_of_nonpos (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr h3) (sub_nonneg.mpr h4)]
  · rw [dpsi_of_ge h4]; norm_num

lemma ddpsi_abs (t : ℝ) : |ddpsi t| ≤ 36 := by
  rw [abs_le]
  rcases le_total t (1 / 2) with h1 | h1
  · rw [ddpsi_of_le h1]; norm_num
  rcases le_total t (2 / 3) with h2 | h2
  · unfold ddpsi
    rw [pos_of_nonneg (by linarith), pos_of_nonpos (by linarith), pos_of_nonpos (by linarith),
      pos_of_nonpos (by linarith)]
    constructor <;> linarith
  rcases le_total t (5 / 6) with h3 | h3
  · unfold ddpsi
    rw [pos_of_nonneg (by linarith), pos_of_nonneg (by linarith), pos_of_nonpos (by linarith),
      pos_of_nonpos (by linarith)]
    constructor <;> linarith
  rcases le_total t 1 with h4 | h4
  · unfold ddpsi
    rw [pos_of_nonneg (by linarith), pos_of_nonneg (by linarith), pos_of_nonneg (by linarith),
      pos_of_nonpos (by linarith)]
    constructor <;> linarith
  · rw [ddpsi_of_ge h4]; norm_num

lemma psi_monotone : Monotone psi :=
  monotone_of_deriv_nonneg (fun t => (psi_hasDerivAt t).differentiableAt)
    (fun t => by rw [(psi_hasDerivAt t).deriv]; exact dpsi_nonneg t)

lemma psi_nonneg (t : ℝ) : 0 ≤ psi t := by
  rcases le_total t (1 / 2) with h | h
  · rw [psi_of_le h]
  · have := psi_monotone h
    rwa [psi_of_le le_rfl] at this

lemma psi_le_one (t : ℝ) : psi t ≤ 1 := by
  rcases le_total t 1 with h | h
  · have := psi_monotone h
    rwa [psi_of_ge le_rfl] at this
  · rw [psi_of_ge h]

structure Shape where
  th : ℝ
  mu : ℝ
  hth : 0 < th
  hth' : th ≤ 1 / 2
  hmu : 0 < mu
  hmu' : mu ≤ 1

namespace Shape

variable (S : Shape)

noncomputable def e : ℝ := 1 / (2 * (1 - S.th))

noncomputable def v : ℝ := S.mu * S.th / 12

noncomputable def tEnd : ℝ := 1 + 12 / S.mu

lemma one_sub_pos : 0 < 1 - S.th := by have := S.hth'; linarith

lemma e_pos : 0 < S.e := by unfold e; have := S.one_sub_pos; positivity

lemma e_le_one : S.e ≤ 1 := by
  unfold e
  have := S.one_sub_pos
  rw [div_le_one (by positivity)]
  have := S.hth'
  linarith

lemma e_gt_half : 1 / 2 < S.e := by
  unfold e
  have h := S.one_sub_pos
  rw [lt_div_iff₀ (by positivity)]
  have := S.hth
  linarith

lemma e_key : S.e * (2 - S.th) = S.e + 1 / 2 := by
  unfold e
  have h := S.one_sub_pos
  field_simp
  ring

lemma v_pos : 0 < S.v := by unfold v; have := S.hth; have := S.hmu; positivity

lemma v_le : S.v ≤ 1 / 24 := by
  unfold v
  have := S.hth; have := S.hth'; have := S.hmu; have := S.hmu'
  nlinarith

lemma tEnd_pos : 0 < S.tEnd := by unfold tEnd; have := S.hmu; positivity

lemma tEnd_ge : 13 ≤ S.tEnd := by
  unfold tEnd
  have h := S.hmu
  have h1 : 12 ≤ 12 / S.mu := by
    rw [le_div_iff₀ h]
    have := S.hmu'
    linarith
  linarith

lemma tEnd_le : S.tEnd ≤ 13 / S.mu := by
  unfold tEnd
  have h := S.hmu
  have h1 : (1 : ℝ) ≤ 1 / S.mu := by
    rw [le_div_iff₀ h]
    have := S.hmu'
    linarith
  have e1 : 13 / S.mu = 1 / S.mu + 12 / S.mu := by ring
  linarith

end Shape

noncomputable def m (t : ℝ) : ℝ := 2 * rr (t - 1) + 2 * rr (-t - 1)

noncomputable def dm (t : ℝ) : ℝ := 2 * pos (t - 1) - 2 * pos (-t - 1)

lemma m_nonneg (t : ℝ) : 0 ≤ m t := by
  unfold m
  have := rr_nonneg (t - 1)
  have := rr_nonneg (-t - 1)
  linarith

lemma m_hasDerivAt (t : ℝ) : HasDerivAt m (dm t) t := by
  have h1 : HasDerivAt (fun s => rr (s - 1)) (pos (t - 1)) t := by
    have := (rr_hasDerivAt (t - 1)).comp t ((hasDerivAt_id t).sub_const 1)
    simp only [mul_one] at this
    exact this
  have h2 : HasDerivAt (fun s => rr (-s - 1)) (-pos (-t - 1)) t := by
    have := (rr_hasDerivAt (-t - 1)).comp t (((hasDerivAt_id t).neg).sub_const 1)
    simp only [mul_neg, mul_one] at this
    exact this
  have hh : HasDerivAt m (2 * pos (t - 1) + 2 * -pos (-t - 1)) t :=
    (h1.const_mul 2).add (h2.const_mul 2)
  convert hh using 1
  unfold dm
  ring

lemma dm_sq (t : ℝ) : dm t ^ 2 = 4 * m t := by
  unfold dm m rr
  rcases le_total t 1 with h1 | h1
  · rw [pos_of_nonpos (by linarith : t - 1 ≤ 0)]
    ring
  · rw [pos_of_nonpos (by linarith : -t - 1 ≤ 0)]
    ring

lemma m_of_abs_le {t : ℝ} (h : |t| ≤ 1) : m t = 0 := by
  have h1 := abs_le.mp h
  unfold m
  rw [rr_of_nonpos (by linarith), rr_of_nonpos (by linarith)]
  ring

lemma m_ge_of_le {t a : ℝ} (ha : 0 ≤ a) (h : 1 + a ≤ |t|) : a ^ 2 ≤ m t := by
  unfold m
  rcases le_abs.mp h with h1 | h1
  · rw [rr_of_nonneg (by linarith)]
    have := rr_nonneg (-t - 1)
    nlinarith
  · rw [rr_of_nonneg (by linarith : 0 ≤ -t - 1)]
    have := rr_nonneg (t - 1)
    nlinarith

variable (S : Shape)

noncomputable def Y (t : ℝ) : ℝ := 1 + m t / S.th ^ 2

noncomputable def P (t : ℝ) : ℝ := Y S t ^ (-S.e)

noncomputable def dP (t : ℝ) : ℝ := -S.e * (dm t / S.th ^ 2) * Y S t ^ (-S.e - 1)

lemma Y_ge_one (t : ℝ) : 1 ≤ Y S t := by
  unfold Y
  have := m_nonneg t
  have := S.hth
  have : 0 ≤ m t / S.th ^ 2 := by positivity
  linarith

lemma Y_pos (t : ℝ) : 0 < Y S t := lt_of_lt_of_le one_pos (Y_ge_one S t)

lemma Y_hasDerivAt (t : ℝ) : HasDerivAt (Y S) (dm t / S.th ^ 2) t := by
  have h := ((m_hasDerivAt t).div_const (S.th ^ 2)).const_add 1
  exact h

lemma P_hasDerivAt (t : ℝ) : HasDerivAt (P S) (dP S t) t := by
  have h : HasDerivAt (P S) (dm t / S.th ^ 2 * -S.e * Y S t ^ (-S.e - 1)) t :=
    (Y_hasDerivAt S t).rpow_const (p := -S.e) (Or.inl (Y_pos S t).ne')
  convert h using 1
  unfold dP
  ring

lemma P_pos (t : ℝ) : 0 < P S t := Real.rpow_pos_of_pos (Y_pos S t) _

lemma P_le_one (t : ℝ) : P S t ≤ 1 := by
  unfold P
  exact Real.rpow_le_one_of_one_le_of_nonpos (Y_ge_one S t) (by have := S.e_pos; linarith)

lemma P_of_abs_le {t : ℝ} (h : |t| ≤ 1) : P S t = 1 := by
  unfold P Y
  rw [m_of_abs_le h]
  simp

lemma P_pow (t : ℝ) : P S t ^ (2 - S.th) = P S t * Y S t ^ (-(1 / 2 : ℝ)) := by
  unfold P
  rw [← Real.rpow_mul (Y_pos S t).le, ← Real.rpow_add (Y_pos S t)]
  congr 1
  have := S.e_key
  linarith

lemma dP_abs (t : ℝ) : |dP S t| ≤ 2 / S.th * P S t ^ (2 - S.th) := by
  have hY := Y_pos S t
  have hth := S.hth
  have he := S.e_pos
  have he1 := S.e_le_one
  have hq : |dm t| / S.th ≤ 2 * Real.sqrt (Y S t) := by
    have h1 : (|dm t| / S.th) ^ 2 ≤ (2 * Real.sqrt (Y S t)) ^ 2 := by
      rw [div_pow, sq_abs, dm_sq, mul_pow, Real.sq_sqrt hY.le]
      unfold Y
      have hm := m_nonneg t
      have : 4 * m t / S.th ^ 2 = 4 * (m t / S.th ^ 2) := by ring
      rw [this]
      nlinarith [div_nonneg hm (sq_nonneg S.th)]
    exact le_of_sq_le_sq h1 (by positivity)
  have hsq : Real.sqrt (Y S t) = Y S t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (Y S t)
  have hsplit : Y S t ^ (-S.e - 1) * Y S t ^ (1 / 2 : ℝ) =
      P S t * Y S t ^ (-(1 / 2 : ℝ)) := by
    unfold P
    rw [← Real.rpow_add hY, ← Real.rpow_add hY]
    congr 1
    ring
  have hpow0 : 0 ≤ Y S t ^ (-S.e - 1) := (Real.rpow_pos_of_pos hY _).le
  have habs : |dP S t| = S.e / S.th * (|dm t| / S.th) * Y S t ^ (-S.e - 1) := by
    unfold dP
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos he, abs_div, abs_of_nonneg hpow0,
      abs_of_pos (by positivity : (0 : ℝ) < S.th ^ 2)]
    field_simp
  rw [habs, P_pow, ← hsplit]
  have hc : S.e / S.th ≤ 1 / S.th := by gcongr
  calc S.e / S.th * (|dm t| / S.th) * Y S t ^ (-S.e - 1)
      ≤ 1 / S.th * (2 * Real.sqrt (Y S t)) * Y S t ^ (-S.e - 1) := by
        gcongr
    _ = 2 / S.th * (Y S t ^ (-S.e - 1) * Y S t ^ (1 / 2 : ℝ)) := by rw [hsq]; ring

noncomputable def gv (y : ℝ) : ℝ := (rr (y - S.v) - rr (y - 3 * S.v)) / (2 * S.v)

noncomputable def dgv (y : ℝ) : ℝ := (pos (y - S.v) - pos (y - 3 * S.v)) / (2 * S.v)

lemma gv_hasDerivAt (y : ℝ) : HasDerivAt (gv S) (dgv S y) y := by
  have h1 : HasDerivAt (fun s => rr (s - S.v)) (pos (y - S.v)) y := by
    have := (rr_hasDerivAt (y - S.v)).comp y ((hasDerivAt_id y).sub_const S.v)
    simp only [mul_one] at this
    exact this
  have h2 : HasDerivAt (fun s => rr (s - 3 * S.v)) (pos (y - 3 * S.v)) y := by
    have := (rr_hasDerivAt (y - 3 * S.v)).comp y ((hasDerivAt_id y).sub_const (3 * S.v))
    simp only [mul_one] at this
    exact this
  exact (h1.sub h2).div_const (2 * S.v)

lemma dgv_nonneg (y : ℝ) : 0 ≤ dgv S y := by
  have hv := S.v_pos
  unfold dgv
  apply div_nonneg _ (by positivity)
  simp only [pos, max_def]
  split_ifs <;> linarith

lemma dgv_le_one (y : ℝ) : dgv S y ≤ 1 := by
  have hv := S.v_pos
  unfold dgv
  rw [div_le_one (by positivity)]
  simp only [pos, max_def]
  split_ifs <;> linarith

lemma gv_of_le {y : ℝ} (h : y ≤ S.v) : gv S y = 0 := by
  have hv := S.v_pos
  unfold gv
  rw [rr_of_nonpos (by linarith), rr_of_nonpos (by linarith)]
  simp

lemma dgv_of_le {y : ℝ} (h : y ≤ S.v) : dgv S y = 0 := by
  have hv := S.v_pos
  unfold dgv
  rw [pos_of_nonpos (by linarith), pos_of_nonpos (by linarith)]
  simp

lemma gv_of_ge {y : ℝ} (h : 3 * S.v ≤ y) : gv S y = y - 2 * S.v := by
  have hv := S.v_pos
  unfold gv
  rw [rr_of_nonneg (by linarith), rr_of_nonneg (by linarith)]
  field_simp
  ring

lemma dgv_of_ge {y : ℝ} (h : 3 * S.v ≤ y) : dgv S y = 1 := by
  have hv := S.v_pos
  unfold dgv
  rw [pos_of_nonneg (by linarith), pos_of_nonneg (by linarith)]
  field_simp
  ring

lemma gv_monotone : Monotone (gv S) :=
  monotone_of_deriv_nonneg (fun y => (gv_hasDerivAt S y).differentiableAt)
    (fun y => by rw [(gv_hasDerivAt S y).deriv]; exact dgv_nonneg S y)

lemma gv_nonneg (y : ℝ) : 0 ≤ gv S y := by
  rcases le_total y S.v with h | h
  · rw [gv_of_le S h]
  · have := gv_monotone S h
    rwa [gv_of_le S le_rfl] at this

lemma gv_le_self {y : ℝ} (hy : 0 ≤ y) : gv S y ≤ y := by
  have hv := S.v_pos
  rcases le_total y (3 * S.v) with h | h
  · have h1 := gv_monotone S h
    rw [gv_of_ge S le_rfl] at h1
    rcases le_total y S.v with h2 | h2
    · rw [gv_of_le S h2]; exact hy
    · unfold gv
      rw [rr_of_nonneg (by linarith), rr_of_nonpos (by linarith), sub_zero,
        div_le_iff₀ (by positivity)]
      nlinarith
  · rw [gv_of_ge S h]; linarith

noncomputable def dphi (t : ℝ) : ℝ := gv S (P S t) / (1 - 2 * S.v)

noncomputable def ddphi (t : ℝ) : ℝ := dgv S (P S t) * dP S t / (1 - 2 * S.v)

lemma one_sub_two_v : 11 / 12 ≤ 1 - 2 * S.v := by have := S.v_le; linarith

lemma dphi_hasDerivAt (t : ℝ) : HasDerivAt (dphi S) (ddphi S t) t := by
  have h := ((gv_hasDerivAt S (P S t)).comp t (P_hasDerivAt S t)).div_const (1 - 2 * S.v)
  exact h

lemma dphi_nonneg (t : ℝ) : 0 ≤ dphi S t := by
  unfold dphi
  have := one_sub_two_v S
  exact div_nonneg (gv_nonneg S _) (by linarith)

lemma dphi_le_one (t : ℝ) : dphi S t ≤ 1 := by
  unfold dphi
  have h := one_sub_two_v S
  rw [div_le_one (by linarith)]
  have h1 := gv_monotone S (P_le_one S t)
  have hv := S.v_le
  have hv0 := S.v_pos
  rw [gv_of_ge S (by linarith : 3 * S.v ≤ 1)] at h1
  exact h1

lemma dphi_of_abs_le {t : ℝ} (h : |t| ≤ 1) : dphi S t = 1 := by
  unfold dphi
  have h1 := one_sub_two_v S
  have hv := S.v_le
  have hv0 := S.v_pos
  rw [P_of_abs_le S h, gv_of_ge S (by linarith : 3 * S.v ≤ 1), div_self (by linarith)]

lemma dphi_le_two_P (t : ℝ) : dphi S t ≤ 2 * P S t := by
  unfold dphi
  have h := one_sub_two_v S
  rw [div_le_iff₀ (by linarith)]
  have h1 := gv_le_self S (P_pos S t).le
  have h2 := P_pos S t
  nlinarith

lemma P_le_v {t : ℝ} (h : S.tEnd ≤ |t|) : P S t ≤ S.v := by
  have hth := S.hth
  have hmu := S.hmu
  have hv := S.v_pos
  have hv1 : S.v ≤ 1 := by have := S.v_le; linarith
  have ha : (0 : ℝ) ≤ S.th / S.v := by positivity
  have hle : 1 + S.th / S.v ≤ |t| := by
    refine le_trans (le_of_eq ?_) h
    unfold Shape.tEnd Shape.v
    field_simp
  have hm := m_ge_of_le ha hle
  have hY : (1 / S.v) ^ 2 ≤ Y S t := by
    unfold Y
    have e1 : (1 / S.v) ^ 2 = (S.th / S.v) ^ 2 / S.th ^ 2 := by field_simp
    rw [e1]
    have : (S.th / S.v) ^ 2 / S.th ^ 2 ≤ m t / S.th ^ 2 := by gcongr
    linarith
  have hY1 : 1 / S.v ≤ Y S t := by
    have h1 : (1 : ℝ) ≤ 1 / S.v := by rw [le_div_iff₀ hv]; linarith
    nlinarith
  have he := S.e_gt_half
  have he1 := S.e_le_one
  unfold P
  rw [Real.rpow_neg (Y_pos S t).le, inv_le_comm₀ (Real.rpow_pos_of_pos (Y_pos S t) _) hv]
  have h2 : S.v⁻¹ ≤ Real.sqrt (Y S t) := by
    rw [← one_div]
    apply Real.le_sqrt_of_sq_le
    exact hY
  calc S.v⁻¹ ≤ Real.sqrt (Y S t) := h2
    _ = Y S t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    _ ≤ Y S t ^ S.e := Real.rpow_le_rpow_of_exponent_le (Y_ge_one S t) he.le

lemma dphi_of_ge {t : ℝ} (h : S.tEnd ≤ |t|) : dphi S t = 0 := by
  unfold dphi
  rw [gv_of_le S (P_le_v S h), zero_div]

lemma ddphi_of_ge {t : ℝ} (h : S.tEnd ≤ |t|) : ddphi S t = 0 := by
  unfold ddphi
  rw [dgv_of_le S (P_le_v S h), zero_mul, zero_div]

lemma ddphi_abs_le (t : ℝ) : |ddphi S t| ≤ 4 / S.th := by
  have h := one_sub_two_v S
  have hth := S.hth
  have h1 := dP_abs S t
  have hP : P S t ^ (2 - S.th) ≤ 1 :=
    Real.rpow_le_one (P_pos S t).le (P_le_one S t) (by have := S.hth'; linarith)
  have h2 : |dP S t| ≤ 2 / S.th := by
    calc _ ≤ 2 / S.th * P S t ^ (2 - S.th) := h1
      _ ≤ 2 / S.th * 1 := by gcongr
      _ = _ := by ring
  unfold ddphi
  rw [abs_div, abs_mul, abs_of_nonneg (dgv_nonneg S _), abs_of_pos (by linarith : 0 < 1 - 2 * S.v),
    div_le_iff₀ (by linarith)]
  have h3 := dgv_le_one S (P S t)
  have h4 := dgv_nonneg S (P S t)
  have h5 : (0 : ℝ) < 4 / S.th := by positivity
  calc dgv S (P S t) * |dP S t| ≤ 1 * (2 / S.th) := by gcongr
    _ ≤ 4 / S.th * (1 - 2 * S.v) := by
      have : 2 / S.th = 4 / S.th * (1 / 2) := by ring
      rw [one_mul, this]
      gcongr
      linarith

lemma ddphi_relative (t : ℝ) : |ddphi S t| ≤ 36 / S.th * dphi S t ^ (2 - S.th) + S.mu := by
  have h := one_sub_two_v S
  have hth := S.hth
  have hth' := S.hth'
  have hv := S.v_pos
  have hP := P_pos S t
  have hP1 := P_le_one S t
  have h1 := dP_abs S t
  have hexp : (0 : ℝ) ≤ 2 - S.th := by linarith
  have habs : |ddphi S t| = dgv S (P S t) * |dP S t| / (1 - 2 * S.v) := by
    unfold ddphi
    rw [abs_div, abs_mul, abs_of_nonneg (dgv_nonneg S _),
      abs_of_pos (by linarith : 0 < 1 - 2 * S.v)]
  have hd0 := dgv_nonneg S (P S t)
  have hd1 := dgv_le_one S (P S t)
  have hbase : |ddphi S t| ≤ 4 / S.th * (dgv S (P S t) * P S t ^ (2 - S.th)) := by
    rw [habs, div_le_iff₀ (by linarith)]
    have hpp : 0 ≤ P S t ^ (2 - S.th) := (Real.rpow_pos_of_pos hP _).le
    calc dgv S (P S t) * |dP S t| ≤ dgv S (P S t) * (2 / S.th * P S t ^ (2 - S.th)) := by gcongr
      _ = 4 / S.th * (dgv S (P S t) * P S t ^ (2 - S.th)) * (1 / 2) := by ring
      _ ≤ 4 / S.th * (dgv S (P S t) * P S t ^ (2 - S.th)) * (1 - 2 * S.v) := by
        gcongr
        linarith
  rcases le_total (3 * S.v) (P S t) with h3 | h3
  · have hg : gv S (P S t) = P S t - 2 * S.v := gv_of_ge S h3
    have hdp : P S t ≤ 3 * dphi S t := by
      unfold dphi
      rw [hg, ← mul_div_assoc, le_div_iff₀ (by linarith)]
      nlinarith
    have hdn := dphi_nonneg S t
    have hpow : P S t ^ (2 - S.th) ≤ 9 * dphi S t ^ (2 - S.th) := by
      calc P S t ^ (2 - S.th) ≤ (3 * dphi S t) ^ (2 - S.th) :=
            Real.rpow_le_rpow hP.le hdp hexp
        _ = 3 ^ (2 - S.th) * dphi S t ^ (2 - S.th) :=
            Real.mul_rpow (by norm_num) hdn
        _ ≤ 9 * dphi S t ^ (2 - S.th) := by
            gcongr
            calc (3 : ℝ) ^ (2 - S.th) ≤ 3 ^ (2 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
              _ = 9 := by norm_num
    have hmu := S.hmu
    calc |ddphi S t| ≤ 4 / S.th * (dgv S (P S t) * P S t ^ (2 - S.th)) := hbase
      _ ≤ 4 / S.th * (1 * (9 * dphi S t ^ (2 - S.th))) := by gcongr
      _ = 36 / S.th * dphi S t ^ (2 - S.th) := by ring
      _ ≤ _ := by linarith
  · have hpow : P S t ^ (2 - S.th) ≤ 3 * S.v := by
      calc P S t ^ (2 - S.th) ≤ P S t ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hP hP1 (by linarith)
        _ = P S t := Real.rpow_one _
        _ ≤ 3 * S.v := h3
    have hdn : 0 ≤ dphi S t ^ (2 - S.th) := Real.rpow_nonneg (dphi_nonneg S t) _
    have hpp : 0 ≤ P S t ^ (2 - S.th) := (Real.rpow_pos_of_pos hP _).le
    calc |ddphi S t| ≤ 4 / S.th * (dgv S (P S t) * P S t ^ (2 - S.th)) := hbase
      _ ≤ 4 / S.th * (1 * (3 * S.v)) := by gcongr
      _ = S.mu := by unfold Shape.v; field_simp; ring
      _ ≤ _ := by
        have : 0 ≤ 36 / S.th * dphi S t ^ (2 - S.th) := by positivity
        linarith

lemma dphi_continuous : Continuous (dphi S) :=
  continuous_iff_continuousAt.mpr (fun t => (dphi_hasDerivAt S t).continuousAt)

noncomputable def phi (t : ℝ) : ℝ := ∫ s in (-S.tEnd)..t, dphi S s

lemma phi_hasDerivAt (t : ℝ) : HasDerivAt (phi S) (dphi S t) t :=
  ((dphi_continuous S).integral_hasStrictDerivAt (-S.tEnd) t).hasDerivAt

lemma phi_monotone : Monotone (phi S) :=
  monotone_of_deriv_nonneg (fun t => (phi_hasDerivAt S t).differentiableAt)
    (fun t => by rw [(phi_hasDerivAt S t).deriv]; exact dphi_nonneg S t)

lemma phi_of_le {t : ℝ} (h : t ≤ -S.tEnd) : phi S t = 0 := by
  unfold phi
  rw [intervalIntegral.integral_symm]
  have hz : ∀ s ∈ Set.uIcc t (-S.tEnd), dphi S s = 0 := by
    intro s hs
    rw [Set.uIcc_of_le h] at hs
    apply dphi_of_ge
    have ht := S.tEnd_pos
    rw [abs_of_nonpos (by linarith [hs.2])]
    linarith [hs.2]
  rw [intervalIntegral.integral_congr hz]
  simp

lemma phi_nonneg (t : ℝ) : 0 ≤ phi S t := by
  rcases le_total t (-S.tEnd) with h | h
  · rw [phi_of_le S h]
  · have := phi_monotone S h
    rwa [phi_of_le S le_rfl] at this

lemma phi_lipschitz (x y : ℝ) : |phi S x - phi S y| ≤ |x - y| := by
  have h := lipschitz_of_deriv (phi S) (dphi S) 1 (phi_hasDerivAt S)
    (fun z => by rw [abs_of_nonneg (dphi_nonneg S z)]; exact dphi_le_one S z) x y
  simpa using h

noncomputable def tailBound (p : ℝ) : ℝ := (1 + p / S.th) ^ (1 - 2 * S.e)

lemma tail_compare {t p : ℝ} (hp : 0 ≤ p) (h : m t = p ^ 2) :
    dphi S t ≤ 4 * (1 + p / S.th) ^ (-(2 * S.e)) := by
  have hth := S.hth
  have he := S.e_pos
  have he1 := S.e_le_one
  have hZ : (0 : ℝ) < 1 + p / S.th := by positivity
  have hY : Y S t = 1 + (p / S.th) ^ 2 := by unfold Y; rw [h]; ring
  have hsq : (1 + p / S.th) ^ 2 ≤ 2 * Y S t := by
    rw [hY]
    nlinarith [sq_nonneg (1 - p / S.th)]
  have h1 : (2 * Y S t) ^ (-S.e) ≤ ((1 + p / S.th) ^ 2) ^ (-S.e) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hsq (by linarith)
  have h2 : ((1 + p / S.th) ^ 2) ^ (-S.e) = (1 + p / S.th) ^ (-(2 * S.e)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  have h3 : (2 * Y S t) ^ (-S.e) = 2 ^ (-S.e) * P S t := by
    unfold P
    exact Real.mul_rpow (by norm_num) (Y_pos S t).le
  have h4 : (1 / 2 : ℝ) ≤ 2 ^ (-S.e) := by
    calc (1 / 2 : ℝ) = 2 ^ (-1 : ℝ) := by norm_num
      _ ≤ 2 ^ (-S.e) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hP := P_pos S t
  have h5 : P S t ≤ 2 * (1 + p / S.th) ^ (-(2 * S.e)) := by
    rw [← h2]
    have : 2 ^ (-S.e) * P S t ≤ ((1 + p / S.th) ^ 2) ^ (-S.e) := by rw [← h3]; exact h1
    nlinarith
  have h6 := dphi_le_two_P S t
  linarith

lemma tailBound_hasDerivAt (a : ℝ) (σ : ℝ) {t : ℝ} (hpos : 0 < 1 + (σ * t - a) / S.th) :
    HasDerivAt (fun s => (1 + (σ * s - a) / S.th) ^ (1 - 2 * S.e))
      ((1 - 2 * S.e) * (σ / S.th) * (1 + (σ * t - a) / S.th) ^ (-(2 * S.e))) t := by
  have hin : HasDerivAt (fun s => 1 + (σ * s - a) / S.th) (σ / S.th) t := by
    have := ((((hasDerivAt_id t).const_mul σ).sub_const a).div_const S.th).const_add 1
    simpa using this
  have h := hin.rpow_const (p := 1 - 2 * S.e) (Or.inl hpos.ne')
  convert h using 1
  have : 1 - 2 * S.e - 1 = -(2 * S.e) := by ring
  rw [this]
  ring

lemma phi_neg_one_le : phi S (-1) ≤ 4 := by
  have hth := S.hth
  have hth' := S.hth'
  have he := S.e_gt_half
  have he1 := S.e_le_one
  have hc : 0 < 2 * S.e - 1 := by linarith
  have hcth : S.th / (2 * S.e - 1) ≤ 1 := by
    rw [div_le_one hc]
    unfold Shape.e
    have h1 := S.one_sub_pos
    rw [show 2 * (1 / (2 * (1 - S.th))) - 1 = S.th / (1 - S.th) by field_simp; ring]
    rw [le_div_iff₀ h1]
    nlinarith
  let C : ℝ := 4 * S.th / (2 * S.e - 1)
  let D : ℝ → ℝ := fun t => C * (1 + (-1 * t - 1) / S.th) ^ (1 - 2 * S.e) - phi S t
  have hD : MonotoneOn D (Set.Iic (-1)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iic _)
    · apply ContinuousOn.sub
      · apply ContinuousOn.mul continuousOn_const
        intro t ht
        have hpos : 0 < 1 + (-1 * t - 1) / S.th := by
          have : 0 ≤ (-1 * t - 1) / S.th := div_nonneg (by simp at ht; linarith) hth.le
          linarith
        exact (tailBound_hasDerivAt S 1 (-1) hpos).continuousAt.continuousWithinAt
      · exact (continuous_iff_continuousAt.mpr
          (fun t => (phi_hasDerivAt S t).continuousAt)).continuousOn
    · intro t ht
      rw [interior_Iic] at ht
      have hpos : 0 < 1 + (-1 * t - 1) / S.th := by
        have : 0 ≤ (-1 * t - 1) / S.th := div_nonneg (by simp at ht; linarith) hth.le
        linarith
      exact (((tailBound_hasDerivAt S 1 (-1) hpos).const_mul C).sub
        (phi_hasDerivAt S t)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Iic] at ht
      have ht' : t < -1 := ht
      have hpos : 0 < 1 + (-1 * t - 1) / S.th := by
        have : 0 ≤ (-1 * t - 1) / S.th := div_nonneg (by linarith) hth.le
        linarith
      have hd : HasDerivAt D (C * ((1 - 2 * S.e) * (-1 / S.th) *
          (1 + (-1 * t - 1) / S.th) ^ (-(2 * S.e))) - dphi S t) t :=
        ((tailBound_hasDerivAt S 1 (-1) hpos).const_mul C).sub (phi_hasDerivAt S t)
      rw [hd.deriv]
      have hm : m t = (-1 * t - 1) ^ 2 := by
        unfold m
        rw [rr_of_nonpos (by linarith), rr_of_nonneg (by linarith)]
        ring
      have hcmp := tail_compare S (by linarith : (0 : ℝ) ≤ -1 * t - 1) hm
      have hcoef : C * ((1 - 2 * S.e) * (-1 / S.th) *
          (1 + (-1 * t - 1) / S.th) ^ (-(2 * S.e))) =
          4 * (1 + (-1 * t - 1) / S.th) ^ (-(2 * S.e)) := by
        simp only [C]
        field_simp
        ring
      rw [hcoef]
      linarith
  have ht0 := S.tEnd_ge
  have hmem1 : (-S.tEnd) ∈ Set.Iic (-1 : ℝ) := by simp; linarith
  have hmem2 : (-1 : ℝ) ∈ Set.Iic (-1 : ℝ) := by simp
  have hmono := hD hmem1 hmem2 (by linarith)
  simp only [D] at hmono
  rw [phi_of_le S le_rfl] at hmono
  have hend : (0 : ℝ) ≤ C * (1 + (-1 * -S.tEnd - 1) / S.th) ^ (1 - 2 * S.e) := by
    have : (0 : ℝ) < 1 + (-1 * -S.tEnd - 1) / S.th := by
      have : (0 : ℝ) ≤ (-1 * -S.tEnd - 1) / S.th := div_nonneg (by linarith) hth.le
      linarith
    have hC : 0 ≤ C := by simp only [C]; positivity
    exact mul_nonneg hC (Real.rpow_pos_of_pos this _).le
  have h1 : (1 + (-1 * (-1 : ℝ) - 1) / S.th) ^ (1 - 2 * S.e) = 1 := by
    norm_num
  rw [h1] at hmono
  have hC4 : C ≤ 4 := by
    simp only [C]
    calc 4 * S.th / (2 * S.e - 1) = 4 * (S.th / (2 * S.e - 1)) := by ring
      _ ≤ 4 * 1 := by gcongr
      _ = 4 := by ring
  linarith

lemma phi_one_le : phi S 1 ≤ 6 := by
  have h := phi_lipschitz S 1 (-1)
  have h4 := phi_neg_one_le S
  have h2 : |(1 : ℝ) - -1| = 2 := by norm_num
  rw [h2] at h
  have := (abs_le.mp h).2
  linarith

lemma phi_le (t : ℝ) : phi S t ≤ 10 := by
  have hth := S.hth
  have hth' := S.hth'
  have he := S.e_gt_half
  have he1 := S.e_le_one
  have hc : 0 < 2 * S.e - 1 := by linarith
  have hcth : S.th / (2 * S.e - 1) ≤ 1 := by
    rw [div_le_one hc]
    unfold Shape.e
    have h1 := S.one_sub_pos
    rw [show 2 * (1 / (2 * (1 - S.th))) - 1 = S.th / (1 - S.th) by field_simp; ring]
    rw [le_div_iff₀ h1]
    nlinarith
  rcases le_total t 1 with ht | ht
  · have := phi_monotone S ht
    have := phi_one_le S
    linarith
  let C : ℝ := 4 * S.th / (2 * S.e - 1)
  let D : ℝ → ℝ := fun t => phi S t + C * (1 + (1 * t - 1) / S.th) ^ (1 - 2 * S.e)
  have hD : AntitoneOn D (Set.Ici 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · apply ContinuousOn.add
      · exact (continuous_iff_continuousAt.mpr
          (fun t => (phi_hasDerivAt S t).continuousAt)).continuousOn
      · apply ContinuousOn.mul continuousOn_const
        intro t ht
        have hpos : 0 < 1 + (1 * t - 1) / S.th := by
          have : 0 ≤ (1 * t - 1) / S.th := div_nonneg (by simp at ht; linarith) hth.le
          linarith
        exact (tailBound_hasDerivAt S 1 1 hpos).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have hpos : 0 < 1 + (1 * t - 1) / S.th := by
        have : 0 ≤ (1 * t - 1) / S.th := div_nonneg (by simp at ht; linarith) hth.le
        linarith
      exact ((phi_hasDerivAt S t).add
        ((tailBound_hasDerivAt S 1 1 hpos).const_mul C)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht' : 1 < t := ht
      have hpos : 0 < 1 + (1 * t - 1) / S.th := by
        have : 0 ≤ (1 * t - 1) / S.th := div_nonneg (by linarith) hth.le
        linarith
      have hd : HasDerivAt D (dphi S t + C * ((1 - 2 * S.e) * (1 / S.th) *
          (1 + (1 * t - 1) / S.th) ^ (-(2 * S.e)))) t :=
        (phi_hasDerivAt S t).add ((tailBound_hasDerivAt S 1 1 hpos).const_mul C)
      rw [hd.deriv]
      have hm : m t = (1 * t - 1) ^ 2 := by
        unfold m
        rw [rr_of_nonneg (by linarith), rr_of_nonpos (by linarith)]
        ring
      have hcmp := tail_compare S (by linarith : (0 : ℝ) ≤ 1 * t - 1) hm
      have hcoef : C * ((1 - 2 * S.e) * (1 / S.th) *
          (1 + (1 * t - 1) / S.th) ^ (-(2 * S.e))) =
          -(4 * (1 + (1 * t - 1) / S.th) ^ (-(2 * S.e))) := by
        simp only [C]
        field_simp
        ring
      rw [hcoef]
      linarith
  have hmem1 : (1 : ℝ) ∈ Set.Ici (1 : ℝ) := by simp
  have hmem2 : t ∈ Set.Ici (1 : ℝ) := ht
  have hanti := hD hmem1 hmem2 ht
  simp only [D] at hanti
  have h1 : (1 + (1 * (1 : ℝ) - 1) / S.th) ^ (1 - 2 * S.e) = 1 := by norm_num
  rw [h1] at hanti
  have hend : (0 : ℝ) ≤ C * (1 + (1 * t - 1) / S.th) ^ (1 - 2 * S.e) := by
    have : (0 : ℝ) < 1 + (1 * t - 1) / S.th := by
      have : (0 : ℝ) ≤ (1 * t - 1) / S.th := div_nonneg (by linarith) hth.le
      linarith
    have hC : 0 ≤ C := by simp only [C]; positivity
    exact mul_nonneg hC (Real.rpow_pos_of_pos this _).le
  have hC4 : C ≤ 4 := by
    simp only [C]
    calc 4 * S.th / (2 * S.e - 1) = 4 * (S.th / (2 * S.e - 1)) := by ring
      _ ≤ 4 * 1 := by gcongr
      _ = 4 := by ring
  have := phi_one_le S
  linarith

end LongTails.Proofs.EllSmoothProfiles
