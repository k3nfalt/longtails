import LongTails.Algorithms.AffineSoftmaxRadius
import LongTails.Proofs.AffineSoftmaxCostParameters

namespace LongTails.Proofs.AffineSoftmaxRadius

open LongTails.Algorithms.AffineSoftmaxRadius

lemma radiusFactor_ge_one (m a b ell : ℝ) : 1 ≤ radiusFactor m a b ell := le_max_left _ _

lemma radiusFactor_ge_sqrt (m a b ell : ℝ) : Real.sqrt (8 * b * ell) ≤ radiusFactor m a b ell :=
  (le_max_left _ _).trans (le_max_right _ _)

lemma radiusFactor_ge_first (m a b ell : ℝ) : (64 * b ^ 2 / m) ^ (3 / 8 : ℝ) ≤ radiusFactor m a b ell :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

lemma radiusFactor_ge_second (m a b ell : ℝ) :
    (1024 * a ^ 2 * b ^ 2 * ell ^ 2 / m) ^ (3 / 14 : ℝ) ≤ radiusFactor m a b ell :=
  (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

lemma publicRadius_bounds {m : ℕ} {G L R ε : ℝ} (hR : 0 < R) :
    0 < publicRadius m G L R ε ∧ publicRadius m G L R ε ≤ 2 * R := by
  have hz := radiusFactor_ge_one (m : ℝ) (G * R / ε) (L * R ^ 2 / ε) (Real.log m)
  have hzp : 0 < radiusFactor (m : ℝ) (G * R / ε) (L * R ^ 2 / ε) (Real.log m) := zero_lt_one.trans_le hz
  exact ⟨div_pos (by positivity) hzp, div_le_self (by positivity) hz⟩

lemma public_temperature_pos {m : ℕ} (hm : 2 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    0 < ε / (2 * Real.log m) := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hl := Real.log_pos hm1
  positivity

lemma publicRadius_local {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hL : 0 ≤ L) (hε : 0 < ε) :
    L * (publicRadius m G L R ε) ^ 2 ≤ ε / (2 * Real.log m) := by
  let z := radiusFactor (m : ℝ) (G * R / ε) (L * R ^ 2 / ε) (Real.log m)
  have hz : 0 < z := zero_lt_one.trans_le (radiusFactor_ge_one _ _ _ _)
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hl := Real.log_pos hm1
  have hs := radiusFactor_ge_sqrt (m : ℝ) (G * R / ε) (L * R ^ 2 / ε) (Real.log m)
  have hs0 := Real.sqrt_nonneg (8 * (L * R ^ 2 / ε) * Real.log m)
  have hsq := Real.sq_sqrt (show 0 ≤ 8 * (L * R ^ 2 / ε) * Real.log m by positivity)
  have hb : 8 * (L * R ^ 2 / ε) * Real.log m ≤ z ^ 2 := by nlinarith
  have he : L * (publicRadius m G L R ε) ^ 2 = 4 * L * R ^ 2 / z ^ 2 := by
    change L * (2 * R / z) ^ 2 = _
    field_simp
    ring
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos hz) (by positivity : 0 < 2 * Real.log m)).2
  have hh := (div_le_iff₀ hε).1 (show 8 * L * R ^ 2 * Real.log m / ε ≤ z ^ 2 by convert hb using 1; ring)
  nlinarith only [hh]

lemma radiusFactor_balance {m a b ell : ℝ} (hm : 0 < m) :
    let z := radiusFactor m a b ell
    64 * b ^ 2 / z ^ 2 ≤ m * z ^ (2 / 3 : ℝ) ∧
      1024 * a ^ 2 * b ^ 2 * ell ^ 2 / z ^ 4 ≤ m * z ^ (2 / 3 : ℝ) := by
  let z := radiusFactor m a b ell
  have hz : 0 < z := zero_lt_one.trans_le (radiusFactor_ge_one _ _ _ _)
  have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity : 0 ≤ 64 * b ^ 2 / m) _)
    (radiusFactor_ge_first m a b ell) (by norm_num : (0 : ℝ) ≤ 8 / 3)
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity : 0 ≤ 1024 * a ^ 2 * b ^ 2 * ell ^ 2 / m) _)
    (radiusFactor_ge_second m a b ell) (by norm_num : (0 : ℝ) ≤ 14 / 3)
  rw [← Real.rpow_mul (by positivity : 0 ≤ 64 * b ^ 2 / m)] at h1
  rw [← Real.rpow_mul (by positivity : 0 ≤ 1024 * a ^ 2 * b ^ 2 * ell ^ 2 / m)] at h2
  norm_num only [show (3 / 8 : ℝ) * (8 / 3) = 1 by norm_num, show (3 / 14 : ℝ) * (14 / 3) = 1 by norm_num, Real.rpow_one] at h1 h2
  have he1 : z ^ (8 / 3 : ℝ) = z ^ 2 * z ^ (2 / 3 : ℝ) := by
    rw [show (8 / 3 : ℝ) = 2 + 2 / 3 by norm_num, Real.rpow_add hz, Real.rpow_two]
  have he2 : z ^ (14 / 3 : ℝ) = z ^ 4 * z ^ (2 / 3 : ℝ) := by
    rw [show (14 / 3 : ℝ) = 4 + 2 / 3 by norm_num, Real.rpow_add hz]
    norm_num
  change 64 * b ^ 2 / m ≤ z ^ (8 / 3 : ℝ) at h1
  change 1024 * a ^ 2 * b ^ 2 * ell ^ 2 / m ≤ z ^ (14 / 3 : ℝ) at h2
  rw [he1] at h1
  rw [he2] at h2
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hz)).2
    have hh := (div_le_iff₀ hm).1 h1
    nlinarith only [hh]
  · apply (div_le_iff₀ (pow_pos hz 4)).2
    have hh := (div_le_iff₀ hm).1 h2
    nlinarith only [hh]

lemma mass_rpow_div {m A : ℝ} (hm : 0 < m) (hA : 0 ≤ A) (p : ℝ) :
    m * (A / m) ^ p = m ^ (1 - p) * A ^ p := by
  rw [Real.div_rpow hA hm.le, Real.rpow_sub hm, Real.rpow_one]
  ring

lemma radiusFactor_work_identity {m a b ell : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (hb : 0 ≤ b) (hell : 0 ≤ ell) :
    m * (radiusFactor m a b ell) ^ (2 / 3 : ℝ) =
      max m (max (2 * m * b ^ (1 / 3 : ℝ) * ell ^ (1 / 3 : ℝ))
        (max ((64 : ℝ) ^ (1 / 4 : ℝ) * m ^ (3 / 4 : ℝ) * Real.sqrt b)
          ((1024 : ℝ) ^ (1 / 7 : ℝ) * m ^ (6 / 7 : ℝ) * (a * b) ^ (2 / 7 : ℝ) * ell ^ (2 / 7 : ℝ)))) := by
  have hfirst : m * (Real.sqrt (8 * b * ell)) ^ (2 / 3 : ℝ) =
      2 * m * b ^ (1 / 3 : ℝ) * ell ^ (1 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ 8 * b * ell)]
    norm_num only [show (1 / 2 : ℝ) * (2 / 3) = 1 / 3 by norm_num]
    rw [Real.mul_rpow (by positivity : 0 ≤ 8 * b) hell, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hb]
    have he : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [he]
    ring
  have hsecond : m * ((64 * b ^ 2 / m) ^ (3 / 8 : ℝ)) ^ (2 / 3 : ℝ) =
      (64 : ℝ) ^ (1 / 4 : ℝ) * m ^ (3 / 4 : ℝ) * Real.sqrt b := by
    rw [← Real.rpow_mul (by positivity : 0 ≤ 64 * b ^ 2 / m)]
    norm_num only [show (3 / 8 : ℝ) * (2 / 3) = 1 / 4 by norm_num]
    rw [mass_rpow_div hm (by positivity), Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 64) (sq_nonneg b)]
    have he : (b ^ 2) ^ (1 / 4 : ℝ) = Real.sqrt b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb, Real.sqrt_eq_rpow]
      norm_num
    rw [he]
    norm_num only [show (1 - 1 / 4 : ℝ) = 3 / 4 by norm_num]
    ring
  have hthird : m * ((1024 * a ^ 2 * b ^ 2 * ell ^ 2 / m) ^ (3 / 14 : ℝ)) ^ (2 / 3 : ℝ) =
      (1024 : ℝ) ^ (1 / 7 : ℝ) * m ^ (6 / 7 : ℝ) * (a * b) ^ (2 / 7 : ℝ) * ell ^ (2 / 7 : ℝ) := by
    rw [← Real.rpow_mul (by positivity : 0 ≤ 1024 * a ^ 2 * b ^ 2 * ell ^ 2 / m)]
    norm_num only [show (3 / 14 : ℝ) * (2 / 3) = 1 / 7 by norm_num]
    rw [mass_rpow_div hm (by positivity)]
    have he : (1024 * a ^ 2 * b ^ 2 * ell ^ 2) ^ (1 / 7 : ℝ) =
        (1024 : ℝ) ^ (1 / 7 : ℝ) * (a * b) ^ (2 / 7 : ℝ) * ell ^ (2 / 7 : ℝ) := by
      rw [show 1024 * a ^ 2 * b ^ 2 * ell ^ 2 = 1024 * (a * b) ^ 2 * ell ^ 2 by ring]
      rw [Real.mul_rpow (by positivity : 0 ≤ 1024 * (a * b) ^ 2) (sq_nonneg ell),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1024) (sq_nonneg (a * b))]
      have hab : ((a * b) ^ 2) ^ (1 / 7 : ℝ) = (a * b) ^ (2 / 7 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (mul_nonneg ha hb)]
        norm_num
      have hl : (ell ^ 2) ^ (1 / 7 : ℝ) = ell ^ (2 / 7 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hell]
        norm_num
      rw [hab, hl]
    rw [he]
    norm_num only [show (1 - 1 / 7 : ℝ) = 6 / 7 by norm_num]
    ring
  unfold radiusFactor
  rw [Real.rpow_max (by norm_num) (by positivity) (by norm_num),
    Real.rpow_max (Real.sqrt_nonneg _) (by positivity) (by norm_num),
    Real.rpow_max (by positivity) (by positivity) (by norm_num)]
  rw [Real.one_rpow, mul_max_of_nonneg _ _ hm.le, mul_max_of_nonneg _ _ hm.le, mul_max_of_nonneg _ _ hm.le]
  rw [mul_one, hfirst, hsecond, hthird]

lemma root_constant_bounds : (64 : ℝ) ^ (1 / 4 : ℝ) ≤ 3 ∧ (1024 : ℝ) ^ (1 / 7 : ℝ) ≤ 3 := by
  constructor
  · calc
      _ ≤ ((3 : ℝ) ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = 3 := by rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  · calc
      _ ≤ ((3 : ℝ) ^ (7 : ℝ)) ^ (1 / 7 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = 3 := by rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]; norm_num

lemma subunit_power_le {ell h p : ℝ} (hell : 0 ≤ ell) (hh : 1 ≤ h) (helh : ell ≤ h)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) : ell ^ p ≤ h :=
  (Real.rpow_le_rpow hell helh hp).trans (Real.rpow_le_self_of_one_le hh hp1)

lemma radiusFactor_work_bound {m a b ell h : ℝ} (hm : 1 ≤ m) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hell : 0 ≤ ell) (hh : 1 ≤ h) (helh : ell ≤ h) :
    m * (radiusFactor m a b ell) ^ (2 / 3 : ℝ) ≤
      3 * h * (m + m * b ^ (1 / 3 : ℝ) + m ^ (3 / 4 : ℝ) * Real.sqrt b +
        m ^ (6 / 7 : ℝ) * (a * b) ^ (2 / 7 : ℝ)) := by
  let v := m * b ^ (1 / 3 : ℝ)
  let w := m ^ (3 / 4 : ℝ) * Real.sqrt b
  let t := m ^ (6 / 7 : ℝ) * (a * b) ^ (2 / 7 : ℝ)
  let S := m + v + w + t
  have hm0 : 0 ≤ m := by linarith
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hmS : m ≤ S := by dsimp [S]; linarith
  have hvS : v ≤ S := by dsimp [S]; linarith
  have hwS : w ≤ S := by dsimp [S]; linarith
  have htS : t ≤ S := by dsimp [S]; linarith
  have he1 : ell ^ (1 / 3 : ℝ) ≤ h := subunit_power_le hell hh helh (by norm_num) (by norm_num)
  have he2 : ell ^ (2 / 7 : ℝ) ≤ h := subunit_power_le hell hh helh (by norm_num) (by norm_num)
  rw [radiusFactor_work_identity (zero_lt_one.trans_le hm) ha hb hell]
  change max m (max (2 * m * b ^ (1 / 3 : ℝ) * ell ^ (1 / 3 : ℝ))
    (max ((64 : ℝ) ^ (1 / 4 : ℝ) * m ^ (3 / 4 : ℝ) * Real.sqrt b)
      ((1024 : ℝ) ^ (1 / 7 : ℝ) * m ^ (6 / 7 : ℝ) * (a * b) ^ (2 / 7 : ℝ) * ell ^ (2 / 7 : ℝ)))) ≤ 3 * h * S
  apply max_le
  · exact hmS.trans (le_mul_of_one_le_left hS (by linarith))
  · apply max_le
    · calc
        _ = 2 * v * ell ^ (1 / 3 : ℝ) := by dsimp [v]; ring
        _ ≤ 3 * S * h := by gcongr; norm_num
        _ = _ := by ring
    · apply max_le
      · calc
          _ = (64 : ℝ) ^ (1 / 4 : ℝ) * w := by dsimp [w]; ring
          _ ≤ 3 * S := mul_le_mul root_constant_bounds.1 hwS hw (by norm_num)
          _ ≤ 3 * h * S := by nlinarith [mul_nonneg (sub_nonneg.mpr hh) hS]
      · calc
          _ = (1024 : ℝ) ^ (1 / 7 : ℝ) * t * ell ^ (2 / 7 : ℝ) := by dsimp [t]; ring
          _ ≤ 3 * S * h := by gcongr; exact root_constant_bounds.2
          _ = _ := by ring

lemma radiusFactor_polynomial_bound {m a b ell W : ℝ} (hm : 1 ≤ m) (hW : 1 ≤ W)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hell : 0 ≤ ell) (haW : a ≤ W) (hbW : b ≤ W) (hlW : ell ≤ W) :
    radiusFactor m a b ell ≤ 8 * W ^ 2 := by
  have hW0 : 0 ≤ W := by linarith
  have hW2 : 1 ≤ W ^ 2 := one_le_pow₀ hW
  have hf : Real.sqrt (8 * b * ell) ≤ 8 * W ^ 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hh : 8 * b * ell ≤ 8 * W ^ 2 := by
      calc
        _ ≤ 8 * W * W := by gcongr
        _ = _ := by ring
    nlinarith [sq_nonneg (W ^ 2 - 1)]
  have hs : (64 * b ^ 2 / m) ^ (3 / 8 : ℝ) ≤ 8 * W ^ 2 := by
    apply le_of_pow_le_pow_left₀ (show (8 : ℕ) ≠ 0 by omega) (by positivity)
    have he : ((64 * b ^ 2 / m) ^ (3 / 8 : ℝ)) ^ 8 = (64 * b ^ 2 / m) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 64 * b ^ 2 / m)]
      norm_num
    rw [he]
    have hbnd : 64 * b ^ 2 / m ≤ 64 * W ^ 2 :=
      (div_le_self (by positivity) hm).trans (by gcongr)
    calc
      _ ≤ (64 * W ^ 2) ^ 3 := by gcongr
      _ = 262144 * W ^ 6 := by ring
      _ ≤ 16777216 * W ^ 16 := mul_le_mul (by norm_num : (262144 : ℝ) ≤ 16777216)
        (pow_le_pow_right₀ hW (show 6 ≤ 16 by omega)) (by positivity) (by norm_num)
      _ = (8 * W ^ 2) ^ 8 := by ring
  have ht : (1024 * a ^ 2 * b ^ 2 * ell ^ 2 / m) ^ (3 / 14 : ℝ) ≤ 8 * W ^ 2 := by
    apply le_of_pow_le_pow_left₀ (show (14 : ℕ) ≠ 0 by omega) (by positivity)
    have he : ((1024 * a ^ 2 * b ^ 2 * ell ^ 2 / m) ^ (3 / 14 : ℝ)) ^ 14 =
        (1024 * a ^ 2 * b ^ 2 * ell ^ 2 / m) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 1024 * a ^ 2 * b ^ 2 * ell ^ 2 / m)]
      norm_num
    rw [he]
    have hbnd : 1024 * a ^ 2 * b ^ 2 * ell ^ 2 / m ≤ 1024 * W ^ 6 := by
      calc
        _ ≤ 1024 * a ^ 2 * b ^ 2 * ell ^ 2 := div_le_self (by positivity) hm
        _ ≤ 1024 * W ^ 2 * W ^ 2 * W ^ 2 := by gcongr
        _ = _ := by ring
    calc
      _ ≤ (1024 * W ^ 6) ^ 3 := by gcongr
      _ = 1073741824 * W ^ 18 := by ring
      _ ≤ 4398046511104 * W ^ 28 := mul_le_mul (by norm_num : (1073741824 : ℝ) ≤ 4398046511104)
        (pow_le_pow_right₀ hW (show 18 ≤ 28 by omega)) (by positivity) (by norm_num)
      _ = (8 * W ^ 2) ^ 14 := by ring
  exact max_le (by nlinarith) (max_le hf (max_le hs ht))

lemma logarithmic_height_bounds {W : ℝ} (hW : 4 ≤ W) :
    let h := 1 + Nat.clog 2 (Nat.ceil W)
    3 ≤ h ∧ W ≤ (2 : ℝ) ^ (h - 1) ∧ Real.log W ≤ h := by
  let h := 1 + Nat.clog 2 (Nat.ceil W)
  have hceil : 4 ≤ Nat.ceil W := by
    have hh := Nat.ceil_mono hW
    norm_num at hh
    exact hh
  have hclog := Nat.clog_mono_right (b := 2) hceil
  norm_num at hclog
  have hh : 3 ≤ h := by dsimp [h]; omega
  have hp : W ≤ (2 : ℝ) ^ (h - 1) := by
    have hc := Nat.le_pow_clog (by norm_num : 1 < 2) (Nat.ceil W)
    have hcr : (Nat.ceil W : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil W)) := by exact_mod_cast hc
    simpa only [h, Nat.add_sub_cancel_left] using (Nat.le_ceil W).trans hcr
  refine ⟨hh, hp, ?_⟩
  have hl := Real.log_le_log (by linarith : 0 < W) hp
  rw [Real.log_pow] at hl
  have hlog : Real.log 2 ≤ 1 := by have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (h - 1))
  have hcast : ((h - 1 : ℕ) : ℝ) ≤ h := by exact_mod_cast Nat.sub_le h 1
  exact (hl.trans (by simpa only [mul_one] using hmul)).trans hcast

lemma public_height_bounds {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hG : 0 < G) (hL : 0 ≤ L) (hR : 0 < R) (hε : 0 < ε) :
    3 ≤ publicDepth m G L R ε ∧ Real.log m ≤ publicDepth m G L R ε ∧
      2 + (m : ℝ) + G * R / ε + L * R ^ 2 / ε ≤ (2 : ℝ) ^ (publicDepth m G L R ε - 1) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have ha : 0 ≤ G * R / ε := by positivity
  have hb : 0 ≤ L * R ^ 2 / ε := by positivity
  have hW : 4 ≤ 2 + (m : ℝ) + G * R / ε + L * R ^ 2 / ε := by linarith
  have hh := logarithmic_height_bounds hW
  refine ⟨hh.1, ?_, hh.2.1⟩
  have hmW : (m : ℝ) ≤ 2 + (m : ℝ) + G * R / ε + L * R ^ 2 / ε := by linarith
  exact (Real.log_le_log hm0 hmW).trans hh.2.2

lemma public_factor_polynomial_bound {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hG : 0 < G) (hL : 0 ≤ L) (hR : 0 < R) (hε : 0 < ε) :
    radiusFactor m (G * R / ε) (L * R ^ 2 / ε) (Real.log m) ≤
      8 * (2 + (m : ℝ) + G * R / ε + L * R ^ 2 / ε) ^ 2 := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have ha : 0 ≤ G * R / ε := by positivity
  have hb : 0 ≤ L * R ^ 2 / ε := by positivity
  have hell : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  have hlm := Real.log_le_sub_one_of_pos hm0
  apply radiusFactor_polynomial_bound (by linarith) (by linarith) ha hb hell <;> linarith

lemma public_compiler_depth_bound {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hG : 0 < G) (hL : 0 ≤ L) (hR : 0 < R) (hε : 0 < ε) :
    LongTails.Algorithms.AffineSoftmaxOuter.compilerDepth G (2 * R) (publicRadius m G L R ε) (ε / 2) ≤
      5 * publicDepth m G L R ε := by
  let h := publicDepth m G L R ε
  let W := 2 + (m : ℝ) + G * R / ε + L * R ^ 2 / ε
  let a := G * R / ε
  let z := radiusFactor m a (L * R ^ 2 / ε) (Real.log m)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ L * R ^ 2 / ε := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have haW : a ≤ W := by dsimp [W, a]; linarith
  have hz : 0 < z := zero_lt_one.trans_le (radiusFactor_ge_one _ _ _ _)
  have hzW : z ≤ 8 * W ^ 2 := public_factor_polynomial_bound hm hG hL hR hε
  have hH := public_height_bounds hm hG hL hR hε
  have hh : 3 ≤ h := hH.1
  have hWp : W ≤ (2 : ℝ) ^ (h - 1) := hH.2.2
  have he : G * (2 * R) ^ 2 / ((ε / 2) * publicRadius m G L R ε) = 4 * a * z := by
    change G * (2 * R) ^ 2 / ((ε / 2) * (2 * R / z)) = 4 * a * z
    dsimp [a]
    field_simp
    ring
  have hQ : G * (2 * R) ^ 2 / ((ε / 2) * publicRadius m G L R ε) ≤ (2 : ℝ) ^ (3 * h + 2) := by
    rw [he]
    calc
      _ ≤ 4 * W * (8 * W ^ 2) := by gcongr
      _ = 32 * W ^ 3 := by ring
      _ ≤ (2 : ℝ) ^ 5 * ((2 : ℝ) ^ (h - 1)) ^ 3 := by gcongr; norm_num
      _ = (2 : ℝ) ^ (5 + (h - 1) * 3) := by rw [← pow_mul, ← pow_add]
      _ = (2 : ℝ) ^ (3 * h + 2) := by congr 1; omega
  have hc : Nat.clog 2 (Nat.ceil (G * (2 * R) ^ 2 / ((ε / 2) * publicRadius m G L R ε))) ≤ 3 * h + 2 := by
    apply Nat.clog_le_of_le_pow
    apply Nat.ceil_le.mpr
    exact_mod_cast hQ
  unfold LongTails.Algorithms.AffineSoftmaxOuter.compilerDepth
  change _ ≤ 5 * h
  omega

lemma public_scale_identity {m : ℕ} {G L R ε : ℝ} (hR : 0 < R) :
    LongTails.Algorithms.AffineSoftmaxOuter.compilerScale (2 * R) (publicRadius m G L R ε) =
      (radiusFactor m (G * R / ε) (L * R ^ 2 / ε) (Real.log m)) ^ (2 / 3 : ℝ) := by
  have hz := zero_lt_one.trans_le (radiusFactor_ge_one (m : ℝ) (G * R / ε) (L * R ^ 2 / ε) (Real.log m))
  unfold LongTails.Algorithms.AffineSoftmaxOuter.compilerScale publicRadius
  congr 1
  field_simp

lemma public_variance_bound {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hε : 0 < ε) :
    let r := publicRadius m G L R ε
    let τ := ε / (2 * Real.log m)
    8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2) * (2 * R) ^ 2 / (ε / 2) ^ 2 ≤
      16 * (m : ℝ) * (radiusFactor m (G * R / ε) (L * R ^ 2 / ε) (Real.log m)) ^ (2 / 3 : ℝ) := by
  let a := G * R / ε
  let b := L * R ^ 2 / ε
  let ell := Real.log m
  let z := radiusFactor m a b ell
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hell : 0 < ell := Real.log_pos hm1
  have hz : 0 < z := zero_lt_one.trans_le (radiusFactor_ge_one _ _ _ _)
  have he : 8 * (L ^ 2 * (publicRadius m G L R ε) ^ 2 + G ^ 2 * L ^ 2 * (publicRadius m G L R ε) ^ 4 /
      (ε / (2 * Real.log m)) ^ 2) * (2 * R) ^ 2 / (ε / 2) ^ 2 =
      8 * (64 * b ^ 2 / z ^ 2 + 1024 * a ^ 2 * b ^ 2 * ell ^ 2 / z ^ 4) := by
    change 8 * (L ^ 2 * (2 * R / z) ^ 2 + G ^ 2 * L ^ 2 * (2 * R / z) ^ 4 /
      (ε / (2 * ell)) ^ 2) * (2 * R) ^ 2 / (ε / 2) ^ 2 = _
    dsimp only [a, b]
    field_simp
    ring
  dsimp only
  rw [he]
  have hh := radiusFactor_balance (a := a) (b := b) (ell := ell) hm0
  change 64 * b ^ 2 / z ^ 2 ≤ (m : ℝ) * z ^ (2 / 3 : ℝ) ∧
    1024 * a ^ 2 * b ^ 2 * ell ^ 2 / z ^ 4 ≤ (m : ℝ) * z ^ (2 / 3 : ℝ) at hh
  change _ ≤ 16 * (m : ℝ) * z ^ (2 / 3 : ℝ)
  nlinarith only [hh.1, hh.2]

lemma public_smooth_cost_bound {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hG : 0 < G) (hL : 0 ≤ L) (hR : 0 < R) (hε : 0 < ε) :
    (2 * R) * Real.sqrt ((L + 2 * G ^ 2 / (ε / (2 * Real.log m))) / (ε / 2)) ≤
      3 * Real.sqrt (L * R ^ 2 / ε) + 6 * (G * R / ε) * Real.sqrt (Real.log m) := by
  let a := G * R / ε
  let b := L * R ^ 2 / ε
  let ell := Real.log m
  let u := (2 * R) * Real.sqrt ((L + 2 * G ^ 2 / (ε / (2 * ell))) / (ε / 2))
  let v := 3 * Real.sqrt b + 6 * a * Real.sqrt ell
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hm1 : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hell : 0 < ell := Real.log_pos hm1
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have heu : u ^ 2 = 8 * b + 32 * a ^ 2 * ell := by
    dsimp only [u]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    dsimp only [a, b]
    field_simp
    ring
  have hev : v ^ 2 = 9 * b + 36 * a ^ 2 * ell + 36 * a * Real.sqrt b * Real.sqrt ell := by
    calc
      _ = 9 * (Real.sqrt b) ^ 2 + 36 * a ^ 2 * (Real.sqrt ell) ^ 2 + 36 * a * Real.sqrt b * Real.sqrt ell := by dsimp [v]; ring
      _ = _ := by rw [Real.sq_sqrt hb, Real.sq_sqrt hell.le]
  have hrem : 0 ≤ b + 4 * a ^ 2 * ell + 36 * a * Real.sqrt b * Real.sqrt ell := by positivity
  change u ≤ v
  nlinarith only [heu, hev, hrem, hu, hv]

lemma public_cost_bracket_bound {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hG : 0 < G) (hL : 0 ≤ L) (hR : 0 < R) (hε : 0 < ε) :
    let r := publicRadius m G L R ε
    let τ := ε / (2 * Real.log m)
    let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
    (m : ℝ) * LongTails.Algorithms.AffineSoftmaxOuter.compilerScale (2 * R) r +
      (2 * R) * Real.sqrt ((L + 2 * G ^ 2 / τ) / (ε / 2)) + V * (2 * R) ^ 2 / (ε / 2) ^ 2 ≤
      60 * (publicDepth m G L R ε : ℝ) *
        ((m : ℝ) + m * (L * R ^ 2 / ε) ^ (1 / 3 : ℝ) + (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (L * R ^ 2 / ε) +
          (m : ℝ) ^ (6 / 7 : ℝ) * ((G * R / ε) * (L * R ^ 2 / ε)) ^ (2 / 7 : ℝ) + G * R / ε) := by
  let a := G * R / ε
  let b := L * R ^ 2 / ε
  let ell := Real.log m
  let h := (publicDepth m G L R ε : ℝ)
  let z := radiusFactor m a b ell
  let S := (m : ℝ) + m * b ^ (1 / 3 : ℝ) + (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt b +
    (m : ℝ) ^ (6 / 7 : ℝ) * (a * b) ^ (2 / 7 : ℝ)
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hell : 0 ≤ ell := Real.log_nonneg hm1
  have hheight := public_height_bounds hm hG hL hR hε
  have hh : 1 ≤ h := by
    have hh3 : (3 : ℝ) ≤ publicDepth m G L R ε := by exact_mod_cast hheight.1
    dsimp [h]
    linarith
  have helh : ell ≤ h := hheight.2.1
  have hwork : (m : ℝ) * z ^ (2 / 3 : ℝ) ≤ 3 * h * S :=
    radiusFactor_work_bound hm1 ha hb hell hh helh
  have hvar := public_variance_bound hm (G := G) (L := L) (R := R) hε
  have hsmooth := public_smooth_cost_bound hm hG hL hR hε
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hwS : (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt b ≤ S := by
    dsimp [S]
    have h1 : 0 ≤ (m : ℝ) * b ^ (1 / 3 : ℝ) := by positivity
    have h2 : 0 ≤ (m : ℝ) ^ (6 / 7 : ℝ) * (a * b) ^ (2 / 7 : ℝ) := by positivity
    linarith
  have hmexp : (1 : ℝ) ≤ (m : ℝ) ^ (3 / 4 : ℝ) := Real.one_le_rpow hm1 (by norm_num)
  have hrootb : Real.sqrt b ≤ h * S :=
    ((le_mul_of_one_le_left (Real.sqrt_nonneg b) hmexp).trans hwS).trans (le_mul_of_one_le_left hS hh)
  have hrootell : Real.sqrt ell ≤ h := by
    rw [Real.sqrt_eq_rpow]
    exact subunit_power_le hell hh helh (by norm_num) (by norm_num)
  have hsmooth' : (2 * R) * Real.sqrt ((L + 2 * G ^ 2 / (ε / (2 * Real.log m))) / (ε / 2)) ≤
      3 * h * S + 6 * a * h := by
    apply hsmooth.trans
    change 3 * Real.sqrt b + 6 * a * Real.sqrt ell ≤ _
    have hh1 := mul_le_mul_of_nonneg_left hrootb (by norm_num : (0 : ℝ) ≤ 3)
    have hh2 := mul_le_mul_of_nonneg_left hrootell (show 0 ≤ 6 * a by positivity)
    nlinarith only [hh1, hh2]
  dsimp only
  rw [public_scale_identity hR]
  change (m : ℝ) * z ^ (2 / 3 : ℝ) + _ + _ ≤ 60 * h * (S + a)
  nlinarith only [hwork, hvar, hsmooth', mul_nonneg (zero_le_one.trans hh) hS, mul_nonneg (zero_le_one.trans hh) ha]

end LongTails.Proofs.AffineSoftmaxRadius
