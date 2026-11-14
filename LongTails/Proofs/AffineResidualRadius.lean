import LongTails.Algorithms.AffineResidualRadius
import LongTails.Proofs.AffineSoftmaxRadius
import LongTails.Proofs.AffineResidualCostParameters

namespace LongTails.Proofs.AffineResidualRadius

open LongTails.Algorithms.AffineResidualRadius

lemma radiusFactor_bounds (m b : ℝ) :
    1 ≤ radiusFactor m b ∧ (max 1 b) ^ (3 / 5 : ℝ) ≤ radiusFactor m b ∧
      radiusFactor m b ≤ (max 1 b) ^ (2 / 3 : ℝ) := by
  have hB : 1 ≤ max 1 b := le_max_left _ _
  have hu : 1 ≤ (max 1 b) ^ (3 / 5 : ℝ) := Real.one_le_rpow hB (by norm_num)
  have huc : (max 1 b) ^ (3 / 5 : ℝ) ≤ (max 1 b) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
  have hz : (max 1 b) ^ (3 / 5 : ℝ) ≤ radiusFactor m b :=
    le_min huc (le_max_left _ _)
  exact ⟨hu.trans hz, hz, min_le_left _ _⟩

lemma publicRadius_bounds {m : ℕ} {L R ε : ℝ} (hR : 0 < R) :
    0 < publicRadius m L R ε ∧ publicRadius m L R ε ≤ 2 * R := by
  have hz := (radiusFactor_bounds m (8 * L * R ^ 2 / ε)).1
  exact ⟨div_pos (by positivity) (zero_lt_one.trans_le hz), div_le_self (by positivity) hz⟩

lemma cache_bound {m b : ℝ} (hm : 0 < m) (hb : 1 ≤ b) :
    m * (radiusFactor m b) ^ (2 / 3 : ℝ) ≤
      m * b ^ (2 / 5 : ℝ) + m ^ (3 / 4 : ℝ) * Real.sqrt b := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hu : (b ^ (3 / 5 : ℝ)) ^ (2 / 3 : ℝ) = b ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_mul hb0]
    norm_num
  have hv : m * ((b ^ 2 / m) ^ (3 / 8 : ℝ)) ^ (2 / 3 : ℝ) =
      m ^ (3 / 4 : ℝ) * Real.sqrt b := by
    rw [← Real.rpow_mul (by positivity : 0 ≤ b ^ 2 / m)]
    norm_num only [show (3 / 8 : ℝ) * (2 / 3) = 1 / 4 by norm_num]
    rw [AffineSoftmaxRadius.mass_rpow_div hm (sq_nonneg b)]
    have he : (b ^ 2) ^ (1 / 4 : ℝ) = Real.sqrt b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb0, Real.sqrt_eq_rpow]
      norm_num
    rw [he]
    norm_num
  have hz : radiusFactor m b ≤ max (b ^ (3 / 5 : ℝ)) ((b ^ 2 / m) ^ (3 / 8 : ℝ)) := by
    simpa only [radiusFactor, max_eq_right hb] using min_le_right
      (b ^ (2 / 3 : ℝ)) (max (b ^ (3 / 5 : ℝ)) ((b ^ 2 / m) ^ (3 / 8 : ℝ)))
  have hpow := Real.rpow_le_rpow (zero_le_one.trans (radiusFactor_bounds m b).1) hz
    (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hmul := mul_le_mul_of_nonneg_left hpow hm.le
  by_cases h : b ^ (3 / 5 : ℝ) ≤ (b ^ 2 / m) ^ (3 / 8 : ℝ)
  · rw [max_eq_right h, hv] at hmul
    exact hmul.trans (le_add_of_nonneg_left (by positivity))
  · rw [max_eq_left (le_of_not_ge h), hu] at hmul
    exact hmul.trans (le_add_of_nonneg_right (by positivity))

lemma residual_initialization_bound {m b : ℝ} (hm : 0 ≤ m) (hb : 1 ≤ b) :
    m * b / radiusFactor m b ≤ m * b ^ (2 / 5 : ℝ) := by
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hz : b ^ (3 / 5 : ℝ) ≤ radiusFactor m b := by
    simpa only [max_eq_right hb] using (radiusFactor_bounds m b).2.1
  have he : b / b ^ (3 / 5 : ℝ) = b ^ (2 / 5 : ℝ) := by
    rw [show (2 / 5 : ℝ) = 1 - 3 / 5 by norm_num, Real.rpow_sub hbpos, Real.rpow_one]
  calc
    _ ≤ m * b / b ^ (3 / 5 : ℝ) := div_le_div_of_nonneg_left (mul_nonneg hm hbpos.le)
      (Real.rpow_pos_of_pos hbpos _) hz
    _ = _ := by rw [mul_div_assoc, he]

lemma dual_variance_bound {m b : ℝ} (hm : 0 ≤ m) (hb : 1 ≤ b) :
    m * b ^ 2 / (radiusFactor m b) ^ (8 / 3 : ℝ) ≤ m * b ^ (2 / 5 : ℝ) := by
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hz : b ^ (3 / 5 : ℝ) ≤ radiusFactor m b := by
    simpa only [max_eq_right hb] using (radiusFactor_bounds m b).2.1
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hbpos.le _) hz (by norm_num : (0 : ℝ) ≤ 8 / 3)
  have he : b ^ 2 / (b ^ (3 / 5 : ℝ)) ^ (8 / 3 : ℝ) = b ^ (2 / 5 : ℝ) := by
    rw [← Real.rpow_mul hbpos.le]
    norm_num only [show (3 / 5 : ℝ) * (8 / 3) = 8 / 5 by norm_num]
    rw [show (2 / 5 : ℝ) = 2 - 8 / 5 by norm_num, Real.rpow_sub hbpos, Real.rpow_two]
  calc
    _ ≤ m * b ^ 2 / (b ^ (3 / 5 : ℝ)) ^ (8 / 3 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ = _ := by rw [mul_div_assoc, he]

lemma primal_variance_bound {m b : ℝ} (hm : 0 < m) (hb : 1 ≤ b) :
    b ^ 2 / (radiusFactor m b) ^ 2 ≤
      b ^ (2 / 3 : ℝ) + m * b ^ (2 / 5 : ℝ) + m ^ (3 / 4 : ℝ) * Real.sqrt b := by
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hzpos : 0 < radiusFactor m b := zero_lt_one.trans_le (radiusFactor_bounds m b).1
  by_cases hcap : b ^ (2 / 3 : ℝ) ≤ max (b ^ (3 / 5 : ℝ)) ((b ^ 2 / m) ^ (3 / 8 : ℝ))
  · have hz : radiusFactor m b = b ^ (2 / 3 : ℝ) := by simp only [radiusFactor, max_eq_right hb, min_eq_left hcap]
    have he : b ^ 2 / (b ^ (2 / 3 : ℝ)) ^ 2 = b ^ (2 / 3 : ℝ) := by
      have hp : (b ^ (2 / 3 : ℝ)) ^ 2 = b ^ (4 / 3 : ℝ) := by
        rw [← Real.rpow_two, ← Real.rpow_mul hbpos.le]
        norm_num
      rw [hp, show (2 / 3 : ℝ) = 2 - 4 / 3 by norm_num, Real.rpow_sub hbpos, Real.rpow_two]
    rw [hz, he]
    have h1 : 0 ≤ m * b ^ (2 / 5 : ℝ) := by positivity
    have h2 : 0 ≤ m ^ (3 / 4 : ℝ) * Real.sqrt b := by positivity
    linarith
  · have hv : (b ^ 2 / m) ^ (3 / 8 : ℝ) ≤ radiusFactor m b := by
      simp only [radiusFactor, max_eq_right hb, min_eq_right (le_of_not_ge hcap)]
      exact le_max_right _ _
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity : 0 ≤ b ^ 2 / m) _) hv
      (by norm_num : (0 : ℝ) ≤ 8 / 3)
    rw [← Real.rpow_mul (by positivity : 0 ≤ b ^ 2 / m)] at hp
    norm_num only [show (3 / 8 : ℝ) * (8 / 3) = 1 by norm_num, Real.rpow_one] at hp
    have he : (radiusFactor m b) ^ (8 / 3 : ℝ) =
        (radiusFactor m b) ^ 2 * (radiusFactor m b) ^ (2 / 3 : ℝ) := by
      rw [show (8 / 3 : ℝ) = 2 + 2 / 3 by norm_num, Real.rpow_add hzpos, Real.rpow_two]
    rw [he] at hp
    have hmul := (div_le_iff₀ hm).1 hp
    have hbal : b ^ 2 / (radiusFactor m b) ^ 2 ≤ m * (radiusFactor m b) ^ (2 / 3 : ℝ) := by
      apply (div_le_iff₀ (sq_pos_of_pos hzpos)).2
      nlinarith only [hmul]
    have hc := hbal.trans (cache_bound hm hb)
    have hnonneg : 0 ≤ b ^ (2 / 3 : ℝ) := by positivity
    linarith

lemma radius_work_bound {m b : ℝ} (hm : 1 ≤ m) (hb : 0 ≤ b) :
    let z := radiusFactor m b
    m * z ^ (2 / 3 : ℝ) + z + m * b / z + b ^ 2 / z ^ 2 + m * b ^ 2 / z ^ (8 / 3 : ℝ) ≤
      8 * (m + m * b ^ (2 / 5 : ℝ) + m ^ (3 / 4 : ℝ) * Real.sqrt b + b ^ (2 / 3 : ℝ)) := by
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  dsimp only
  by_cases hb1 : 1 ≤ b
  · have hc := cache_bound hmpos hb1
    have hi := residual_initialization_bound hmpos.le hb1
    have hp := primal_variance_bound hmpos hb1
    have hd := dual_variance_bound hmpos.le hb1
    have hz : radiusFactor m b ≤ b ^ (2 / 3 : ℝ) := by
      simpa only [max_eq_right hb1] using (radiusFactor_bounds m b).2.2
    have h1 : 0 ≤ m * b ^ (2 / 5 : ℝ) := by positivity
    have h2 : 0 ≤ m ^ (3 / 4 : ℝ) * Real.sqrt b := by positivity
    have h3 : 0 ≤ b ^ (2 / 3 : ℝ) := by positivity
    linarith
  · have hbupper : b ≤ 1 := le_of_not_ge hb1
    have hz : radiusFactor m b = 1 := by
      simp only [radiusFactor, max_eq_left hbupper, Real.one_rpow, one_pow]
      exact min_eq_left (le_max_left _ _)
    rw [hz]
    simp only [Real.one_rpow, one_pow, mul_one, div_one]
    have hmb : m * b ≤ m := by nlinarith [mul_nonneg hmpos.le (sub_nonneg.mpr hbupper)]
    have hb2 : b ^ 2 ≤ 1 := by nlinarith
    have hmb2 : m * b ^ 2 ≤ m := by nlinarith [mul_nonneg hmpos.le (sub_nonneg.mpr hb2)]
    have h1 : 0 ≤ m * b ^ (2 / 5 : ℝ) := by positivity
    have h2 : 0 ≤ m ^ (3 / 4 : ℝ) * Real.sqrt b := by positivity
    have h3 : 0 ≤ b ^ (2 / 3 : ℝ) := by positivity
    linarith

lemma dimensionless_work_identity (m L D ε : ℝ) {z : ℝ} (hz : 0 < z) (hε : 0 < ε) :
    let t := z ^ (2 / 3 : ℝ)
    let r := D / z
    let b := L * D ^ 2 / ε
    m * t + t * Real.sqrt t + m * L * r ^ 2 * t * Real.sqrt t / ε +
      L ^ 2 * t ^ 3 * r ^ 4 / ε ^ 2 + m * L ^ 2 * t ^ 2 * r ^ 4 / ε ^ 2 =
      m * z ^ (2 / 3 : ℝ) + z + m * b / z + b ^ 2 / z ^ 2 + m * b ^ 2 / z ^ (8 / 3 : ℝ) := by
  let t := z ^ (2 / 3 : ℝ)
  have htroot : t * Real.sqrt t = z := by
    dsimp [t]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz.le, ← Real.rpow_add hz]
    norm_num
  have ht3 : t ^ 3 = z ^ 2 := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    norm_num
  have ht2 : t ^ 2 * z ^ (8 / 3 : ℝ) = z ^ 4 := by
    dsimp [t]
    rw [← Real.rpow_two, ← Real.rpow_mul hz.le, ← Real.rpow_add hz]
    norm_num
  have hi : m * L * (D / z) ^ 2 * t * Real.sqrt t / ε = m * (L * D ^ 2 / ε) / z := by
    calc
      _ = m * L * (D / z) ^ 2 * (t * Real.sqrt t) / ε := by ring
      _ = _ := by rw [htroot]; field_simp
  have hp : L ^ 2 * t ^ 3 * (D / z) ^ 4 / ε ^ 2 = (L * D ^ 2 / ε) ^ 2 / z ^ 2 := by
    rw [ht3]
    field_simp
  have hd : m * L ^ 2 * t ^ 2 * (D / z) ^ 4 / ε ^ 2 =
      m * (L * D ^ 2 / ε) ^ 2 / z ^ (8 / 3 : ℝ) := by
    have hzp : 0 < z ^ (8 / 3 : ℝ) := Real.rpow_pos_of_pos hz _
    field_simp
    linear_combination (m * L ^ 2 * D ^ 4) * ht2
  change m * t + t * Real.sqrt t + m * L * (D / z) ^ 2 * t * Real.sqrt t / ε +
    L ^ 2 * t ^ 3 * (D / z) ^ 4 / ε ^ 2 + m * L ^ 2 * t ^ 2 * (D / z) ^ 4 / ε ^ 2 = _
  rw [hi, hp, hd, htroot]

lemma radius_localWork_bound (m : ℕ) (hm : 2 ≤ m) {L D ε H ell : ℝ}
    (hL : 0 ≤ L) (hD : 0 < D) (hε : 0 < ε) (hH : 1 ≤ H)
    (hell : 1 ≤ ell) (hlog : Real.log m ≤ ell) :
    let b := L * D ^ 2 / ε
    let z := radiusFactor m b
    let r := D / z
    let t := z ^ (2 / 3 : ℝ)
    t * (m + AffineResidualCostParameters.localWork m (ε / Real.log m)
      (ε * H ^ 2 / (t * r ^ 2)) L r) ≤
      32 * ell * (m + m * b ^ (2 / 5 : ℝ) + (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt b + b ^ (2 / 3 : ℝ)) := by
  let b := L * D ^ 2 / ε
  let z := radiusFactor m b
  have hz : 1 ≤ z := (radiusFactor_bounds m b).1
  have hzp : 0 < z := zero_lt_one.trans_le hz
  have hr : 0 < D / z := div_pos hD hzp
  have ht : 1 ≤ z ^ (2 / 3 : ℝ) := Real.one_le_rpow hz (by norm_num)
  have hlocal := AffineResidualCostParameters.localWork_scaled_bound m hm hL hr hε hH ht hell hlog
  have hid := dimensionless_work_identity m L D ε hzp hε
  dsimp only at hid
  rw [hid] at hlocal
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hrad := radius_work_bound hm1 hb
  dsimp only at hrad
  apply hlocal.trans
  have hh := mul_le_mul_of_nonneg_left hrad (show 0 ≤ 4 * ell by linarith)
  convert hh using 1
  ring

open LongTails.Algorithms.AffineSoftmaxRadius (publicDepth)

lemma public_factor_polynomial_bound {m : ℕ} {G L R ε : ℝ}
    (hG : 0 < G) (hL : 0 ≤ L) (hR : 0 < R) (hε : 0 < ε) :
    radiusFactor m (8 * L * R ^ 2 / ε) ≤
      8 * (2 + (m : ℝ) + G * R / ε + L * R ^ 2 / ε) ^ 2 := by
  let b := L * R ^ 2 / ε
  let W := 2 + (m : ℝ) + G * R / ε + b
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ha : 0 ≤ G * R / ε := by positivity
  have hW : 1 ≤ W := by dsimp [W]; have hn := Nat.cast_nonneg (α := ℝ) m; linarith
  have hbW : b ≤ W := by dsimp [W]; have hn := Nat.cast_nonneg (α := ℝ) m; linarith
  have hz := (radiusFactor_bounds (m : ℝ) (8 * b)).2.2
  have hp : (max 1 (8 * b)) ^ (2 / 3 : ℝ) ≤ max 1 (8 * b) :=
    Real.rpow_le_self_of_one_le (le_max_left _ _) (by norm_num)
  have hmax : max 1 (8 * b) ≤ 8 * W := max_le (by linarith) (by linarith)
  have hWW : W ≤ W ^ 2 := by nlinarith
  change radiusFactor m (8 * L * R ^ 2 / ε) ≤ 8 * W ^ 2
  have he : 8 * L * R ^ 2 / ε = 8 * b := by dsimp [b]; ring
  rw [he]
  exact (hz.trans hp).trans (hmax.trans (by nlinarith))

lemma public_compiler_depth_bound {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hG : 0 < G) (hL : 0 ≤ L) (hR : 0 < R) (hε : 0 < ε) :
    LongTails.Algorithms.AffineSoftmaxOuter.compilerDepth G (2 * R) (publicRadius m L R ε) (ε / 2) ≤
      5 * publicDepth m G L R ε := by
  let h := publicDepth m G L R ε
  let W := 2 + (m : ℝ) + G * R / ε + L * R ^ 2 / ε
  let a := G * R / ε
  let z := radiusFactor m (8 * L * R ^ 2 / ε)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ L * R ^ 2 / ε := by positivity
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have haW : a ≤ W := by dsimp [W, a]; linarith
  have hz : 0 < z := zero_lt_one.trans_le ((radiusFactor_bounds (m : ℝ) (8 * L * R ^ 2 / ε)).1)
  have hzW : z ≤ 8 * W ^ 2 := public_factor_polynomial_bound hG hL hR hε
  have hH := AffineSoftmaxRadius.public_height_bounds hm hG hL hR hε
  have hh : 3 ≤ h := hH.1
  have hWp : W ≤ (2 : ℝ) ^ (h - 1) := hH.2.2
  have he : G * (2 * R) ^ 2 / ((ε / 2) * publicRadius m L R ε) = 4 * a * z := by
    change G * (2 * R) ^ 2 / ((ε / 2) * (2 * R / z)) = 4 * a * z
    dsimp [a]
    field_simp
    ring
  have hQ : G * (2 * R) ^ 2 / ((ε / 2) * publicRadius m L R ε) ≤ (2 : ℝ) ^ (3 * h + 2) := by
    rw [he]
    calc
      _ ≤ 4 * W * (8 * W ^ 2) := by gcongr
      _ = 32 * W ^ 3 := by ring
      _ ≤ (2 : ℝ) ^ 5 * ((2 : ℝ) ^ (h - 1)) ^ 3 := by gcongr; norm_num
      _ = (2 : ℝ) ^ (5 + (h - 1) * 3) := by rw [← pow_mul, ← pow_add]
      _ = (2 : ℝ) ^ (3 * h + 2) := by congr 1; omega
  have hc : Nat.clog 2 (Nat.ceil (G * (2 * R) ^ 2 / ((ε / 2) * publicRadius m L R ε))) ≤ 3 * h + 2 := by
    apply Nat.clog_le_of_le_pow
    apply Nat.ceil_le.mpr
    exact_mod_cast hQ
  unfold LongTails.Algorithms.AffineSoftmaxOuter.compilerDepth
  change _ ≤ 5 * h
  omega

lemma public_scale_identity {m : ℕ} {L R ε : ℝ} (hR : 0 < R) :
    LongTails.Algorithms.AffineSoftmaxOuter.compilerScale (2 * R) (publicRadius m L R ε) =
      (radiusFactor m (8 * L * R ^ 2 / ε)) ^ (2 / 3 : ℝ) := by
  have hz := zero_lt_one.trans_le ((radiusFactor_bounds (m : ℝ) (8 * L * R ^ 2 / ε)).1)
  unfold LongTails.Algorithms.AffineSoftmaxOuter.compilerScale publicRadius
  congr 1
  field_simp

lemma rate_scale_eight {m b : ℝ} (hm : 0 ≤ m) (hb : 0 ≤ b) :
    m + m * (8 * b) ^ (2 / 5 : ℝ) + m ^ (3 / 4 : ℝ) * Real.sqrt (8 * b) +
      (8 * b) ^ (2 / 3 : ℝ) ≤
    8 * (m + m * b ^ (2 / 5 : ℝ) + m ^ (3 / 4 : ℝ) * Real.sqrt b + b ^ (2 / 3 : ℝ)) := by
  have hp (p : ℝ) (hp : p ≤ 1) : (8 * b) ^ p ≤ 8 * b ^ p := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hb]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by norm_num) hp)
      (Real.rpow_nonneg hb p)
  have h1 := mul_le_mul_of_nonneg_left (hp (2 / 5) (by norm_num)) hm
  have h2 := mul_le_mul_of_nonneg_left (hp (1 / 2) (by norm_num))
    (Real.rpow_nonneg hm (3 / 4))
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h2
  have h3 := hp (2 / 3) (by norm_num)
  nlinarith

lemma meanCostBound_public_le {m : ℕ} (hm : 2 ≤ m) {G L R ε : ℝ}
    (hG : 0 < G) (hL : 0 ≤ L) (hR : 0 < R) (hε : 0 < ε) :
    meanCostBound m G L R ε ≤ 600000000000000000000 * (publicDepth m G L R ε : ℝ) ^ 8 *
      ((m : ℝ) + m * (L * R ^ 2 / ε) ^ (2 / 5 : ℝ) +
        (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (L * R ^ 2 / ε) + (L * R ^ 2 / ε) ^ (2 / 3 : ℝ)) := by
  let r := publicRadius m L R ε
  let H := LongTails.Algorithms.AffineSoftmaxOuter.compilerDepth G (2 * R) r (ε / 2)
  let t := LongTails.Algorithms.AffineSoftmaxOuter.compilerScale (2 * R) r
  let μ := LongTails.Algorithms.AffineSoftmaxOuter.compilerFloor G (2 * R) r (ε / 2)
  let τ := ε / (2 * Real.log m)
  let h := (publicDepth m G L R ε : ℝ)
  let b := L * R ^ 2 / ε
  let S := (m : ℝ) + m * b ^ (2 / 5 : ℝ) + (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt b + b ^ (2 / 3 : ℝ)
  have hh := AffineSoftmaxRadius.public_height_bounds hm hG hL hR hε
  have hh1 : 1 ≤ h := by
    have hh3 : (3 : ℝ) ≤ (publicDepth m G L R ε : ℝ) := by exact_mod_cast hh.1
    dsimp [h]
    linarith
  have hH1 : (1 : ℝ) ≤ H := by
    have hn := AffineSoftmaxOuterParameters.compilerDepth_ge_three G (2 * R) r (ε / 2)
    exact_mod_cast (show 1 ≤ H by omega)
  have hdepth : (H : ℝ) ≤ 5 * h := by
    dsimp [H, h, r]
    exact_mod_cast public_compiler_depth_bound hm hG hL hR hε
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hraw := radius_localWork_bound m hm hL (show 0 < 2 * R by positivity)
    (show 0 < ε / 2 by positivity) hH1 hh1 hh.2.1
  dsimp only at hraw
  have hbident : L * (2 * R) ^ 2 / (ε / 2) = 8 * L * R ^ 2 / ε := by ring
  have htemp : (ε / 2) / Real.log m = ε / (2 * Real.log m) := by ring
  rw [hbident, htemp] at hraw
  have hwork : t * (m + AffineResidualCostParameters.localWork m τ μ L r) ≤
      32 * h * ((m : ℝ) + m * (8 * b) ^ (2 / 5 : ℝ) +
        (m : ℝ) ^ (3 / 4 : ℝ) * Real.sqrt (8 * b) + (8 * b) ^ (2 / 3 : ℝ)) := by
    have he : 8 * L * R ^ 2 / ε = 8 * b := by dsimp [b]; ring
    have ht0 : t = (radiusFactor m (8 * L * R ^ 2 / ε)) ^ (2 / 3 : ℝ) := public_scale_identity hR
    have hμ0 : μ = (ε / 2) * (H : ℝ) ^ 2 /
        ((radiusFactor m (8 * L * R ^ 2 / ε)) ^ (2 / 3 : ℝ) * r ^ 2) := by
      change (ε / 2) * (H : ℝ) ^ 2 / (t * r ^ 2) = _
      rw [ht0]
    rw [ht0, hμ0]
    simpa only [r, publicRadius, τ, he] using hraw

  have hwork' : t * (m + AffineResidualCostParameters.localWork m τ μ L r) ≤ 256 * h * S := by
    have hs := rate_scale_eight (Nat.cast_nonneg m) hb
    have ha := hwork.trans (mul_le_mul_of_nonneg_left hs (show 0 ≤ 32 * h by positivity))
    convert ha using 1
    dsimp [S]
    ring
  have hτ : 0 < τ := AffineSoftmaxRadius.public_temperature_pos hm hε
  have hr := publicRadius_bounds (m := m) (L := L) (ε := ε) hR
  have hμ : 0 < μ := AffineSoftmaxOuterParameters.compilerFloor_pos hr.1 hr.2 (by positivity)
  have hnonneg : 0 ≤ t * (m + AffineResidualCostParameters.localWork m τ μ L r) := by
    apply mul_nonneg
    · exact Real.rpow_nonneg (div_nonneg (by positivity : 0 ≤ 2 * R) hr.1.le) _
    · exact add_nonneg (Nat.cast_nonneg m) (AffineResidualCostParameters.localWork_nonneg m hτ hμ hL)
  change 30000000000000 * (H : ℝ) ^ 7 * t * (m + AffineResidualCostParameters.localWork m τ μ L r) ≤ _
  calc
    _ = 30000000000000 * (H : ℝ) ^ 7 * (t * (m + AffineResidualCostParameters.localWork m τ μ L r)) := by ring
    _ ≤ 30000000000000 * (5 * h) ^ 7 * (256 * h * S) := by gcongr
    _ = 600000000000000000000 * h ^ 8 * S := by ring

end LongTails.Proofs.AffineResidualRadius
