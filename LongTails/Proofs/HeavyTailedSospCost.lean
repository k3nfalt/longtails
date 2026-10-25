import LongTails.Proofs.HeavyTailedSospTuning

namespace LongTails.Proofs.HeavyTailedSospCost

open LongTails.Setups.HeavyTailedHessianVector
open LongTails.Algorithms.HeavyTailedSospTuned
open HeavyTailedSospTuning

lemma resetBatch_upper (p : Params) (hp : 1 < p.p) (hσg : 0 ≤ p.σg)
    (hε : 0 < p.ε) : (resetBatch p : ℝ) ≤ 2 * resetScale p ^ conjugate p := by
  have ha := resetScale_ge_one p hp hσg hε
  have hr : 0 ≤ conjugate p := (conjugate_holder p hp).symm.nonneg
  have hpow : 1 ≤ resetScale p ^ conjugate p := Real.one_le_rpow ha hr
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (by linarith : 0 ≤ resetScale p) (conjugate p))
  change (resetBatch p : ℝ) < resetScale p ^ conjugate p + 1 at hc
  linarith

lemma transportBatch_upper (p : Params) (hp : 1 < p.p) (hL : 0 < p.L)
    (hρ : 0 < p.ρ) (hσh : 0 ≤ p.σh) (hε : 0 < p.ε) :
    (transportBatch p : ℝ) ≤ 2 + (epochCount p : ℝ) ^ (conjugate p - 1) * transportScale p ^ conjugate p := by
  have hz := transportScale_nonneg p hp hL hρ hσh hε
  have hc := Nat.ceil_lt_add_one (mul_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg (epochCount p)) (conjugate p - 1))
    (Real.rpow_nonneg hz (conjugate p)))
  unfold transportBatch
  push_cast
  linarith

lemma epoch_transport_scale (p : Params) (hp : 1 < p.p) (hL : 0 < p.L)
    (hρ : 0 < p.ρ) (hσg : 0 ≤ p.σg) (hσh : 0 ≤ p.σh) (hε : 0 < p.ε)
    (hq : 1 < epochCount p) : (epochCount p : ℝ) * transportScale p ≤ resetScale p := by
  have ha : 0 < resetScale p := lt_of_lt_of_le (by norm_num) (resetScale_ge_one p hp hσg hε)
  have hz := transportScale_nonneg p hp hL hρ hσh hε
  have hT : (0 : ℝ) < cycleCount p := by exact_mod_cast cycleCount_pos p
  have hden : 0 < resetScale p + cycleCount p * transportScale p := by positivity
  have hratio : 0 ≤ (cycleCount p : ℝ) * resetScale p /
      (resetScale p + cycleCount p * transportScale p) := by positivity
  have hf := Nat.floor_le hratio
  have hqeq : epochCount p = ⌊(cycleCount p : ℝ) * resetScale p /
      (resetScale p + cycleCount p * transportScale p)⌋₊ := by
    unfold epochCount at hq ⊢
    omega
  rw [← hqeq] at hf
  have hb := (le_div_iff₀ hden).mp hf
  have hqa : 0 ≤ (epochCount p : ℝ) * resetScale p := by positivity
  apply (mul_le_mul_iff_left₀ hT).mp
  nlinarith

lemma epoch_transport_power (p : Params) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hσg : 0 ≤ p.σg) (hσh : 0 ≤ p.σh) (hε : 0 < p.ε) :
    (epochCount p : ℝ) ^ (conjugate p - 1) * transportScale p ^ conjugate p ≤
      transportScale p ^ conjugate p + resetScale p ^ (conjugate p - 1) * transportScale p := by
  have hz := transportScale_nonneg p hp hL hρ hσh hε
  have ha : 0 ≤ resetScale p := le_trans (by norm_num) (resetScale_ge_one p hp hσg hε)
  have hr := conjugate_ge_two p hp hp2
  by_cases hq : epochCount p = 1
  · simp only [hq, Nat.cast_one, Real.one_rpow, one_mul]
    exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg ha _) hz)
  have hqgt : 1 < epochCount p := by have := epochCount_pos p; omega
  have hscale := epoch_transport_scale p hp hL hρ hσg hσh hε hqgt
  have hpow := Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg _) hz) hscale
    (by linarith : 0 ≤ conjugate p - 1)
  have hmul := mul_le_mul_of_nonneg_right hpow hz
  have hid : (epochCount p : ℝ) ^ (conjugate p - 1) * transportScale p ^ conjugate p =
      ((epochCount p : ℝ) * transportScale p) ^ (conjugate p - 1) * transportScale p := by
    rw [Real.mul_rpow (Nat.cast_nonneg _) hz]
    have hzpow := Real.rpow_add_of_nonneg hz
      (by linarith : 0 ≤ conjugate p - 1) (by norm_num : (0 : ℝ) ≤ 1)
    rw [show conjugate p - 1 + 1 = conjugate p by ring, Real.rpow_one] at hzpow
    rw [hzpow]
    ring
  rw [hid]
  exact hmul.trans (le_add_of_nonneg_left (Real.rpow_nonneg hz _))

lemma estimator_work_algebra {a z r T q B b : ℝ}
    (ha : 0 < a) (hz : 0 ≤ z) (hT : 0 < T) (hq : 0 < q)
    (hB : B ≤ 2 * a ^ r) (hb : b ≤ 2 + z ^ r + a ^ (r - 1) * z)
    (hi : 1 / q ≤ 2 / T + 2 * z / a) :
    (2 * T / q + 1) * B + 2 * T * b ≤
      10 * (a ^ r + T * (1 + a ^ (r - 1) * z + z ^ r)) := by
  have h1 := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 2 * T)
  have hid : 2 * T * (2 / T + 2 * z / a) = 4 + 4 * T * z / a := by field_simp; ring
  rw [hid] at h1
  simp only [mul_one_div] at h1
  have hfactor : 2 * T / q + 1 ≤ 5 + 4 * T * z / a := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2 * T / q + 1)
  have h3 := mul_le_mul_of_nonneg_right hfactor (by positivity : 0 ≤ 2 * a ^ r)
  have h4 := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 2 * T)
  have hpow : a ^ r / a = a ^ (r - 1) := (Real.rpow_sub_one ha.ne' r).symm
  have hid2 : (5 + 4 * T * z / a) * (2 * a ^ r) =
      10 * a ^ r + 8 * T * a ^ (r - 1) * z := by rw [← hpow]; ring
  rw [hid2] at h3
  have hzpow := Real.rpow_nonneg hz r
  nlinarith [mul_nonneg hT.le hzpow]

lemma estimator_work_upper (p : Params) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hσg : 0 ≤ p.σg) (hσh : 0 ≤ p.σh) (hε : 0 < p.ε) :
    (2 * (cycleCount p : ℝ) / (max 1 (epochCount p) : ℕ) + 1) * (max 1 (resetBatch p) : ℕ) +
      2 * cycleCount p * (max 1 (transportBatch p) : ℕ) ≤
    10 * (resetScale p ^ conjugate p + cycleCount p *
      (1 + resetScale p ^ (conjugate p - 1) * transportScale p + transportScale p ^ conjugate p)) := by
  rw [max_eq_right (show 1 ≤ epochCount p from epochCount_pos p),
    max_eq_right (show 1 ≤ resetBatch p from resetBatch_pos p hp hσg hε),
    max_eq_right (show 1 ≤ transportBatch p from transportBatch_pos p)]
  apply estimator_work_algebra
    (lt_of_lt_of_le (by norm_num) (resetScale_ge_one p hp hσg hε))
    (transportScale_nonneg p hp hL hρ hσh hε)
    (by exact_mod_cast cycleCount_pos p) (by exact_mod_cast epochCount_pos p)
    (resetBatch_upper p hp hσg hε) _ (epoch_inverse_bound p hp hL hρ hσg hσh hε)
  have h1 := transportBatch_upper p hp hL hρ hσh hε
  have h2 := epoch_transport_power p hp hp2 hL hρ hσg hσh hε
  linarith

lemma stepSize_public_bounds (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ) (hε : 0 < p.ε) :
    p.ε / (2500 * (p.L + Real.sqrt (p.ρ * p.ε))) ≤ stepSize p ∧
      stepSize p ≤ p.ε / (500 * (p.L + Real.sqrt (p.ρ * p.ε))) := by
  have hγ := curvature_pos p hρ hε
  have hid := curvature_accuracy p hρ hε
  have hstep : stepSize p = p.ε / (2500 * (p.L + curvature p)) := by
    unfold stepSize accuracy
    field_simp
    ring
  rw [hstep]
  constructor
  · apply div_le_div_of_nonneg_left hε.le (by positivity)
    nlinarith
  · apply div_le_div_of_nonneg_left hε.le (by positivity)
    nlinarith

lemma cycleCount_public_upper (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ)
    (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    (cycleCount p : ℝ) ≤ (2 : ℝ) ^ 23 * (1 + p.Δ * (p.L + Real.sqrt (p.ρ * p.ε)) / p.ε ^ 2) := by
  have hh := stepSize_pos p hL hρ hε
  have he := accuracy_pos p hε
  have hS : 0 < p.L + Real.sqrt (p.ρ * p.ε) := by positivity
  have hratio : 0 ≤ 100 * p.Δ / (stepSize p * accuracy p) := by positivity
  have hc := Nat.ceil_lt_add_one hratio
  have hceil : (cycleCount p : ℝ) ≤ 1 + 100 * p.Δ / (stepSize p * accuracy p) := by
    unfold cycleCount
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) (by linarith)
  have hlo := (stepSize_public_bounds p hL hρ hε).1
  have hden : p.ε ^ 2 / (62500 * (p.L + Real.sqrt (p.ρ * p.ε))) ≤ stepSize p * accuracy p := by
    have hb := mul_le_mul_of_nonneg_right hlo he.le
    unfold accuracy at hb ⊢
    convert hb using 1
    field_simp
    ring
  have hr := div_le_div_of_nonneg_left (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) hΔ)
    (by positivity : 0 < p.ε ^ 2 / (62500 * (p.L + Real.sqrt (p.ρ * p.ε)))) hden
  have hid : 100 * p.Δ / (p.ε ^ 2 / (62500 * (p.L + Real.sqrt (p.ρ * p.ε)))) =
      6250000 * (p.Δ * (p.L + Real.sqrt (p.ρ * p.ε)) / p.ε ^ 2) := by field_simp; ring
  rw [hid] at hr
  have hn : 0 ≤ p.Δ * (p.L + Real.sqrt (p.ρ * p.ε)) / p.ε ^ 2 := by positivity
  norm_num
  nlinarith

lemma resetScale_public_upper (p : Params) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hσg : 0 ≤ p.σg) (hε : 0 < p.ε) :
    resetScale p ≤ (2 : ℝ) ^ 26 * conjugate p * (1 + p.σg / p.ε) := by
  have hr := conjugate_ge_two p hp hp2
  have hn : 0 ≤ p.σg / p.ε := div_nonneg hσg hε.le
  have hid : resetScale p = 1 + 36000000 * conjugate p * (p.σg / p.ε) := by
    unfold resetScale momentConstant errorScale accuracy
    ring
  rw [hid]
  norm_num
  nlinarith [mul_nonneg (by linarith : 0 ≤ conjugate p) hn]

lemma transportScale_public_upper (p : Params) (hp : 1 < p.p) (hp2 : p.p ≤ 2)
    (hL : 0 < p.L) (hρ : 0 < p.ρ) (hσh : 0 ≤ p.σh) (hε : 0 < p.ε) :
    transportScale p ≤ (2 : ℝ) ^ 20 * conjugate p *
      (p.σh / (p.L + Real.sqrt (p.ρ * p.ε)) + p.ρ * p.ε / (p.L + Real.sqrt (p.ρ * p.ε)) ^ 2) := by
  let S := p.L + Real.sqrt (p.ρ * p.ε)
  have hS : 0 < S := by dsimp [S]; positivity
  have hr := conjugate_ge_two p hp hp2
  have hh := stepSize_pos p hL hρ hε
  have hu : stepSize p ≤ p.ε / (500 * S) := (stepSize_public_bounds p hL hρ hε).2
  have hl : p.σh + p.ρ * stepSize p ≤ p.σh + p.ρ * (p.ε / (500 * S)) := by nlinarith
  have hm := mul_le_mul hl hu hh.le (by positivity : 0 ≤ p.σh + p.ρ * (p.ε / (500 * S)))
  have hb := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 252000000 * conjugate p / p.ε)
  have hid : transportScale p = 252000000 * conjugate p / p.ε *
      ((p.σh + p.ρ * stepSize p) * stepSize p) := by
    unfold transportScale transportNoise momentConstant errorScale accuracy
    ring
  have heq : 252000000 * conjugate p / p.ε *
      ((p.σh + p.ρ * (p.ε / (500 * S))) * (p.ε / (500 * S))) =
      504000 * conjugate p * (p.σh / S) + 1008 * conjugate p * (p.ρ * p.ε / S ^ 2) := by
    field_simp
    ring
  rw [← hid, heq] at hb
  have hn1 : 0 ≤ conjugate p * (p.σh / S) := by positivity
  have hn2 : 0 ≤ conjugate p * (p.ρ * p.ε / S ^ 2) := by positivity
  change transportScale p ≤ (2 : ℝ) ^ 20 * conjugate p * (p.σh / S + p.ρ * p.ε / S ^ 2)
  norm_num
  nlinarith

lemma log_le_self_mul_log_two {r : ℝ} (hr : 2 ≤ r) : Real.log r ≤ r * Real.log 2 := by
  have hr0 : 0 < r := by linarith
  have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < r / 2)
  rw [Real.log_div hr0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h1
  have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h2
  nlinarith [mul_nonneg (by linarith : 0 ≤ r - 1) (by linarith : 0 ≤ Real.log 2 - 1 / 2)]

lemma conjugate_power_envelope {r : ℝ} (hr : 2 ≤ r) : r ^ r ≤ (2 : ℝ) ^ (r ^ 2) := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < r), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right (log_le_self_mul_log_two hr) (by linarith : 0 ≤ r)
  nlinarith

lemma estimator_scale_bound {a z r T A Z U C K : ℝ}
    (ha : 0 ≤ a) (hz : 0 ≤ z) (hr : 1 ≤ r)
    (hA : 0 ≤ A) (hZ : 0 ≤ Z) (hU : 0 ≤ U) (hC : 1 ≤ C) (hK : 1 ≤ K)
    (haA : a ≤ C * A) (hzZ : z ≤ C * Z) (hTU : T ≤ K * U) :
    a ^ r + T * (1 + a ^ (r - 1) * z + z ^ r) ≤
      K * C ^ r * (A ^ r + U * (1 + A ^ (r - 1) * Z + Z ^ r)) := by
  have hC0 : 0 ≤ C := by linarith
  have hpow : 1 ≤ C ^ r := Real.one_le_rpow hC (by linarith)
  have ha1 := Real.rpow_le_rpow ha haA (by linarith : 0 ≤ r)
  rw [Real.mul_rpow hC0 hA] at ha1
  have hz1 := Real.rpow_le_rpow hz hzZ (by linarith : 0 ≤ r)
  rw [Real.mul_rpow hC0 hZ] at hz1
  have ha2 := Real.rpow_le_rpow ha haA (by linarith : 0 ≤ r - 1)
  have ham := mul_le_mul ha2 hzZ hz (Real.rpow_nonneg (mul_nonneg hC0 hA) _)
  rw [Real.mul_rpow hC0 hA] at ham
  have hCp : C ^ (r - 1) * C = C ^ r := by
    rw [← Real.rpow_add_one (by linarith : C ≠ 0)]
    congr 1
    ring
  have hmix : a ^ (r - 1) * z ≤ C ^ r * (A ^ (r - 1) * Z) := by
    calc
      _ ≤ (C ^ (r - 1) * A ^ (r - 1)) * (C * Z) := ham
      _ = (C ^ (r - 1) * C) * (A ^ (r - 1) * Z) := by ring
      _ = _ := by rw [hCp]
  have hsum : 1 + a ^ (r - 1) * z + z ^ r ≤
      C ^ r * (1 + A ^ (r - 1) * Z + Z ^ r) := by nlinarith
  have hsum0 : 0 ≤ 1 + a ^ (r - 1) * z + z ^ r := by positivity
  have hsum1 : 0 ≤ C ^ r * (1 + A ^ (r - 1) * Z + Z ^ r) := by positivity
  have hprod := mul_le_mul hTU hsum hsum0 (by positivity : 0 ≤ K * U)
  have hfirst : C ^ r * A ^ r ≤ K * (C ^ r * A ^ r) := by
    have hb := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ C ^ r * A ^ r)
    simpa only [one_mul] using hb
  nlinarith

lemma estimator_constant_envelope {r : ℝ} (hr : 2 ≤ r) :
    100 * (2 : ℝ) ^ 23 * (((2 : ℝ) ^ 26 * r) ^ r) ≤ (2 : ℝ) ^ (32 * r ^ 2) := by
  have hr0 : 0 ≤ r := by linarith
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 ^ 26) hr0]
  have hb := conjugate_power_envelope hr
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 100 * (2 : ℝ) ^ 23 * ((2 : ℝ) ^ 26) ^ r)
  have hp26 : (((2 : ℝ) ^ 26) ^ r) = (2 : ℝ) ^ (26 * r) := by
    rw [← Real.rpow_natCast (2 : ℝ) 26, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hp26] at hh ⊢
  have h100 : (100 : ℝ) ≤ (2 : ℝ) ^ (7 : ℝ) := by norm_num
  have hc := mul_le_mul_of_nonneg_right h100
    (by positivity : 0 ≤ (2 : ℝ) ^ 23 * ((2 : ℝ) ^ (26 * r)) * (2 : ℝ) ^ (r ^ 2))
  have hid : (2 : ℝ) ^ (7 : ℝ) * ((2 : ℝ) ^ 23 * (2 : ℝ) ^ (26 * r) * (2 : ℝ) ^ (r ^ 2)) =
      (2 : ℝ) ^ (30 + 26 * r + r ^ 2) := by
    rw [← Real.rpow_natCast (2 : ℝ) 23]
    repeat rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hid] at hc
  have he : 30 + 26 * r + r ^ 2 ≤ 32 * r ^ 2 := by nlinarith [sq_nonneg (r - 2)]
  have hd := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  nlinarith

lemma estimator_public_envelope (p : Params) (hvalid : spec.valid p) :
    let S := p.L + Real.sqrt (p.ρ * p.ε)
    let A := 1 + p.σg / p.ε
    let Z := p.σh / S + p.ρ * p.ε / S ^ 2
    let U := 1 + p.Δ * S / p.ε ^ 2
    10 * ((2 * (cycleCount p : ℝ) / (max 1 (epochCount p) : ℕ) + 1) * (max 1 (resetBatch p) : ℕ) +
      2 * cycleCount p * (max 1 (transportBatch p) : ℕ)) ≤
      (2 : ℝ) ^ (32 * conjugate p ^ 2) *
        (A ^ conjugate p + U * (1 + A ^ (conjugate p - 1) * Z + Z ^ conjugate p)) := by
  intro S A Z U
  rcases hvalid with ⟨hd, hL, hρ, hσg, hσh, hp, hp2, hΔ, hε⟩
  have hS : 0 < S := by dsimp [S]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hr := conjugate_ge_two p hp hp2
  let C := (2 : ℝ) ^ 26 * conjugate p
  have hC : 1 ≤ C := by dsimp [C]; norm_num; linarith
  have ha := resetScale_public_upper p hp hp2 hσg hε
  have hz : transportScale p ≤ C * Z := by
    have hh := transportScale_public_upper p hp hp2 hL hρ hσh hε
    change transportScale p ≤ (2 : ℝ) ^ 20 * conjugate p * Z at hh
    have hn : 0 ≤ conjugate p * Z := by positivity
    dsimp [C]
    norm_num at hh ⊢
    nlinarith
  have hT := cycleCount_public_upper p hL hρ hΔ hε
  have hs := estimator_scale_bound
    (le_trans (by norm_num) (resetScale_ge_one p hp hσg hε))
    (transportScale_nonneg p hp hL hρ hσh hε) (by linarith : 1 ≤ conjugate p)
    hA hZ hU hC (by norm_num : (1 : ℝ) ≤ (2 : ℝ) ^ 23) ha hz hT
  have hw := estimator_work_upper p hp hp2 hL hρ hσg hσh hε
  have hc := estimator_constant_envelope hr
  have hX : 0 ≤ A ^ conjugate p + U * (1 + A ^ (conjugate p - 1) * Z + Z ^ conjugate p) := by positivity
  have hlast := mul_le_mul_of_nonneg_right hc hX
  change 100 * (2 : ℝ) ^ 23 * C ^ conjugate p * _ ≤ _ at hlast
  nlinarith

end LongTails.Proofs.HeavyTailedSospCost
