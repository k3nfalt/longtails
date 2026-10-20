import LongTails.Proofs.RiverValleyExpect

namespace OracleTemplate.RiverValley

lemma amgm_le {x y c : ℝ} (hc : 0 < c) : x * y ≤ c * x ^ 2 / 2 + y ^ 2 / (2 * c) := by
  have h : 0 ≤ (c * x - y) ^ 2 / (2 * c) := by positivity
  have e : (c * x - y) ^ 2 / (2 * c) = c * x ^ 2 / 2 + y ^ 2 / (2 * c) - x * y := by
    field_simp; ring
  linarith

lemma t_r0m {η Γ LJ G Luv lam μ na nw nm nr0 nd0 Lm : ℝ} (hη0 : 0 ≤ η) (hΓ0 : 0 ≤ Γ)
    (hΓ : Γ ≤ 1 / 16) (hLJ : 0 ≤ LJ) (hLuv : 0 ≤ Luv) (hna : 0 ≤ na) (hnaG : na ≤ G)
    (hnm : nm ≤ Γ * na) (hnr0 : 0 ≤ nr0) (hnr0a : nr0 ≤ LJ * nd0 ^ 2)
    (hnd0 : 0 ≤ nd0) (hnd0' : nd0 ≤ η * (na + Luv * nw)) (hη2μ : η ^ 2 * μ ≤ η / 8)
    (hLJGμ : 128 * (LJ * G) ≤ μ) (hηLuv : η * Luv ≤ 1 / 128) (hLJGLm : LJ * G ≤ Lm)
    (hlam0 : 0 ≤ lam) (hμ : 0 < μ) (hlamLuv : 32 * Lm * Luv ≤ lam * μ) :
    nm * nr0 ≤ η * na ^ 2 / 8192 + η * lam * μ * nw ^ 2 / 64 := by
  have hG : 0 ≤ G := hna.trans hnaG
  have hd2 : nd0 ^ 2 ≤ 2 * η ^ 2 * (na ^ 2 + Luv ^ 2 * nw ^ 2) := by
    have h1 := pow_le_pow_left₀ hnd0 hnd0' 2
    have hs : (na + Luv * nw) ^ 2 ≤ 2 * (na ^ 2 + Luv ^ 2 * nw ^ 2) := by
      nlinarith [sq_nonneg (na - Luv * nw)]
    have h2 := mul_le_mul_of_nonneg_left hs (sq_nonneg η)
    have e : (η * (na + Luv * nw)) ^ 2 = η ^ 2 * (na + Luv * nw) ^ 2 := by ring
    linarith
  have h1 : nm * nr0 ≤ Γ * na * (LJ * (2 * η ^ 2 * (na ^ 2 + Luv ^ 2 * nw ^ 2))) := by
    have hnr : nr0 ≤ LJ * (2 * η ^ 2 * (na ^ 2 + Luv ^ 2 * nw ^ 2)) :=
      hnr0a.trans (mul_le_mul_of_nonneg_left hd2 hLJ)
    exact mul_le_mul hnm hnr hnr0 (mul_nonneg hΓ0 hna)
  have h2 : Γ * na * (LJ * (2 * η ^ 2 * (na ^ 2 + Luv ^ 2 * nw ^ 2))) ≤
      2 * Γ * (LJ * G) * η ^ 2 * na ^ 2 + 2 * Γ * (LJ * G) * (η * Luv) ^ 2 * nw ^ 2 := by
    have := mul_le_mul_of_nonneg_left hnaG
      (by positivity : 0 ≤ 2 * Γ * LJ * η ^ 2 * (na ^ 2 + Luv ^ 2 * nw ^ 2))
    linear_combination this
  have h3 : 2 * Γ * (LJ * G) * η ^ 2 * na ^ 2 ≤ η * na ^ 2 / 8192 := by
    have a1 : (LJ * G) * η ^ 2 ≤ η / 1024 := by
      have := mul_le_mul_of_nonneg_left hLJGμ (sq_nonneg η)
      linarith
    have a2 := mul_le_mul hΓ a1 (by positivity) (by norm_num)
    have := mul_le_mul_of_nonneg_left a2 (by positivity : (0:ℝ) ≤ 2 * na ^ 2)
    linarith
  have h4 : 2 * Γ * (LJ * G) * (η * Luv) ^ 2 * nw ^ 2 ≤ η * lam * μ * nw ^ 2 / 64 := by
    have a1 : (η * Luv) ^ 2 ≤ η * Luv / 128 := by
      have := mul_le_mul_of_nonneg_left hηLuv (mul_nonneg hη0 hLuv)
      linarith
    have a2 : 2 * Γ * (LJ * G) ≤ Lm / 8 := by
      have := mul_le_mul hΓ hLJGLm (by positivity) (by norm_num); linarith
    have hLm0 : 0 ≤ Lm := le_trans (mul_nonneg hLJ hG) hLJGLm
    have a3 : 2 * Γ * (LJ * G) * (η * Luv) ^ 2 ≤ Lm / 8 * (η * Luv / 128) :=
      mul_le_mul a2 a1 (sq_nonneg _) (by positivity)
    have a4 : Lm / 8 * (η * Luv / 128) ≤ η * lam * μ / 64 := by
      have := mul_le_mul_of_nonneg_left hlamLuv hη0
      have : 0 ≤ η * lam * μ := by positivity
      linarith
    have := mul_le_mul_of_nonneg_right (a3.trans a4) (sq_nonneg nw)
    linarith
  linarith

lemma t_r0Y {η Γ LJ G Luv lam μ Lv na nw nY nr0 : ℝ} (hη0 : 0 ≤ η) (hΓ0 : 0 ≤ Γ)
    (hΓ2 : Γ ^ 2 ≤ 1 / 256) (hLJ : 0 ≤ LJ) (hLuv : Luv = Γ * μ) (hμ : 0 < μ) (hμLv : μ ≤ Lv)
    (hna : 0 ≤ na) (hnaG : na ≤ G) (hnw : 0 ≤ nw) (hlam0 : 0 ≤ lam) (hlamμ : lam ≤ μ / 8)
    (hnY' : nY ≤ 2 * nw + η * Γ * na) (hnr0 : 0 ≤ nr0)
    (hnr0b : nr0 ≤ 4 * LJ * η ^ 2 * na ^ 2 + 4 * Γ * η * Luv * nw) (hηLv : 8 * η * Lv ≤ 1)
    (hLJGμ : 128 * (LJ * G) ≤ μ) (hηLuv : η * Luv ≤ 1 / 128) :
    2 * lam * nY * nr0 ≤ η * na ^ 2 * (5 / 128) + η * lam * μ * nw ^ 2 * (3 / 32) := by
  have hG : 0 ≤ G := hna.trans hnaG
  have hΓ16 : Γ ≤ 1 / 16 := by nlinarith
  have hημ : η * μ ≤ 1 / 8 := by
    have := mul_le_mul_of_nonneg_left hμLv hη0; linarith
  have c2 : η ^ 2 * μ ^ 2 ≤ 1 / 64 := by
    have := pow_le_pow_left₀ (mul_nonneg hη0 hμ.le) hημ 2
    have e : (η * μ) ^ 2 = η ^ 2 * μ ^ 2 := by ring
    linarith
  have hlμ : 0 ≤ lam * μ := by positivity
  have h0 : 2 * lam * nY * nr0 ≤
      2 * lam * ((2 * nw + η * Γ * na) * (4 * LJ * η ^ 2 * na ^ 2 + 4 * Γ * η * Luv * nw)) := by
    have e : 2 * lam * nY * nr0 = 2 * lam * (nY * nr0) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul hnY' hnr0b hnr0 (by positivity)
  have ha : 2 * lam * (2 * nw * (4 * LJ * η ^ 2 * na ^ 2)) ≤
      η * na ^ 2 / 64 + η * lam * μ * nw ^ 2 / 64 := by
    have b1 : 2 * lam * (2 * nw * (4 * LJ * η ^ 2 * na ^ 2)) ≤
        η * (16 * lam * (LJ * G) * η) * (na * nw) := by
      have := mul_le_mul_of_nonneg_left hnaG
        (by positivity : (0:ℝ) ≤ 16 * lam * LJ * η ^ 2 * na * nw)
      linear_combination this
    have b2 : 16 * lam * (LJ * G) * η * (na * nw) ≤
        na ^ 2 / 64 + 16 * (16 * lam * (LJ * G) * η) ^ 2 * nw ^ 2 := by
      have := amgm_le (x := na) (y := 16 * lam * (LJ * G) * η * nw) (c := 1 / 32) (by norm_num)
      linear_combination this
    have b3 : 16 * (16 * lam * (LJ * G) * η) ^ 2 ≤ lam * μ / 64 := by
      have c1 : (LJ * G) ^ 2 ≤ μ ^ 2 / 16384 := by
        have := pow_le_pow_left₀ (mul_nonneg hLJ hG) (by linarith : LJ * G ≤ μ / 128) 2
        linarith
      have c3 : lam ^ 2 ≤ lam * μ / 8 := by
        have := mul_le_mul_of_nonneg_left hlamμ hlam0; linarith
      have d1 := mul_le_mul c3 c1 (sq_nonneg _) (by positivity)
      have d2 := mul_le_mul_of_nonneg_left d1 (by positivity : (0:ℝ) ≤ 4096 * η ^ 2)
      have d4 := mul_le_mul_of_nonneg_left c2 (by positivity : (0:ℝ) ≤ lam * μ / 32)
      linarith
    have b4 := mul_le_mul_of_nonneg_left b2 hη0
    have b5 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right b3 (sq_nonneg nw)) hη0
    linarith
  have hb : 2 * lam * (2 * nw * (4 * Γ * η * Luv * nw)) ≤ η * lam * μ * nw ^ 2 / 16 := by
    rw [hLuv]
    have := mul_le_mul_of_nonneg_left hΓ2 (by positivity : (0:ℝ) ≤ 16 * lam * η * μ * nw ^ 2)
    linarith
  have hc : 2 * lam * (η * Γ * na * (4 * LJ * η ^ 2 * na ^ 2)) ≤ η * na ^ 2 / 128 := by
    have b1 : 2 * lam * (η * Γ * na * (4 * LJ * η ^ 2 * na ^ 2)) ≤
        η * na ^ 2 * (8 * lam * Γ * (LJ * G) * η ^ 2) := by
      have := mul_le_mul_of_nonneg_left hnaG
        (by positivity : (0:ℝ) ≤ 8 * lam * η ^ 3 * Γ * LJ * na ^ 2)
      linear_combination this
    have b2 : 8 * lam * Γ * (LJ * G) * η ^ 2 ≤ 1 / 128 := by
      have c3 : lam * (LJ * G) ≤ μ / 8 * (μ / 128) :=
        mul_le_mul hlamμ (by linarith) (mul_nonneg hLJ hG) (by positivity)
      have c4 := mul_le_mul hΓ16 c3 (by positivity) (by norm_num)
      have c5 := mul_le_mul_of_nonneg_left c4 (by positivity : (0:ℝ) ≤ 8 * η ^ 2)
      linarith
    have := mul_le_mul_of_nonneg_left b2 (by positivity : (0:ℝ) ≤ η * na ^ 2)
    linarith
  have hd : 2 * lam * (η * Γ * na * (4 * Γ * η * Luv * nw)) ≤
      η * na ^ 2 / 64 + η * lam * μ * nw ^ 2 / 64 := by
    have b1 : 2 * lam * (η * Γ * na * (4 * Γ * η * Luv * nw)) ≤
        η * (lam * Γ ^ 2 / 16) * (na * nw) := by
      have := mul_le_mul_of_nonneg_left hηLuv
        (by positivity : (0:ℝ) ≤ 8 * lam * η * Γ ^ 2 * na * nw)
      linear_combination this
    have b2 : lam * Γ ^ 2 / 16 * (na * nw) ≤
        na ^ 2 / 64 + 16 * (lam * Γ ^ 2 / 16) ^ 2 * nw ^ 2 := by
      have := amgm_le (x := na) (y := lam * Γ ^ 2 / 16 * nw) (c := 1 / 32) (by norm_num)
      linear_combination this
    have b3 : 16 * (lam * Γ ^ 2 / 16) ^ 2 ≤ lam * μ / 64 := by
      have g4 : Γ ^ 4 ≤ 1 / 65536 := by
        have := pow_le_pow_left₀ (sq_nonneg Γ) hΓ2 2
        linarith
      have c1 : lam * Γ ^ 4 ≤ μ / 8 * (1 / 65536) :=
        mul_le_mul hlamμ g4 (by positivity) (by positivity)
      have := mul_le_mul_of_nonneg_left c1 hlam0
      linarith
    have b4 := mul_le_mul_of_nonneg_left b2 hη0
    have b5 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right b3 (sq_nonneg nw)) hη0
    linarith
  have hsplit : 2 * lam * ((2 * nw + η * Γ * na) * (4 * LJ * η ^ 2 * na ^ 2 +
      4 * Γ * η * Luv * nw)) =
      2 * lam * (2 * nw * (4 * LJ * η ^ 2 * na ^ 2)) +
      2 * lam * (2 * nw * (4 * Γ * η * Luv * nw)) +
      2 * lam * (η * Γ * na * (4 * LJ * η ^ 2 * na ^ 2)) +
      2 * lam * (η * Γ * na * (4 * Γ * η * Luv * nw)) := by ring
  linarith

lemma t_noiseY {η Γ LJ G lam μ Lv na nw nY c2 σu : ℝ} (hη0 : 0 ≤ η) (hΓ0 : 0 ≤ Γ)
    (hLJ : 0 ≤ LJ) (hμ : 0 < μ) (hμLv : μ ≤ Lv) (hna : 0 ≤ na) (hnaG : na ≤ G)
    (hlam0 : 0 ≤ lam) (hnY' : nY ≤ 2 * nw + η * Γ * na) (hηLv : 8 * η * Lv ≤ 1)
    (hc2 : 0 ≤ c2) (hσu : 0 ≤ σu) (hlamc : 2 * c2 * σu / Lv ≤ lam) :
    2 * lam * nY * (LJ * η ^ 2 * σu ^ 2) + nY * (c2 * η ^ 2 * σu ^ 2) ≤
      η * lam * μ * nw ^ 2 / 8 + η ^ 2 * (8 * lam * LJ ^ 2 * σu ^ 4 / (μ * Lv) +
        lam * LJ * Γ * G * σu ^ 2 / (4 * Lv) + c2 * σu ^ 3 / μ + c2 * Γ * G * σu ^ 2 / (8 * Lv)) := by
  have hG : 0 ≤ G := hna.trans hnaG
  have hLv : 0 < Lv := lt_of_lt_of_le hμ hμLv
  have hY2 : nY ≤ 2 * nw + η * Γ * G :=
    hnY'.trans (by have := mul_le_mul_of_nonneg_left hnaG (mul_nonneg hη0 hΓ0); linarith)
  have hη3 : η ^ 3 ≤ η ^ 2 / (8 * Lv) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hηLv (sq_nonneg η); linarith
  have k1 : 2 * lam * nY * (LJ * η ^ 2 * σu ^ 2) ≤
      2 * lam * (2 * nw + η * Γ * G) * (LJ * η ^ 2 * σu ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY2 (by positivity)) (by positivity)
  have k2 : nY * (c2 * η ^ 2 * σu ^ 2) ≤ (2 * nw + η * Γ * G) * (c2 * η ^ 2 * σu ^ 2) :=
    mul_le_mul_of_nonneg_right hY2 (by positivity)
  have k3 : 4 * lam * LJ * η ^ 2 * σu ^ 2 * nw ≤
      η * lam * μ * nw ^ 2 / 16 + 64 * lam * LJ ^ 2 * η ^ 3 * σu ^ 4 / μ := by
    have h0 : 0 ≤ η * lam / (16 * μ) * (μ * nw - 32 * LJ * η * σu ^ 2) ^ 2 := by positivity
    have e : η * lam / (16 * μ) * (μ * nw - 32 * LJ * η * σu ^ 2) ^ 2 =
        η * lam * μ * nw ^ 2 / 16 + 64 * lam * LJ ^ 2 * η ^ 3 * σu ^ 4 / μ -
          4 * lam * LJ * η ^ 2 * σu ^ 2 * nw := by
      field_simp; ring
    linarith
  have k4 : 64 * lam * LJ ^ 2 * η ^ 3 * σu ^ 4 / μ ≤ η ^ 2 * (8 * lam * LJ ^ 2 * σu ^ 4 / (μ * Lv)) := by
    have := mul_le_mul_of_nonneg_left hη3 (by positivity : (0:ℝ) ≤ 64 * lam * LJ ^ 2 * σu ^ 4 / μ)
    have e1 : 64 * lam * LJ ^ 2 * σu ^ 4 / μ * η ^ 3 = 64 * lam * LJ ^ 2 * η ^ 3 * σu ^ 4 / μ := by
      ring
    have e2 : 64 * lam * LJ ^ 2 * σu ^ 4 / μ * (η ^ 2 / (8 * Lv)) =
        η ^ 2 * (8 * lam * LJ ^ 2 * σu ^ 4 / (μ * Lv)) := by field_simp; ring
    linarith
  have k5 : 2 * lam * (η * Γ * G) * (LJ * η ^ 2 * σu ^ 2) ≤
      η ^ 2 * (lam * LJ * Γ * G * σu ^ 2 / (4 * Lv)) := by
    have := mul_le_mul_of_nonneg_left hη3 (by positivity : (0:ℝ) ≤ 2 * lam * Γ * G * LJ * σu ^ 2)
    have e2 : 2 * lam * Γ * G * LJ * σu ^ 2 * (η ^ 2 / (8 * Lv)) =
        η ^ 2 * (lam * LJ * Γ * G * σu ^ 2 / (4 * Lv)) := by field_simp; ring
    nlinarith
  have k6 : 2 * nw * (c2 * η ^ 2 * σu ^ 2) ≤
      c2 * η ^ 2 * σu * μ * nw ^ 2 + η ^ 2 * (c2 * σu ^ 3 / μ) := by
    have h0 : 0 ≤ c2 * η ^ 2 * σu / μ * (μ * nw - σu) ^ 2 := by positivity
    have e : c2 * η ^ 2 * σu / μ * (μ * nw - σu) ^ 2 =
        c2 * η ^ 2 * σu * μ * nw ^ 2 + η ^ 2 * (c2 * σu ^ 3 / μ) - 2 * nw * (c2 * η ^ 2 * σu ^ 2) := by
      field_simp; ring
    linarith
  have k7 : c2 * η ^ 2 * σu * μ * nw ^ 2 ≤ η * lam * μ * nw ^ 2 / 16 := by
    have a1 : c2 * σu * η ≤ lam / 16 := by
      have b1 : c2 * σu * η ≤ c2 * σu / (8 * Lv) := by
        rw [le_div_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_left hηLv (mul_nonneg hc2 hσu); linarith
      have b2 : c2 * σu / (8 * Lv) = (2 * c2 * σu / Lv) / 16 := by field_simp; ring
      linarith
    have := mul_le_mul_of_nonneg_left a1 (by positivity : (0:ℝ) ≤ η * μ * nw ^ 2)
    nlinarith
  have k8 : η * Γ * G * (c2 * η ^ 2 * σu ^ 2) ≤ η ^ 2 * (c2 * Γ * G * σu ^ 2 / (8 * Lv)) := by
    have := mul_le_mul_of_nonneg_left hη3 (by positivity : (0:ℝ) ≤ Γ * G * c2 * σu ^ 2)
    have e2 : Γ * G * c2 * σu ^ 2 * (η ^ 2 / (8 * Lv)) =
        η ^ 2 * (c2 * Γ * G * σu ^ 2 / (8 * Lv)) := by field_simp
    nlinarith
  have e1 : 2 * lam * (2 * nw + η * Γ * G) * (LJ * η ^ 2 * σu ^ 2) =
      4 * lam * LJ * η ^ 2 * σu ^ 2 * nw + 2 * lam * (η * Γ * G) * (LJ * η ^ 2 * σu ^ 2) := by ring
  have e2 : (2 * nw + η * Γ * G) * (c2 * η ^ 2 * σu ^ 2) =
      2 * nw * (c2 * η ^ 2 * σu ^ 2) + η * Γ * G * (c2 * η ^ 2 * σu ^ 2) := by ring
  nlinarith

lemma t_drift {η Γ μ Luv lam na nw nY nd0 Lm : ℝ} (hη0 : 0 ≤ η) (hΓ0 : 0 ≤ Γ)
    (hΓ : Γ ≤ 1 / 16) (hna : 0 ≤ na) (hnw : 0 ≤ nw)
    (hnY' : nY ≤ 2 * nw + η * Γ * na) (hnd0 : 0 ≤ nd0)
    (hnd0' : nd0 ≤ η * (na + Luv * nw)) (hLm0 : 0 ≤ Lm) (hLmμ : 64 * Lm ≤ μ)
    (hη2μ : η ^ 2 * μ ≤ η / 8) (hηLuv : η * Luv ≤ 1 / 128) (hlamLm : 256 * Lm ^ 2 ≤ lam * μ)
    (hlamLuv : 32 * Lm * Luv ≤ lam * μ) :
    nY * (Lm * nd0) ≤ η * na ^ 2 / 15 + η * lam * μ * nw ^ 2 / 7 := by
  have h0 : nY * (Lm * nd0) ≤ (2 * nw + η * Γ * na) * (Lm * (η * (na + Luv * nw))) :=
    mul_le_mul hnY' (mul_le_mul_of_nonneg_left hnd0' hLm0) (by positivity) (by positivity)
  have e : (2 * nw + η * Γ * na) * (Lm * (η * (na + Luv * nw))) =
      η * (2 * Lm * (na * nw)) + η * (2 * Lm * Luv) * nw ^ 2 + η ^ 2 * (Γ * Lm) * na ^ 2 +
        η * (Γ * Lm * (η * Luv)) * (na * nw) := by ring
  have a1 : 2 * Lm * (na * nw) ≤ na ^ 2 / 16 + lam * μ * nw ^ 2 / 16 := by
    have h1 := amgm_le (x := na) (y := 2 * Lm * nw) (c := 1 / 8) (by norm_num)
    have h2 : 16 * Lm ^ 2 * nw ^ 2 ≤ lam * μ * nw ^ 2 / 16 := by
      have := mul_le_mul_of_nonneg_right hlamLm (sq_nonneg nw); linarith
    linear_combination h1 + h2
  have a2 : 2 * Lm * Luv ≤ lam * μ / 16 := by linarith
  have a3 : η ^ 2 * (Γ * Lm) ≤ η / 8192 := by
    have b1 : Γ * Lm ≤ μ / 1024 := by
      have := mul_le_mul hΓ (by linarith : Lm ≤ μ / 64) hLm0 (by norm_num); linarith
    have := mul_le_mul_of_nonneg_left b1 (sq_nonneg η)
    nlinarith
  have a4 : Γ * Lm * (η * Luv) * (na * nw) ≤ na ^ 2 / 65536 + lam * μ * nw ^ 2 / 65536 := by
    have b1 : Γ * Lm * (η * Luv) ≤ Γ * Lm / 128 :=
      by have := mul_le_mul_of_nonneg_left hηLuv (mul_nonneg hΓ0 hLm0); linarith
    have b2 : Γ * Lm / 128 * (na * nw) ≤ Γ ^ 2 * na ^ 2 / 256 + Lm ^ 2 * nw ^ 2 / 256 := by
      nlinarith [sq_nonneg (Γ * na - Lm * nw)]
    have b3 : Γ ^ 2 * na ^ 2 / 256 ≤ na ^ 2 / 65536 := by
      have : Γ ^ 2 ≤ 1 / 256 := by nlinarith
      have := mul_le_mul_of_nonneg_right this (sq_nonneg na); linarith
    have b4 : Lm ^ 2 * nw ^ 2 / 256 ≤ lam * μ * nw ^ 2 / 65536 := by
      have := mul_le_mul_of_nonneg_right hlamLm (sq_nonneg nw); linarith
    have := mul_le_mul_of_nonneg_right b1 (mul_nonneg hna hnw)
    linarith
  have f1 := mul_le_mul_of_nonneg_left a1 hη0
  have f2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right a2 (sq_nonneg nw)) hη0
  have f3 := mul_le_mul_of_nonneg_right a3 (sq_nonneg na)
  have f4 := mul_le_mul_of_nonneg_left a4 hη0
  have hlμ : 0 ≤ lam * μ := le_trans (by positivity) hlamLm
  have : 0 ≤ η * lam * μ * nw ^ 2 := by
    have := mul_nonneg (mul_nonneg hη0 hlμ) (sq_nonneg nw); linarith
  nlinarith

lemma t_Cd {η Γ μ Lh Luv lam na nw nd0 Lm Lm' : ℝ} (hΓ0 : 0 ≤ Γ)
    (hΓ : Γ ≤ 1 / 16) (hμ : 0 < μ) (hLuv : Luv = Γ * μ) (hLh : 0 ≤ Lh) (hLh16 : 16 * Lh ≤ μ)
    (hnd0 : 0 ≤ nd0) (hnd0' : nd0 ≤ η * (na + Luv * nw))
    (hLm0 : 0 ≤ Lm) (hLmLm' : Lm ≤ Lm') (hLmμ : 64 * Lm' ≤ μ) (hΓLh : Γ * Lh ≤ Lm')
    (hη2μ : η ^ 2 * μ ≤ η / 8) (hlam0 : 0 ≤ lam) (hlamμ : lam ≤ μ / 8)
    (hlamΓ : 32 * Γ * Lm' ≤ lam) :
    (Lh / 2 + 2 * Γ * Lm + 8 * lam * Γ ^ 2) * (2 * nd0 ^ 2) ≤
      η * na ^ 2 / 32 + η * lam * μ * nw ^ 2 / 16 := by
  set Cd := Lh / 2 + 2 * Γ * Lm + 8 * lam * Γ ^ 2
  have hΓ2 : Γ ^ 2 ≤ 1 / 256 := by nlinarith
  have hCd0 : 0 ≤ Cd := by positivity
  have hCdμ : Cd ≤ μ / 16 := by
    have b1 : 2 * Γ * Lm ≤ μ / 512 := by
      have := mul_le_mul hΓ (by linarith : Lm ≤ μ / 64) hLm0 (by norm_num); linarith
    have b2 : 8 * lam * Γ ^ 2 ≤ μ / 256 := by
      have := mul_le_mul hlamμ hΓ2 (sq_nonneg _) (by positivity); linarith
    simp only [Cd]; linarith
  have hCdΓ : 8 * Cd * Γ ^ 2 ≤ lam := by
    have b1 : 4 * Γ ^ 2 * Lh ≤ lam / 8 := by
      have := mul_le_mul_of_nonneg_left hΓLh hΓ0
      nlinarith
    have b2 : 16 * Γ ^ 3 * Lm ≤ lam / 512 := by
      have c1 : Γ ^ 2 * (32 * Γ * Lm') ≤ 1 / 256 * lam := mul_le_mul hΓ2 hlamΓ
        (mul_nonneg (mul_nonneg (by norm_num) hΓ0) (hLm0.trans hLmLm')) (by norm_num)
      have c2 := mul_le_mul_of_nonneg_left hLmLm' (pow_nonneg hΓ0 3)
      nlinarith
    have b3 : 64 * lam * Γ ^ 4 ≤ lam / 1024 := by
      have : Γ ^ 4 ≤ 1 / 65536 := by
        have := pow_le_pow_left₀ (sq_nonneg Γ) hΓ2 2; nlinarith
      have := mul_le_mul_of_nonneg_left this hlam0; linarith
    have e : 8 * Cd * Γ ^ 2 = 4 * Γ ^ 2 * Lh + 16 * Γ ^ 3 * Lm + 64 * lam * Γ ^ 4 := by
      simp only [Cd]; ring
    linarith
  have hd2 : nd0 ^ 2 ≤ 2 * η ^ 2 * (na ^ 2 + Luv ^ 2 * nw ^ 2) := by
    have h1 := pow_le_pow_left₀ hnd0 hnd0' 2
    have hs : (na + Luv * nw) ^ 2 ≤ 2 * (na ^ 2 + Luv ^ 2 * nw ^ 2) := by
      nlinarith [sq_nonneg (na - Luv * nw)]
    have h2 := mul_le_mul_of_nonneg_left hs (sq_nonneg η)
    have e : (η * (na + Luv * nw)) ^ 2 = η ^ 2 * (na + Luv * nw) ^ 2 := by ring
    linarith
  have h1 := mul_le_mul_of_nonneg_left hd2 (by positivity : (0:ℝ) ≤ 2 * Cd)
  have a1 : 4 * Cd * η ^ 2 * na ^ 2 ≤ η * na ^ 2 / 32 := by
    have := mul_le_mul_of_nonneg_left hCdμ (by positivity : (0:ℝ) ≤ 4 * η ^ 2 * na ^ 2)
    nlinarith
  have a2 : 4 * Cd * η ^ 2 * Luv ^ 2 * nw ^ 2 ≤ η * lam * μ * nw ^ 2 / 16 := by
    rw [hLuv]
    have b1 : 4 * Cd * η ^ 2 * (Γ * μ) ^ 2 = (8 * Cd * Γ ^ 2) * (η ^ 2 * μ) * μ / 2 := by ring
    have b2 := mul_le_mul hCdΓ hη2μ (by positivity) hlam0
    have b3 := mul_le_mul_of_nonneg_right b2 (by positivity : (0:ℝ) ≤ μ * nw ^ 2 / 2)
    nlinarith
  nlinarith

lemma descent_real {η μ Lv Lh LJ G Γ Luv lam σu σv Lm Lm' c2 c' na nw nm nY nd0 nr0 mJa Ysq : ℝ}
    (hμ : 0 < μ) (hμLv : μ ≤ Lv) (hη0 : 0 ≤ η) (hη : 8 * η * Lv ≤ 1) (hΓ0 : 0 ≤ Γ)
    (hΓ : 16 * Γ ≤ 1) (hLuv : Luv = Γ * μ) (hLh : 0 ≤ Lh) (hLh16 : 16 * Lh ≤ μ) (hLJ : 0 ≤ LJ)
    (hG : 0 ≤ G) (hσu : 0 ≤ σu)
    (hLm : Lm = Γ * Lh + LJ * G + 2 * Γ ^ 2 * LJ * G) (hLm' : Lm' = Γ * Lh + 2 * LJ * G)
    (hLmμ : 64 * Lm' ≤ μ) (hc2 : 0 ≤ c2) (hc2c : c2 ≤ c') (hcσ : 64 * c' * σu ≤ μ * Lv)
    (hlam : lam = (256 * Lm' ^ 2 + 32 * Lm' * Luv) / μ + 2 * c' * σu / Lv)
    (hna : 0 ≤ na) (hnaG : na ≤ G) (hnw : 0 ≤ nw) (hnm' : nm ≤ Γ * na)
    (hmJa : mJa ≤ Γ ^ 2 * na ^ 2)
    (hY : Ysq ≤ (1 - η * μ) * nw ^ 2 + 3 * η * Γ ^ 2 * na ^ 2 / μ)
    (hnY' : nY ≤ 2 * nw + η * Γ * na)
    (hnd0 : 0 ≤ nd0) (hnd0' : nd0 ≤ η * (na + Luv * nw))
    (hnr0 : 0 ≤ nr0) (hnr0a : nr0 ≤ LJ * nd0 ^ 2)
    (hnr0b : nr0 ≤ 4 * LJ * η ^ 2 * na ^ 2 + 4 * Γ * η * Luv * nw) :
    -η * (na ^ 2 - mJa) + lam * (Ysq - nw ^ 2) + (nm + 2 * lam * nY) * (nr0 + LJ * η ^ 2 * σu ^ 2) +
        nY * (Lm * nd0 + c2 * η ^ 2 * σu ^ 2) +
        (Lh / 2 + 2 * Γ * Lm + 8 * lam * Γ ^ 2) * (2 * nd0 ^ 2 + 2 * η ^ 2 * σu ^ 2) +
        2 * lam * η ^ 2 * (2 * σv ^ 2 + 2 * Γ ^ 2 * σu ^ 2) + Lm * η ^ 2 * (σu * σv + Γ * σu ^ 2) ≤
      -(η / 2) * na ^ 2 - η * lam * μ / 2 * nw ^ 2 +
        η ^ 2 * (2 * (Lh / 2 + 2 * Γ * Lm + 8 * lam * Γ ^ 2) * σu ^ 2 +
          4 * lam * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + Lm * (σu * σv + Γ * σu ^ 2) +
          Γ * G * LJ * σu ^ 2 + c' * σu ^ 3 / μ + c' * Γ * G * σu ^ 2 / (8 * Lv) +
          8 * lam * LJ ^ 2 * σu ^ 4 / (μ * Lv) + lam * LJ * Γ * G * σu ^ 2 / (4 * Lv)) := by
  have hLv : 0 < Lv := lt_of_lt_of_le hμ hμLv
  -- parameter facts
  have hLJG : 0 ≤ LJ * G := mul_nonneg hLJ hG
  have hΓLh : 0 ≤ Γ * Lh := mul_nonneg hΓ0 hLh
  have hLm'0 : 0 ≤ Lm' := by rw [hLm']; linarith
  have hLmLm' : Lm ≤ Lm' := by
    have : 2 * Γ ^ 2 * LJ * G ≤ LJ * G := by
      have h1 : 2 * Γ ^ 2 ≤ 1 := by nlinarith
      have := mul_le_mul_of_nonneg_right h1 hLJG
      linarith
    rw [hLm, hLm']; linarith
  have hLm0 : 0 ≤ Lm := by rw [hLm]; positivity
  have hc'0 : 0 ≤ c' := le_trans hc2 hc2c
  have hLJGμ : 128 * (LJ * G) ≤ μ := by
    have : 2 * (LJ * G) ≤ Lm' := by rw [hLm']; linarith
    linarith
  have hΓLm'2 : 32 * Γ * Lm' ≤ 2 * Lm' := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 16 * Γ) hLm'0
    linarith
  have hlam1 : 256 * Lm' ^ 2 / μ ≤ μ / 16 := by
    rw [div_le_div_iff₀ hμ (by norm_num)]
    have h := mul_le_mul hLmμ hLmμ (by positivity) hμ.le
    linear_combination h
  have hlam3 : 2 * c' * σu / Lv ≤ μ / 32 := by
    rw [div_le_div_iff₀ hLv (by norm_num)]; linear_combination hcσ
  have hA0 : 0 ≤ 256 * Lm' ^ 2 / μ := by positivity
  have hC0 : 0 ≤ 2 * c' * σu / Lv := by positivity
  have hlamEq : lam = 256 * Lm' ^ 2 / μ + 32 * Γ * Lm' + 2 * c' * σu / Lv := by
    rw [hlam, hLuv]; field_simp
  have hlam0 : 0 ≤ lam := by rw [hlamEq]; have := mul_nonneg hΓ0 hLm'0; linarith
  have hlamμ : lam ≤ μ / 8 := by rw [hlamEq]; linarith
  have hlamμE : lam * μ = 256 * Lm' ^ 2 + (32 * Γ * Lm' + 2 * c' * σu / Lv) * μ := by
    rw [hlamEq]; field_simp; ring
  have hlamLm : 256 * Lm ^ 2 ≤ lam * μ := by
    have h1 := pow_le_pow_left₀ hLm0 hLmLm' 2
    have h2 : 0 ≤ (32 * Γ * Lm' + 2 * c' * σu / Lv) * μ := by
      have := mul_nonneg hΓ0 hLm'0; positivity
    linarith
  have hlamΓ : 32 * Γ * Lm' ≤ lam := by rw [hlamEq]; linarith
  have hlamLuv : 32 * Lm * Luv ≤ lam * μ := by
    have h1 : 32 * Γ * Lm' * μ ≤ lam * μ := mul_le_mul_of_nonneg_right hlamΓ hμ.le
    have h2 : 32 * Lm * Luv ≤ 32 * Γ * Lm' * μ := by
      rw [hLuv]
      have := mul_le_mul_of_nonneg_right hLmLm' (mul_nonneg hΓ0 hμ.le)
      linarith
    linarith
  have hlamc : 2 * c2 * σu / Lv ≤ lam := by
    have : 2 * c2 * σu / Lv ≤ 2 * c' * σu / Lv := by
      apply div_le_div_of_nonneg_right _ hLv.le
      have := mul_le_mul_of_nonneg_right hc2c hσu
      linarith
    rw [hlamEq]; have := mul_nonneg hΓ0 hLm'0; linarith
  have hημ : η * μ ≤ 1 / 8 := by
    have := mul_le_mul_of_nonneg_left hμLv hη0; linarith
  have hηLv : η * Lv ≤ 1 / 8 := by linarith
  have hΓ16 : Γ ≤ 1 / 16 := by linarith
  have hΓ2 : Γ ^ 2 ≤ 1 / 256 := by
    calc Γ ^ 2 = Γ * Γ := sq Γ
      _ ≤ 1 / 16 * (1 / 16) := mul_le_mul hΓ16 hΓ16 hΓ0 (by norm_num)
      _ = 1 / 256 := by norm_num
  have hηLuv : η * Luv ≤ 1 / 128 := by
    rw [hLuv]
    have h1 := mul_le_mul hΓ16 hημ (mul_nonneg hη0 hμ.le) (by norm_num)
    linear_combination h1
  have hLuv0 : 0 ≤ Luv := by rw [hLuv]; positivity
  have hη2 : η ^ 2 ≤ η / (8 * Lv) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hη hη0
    linear_combination this
  have hη2μ : η ^ 2 * μ ≤ η / 8 := by
    have := mul_le_mul_of_nonneg_left hημ hη0
    linear_combination this
  have hLJGLm : LJ * G ≤ Lm := by
    rw [hLm]; have := mul_nonneg (mul_nonneg (sq_nonneg Γ) hLJ) hG; linarith
  have T1 : -η * (na ^ 2 - mJa) ≤ -η * na ^ 2 + η * na ^ 2 / 256 := by
    have a := mul_le_mul_of_nonneg_left hmJa hη0
    have b := mul_le_mul_of_nonneg_left hΓ2 (mul_nonneg hη0 (sq_nonneg na))
    linarith
  have T2 : lam * (Ysq - nw ^ 2) ≤ -(η * lam * μ * nw ^ 2) + η * na ^ 2 / 512 := by
    have a := mul_le_mul_of_nonneg_left hY hlam0
    have hk : lam * Γ ^ 2 ≤ μ / 2048 := by
      have := mul_le_mul hlamμ hΓ2 (sq_nonneg _) (by positivity); linarith
    have b : lam * (3 * η * Γ ^ 2 * na ^ 2 / μ) ≤ η * na ^ 2 / 512 := by
      have e : lam * (3 * η * Γ ^ 2 * na ^ 2 / μ) = 3 * η * na ^ 2 * (lam * Γ ^ 2) / μ := by ring
      rw [e, div_le_iff₀ hμ]
      have := mul_le_mul_of_nonneg_left hk (by positivity : (0:ℝ) ≤ 3 * η * na ^ 2)
      have : 0 ≤ η * na ^ 2 * μ := by positivity
      linarith
    have e2 : lam * ((1 - η * μ) * nw ^ 2) = lam * nw ^ 2 - η * lam * μ * nw ^ 2 := by ring
    linarith
  have T3 := t_r0m hη0 hΓ0 hΓ16 hLJ hLuv0 hna hnaG hnm' hnr0 hnr0a hnd0 hnd0' hη2μ hLJGμ
    hηLuv hLJGLm hlam0 hμ hlamLuv
  have T4 : nm * (LJ * η ^ 2 * σu ^ 2) ≤ η ^ 2 * (Γ * G * LJ * σu ^ 2) := by
    have a : nm ≤ Γ * G := hnm'.trans (mul_le_mul_of_nonneg_left hnaG hΓ0)
    have := mul_le_mul_of_nonneg_right a (by positivity : (0:ℝ) ≤ LJ * η ^ 2 * σu ^ 2)
    linarith
  have T5 := t_r0Y hη0 hΓ0 hΓ2 hLJ hLuv hμ hμLv hna hnaG hnw hlam0 hlamμ hnY' hnr0 hnr0b hη
    hLJGμ hηLuv
  have T6 := t_noiseY hη0 hΓ0 hLJ hμ hμLv hna hnaG hlam0 hnY' hη hc2 hσu hlamc
  have T7 := t_drift hη0 hΓ0 hΓ16 hna hnw hnY' hnd0 hnd0' hLm0
    (by linarith) hη2μ hηLuv hlamLm hlamLuv
  have hΓLh' : Γ * Lh ≤ Lm' := by rw [hLm']; linarith
  have T8 := t_Cd hΓ0 hΓ16 hμ hLuv hLh hLh16 hnd0 hnd0' hLm0 hLmLm' hLmμ hΓLh'
    hη2μ hlam0 hlamμ hlamΓ
  have T9 : η ^ 2 * (c2 * σu ^ 3 / μ + c2 * Γ * G * σu ^ 2 / (8 * Lv)) ≤
      η ^ 2 * (c' * σu ^ 3 / μ + c' * Γ * G * σu ^ 2 / (8 * Lv)) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg η)
    have a : c2 * σu ^ 3 / μ ≤ c' * σu ^ 3 / μ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc2c (by positivity)) hμ.le
    have b : c2 * Γ * G * σu ^ 2 / (8 * Lv) ≤ c' * Γ * G * σu ^ 2 / (8 * Lv) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have := mul_le_mul_of_nonneg_right hc2c (by positivity : (0:ℝ) ≤ Γ * G * σu ^ 2)
      linarith
    linarith
  have hlμ : 0 ≤ η * lam * μ * nw ^ 2 := by positivity
  have hna2 : 0 ≤ η * na ^ 2 := by positivity
  have e1 : (nm + 2 * lam * nY) * (nr0 + LJ * η ^ 2 * σu ^ 2) =
      nm * nr0 + nm * (LJ * η ^ 2 * σu ^ 2) + 2 * lam * nY * nr0 +
        2 * lam * nY * (LJ * η ^ 2 * σu ^ 2) := by ring
  have e2 : nY * (Lm * nd0 + c2 * η ^ 2 * σu ^ 2) = nY * (Lm * nd0) + nY * (c2 * η ^ 2 * σu ^ 2) :=
    by ring
  have e3 : (Lh / 2 + 2 * Γ * Lm + 8 * lam * Γ ^ 2) * (2 * nd0 ^ 2 + 2 * η ^ 2 * σu ^ 2) =
      (Lh / 2 + 2 * Γ * Lm + 8 * lam * Γ ^ 2) * (2 * nd0 ^ 2) +
        η ^ 2 * (2 * (Lh / 2 + 2 * Γ * Lm + 8 * lam * Γ ^ 2) * σu ^ 2) := by ring
  rw [e1, e2, e3]
  linarith


lemma Y_real {η μ Lv Γ Luv nw na D nz2 iwz Ysq : ℝ} (hμ : 0 < μ) (hμLv : μ ≤ Lv) (hη0 : 0 ≤ η)
    (hη : 8 * η * Lv ≤ 1) (hΓ0 : 0 ≤ Γ) (hΓ : 16 * Γ ≤ 1) (hLuv : Luv = Γ * μ)
    (hD : μ * nw ^ 2 ≤ D) (hY : Ysq = nw ^ 2 - 2 * η * iwz + η ^ 2 * nz2)
    (hiwz : D - Γ * Luv * nw ^ 2 - Γ * nw * na ≤ iwz)
    (hnz : nz2 ≤ 3 * (Lv * D + Γ ^ 2 * Luv ^ 2 * nw ^ 2 + Γ ^ 2 * na ^ 2)) :
    Ysq ≤ (1 - η * μ) * nw ^ 2 + 3 * η * Γ ^ 2 * na ^ 2 / μ := by
  have hLv : 0 < Lv := lt_of_lt_of_le hμ hμLv
  have hημ : η * μ ≤ 1 / 8 := by have := mul_le_mul_of_nonneg_left hμLv hη0; linarith
  have hΓ2 : Γ ^ 2 ≤ 1 / 256 := by nlinarith
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have h1 : Ysq ≤ nw ^ 2 - 2 * η * (D - Γ * Luv * nw ^ 2 - Γ * nw * na) +
      η ^ 2 * (3 * (Lv * D + Γ ^ 2 * Luv ^ 2 * nw ^ 2 + Γ ^ 2 * na ^ 2)) := by
    rw [hY]
    have a := mul_le_mul_of_nonneg_left hiwz (by positivity : (0:ℝ) ≤ 2 * η)
    have b := mul_le_mul_of_nonneg_left hnz (sq_nonneg η)
    linarith
  have a1 : 3 * η ^ 2 * Lv * D ≤ 3 / 8 * η * D := by
    have := mul_le_mul_of_nonneg_left hη (by positivity : (0:ℝ) ≤ 3 / 8 * η * D)
    linarith
  have a2 : 2 * η * Γ * Luv * nw ^ 2 ≤ η * μ * nw ^ 2 / 128 := by
    rw [hLuv]
    have := mul_le_mul_of_nonneg_left hΓ2 (by positivity : (0:ℝ) ≤ 2 * η * μ * nw ^ 2)
    linarith
  have a3 : 2 * η * Γ * nw * na ≤ η * μ * nw ^ 2 / 2 + 2 * η * Γ ^ 2 * na ^ 2 / μ := by
    have h0 : 0 ≤ η / (2 * μ) * (μ * nw - 2 * Γ * na) ^ 2 := by positivity
    have e : η / (2 * μ) * (μ * nw - 2 * Γ * na) ^ 2 =
        η * μ * nw ^ 2 / 2 + 2 * η * Γ ^ 2 * na ^ 2 / μ - 2 * η * Γ * nw * na := by
      field_simp; ring
    linarith
  have a4 : 3 * η ^ 2 * Γ ^ 2 * Luv ^ 2 * nw ^ 2 ≤ η * μ * nw ^ 2 / 128 := by
    rw [hLuv]
    have b1 : Γ ^ 4 ≤ 1 / 65536 := by
      have := pow_le_pow_left₀ (sq_nonneg Γ) hΓ2 2; linarith
    have b2 := mul_le_mul_of_nonneg_left hημ (by positivity : (0:ℝ) ≤ 3 * η * μ * Γ ^ 4 * nw ^ 2)
    have b3 := mul_le_mul_of_nonneg_left b1 (by positivity : (0:ℝ) ≤ 3 / 8 * η * μ * nw ^ 2)
    nlinarith
  have a5 : 3 * η ^ 2 * Γ ^ 2 * na ^ 2 ≤ 3 / 8 * η * Γ ^ 2 * na ^ 2 / μ := by
    rw [le_div_iff₀ hμ]
    have := mul_le_mul_of_nonneg_left hημ (by positivity : (0:ℝ) ≤ 3 * η * Γ ^ 2 * na ^ 2)
    linarith
  have a6 : 13 / 8 * η * μ * nw ^ 2 ≤ 13 / 8 * η * D :=
    by have := mul_le_mul_of_nonneg_left hD (by positivity : (0:ℝ) ≤ 13 / 8 * η); linarith
  have e : 3 / 8 * η * Γ ^ 2 * na ^ 2 / μ + 2 * η * Γ ^ 2 * na ^ 2 / μ ≤
      3 * η * Γ ^ 2 * na ^ 2 / μ := by
    have : 0 ≤ η * Γ ^ 2 * na ^ 2 / μ := by positivity
    have e1 : 3 / 8 * η * Γ ^ 2 * na ^ 2 / μ = 3 / 8 * (η * Γ ^ 2 * na ^ 2 / μ) := by ring
    have e2 : 2 * η * Γ ^ 2 * na ^ 2 / μ = 2 * (η * Γ ^ 2 * na ^ 2 / μ) := by ring
    have e3 : 3 * η * Γ ^ 2 * na ^ 2 / μ = 3 * (η * Γ ^ 2 * na ^ 2 / μ) := by ring
    linarith
  nlinarith

open MeasureTheory
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {K : Submodule ℝ E} [K.HasOrthogonalProjection]
variable {h : E → ℝ} {gh : E → E}
  {Hh : E → E →L[ℝ] E} {φ : E → E} {Jφ : E → E →L[ℝ] E} {DJ : E → E →L[ℝ] E →L[ℝ] E}
  {A : E →L[ℝ] E} {Lh ρh G Luv μ Lv LJ ρJ : ℝ}

namespace Model

variable (H : Model K h gh Hh φ Jφ DJ A Lh ρh G Luv μ Lv LJ ρJ)
include H

omit [MeasurableSpace E] [BorelSpace E] in
lemma hill_bounds (x : E) {η : ℝ} (hη0 : 0 ≤ η) (hη : 8 * η * Lv ≤ 1) (hΓ : 16 * Luv ≤ μ) :
    ‖Yv K gh φ Jφ A η x‖ ^ 2 ≤ (1 - η * μ) * ‖wv K φ x‖ ^ 2 +
        3 * η * (Luv / μ) ^ 2 * ‖ar K gh (Kᗮ.starProjection x)‖ ^ 2 / μ ∧
      ‖Yv K gh φ Jφ A η x‖ ≤ 2 * ‖wv K φ x‖ + η * (Luv / μ) * ‖ar K gh (Kᗮ.starProjection x)‖ ∧
      ‖d0v K gh φ Jφ A η x‖ ≤ η * (‖ar K gh (Kᗮ.starProjection x)‖ + Luv * ‖wv K φ x‖) := by
  set y := Kᗮ.starProjection x
  set w := wv K φ x
  set a := ar K gh y
  set J := Jr K Jφ y
  set v := ContinuousLinearMap.adjoint J (A w)
  set Γ := Luv / μ
  have hμ := H.μpos
  have hμLv := H.μ_le
  have hΓ0 : 0 ≤ Γ := div_nonneg H.Luv_nn hμ.le
  have hΓ16 : 16 * Γ ≤ 1 := by
    simp only [Γ]; rw [← mul_div_assoc, div_le_one hμ]; exact hΓ
  have hLuv : Luv = Γ * μ := by simp only [Γ]; field_simp
  have hwK : w ∈ K := wv_mem H x
  have hJ : ‖J‖ ≤ Γ := H.Jr_norm y
  have hv : ‖v‖ ≤ Luv * ‖w‖ := H.adjJA_norm x
  have hJv : ‖J v‖ ≤ Γ * Luv * ‖w‖ :=
    (J.le_opNorm _).trans (by
      have := mul_le_mul hJ hv (norm_nonneg _) hΓ0; linarith)
  have hJa : ‖J a‖ ≤ Γ * ‖a‖ := (J.le_opNorm _).trans (mul_le_mul_of_nonneg_right hJ (norm_nonneg _))
  have hAw2 : ‖A w‖ ^ 2 ≤ Lv * ⟪A w, w⟫ := H.A_cocoercive hwK
  have hAw : ‖A w‖ ≤ Lv * ‖w‖ := H.A_upper w hwK
  have hD : μ * ‖w‖ ^ 2 ≤ ⟪A w, w⟫ := H.A_lower w hwK
  set z := A w + J v - J a
  have hYz : Yv K gh φ Jφ A η x = w - η • z := by
    simp only [Yv, z, smul_sub, smul_add]; abel
  have hiwz : ⟪A w, w⟫ - Γ * Luv * ‖w‖ ^ 2 - Γ * ‖w‖ * ‖a‖ ≤ ⟪w, z⟫ := by
    simp only [z, inner_sub_right, inner_add_right]
    have e1 : ⟪w, A w⟫ = ⟪A w, w⟫ := real_inner_comm _ _
    have e2 : -⟪w, J v⟫ ≤ Γ * Luv * ‖w‖ ^ 2 := by
      have := abs_real_inner_le_norm w (J v)
      have h2 := mul_le_mul_of_nonneg_left hJv (norm_nonneg w)
      have := neg_abs_le ⟪w, J v⟫
      nlinarith
    have e3 : ⟪w, J a⟫ ≤ Γ * ‖w‖ * ‖a‖ := by
      have := real_inner_le_norm w (J a)
      have h2 := mul_le_mul_of_nonneg_left hJa (norm_nonneg w)
      nlinarith
    linarith
  have hnz : ‖z‖ ^ 2 ≤ 3 * (Lv * ⟪A w, w⟫ + Γ ^ 2 * Luv ^ 2 * ‖w‖ ^ 2 + Γ ^ 2 * ‖a‖ ^ 2) := by
    have h1 : ‖z‖ ≤ ‖A w‖ + ‖J v‖ + ‖J a‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have h2 : ‖z‖ ^ 2 ≤ 3 * (‖A w‖ ^ 2 + ‖J v‖ ^ 2 + ‖J a‖ ^ 2) := by
      have := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖A w‖ - ‖J v‖), sq_nonneg (‖A w‖ - ‖J a‖),
        sq_nonneg (‖J v‖ - ‖J a‖)]
    have h3 := pow_le_pow_left₀ (norm_nonneg _) hJv 2
    have h4 := pow_le_pow_left₀ (norm_nonneg _) hJa 2
    have e3 : (Γ * Luv * ‖w‖) ^ 2 = Γ ^ 2 * Luv ^ 2 * ‖w‖ ^ 2 := by ring
    have e4 : (Γ * ‖a‖) ^ 2 = Γ ^ 2 * ‖a‖ ^ 2 := by ring
    linarith
  have hYsq : ‖Yv K gh φ Jφ A η x‖ ^ 2 = ‖w‖ ^ 2 - 2 * η * ⟪w, z⟫ + η ^ 2 * ‖z‖ ^ 2 := by
    rw [hYz, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  refine ⟨Y_real hμ hμLv hη0 hη hΓ0 hΓ16 hLuv hD hYsq hiwz hnz, ?_, ?_⟩
  · rw [hYz]
    have hηLv : η * Lv ≤ 1 / 8 := by linarith
    have hΓLuv : Γ * Luv ≤ Lv := by
      rw [hLuv]; have : Γ ≤ 1 / 16 := by linarith
      nlinarith [mul_le_mul this hμLv hμ.le (by norm_num : (0:ℝ) ≤ 1 / 16)]
    have h1 : ‖z‖ ≤ (Lv + Γ * Luv) * ‖w‖ + Γ * ‖a‖ := by
      have : ‖z‖ ≤ ‖A w‖ + ‖J v‖ + ‖J a‖ :=
        (norm_sub_le (A w + J v) (J a)).trans (add_le_add (norm_add_le (A w) (J v)) le_rfl)
      calc ‖z‖ ≤ ‖A w‖ + ‖J v‖ + ‖J a‖ := this
        _ ≤ Lv * ‖w‖ + Γ * Luv * ‖w‖ + Γ * ‖a‖ := by gcongr
        _ = _ := by ring
    calc ‖w - η • z‖ ≤ ‖w‖ + η * ‖z‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη0]
      _ ≤ ‖w‖ + η * ((Lv + Γ * Luv) * ‖w‖ + Γ * ‖a‖) := by gcongr
      _ ≤ 2 * ‖w‖ + η * Γ * ‖a‖ := by
          have hh := mul_le_mul_of_nonneg_left hΓLuv hη0
          have := mul_le_mul_of_nonneg_left (by linarith : η * (Lv + Γ * Luv) ≤ 1)
            (norm_nonneg w)
          nlinarith
  · show ‖-(η • (a - v))‖ ≤ _
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη0]
    gcongr
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hv)

omit [MeasurableSpace E] [BorelSpace E] in
lemma r0_bounds (x : E) {η : ℝ} (hη0 : 0 ≤ η) :
    let y := Kᗮ.starProjection x
    let d0 := d0v K gh φ Jφ A η x
    ‖φ (y + d0) - φ y - Jφ y d0‖ ≤ LJ * ‖d0‖ ^ 2 ∧
      ‖φ (y + d0) - φ y - Jφ y d0‖ ≤ 4 * LJ * η ^ 2 * ‖ar K gh y‖ ^ 2 +
        4 * (Luv / μ) * η * Luv * ‖wv K φ x‖ := by
  intro y d0
  set a := ar K gh y
  set v := ContinuousLinearMap.adjoint (Jr K Jφ y) (A (wv K φ x))
  have hv : ‖v‖ ≤ Luv * ‖wv K φ x‖ := H.adjJA_norm x
  have hd0 : d0 = -(η • (a - v)) := rfl
  have hmem : d0 ∈ Kᗮ := by
    rw [hd0]; exact Kᗮ.neg_mem (Kᗮ.smul_mem _ (Kᗮ.sub_mem (Q_mem _) (adjJ_mem Jφ _ _)))
  have hnd : ‖d0‖ ≤ η * (‖a‖ + ‖v‖) := by
    rw [hd0, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη0]
    gcongr; exact norm_sub_le _ _
  have t1 := H.φ_taylor y d0
  have t2 := H.φ_river y d0 hmem
  refine ⟨t1, ?_⟩
  have hΓ0 : 0 ≤ Luv / μ := div_nonneg H.Luv_nn H.μpos.le
  rcases le_total ‖v‖ ‖a‖ with hva | hav
  · have h1 : ‖d0‖ ≤ 2 * η * ‖a‖ := by nlinarith
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := mul_le_mul_of_nonneg_left h2 H.LJ_nn
    have : 0 ≤ 4 * (Luv / μ) * η * Luv * ‖wv K φ x‖ := by
      have := H.Luv_nn; positivity
    nlinarith
  · have h1 : ‖d0‖ ≤ 2 * η * (Luv * ‖wv K φ x‖) := by nlinarith
    have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ 2 * (Luv / μ))
    have : 0 ≤ 4 * LJ * η ^ 2 * ‖a‖ ^ 2 := by have := H.LJ_nn; positivity
    nlinarith


omit [MeasurableSpace E] [BorelSpace E] in
lemma c2_le (hΓ : 16 * Luv ≤ μ) :
    G * ρJ + LJ * Lh + Luv / μ * ρh + Luv / μ * G * (2 * (Luv / μ) * ρJ + LJ ^ 2) +
        2 * (Luv / μ) * LJ * (Luv / μ * Lh + LJ * G + 2 * (Luv / μ) ^ 2 * LJ * G) ≤
      2 * G * ρJ + 2 * LJ * Lh + Luv / μ * ρh + G * LJ ^ 2 := by
  set Γ := Luv / μ
  have hΓ0 : 0 ≤ Γ := div_nonneg H.Luv_nn H.μpos.le
  have hΓ16 : Γ ≤ 1 / 16 := by
    simp only [Γ]; rw [div_le_iff₀ H.μpos]; linarith
  have hG := H.G_nn; have hLJ := H.LJ_nn; have hLh := H.Lh_nn; have hρJ := H.ρJ_nn
  have hΓ2 : Γ ^ 2 ≤ 1 / 256 := by nlinarith
  have hΓ3 : Γ ^ 3 ≤ 1 / 4096 := by nlinarith
  have a1 : 2 * Γ ^ 2 * G * ρJ ≤ G * ρJ := by
    have := mul_le_mul_of_nonneg_left hΓ2 (by positivity : (0:ℝ) ≤ 2 * G * ρJ); nlinarith
  have a2 : 2 * Γ ^ 2 * LJ * Lh ≤ LJ * Lh := by
    have := mul_le_mul_of_nonneg_left hΓ2 (by positivity : (0:ℝ) ≤ 2 * LJ * Lh); nlinarith
  have a3 : (3 * Γ + 4 * Γ ^ 3) * (G * LJ ^ 2) ≤ G * LJ ^ 2 := by
    have : 3 * Γ + 4 * Γ ^ 3 ≤ 1 := by nlinarith
    have := mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ G * LJ ^ 2); linarith
  nlinarith

lemma descent {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
    {ζ : Ω → E} {σu σv : ℝ} (N : NoiseAt K p ζ σu σv) (hσu : 0 ≤ σu) (hσv : 0 ≤ σv) (x : E)
    {η : ℝ} (hη0 : 0 ≤ η) (hη : 8 * η * Lv ≤ 1) (hΓ : 16 * Luv ≤ μ) (hLh16 : 16 * Lh ≤ μ)
    (hLm : 64 * (Luv / μ * Lh + 2 * LJ * G) ≤ μ)
    (hc : 64 * (2 * G * ρJ + 2 * LJ * Lh + Luv / μ * ρh + G * LJ ^ 2) * σu ≤ μ * Lv) :
    let Γ := Luv / μ
    let Lm := Γ * Lh + LJ * G + 2 * Γ ^ 2 * LJ * G
    let Lm' := Γ * Lh + 2 * LJ * G
    let c' := 2 * G * ρJ + 2 * LJ * Lh + Γ * ρh + G * LJ ^ 2
    let lam := (256 * Lm' ^ 2 + 32 * Lm' * Luv) / μ + 2 * c' * σu / Lv
    Integrable (fun ω => Vfun K h gh φ Jφ lam (x - η • (gradF K gh φ Jφ A x + ζ ω))) p ∧
    ∫ ω, Vfun K h gh φ Jφ lam (x - η • (gradF K gh φ Jφ A x + ζ ω)) ∂p ≤
      Vfun K h gh φ Jφ lam x - (η / 2) * ‖ar K gh (Kᗮ.starProjection x)‖ ^ 2 -
        η * lam * μ / 2 * ‖wv K φ x‖ ^ 2 +
        η ^ 2 * (2 * (Lh / 2 + 2 * Γ * Lm + 8 * lam * Γ ^ 2) * σu ^ 2 +
          4 * lam * (σv ^ 2 + Γ ^ 2 * σu ^ 2) + Lm * (σu * σv + Γ * σu ^ 2) +
          Γ * G * LJ * σu ^ 2 + c' * σu ^ 3 / μ + c' * Γ * G * σu ^ 2 / (8 * Lv) +
          8 * lam * LJ ^ 2 * σu ^ 4 / (μ * Lv) + lam * LJ * Γ * G * σu ^ 2 / (4 * Lv)) := by
  intro Γ Lm Lm' c' lam
  have hμ := H.μpos
  have hLv : 0 < Lv := lt_of_lt_of_le hμ H.μ_le
  have hΓ0 : 0 ≤ Γ := div_nonneg H.Luv_nn hμ.le
  have hΓ16 : 16 * Γ ≤ 1 := by
    simp only [Γ]; rw [← mul_div_assoc, div_le_one hμ]; exact hΓ
  have hLuv : Luv = Γ * μ := by simp only [Γ]; field_simp
  have hlam0 : 0 ≤ lam := by
    have := H.Lh_nn; have := H.LJ_nn; have := H.G_nn; have := H.ρJ_nn; have := H.ρh_nn
    have := H.Luv_nn
    simp only [lam, Lm', c']; positivity
  obtain ⟨hint, hstep⟩ := H.step_bound N hσu hσv x η lam hlam0
  refine ⟨hint, ?_⟩
  obtain ⟨hY2, hY1, hd0⟩ := H.hill_bounds x hη0 hη hΓ
  obtain ⟨hr1, hr2⟩ := H.r0_bounds x hη0
  obtain ⟨hm1, hm2⟩ := H.mr_bounds (Kᗮ.starProjection x)
  have haG := H.ar_norm (Kᗮ.starProjection x)
  have hmJa : ⟪mr K gh Jφ (Kᗮ.starProjection x), Jr K Jφ (Kᗮ.starProjection x)
      (ar K gh (Kᗮ.starProjection x))⟫ ≤ Γ ^ 2 * ‖ar K gh (Kᗮ.starProjection x)‖ ^ 2 := by
    rcases le_total 0 ⟪mr K gh Jφ (Kᗮ.starProjection x), Jr K Jφ (Kᗮ.starProjection x)
      (ar K gh (Kᗮ.starProjection x))⟫ with h0 | h0
    · have : 0 ≤ Γ ^ 2 * ⟪mr K gh Jφ (Kᗮ.starProjection x), Jr K Jφ (Kᗮ.starProjection x)
          (ar K gh (Kᗮ.starProjection x))⟫ := by positivity
      linarith
    · have : 0 ≤ Γ ^ 2 * ‖ar K gh (Kᗮ.starProjection x)‖ ^ 2 := by positivity
      linarith
  have hc2 := H.c2_le hΓ
  have hc20 : 0 ≤ G * ρJ + LJ * Lh + Luv / μ * ρh + Luv / μ * G * (2 * (Luv / μ) * ρJ + LJ ^ 2) +
      2 * (Luv / μ) * LJ * (Luv / μ * Lh + LJ * G + 2 * (Luv / μ) ^ 2 * LJ * G) := by
    have := H.Lh_nn; have := H.LJ_nn; have := H.G_nn; have := H.ρJ_nn; have := H.ρh_nn
    positivity
  have key := descent_real (η := η) (μ := μ) (Lv := Lv) (Lh := Lh) (LJ := LJ) (G := G) (Γ := Γ)
    (Luv := Luv) (lam := lam) (σu := σu) (σv := σv) (Lm := Lm) (Lm' := Lm') (c' := c')
    hμ H.μ_le hη0 hη hΓ0 hΓ16 hLuv H.Lh_nn hLh16 H.LJ_nn H.G_nn hσu rfl rfl hLm hc20 hc2 hc rfl
    (norm_nonneg _) haG (norm_nonneg _) hm1 hmJa hY2 hY1 (norm_nonneg _) hd0 (norm_nonneg _) hr1 hr2
  linarith

end Model

end OracleTemplate.RiverValley
