import Mathlib

namespace OracleTemplate.MinimaxLmo

lemma tune_x {ℓ ω y x : ℝ} (hℓ : 0 ≤ ℓ) (hω : 0 ≤ ω) (hℓω : 32 * ℓ * ω ≤ 1) (hy : 1 ≤ y)
    (hx : x = 4 * ω / 3 + y / (48 * (1 + ℓ * y))) :
    0 < x ∧ 16 * ℓ * x ≤ 1 ∧ ω ≤ 3 * x / 4 ∧ y ≤ 48 * (1 + ℓ * y) * x := by
  have hA : 0 < 1 + ℓ * y := by positivity
  set x₀ := y / (48 * (1 + ℓ * y)) with hx₀
  have hx₀0 : 0 < x₀ := by positivity
  have e1 : 48 * (1 + ℓ * y) * x₀ = y := by rw [hx₀]; field_simp
  have h1 : 48 * (16 * ℓ * x₀) ≤ 16 := by
    have e2 : 48 * (16 * ℓ * x₀) = 16 * (ℓ * (48 * (1 + ℓ * y) * x₀)) / (1 + ℓ * y) := by
      field_simp
    rw [e2, e1, div_le_iff₀ hA]
    nlinarith
  subst hx
  refine ⟨by positivity, by nlinarith, by linarith, ?_⟩
  have : 0 ≤ 48 * (1 + ℓ * y) * (4 * ω / 3) := by positivity
  nlinarith

lemma tune_lambda {κ ℓ q d Lx y ϑy θi ib x cc n : ℝ} (hκ : 1 ≤ κ) (hℓ : 0 ≤ ℓ) (hq : 1 ≤ q) (hLx : 0 ≤ Lx)
    (hdq : d ≤ q ^ 2) (hy : y = q + Lx) (hθ : θi = 1024 * (1 + ℓ) * (1 + ℓ * y) ^ 2)
    (hib : ib = κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) * θi) (hx0 : 0 < x) (hxy : y ≤ 48 * (1 + ℓ * y) * x)
    (hc : cc = κ * (192 * x + 192 * ϑy ^ 2 / x + 512 * ϑy ^ 2)) (hn0 : 0 < n)
    (hn : 768 * κ * (1 + ℓ * y) * q * (ℓ * q ^ 2 + Lx) ≤ n) :
    4 * κ * (ℓ * q ^ 2 + Lx) * (cc / ib + d / n) ≤ x := by
  obtain ⟨Q, hQ⟩ : ∃ Q, ℓ * q ^ 2 + Lx = Q := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, 1 + ℓ * y = A := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, 2 ^ 16 * ϑy ^ 2 + 3 * y + 1 = Y := ⟨_, rfl⟩
  rw [hQ] at hn ⊢
  rw [hA] at hθ hxy hn
  rw [hY] at hib
  have hy1 : 1 ≤ y := by rw [hy]; linarith
  have hqy : q ≤ y := by rw [hy]; linarith
  have hℓy : 0 ≤ ℓ * y := by positivity
  have hA1 : 1 ≤ A := by rw [← hA]; linarith
  have hQ0 : 0 ≤ Q := by rw [← hQ]; positivity
  have hq2y : ℓ * q ^ 2 ≤ ℓ * y ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hqy 2) hℓ
  have hLxy : Lx ≤ y := by rw [hy]; linarith
  have hyA : y * A = y + ℓ * y ^ 2 := by rw [← hA]; ring
  have hQA : Q ≤ y * A := by rw [hyA, ← hQ]; linarith
  have hyy : y ≤ y ^ 2 := by
    have := mul_le_mul_of_nonneg_left hy1 (by linarith : (0 : ℝ) ≤ y)
    rw [sq]; linarith
  have hQ2 : Q ≤ (1 + ℓ) * y ^ 2 := by
    have e : (1 + ℓ) * y ^ 2 = y ^ 2 + ℓ * y ^ 2 := by ring
    rw [e, ← hQ]; linarith
  have hθ0 : 0 < θi := by rw [hθ]; positivity
  have hY3 : 3 * y ≤ Y := by
    have : 0 ≤ 2 ^ 16 * ϑy ^ 2 := by positivity
    rw [← hY]; linarith
  have hY0 : 0 < Y := by linarith
  have hYϑ : 2 ^ 16 * ϑy ^ 2 ≤ Y := by rw [← hY]; linarith
  have hκ0 : 0 < κ := by linarith
  have hAx : y ≤ 48 * (A * x) := by rw [← mul_assoc]; exact hxy
  have hA0 : 0 ≤ A := by linarith
  have hAA : A ≤ A ^ 2 := by
    have := mul_le_mul_of_nonneg_left hA1 hA0
    rw [sq]; linarith
  have hi : 3072 * Q ≤ Y * θi := by
    have h1 : y * A ≤ y * A ^ 2 := mul_le_mul_of_nonneg_left hAA (by linarith)
    have h4 : 1024 * A ^ 2 ≤ 1024 * (1 + ℓ) * A ^ 2 := by
      have : 0 ≤ ℓ * A ^ 2 := by positivity
      have e : 1024 * (1 + ℓ) * A ^ 2 = 1024 * A ^ 2 + 1024 * (ℓ * A ^ 2) := by ring
      rw [e]; linarith
    have h2 : (3 * y) * (1024 * A ^ 2) ≤ Y * (1024 * (1 + ℓ) * A ^ 2) :=
      mul_le_mul hY3 h4 (by positivity) hY0.le
    have e : (3 * y) * (1024 * A ^ 2) = 3072 * (y * A ^ 2) := by ring
    rw [hθ]; linarith
  have hAx2 : y ^ 2 ≤ 2304 * (A * x) ^ 2 := by
    have := pow_le_pow_left₀ (by linarith) hAx 2
    have e : (48 * (A * x)) ^ 2 = 2304 * (A * x) ^ 2 := by ring
    linarith
  have hii : 3 * Q ≤ 64 * x ^ 2 * θi := by
    have h2 : 64 * x ^ 2 * θi = 65536 * ((1 + ℓ) * (A * x) ^ 2) := by rw [hθ]; ring
    have h4 : (1 + ℓ) * y ^ 2 ≤ (1 + ℓ) * (2304 * (A * x) ^ 2) :=
      mul_le_mul_of_nonneg_left hAx2 (by linarith)
    have h3 : 0 ≤ (1 + ℓ) * (A * x) ^ 2 := by positivity
    have e : (1 + ℓ) * (2304 * (A * x) ^ 2) = 2304 * ((1 + ℓ) * (A * x) ^ 2) := by ring
    rw [h2]; linarith
  have hiii : Q ≤ 8 * x * θi := by
    have h1 : 8 * x * θi = 8192 * (1 + ℓ) * A * (A * x) := by rw [hθ]; ring
    have h2 : y * A ≤ 48 * (A * x) * A := mul_le_mul_of_nonneg_right hAx hA0
    have h3 : 8192 * A * (A * x) ≤ 8192 * (1 + ℓ) * A * (A * x) := by
      have : 0 ≤ ℓ * A * (A * x) := by positivity
      have e : 8192 * (1 + ℓ) * A * (A * x) = 8192 * A * (A * x) + 8192 * (ℓ * A * (A * x)) := by ring
      rw [e]; linarith
    have e : 48 * (A * x) * A = 48 * (A * (A * x)) := by ring
    have e2 : 8192 * A * (A * x) = 8192 * (A * (A * x)) := by ring
    rw [h1]; linarith
  have hiv : 16 * κ * Q * d ≤ n * x := by
    have h1 : 768 * κ * A * q * Q * x ≤ n * x := mul_le_mul_of_nonneg_right hn hx0.le
    have h2 : 16 * κ * q * Q * y ≤ 16 * κ * q * Q * (48 * (A * x)) :=
      mul_le_mul_of_nonneg_left hAx (by positivity)
    have h3 : d ≤ q * y := by
      have := mul_le_mul_of_nonneg_left hqy (by linarith : (0 : ℝ) ≤ q)
      rw [sq] at hdq; linarith
    have h4 : 16 * κ * Q * d ≤ 16 * κ * Q * (q * y) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have e1 : 16 * κ * q * Q * (48 * (A * x)) = 768 * κ * A * q * Q * x := by ring
    have e2 : 16 * κ * Q * (q * y) = 16 * κ * q * Q * y := by ring
    linarith
  have hcib : cc / ib = (192 * x + 192 * ϑy ^ 2 / x + 512 * ϑy ^ 2) / (κ * (Y * θi)) := by
    rw [hc, hib]; field_simp
  have hYθ : 0 < Y * θi := by positivity
  have t1 : 4 * Q * (192 * x) ≤ x / 4 * (Y * θi) := by
    have := mul_le_mul_of_nonneg_left hi (by positivity : (0 : ℝ) ≤ x / 4)
    have e : 4 * Q * (192 * x) = x / 4 * (3072 * Q) := by ring
    linarith
  have t2 : 4 * Q * (192 * ϑy ^ 2 / x) ≤ x / 4 * (Y * θi) := by
    have a1 : 1024 * ϑy ^ 2 * (3 * Q) ≤ 1024 * ϑy ^ 2 * (64 * x ^ 2 * θi) :=
      mul_le_mul_of_nonneg_left hii (by positivity)
    have a2 : 2 ^ 16 * ϑy ^ 2 * (x ^ 2 * θi) ≤ Y * (x ^ 2 * θi) :=
      mul_le_mul_of_nonneg_right hYϑ (by positivity)
    have e2 : 4 * Q * (192 * ϑy ^ 2 / x) = 3072 * Q * ϑy ^ 2 / (4 * x) := by field_simp; ring
    rw [e2, div_le_iff₀ (by positivity)]
    have e3 : x / 4 * (Y * θi) * (4 * x) = Y * (x ^ 2 * θi) := by ring
    have e4 : 1024 * ϑy ^ 2 * (64 * x ^ 2 * θi) = 2 ^ 16 * ϑy ^ 2 * (x ^ 2 * θi) := by ring
    have e5 : 1024 * ϑy ^ 2 * (3 * Q) = 3072 * Q * ϑy ^ 2 := by ring
    rw [e3]; linarith
  have t3 : 4 * Q * (512 * ϑy ^ 2) ≤ x / 4 * (Y * θi) := by
    have a1 : 8192 * ϑy ^ 2 * Q ≤ 8192 * ϑy ^ 2 * (8 * x * θi) :=
      mul_le_mul_of_nonneg_left hiii (by positivity)
    have a2 : 2 ^ 16 * ϑy ^ 2 * (x * θi) ≤ Y * (x * θi) :=
      mul_le_mul_of_nonneg_right hYϑ (by positivity)
    have e1 : 8192 * ϑy ^ 2 * (8 * x * θi) = 2 ^ 16 * ϑy ^ 2 * (x * θi) := by ring
    have e2 : x / 4 * (Y * θi) = Y * (x * θi) / 4 := by ring
    have e3 : 4 * Q * (512 * ϑy ^ 2) = 8192 * ϑy ^ 2 * Q / 4 := by ring
    rw [e2, e3]; linarith
  have hP : 4 * κ * Q * (cc / ib) ≤ 3 * x / 4 := by
    rw [hcib]
    have e1 : 4 * κ * Q * ((192 * x + 192 * ϑy ^ 2 / x + 512 * ϑy ^ 2) / (κ * (Y * θi))) =
        (4 * Q * (192 * x) + 4 * Q * (192 * ϑy ^ 2 / x) + 4 * Q * (512 * ϑy ^ 2)) / (Y * θi) := by
      field_simp
    rw [e1, div_le_iff₀ hYθ]
    linarith
  have hD : 4 * κ * Q * (d / n) ≤ x / 4 := by
    rw [mul_div_assoc', div_le_iff₀ hn0]
    linarith
  calc 4 * κ * Q * (cc / ib + d / n) = 4 * κ * Q * (cc / ib) + 4 * κ * Q * (d / n) := by ring
    _ ≤ 3 * x / 4 + x / 4 := add_le_add hP hD
    _ = x := by ring

lemma div_add_div_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hd : 0 < d) :
    (a + b) / (c + d) ≤ a / c + b / d := by
  rw [add_div]
  exact add_le_add (div_le_div_of_nonneg_left ha hc (by linarith))
    (div_le_div_of_nonneg_left hb hd (by linarith))

lemma tune_cond {κ ℓ q d Lx y ϑy θi ib x cc n : ℝ} (hκ : 1 ≤ κ) (hℓ : 0 ≤ ℓ) (hq : 1 ≤ q) (hLx : 0 ≤ Lx)
    (hd0 : 0 < d) (hdq : d ≤ q ^ 2) (hy : y = q + Lx) (hθ : θi = 1024 * (1 + ℓ) * (1 + ℓ * y) ^ 2)
    (hib : ib = κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) * θi) (hx0 : 0 < x) (hxy : y ≤ 48 * (1 + ℓ * y) * x)
    (hc : cc = κ * (192 * x + 192 * ϑy ^ 2 / x + 512 * ϑy ^ 2)) (hn0 : 0 < n)
    (hn : 4608 * κ * (1 + ℓ * y) * q * ib ≤ n) :
    8 * κ ^ 2 * ϑy ^ 4 / (ib * cc ^ 2 * x) + 2 * κ ^ 2 * ϑy ^ 2 / (ib ^ 2 * x) + κ * d / n +
      κ * (4 * (x ^ 2 + ϑy ^ 2) / ib ^ 2 + 2 * d ^ 2 / n ^ 2) / (cc / ib + d / n) ≤ x / (8 * ib) := by
  obtain ⟨A, hA⟩ : ∃ A, 1 + ℓ * y = A := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, 2 ^ 16 * ϑy ^ 2 + 3 * y + 1 = Y := ⟨_, rfl⟩
  rw [hA] at hθ hxy hn
  rw [hY] at hib
  have hy1 : 1 ≤ y := by rw [hy]; linarith
  have hqy : q ≤ y := by rw [hy]; linarith
  have hℓy : 0 ≤ ℓ * y := by positivity
  have hA1 : 1 ≤ A := by rw [← hA]; linarith
  have hκ0 : 0 < κ := by linarith
  have hθ1 : 1 ≤ θi := by
    have h1 : 1 ≤ A ^ 2 := one_le_pow₀ hA1
    have h2 : 1 ≤ (1 + ℓ) * A ^ 2 := one_le_mul_of_one_le_of_one_le (by linarith) h1
    rw [hθ]; linarith
  have hθ0 : 0 < θi := by linarith
  have hYϑ : 2 ^ 16 * ϑy ^ 2 ≤ Y := by rw [← hY]; linarith
  have hY0 : 0 < Y := by rw [← hY]; positivity
  have hib0 : 0 < ib := by rw [hib]; positivity
  have hccx : 192 * κ * x ^ 2 + 192 * κ * ϑy ^ 2 ≤ cc * x := by
    have e : cc * x = 192 * κ * x ^ 2 + 192 * κ * ϑy ^ 2 + κ * (512 * ϑy ^ 2 * x) := by
      rw [hc]; field_simp
    have : 0 ≤ κ * (512 * ϑy ^ 2 * x) := by positivity
    rw [e]; linarith
  have hcc0 : 0 < cc := by rw [hc]; positivity
  have hAx : y ≤ 48 * (A * x) := by rw [← mul_assoc]; exact hxy
  have hθx : 1 / 4 ≤ θi * x ^ 2 := by
    have h1 : y ^ 2 ≤ 2304 * (A * x) ^ 2 := by
      have := pow_le_pow_left₀ (by linarith) hAx 2
      have e : (48 * (A * x)) ^ 2 = 2304 * (A * x) ^ 2 := by ring
      linarith
    have h2 : θi * x ^ 2 = 1024 * (A * x) ^ 2 + 1024 * (ℓ * (A * x) ^ 2) := by rw [hθ]; ring
    have h3 : 0 ≤ ℓ * (A * x) ^ 2 := by positivity
    have h4 : 1 ≤ y ^ 2 := one_le_pow₀ hy1
    rw [h2]; linarith
  have hD : 48 * κ * d * ib ≤ n * x := by
    have h1 : 4608 * κ * A * q * ib * x ≤ n * x := mul_le_mul_of_nonneg_right hn hx0.le
    have h2 : 96 * κ * q * ib * y ≤ 96 * κ * q * ib * (48 * (A * x)) :=
      mul_le_mul_of_nonneg_left hAx (by positivity)
    have h3 : d ≤ q * y := by
      have := mul_le_mul_of_nonneg_left hqy (by linarith : (0 : ℝ) ≤ q)
      rw [sq] at hdq; linarith
    have h4 : 48 * κ * ib * d ≤ 48 * κ * ib * (q * y) := mul_le_mul_of_nonneg_left h3 (by positivity)
    have h5 : 0 ≤ 48 * κ * ib * (q * y) := by positivity
    have e1 : 96 * κ * q * ib * (48 * (A * x)) = 4608 * κ * A * q * ib * x := by ring
    have e2 : 48 * κ * ib * (q * y) = 48 * κ * q * ib * y := by ring
    have e3 : 48 * κ * d * ib = 48 * κ * ib * d := by ring
    linarith
  have p1 : 8 * κ ^ 2 * ϑy ^ 4 / (ib * cc ^ 2 * x) ≤ x / (48 * ib) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 192 * κ * ϑy ^ 2 ≤ cc * x := by
      have : 0 ≤ 192 * κ * x ^ 2 := by positivity
      linarith
    have h2 : (192 * κ * ϑy ^ 2) ^ 2 ≤ (cc * x) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
    have h3 : 384 * (κ ^ 2 * ϑy ^ 4) ≤ (cc * x) ^ 2 := by
      have e : (192 * κ * ϑy ^ 2) ^ 2 = 36864 * (κ ^ 2 * ϑy ^ 4) := by ring
      have : 0 ≤ κ ^ 2 * ϑy ^ 4 := by positivity
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ ib)
    have e1 : 8 * κ ^ 2 * ϑy ^ 4 * (48 * ib) = ib * (384 * (κ ^ 2 * ϑy ^ 4)) := by ring
    have e2 : x * (ib * cc ^ 2 * x) = ib * (cc * x) ^ 2 := by ring
    rw [e1, e2]; exact h4
  have p2 : 2 * κ ^ 2 * ϑy ^ 2 / (ib ^ 2 * x) ≤ x / (48 * ib) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 96 * κ ^ 2 * ϑy ^ 2 ≤ ib * x ^ 2 := by
      have e : ib * x ^ 2 = κ ^ 2 * (Y * (θi * x ^ 2)) := by rw [hib]; ring
      have a2 : 2 ^ 16 * ϑy ^ 2 * (1 / 4) ≤ Y * (θi * x ^ 2) :=
        mul_le_mul hYϑ hθx (by norm_num) hY0.le
      have a3 := mul_le_mul_of_nonneg_left a2 (by positivity : (0 : ℝ) ≤ κ ^ 2)
      have a4 : 0 ≤ κ ^ 2 * ϑy ^ 2 := by positivity
      have e2 : κ ^ 2 * (2 ^ 16 * ϑy ^ 2 * (1 / 4)) = 16384 * (κ ^ 2 * ϑy ^ 2) := by ring
      rw [e]; linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * ib)
    have e1 : 2 * κ ^ 2 * ϑy ^ 2 * (48 * ib) = 2 * ib * (48 * κ ^ 2 * ϑy ^ 2) := by ring
    have e2 : x * (ib ^ 2 * x) = ib * (ib * x ^ 2) := by ring
    have h3 : 0 ≤ 2 * ib * (48 * κ ^ 2 * ϑy ^ 2) := by positivity
    rw [e1, e2]
    have e3 : 2 * ib * (96 * κ ^ 2 * ϑy ^ 2) = 2 * (2 * ib * (48 * κ ^ 2 * ϑy ^ 2)) := by ring
    have e4 : 2 * ib * (ib * x ^ 2) = 2 * (ib * (ib * x ^ 2)) := by ring
    linarith
  have p3 : κ * d / n ≤ x / (48 * ib) := by
    rw [div_le_div_iff₀ hn0 (by positivity)]
    have e : κ * d * (48 * ib) = 48 * κ * d * ib := by ring
    rw [e]; linarith
  have p4 : κ * (4 * (x ^ 2 + ϑy ^ 2) / ib ^ 2) / (cc / ib) ≤ x / (48 * ib) := by
    have e : κ * (4 * (x ^ 2 + ϑy ^ 2) / ib ^ 2) / (cc / ib) = 4 * κ * (x ^ 2 + ϑy ^ 2) / (ib * cc) := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have h := mul_le_mul_of_nonneg_left hccx (by positivity : (0 : ℝ) ≤ ib)
    have e1 : 4 * κ * (x ^ 2 + ϑy ^ 2) * (48 * ib) = ib * (192 * κ * x ^ 2 + 192 * κ * ϑy ^ 2) := by ring
    have e2 : x * (ib * cc) = ib * (cc * x) := by ring
    rw [e1, e2]; exact h
  have p5 : κ * (2 * d ^ 2 / n ^ 2) / (d / n) = 2 * (κ * d / n) := by field_simp
  have p45 : κ * (4 * (x ^ 2 + ϑy ^ 2) / ib ^ 2 + 2 * d ^ 2 / n ^ 2) / (cc / ib + d / n) ≤
      x / (48 * ib) + 2 * (x / (48 * ib)) := by
    have h1 := div_add_div_le (a := κ * (4 * (x ^ 2 + ϑy ^ 2) / ib ^ 2)) (b := κ * (2 * d ^ 2 / n ^ 2))
      (c := cc / ib) (d := d / n) (by positivity) (by positivity) (by positivity) (by positivity)
    rw [← mul_add, p5] at h1
    linarith
  have e8 : x / (8 * ib) = 6 * (x / (48 * ib)) := by field_simp; ring
  rw [e8]
  linarith

lemma tune_phys {ε u κ ℓ d q ϑy ω Lx y θi ib ia x cc n L₀ μ L₁ σy W s r c β lam a : ℝ}
    (hε : 0 < ε) (hu : 0 < u) (hκ : 1 ≤ κ) (hℓ : 0 ≤ ℓ) (hd : 1 ≤ d) (hq0 : 0 ≤ q)
    (hq2 : q ^ 2 = (1 + κ) * d) (hω : 0 ≤ ω) (hℓω : 32 * ℓ * ω ≤ 1) (hLx : 0 ≤ Lx)
    (hy : y = q + Lx) (hθ : θi = 1024 * (1 + ℓ) * (1 + ℓ * y) ^ 2)
    (hib : ib = κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) * θi) (hia : 1 ≤ ia)
    (hx : x = 4 * ω / 3 + y / (48 * (1 + ℓ * y)))
    (hcc : cc = κ * (192 * x + 192 * ϑy ^ 2 / x + 512 * ϑy ^ 2)) (hn0 : 0 < n)
    (hn6 : 16 * (1 + κ) * ℓ * d * ia ≤ n) (hn7 : 4608 * κ * (1 + ℓ * y) * q * ib ≤ n)
    (hn8 : 768 * κ * (1 + ℓ * y) * q * (ℓ * q ^ 2 + Lx) ≤ n)
    (hL₀ : L₀ = ε / u) (hμ : μ = ε / (κ * u)) (hL₁ : L₁ = ℓ / u) (hσy : σy = ϑy * ε) (hW : W = ω * u)
    (hs : s = d * u / n) (hr : r = x * u) (hc : c = cc * ε) (hβ : β = 1 / (ib * μ))
    (hlam : lam = 1 / (β * c + L₀ / μ * s)) (ha : a = 1 / ia) :
    0 < s ∧ 0 < a ∧ a ≤ 1 ∧ 16 * (1 + L₀ / μ) * L₁ * s ≤ a ∧ 16 * L₁ * r ≤ 1 ∧ 0 < β ∧
      2 * β * L₀ ^ 2 ≤ μ ∧ β * μ ≤ 1 ∧ 0 < c ∧ L₀ * r ≤ c / 2 ∧ 0 < r ∧ W ≤ 3 * r / 4 ∧ 0 < lam ∧
      lam * (β * c + L₀ / μ * s) = 1 ∧
      (8 * β * σy ^ 4 / (μ * c ^ 2) + 2 * β ^ 2 * σy ^ 2) / (2 * (r / 2)) + L₀ / μ * s +
        lam * (4 * β ^ 2 * (L₀ ^ 2 * r ^ 2 + σy ^ 2) + 2 * (L₀ / μ * s) ^ 2) ≤ β * μ * (r / 2) / 4 ∧
      ℓ * q ^ 2 + Lx ≤ lam * r / 4 := by
  have hκ0 : 0 < κ := by linarith
  have hKd : d ≤ (1 + κ) * d := by
    have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ 1 + κ) (by linarith : (0 : ℝ) ≤ d)
    linarith
  have hdq : d ≤ q ^ 2 := by rw [hq2]; exact hKd
  have hq1 : 1 ≤ q := by
    have h1 : 1 ≤ q ^ 2 := by linarith
    by_contra h
    push Not at h
    have : q ^ 2 < 1 := by
      have := mul_lt_mul'' h h hq0 hq0
      rw [sq]; linarith
    linarith
  have hy1 : 1 ≤ y := by rw [hy]; linarith
  obtain ⟨hx0, hx16, hωx, hxy⟩ := tune_x hℓ hω hℓω hy1 hx
  have hθ1 : 1024 ≤ θi := by
    have hA : 1 ≤ 1 + ℓ * y := by have : 0 ≤ ℓ * y := by positivity
                                  linarith
    have h2 : 1 ≤ (1 + ℓ) * (1 + ℓ * y) ^ 2 := one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hA)
    rw [hθ]; linarith
  have hY1 : 1 ≤ 2 ^ 16 * ϑy ^ 2 + 3 * y + 1 := by
    have : 0 ≤ 2 ^ 16 * ϑy ^ 2 := by positivity
    linarith
  have hib1 : 1024 * κ ^ 2 ≤ ib := by
    have h1 : 1024 ≤ (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) * θi := by
      have := mul_le_mul hY1 hθ1 (by norm_num) (by linarith)
      linarith
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ κ ^ 2)
    rw [hib]; linarith
  have hκ2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  have hib0 : 0 < ib := by linarith
  have hccx : 192 * κ * x ≤ cc := by
    have : 0 ≤ κ * (192 * ϑy ^ 2 / x + 512 * ϑy ^ 2) := by positivity
    have e : cc = 192 * κ * x + κ * (192 * ϑy ^ 2 / x + 512 * ϑy ^ 2) := by rw [hcc]; ring
    linarith
  have hcc0 : 0 < cc := by
    have : 0 < 192 * κ * x := by positivity
    linarith
  have hκ' : ε / u / (ε / (κ * u)) = κ := by field_simp
  subst hL₀ hμ hL₁ hσy hW hs hr hc ha
  subst hβ
  subst hlam
  rw [hκ']
  have hden : 1 / (ib * (ε / (κ * u))) * (cc * ε) + κ * (d * u / n) = κ * u * (cc / ib + d / n) := by
    field_simp
  obtain ⟨F, hF⟩ : ∃ F, cc / ib + d / n = F := ⟨_, rfl⟩
  have hF0 : 0 < F := by rw [← hF]; positivity
  rw [hF] at hden
  rw [hden]
  have hlam0 : 0 < 1 / (κ * u * F) := by positivity
  refine ⟨by positivity, by positivity, ?_, ?_, ?_, by positivity, ?_, ?_, by positivity, ?_, by positivity,
    ?_, hlam0, ?_, ?_, ?_⟩
  · rw [div_le_one (by linarith)]; exact hia
  · have e : 16 * (1 + κ) * (ℓ / u) * (d * u / n) = 16 * (1 + κ) * ℓ * d / n := by field_simp
    rw [e, div_le_div_iff₀ hn0 (by linarith)]
    linarith
  · have e : 16 * (ℓ / u) * (x * u) = 16 * ℓ * x := by field_simp
    rw [e]; exact hx16
  · have e : 2 * (1 / (ib * (ε / (κ * u)))) * (ε / u) ^ 2 = ε / (κ * u) * (2 * κ ^ 2 / ib) := by
      field_simp
    rw [e]
    have h : 2 * κ ^ 2 / ib ≤ 1 := by rw [div_le_one hib0]; linarith
    have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ ε / (κ * u))
    linarith
  · have e : 1 / (ib * (ε / (κ * u))) * (ε / (κ * u)) = 1 / ib := by field_simp
    rw [e, div_le_one hib0]; linarith
  · have e : ε / u * (x * u) = ε * x := by field_simp
    rw [e]
    have h1 : 2 * x ≤ 192 * κ * x := by
      have := mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ 192 * κ) hx0.le
      linarith
    have h2 : 2 * x * ε ≤ cc * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
    have e2 : ε * x = 2 * x * ε / 2 := by ring
    rw [e2]; linarith
  · have := mul_le_mul_of_nonneg_right hωx hu.le
    linarith
  · field_simp
  · have e1 : (8 * (1 / (ib * (ε / (κ * u)))) * (ϑy * ε) ^ 4 / (ε / (κ * u) * (cc * ε) ^ 2) +
          2 * (1 / (ib * (ε / (κ * u)))) ^ 2 * (ϑy * ε) ^ 2) / (2 * (x * u / 2)) =
        u * (8 * κ ^ 2 * ϑy ^ 4 / (ib * cc ^ 2 * x) + 2 * κ ^ 2 * ϑy ^ 2 / (ib ^ 2 * x)) := by
      field_simp
    have e2 : κ * (d * u / n) = u * (κ * d / n) := by field_simp
    have e3 : 4 * (1 / (ib * (ε / (κ * u)))) ^ 2 * ((ε / u) ^ 2 * (x * u) ^ 2 + (ϑy * ε) ^ 2) +
        2 * (κ * (d * u / n)) ^ 2 = (κ * u) ^ 2 * (4 * (x ^ 2 + ϑy ^ 2) / ib ^ 2 + 2 * d ^ 2 / n ^ 2) := by
      field_simp
    have e4 : 1 / (κ * u * F) * ((κ * u) ^ 2 * (4 * (x ^ 2 + ϑy ^ 2) / ib ^ 2 + 2 * d ^ 2 / n ^ 2)) =
        u * (κ * (4 * (x ^ 2 + ϑy ^ 2) / ib ^ 2 + 2 * d ^ 2 / n ^ 2) / F) := by
      field_simp
    have e5 : 1 / (ib * (ε / (κ * u))) * (ε / (κ * u)) * (x * u / 2) / 4 = u * (x / (8 * ib)) := by
      field_simp; ring
    rw [e1, e3, e2, e4, e5]
    have hcond := tune_cond hκ hℓ hq1 hLx (by linarith) hdq hy hθ hib hx0 hxy hcc hn0 hn7
    rw [hF] at hcond
    have := mul_le_mul_of_nonneg_left hcond hu.le
    linarith
  · have hl := tune_lambda hκ hℓ hq1 hLx hdq hy hθ hib hx0 hxy hcc hn0 hn8
    rw [hF] at hl
    have e : 1 / (κ * u * F) * (x * u) / 4 = x / (4 * κ * F) := by field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith

lemma tune_sum {ε u κ ℓ d g ϑx ϑy ω ib ia cc n L₀ μ L₁ σy W Δ ζ σx G₀ s c β a : ℝ}
    (hε : 0 < ε) (hu : 0 < u) (hκ : 1 ≤ κ) (hℓ : 0 ≤ ℓ) (hd : 1 ≤ d) (hϑx : 0 ≤ ϑx) (hω : 0 ≤ ω)
    (hn1 : 1 ≤ n) (hib : 2 ^ 16 * κ ^ 2 * ϑy ^ 2 ≤ ib) (hib1 : 1 ≤ ib) (hia : ia = 8192 * ϑx ^ 2 + 1)
    (hcc : 512 * κ * ϑy ^ 2 ≤ cc) (hcc0 : 0 < cc)
    (hn1' : 64 * (1 + ℓ * g) * ω * ia ≤ n) (hn2 : 96 * (1 + κ) * d * ia ≤ n) (hn3 : 512 * ω * ib ≤ n)
    (hn4 : 320 * κ * d * ib ≤ n) (hn5 : 91 * ϑx * ia ≤ n)
    (hL₀ : L₀ = ε / u) (hμ : μ = ε / (κ * u)) (hL₁ : L₁ = ℓ / u) (hσy : σy = ϑy * ε) (hW : W = ω * u)
    (hΔ : Δ ≤ d * ε * u / 32) (hζσ : ζ * σx = ϑx * ε) (hG₀ : G₀ ≤ ε * g)
    (hs : s = d * u / n) (hc : c = cc * ε) (hβ : β = 1 / (ib * μ)) (ha : a = 1 / ia) :
    2 * Δ / s + 4 * (L₀ + L₁ * G₀) * W / a + 4 * n * (1 + L₀ / μ) * L₀ * s / a + (1 + L₀ / μ) * L₀ * s / 4 +
        n * (1 + L₀ / μ) * L₀ * s +
        4 * L₀ * (8 * W / (β * μ) + n * Real.sqrt (4 / (β * μ) * (2 * (8 * β * σy ^ 4 / (μ * c ^ 2) +
          2 * β ^ 2 * σy ^ 2) + 5 * (L₀ / μ * s) ^ 2 / (β * μ)))) +
        4 * ζ * (Real.sqrt 2 * σx * (1 / a + n * Real.sqrt a)) ≤ 9 / 16 * (n * ε) := by
  have hκ0 : 0 < κ := by linarith
  have hn0 : 0 < n := by linarith
  have hia1 : 1 ≤ ia := by
    have : 0 ≤ 8192 * ϑx ^ 2 := by positivity
    rw [hia]; linarith
  have hia0 : 0 < ia := by linarith
  have hib0 : 0 < ib := by linarith
  have hκ' : ε / u / (ε / (κ * u)) = κ := by field_simp
  subst hL₀ hμ hL₁ hσy hW hs hc ha
  subst hβ
  rw [hκ']
  have T1 : 2 * Δ / (d * u / n) ≤ n * ε / 16 := by
    rw [div_le_iff₀ (by positivity)]
    have e : n * ε / 16 * (d * u / n) = d * ε * u / 16 := by field_simp
    rw [e]; linarith
  have T2 : 4 * (ε / u + ℓ / u * G₀) * (ω * u) / (1 / ia) ≤ n * ε / 16 := by
    have e : 4 * (ε / u + ℓ / u * G₀) * (ω * u) / (1 / ia) = 4 * (ε + ℓ * G₀) * ω * ia := by
      field_simp
    rw [e]
    have h1 : ℓ * G₀ ≤ ℓ * (ε * g) := mul_le_mul_of_nonneg_left hG₀ hℓ
    have h2 : 4 * (ε + ℓ * G₀) * ω * ia ≤ 4 * (ε + ℓ * (ε * g)) * ω * ia := by
      have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ 4 * ω * ia)
      linarith
    have h3 := mul_le_mul_of_nonneg_left hn1' (by positivity : (0 : ℝ) ≤ ε / 16)
    have e2 : 4 * (ε + ℓ * (ε * g)) * ω * ia = ε / 16 * (64 * (1 + ℓ * g) * ω * ia) := by ring
    linarith
  have T3 : 4 * n * (1 + κ) * (ε / u) * (d * u / n) / (1 / ia) + (1 + κ) * (ε / u) * (d * u / n) / 4 +
      n * (1 + κ) * (ε / u) * (d * u / n) ≤ n * ε / 16 := by
    have e1 : 4 * n * (1 + κ) * (ε / u) * (d * u / n) / (1 / ia) = 4 * ((1 + κ) * d * ε) * ia := by
      field_simp
    have e2 : (1 + κ) * (ε / u) * (d * u / n) / 4 = (1 + κ) * d * ε / (4 * n) := by field_simp
    have e3 : n * (1 + κ) * (ε / u) * (d * u / n) = (1 + κ) * d * ε := by field_simp
    rw [e1, e2, e3]
    have hP : 0 ≤ (1 + κ) * d * ε := by positivity
    have h1 : (1 + κ) * d * ε / (4 * n) ≤ (1 + κ) * d * ε * ia / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := mul_le_mul hia1 hn1 zero_le_one hia0.le
      have := mul_le_mul_of_nonneg_left this hP
      linarith
    have h2 : (1 + κ) * d * ε ≤ (1 + κ) * d * ε * ia := le_mul_of_one_le_right hP hia1
    have h3 := mul_le_mul_of_nonneg_left hn2 (by positivity : (0 : ℝ) ≤ ε / 16)
    have e4 : ε / 16 * (96 * (1 + κ) * d * ia) = 6 * ((1 + κ) * d * ε * ia) := by ring
    have e5 : 4 * ((1 + κ) * d * ε) * ia = 4 * ((1 + κ) * d * ε * ia) := by ring
    linarith
  have T4 : 4 * (ε / u) * (8 * (ω * u) / (1 / (ib * (ε / (κ * u))) * (ε / (κ * u)))) ≤ n * ε / 16 := by
    have e : 4 * (ε / u) * (8 * (ω * u) / (1 / (ib * (ε / (κ * u))) * (ε / (κ * u)))) = ε / 16 * (512 * ω * ib) := by
      field_simp; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hn3 (by positivity : (0 : ℝ) ≤ ε / 16)
    linarith
  have hV : 4 / (1 / (ib * (ε / (κ * u))) * (ε / (κ * u))) *
      (2 * (8 * (1 / (ib * (ε / (κ * u)))) * (ϑy * ε) ^ 4 / (ε / (κ * u) * (cc * ε) ^ 2) +
        2 * (1 / (ib * (ε / (κ * u)))) ^ 2 * (ϑy * ε) ^ 2) +
        5 * (κ * (d * u / n)) ^ 2 / (1 / (ib * (ε / (κ * u))) * (ε / (κ * u)))) =
      u ^ 2 * (64 * κ ^ 2 * ϑy ^ 4 / cc ^ 2 + 16 * κ ^ 2 * ϑy ^ 2 / ib + 20 * (κ * d * ib) ^ 2 / n ^ 2) := by
    field_simp; ring
  have V1 : 64 * κ ^ 2 * ϑy ^ 4 / cc ^ 2 ≤ 1 / 4096 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h := pow_le_pow_left₀ (by positivity) hcc 2
    have e : (512 * κ * ϑy ^ 2) ^ 2 = 64 * κ ^ 2 * ϑy ^ 4 * 4096 := by ring
    linarith
  have V2 : 16 * κ ^ 2 * ϑy ^ 2 / ib ≤ 1 / 4096 := by
    rw [div_le_div_iff₀ hib0 (by norm_num)]
    linarith
  have V3 : 20 * (κ * d * ib) ^ 2 / n ^ 2 ≤ 1 / 4096 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have h := pow_le_pow_left₀ (by positivity) hn4 2
    have e : (320 * κ * d * ib) ^ 2 = 102400 * (κ * d * ib) ^ 2 := by ring
    have : 0 ≤ (κ * d * ib) ^ 2 := by positivity
    linarith
  have T5 : 4 * (ε / u) * (n * Real.sqrt (4 / (1 / (ib * (ε / (κ * u))) * (ε / (κ * u))) *
      (2 * (8 * (1 / (ib * (ε / (κ * u)))) * (ϑy * ε) ^ 4 / (ε / (κ * u) * (cc * ε) ^ 2) +
        2 * (1 / (ib * (ε / (κ * u)))) ^ 2 * (ϑy * ε) ^ 2) +
        5 * (κ * (d * u / n)) ^ 2 / (1 / (ib * (ε / (κ * u))) * (ε / (κ * u)))))) ≤ 3 * (n * ε / 16) := by
    rw [hV]
    have h1 : u ^ 2 * (64 * κ ^ 2 * ϑy ^ 4 / cc ^ 2 + 16 * κ ^ 2 * ϑy ^ 2 / ib + 20 * (κ * d * ib) ^ 2 / n ^ 2) ≤
        (3 * u / 64) ^ 2 := by
      have := mul_le_mul_of_nonneg_left (by linarith : 64 * κ ^ 2 * ϑy ^ 4 / cc ^ 2 + 16 * κ ^ 2 * ϑy ^ 2 / ib +
        20 * (κ * d * ib) ^ 2 / n ^ 2 ≤ 3 / 4096) (by positivity : (0 : ℝ) ≤ u ^ 2)
      have e : (3 * u / 64) ^ 2 = u ^ 2 * (9 / 4096) := by ring
      have : 0 ≤ u ^ 2 := by positivity
      linarith
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq (by positivity)] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * (ε / u) * n)
    have e : 4 * (ε / u) * n * (3 * u / 64) = 3 * (n * ε / 16) := by field_simp; ring
    linarith
  have hs2 : Real.sqrt 2 ≤ 91 / 64 := by
    rw [show (91 / 64 : ℝ) = Real.sqrt ((91 / 64) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have T6 : 4 * ζ * (Real.sqrt 2 * σx * (1 / (1 / ia) + n * Real.sqrt (1 / ia))) ≤ 2 * (n * ε / 16) := by
    have e : 4 * ζ * (Real.sqrt 2 * σx * (1 / (1 / ia) + n * Real.sqrt (1 / ia))) =
        ε * (4 * Real.sqrt 2 * ϑx * ia) + ε * n * (4 * Real.sqrt 2 * ϑx * Real.sqrt (1 / ia)) := by
      have e1 : 4 * ζ * (Real.sqrt 2 * σx * (1 / (1 / ia) + n * Real.sqrt (1 / ia))) =
          4 * Real.sqrt 2 * (ζ * σx) * (ia + n * Real.sqrt (1 / ia)) := by field_simp
      rw [e1, hζσ]; ring
    rw [e]
    have h1 : 4 * Real.sqrt 2 * ϑx * ia ≤ n / 16 := by
      have : 4 * Real.sqrt 2 * ϑx * ia ≤ 4 * (91 / 64) * ϑx * ia := by
        have := mul_le_mul_of_nonneg_right hs2 (by positivity : (0 : ℝ) ≤ 4 * ϑx * ia)
        linarith
      linarith
    have h2 : 4 * Real.sqrt 2 * ϑx * Real.sqrt (1 / ia) ≤ 1 / 16 := by
      have hw : 0 ≤ 4 * Real.sqrt 2 * ϑx * Real.sqrt (1 / ia) := by positivity
      rw [← pow_le_pow_iff_left₀ hw (by norm_num) (two_ne_zero)]
      have e2 : (4 * Real.sqrt 2 * ϑx * Real.sqrt (1 / ia)) ^ 2 =
          16 * (Real.sqrt 2) ^ 2 * ϑx ^ 2 * (Real.sqrt (1 / ia)) ^ 2 := by ring
      rw [e2, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]
      rw [hia]
      have e3 : 16 * 2 * ϑx ^ 2 * (1 / (8192 * ϑx ^ 2 + 1)) = 32 * ϑx ^ 2 / (8192 * ϑx ^ 2 + 1) := by
        ring
      rw [e3, div_le_iff₀ (by positivity)]
      linarith
    have h3 := mul_le_mul_of_nonneg_left h1 hε.le
    have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ ε * n)
    linarith
  have e8 : 4 * (ε / u) * (8 * (ω * u) / (1 / (ib * (ε / (κ * u))) * (ε / (κ * u))) +
      n * Real.sqrt (4 / (1 / (ib * (ε / (κ * u))) * (ε / (κ * u))) *
      (2 * (8 * (1 / (ib * (ε / (κ * u)))) * (ϑy * ε) ^ 4 / (ε / (κ * u) * (cc * ε) ^ 2) +
        2 * (1 / (ib * (ε / (κ * u)))) ^ 2 * (ϑy * ε) ^ 2) +
        5 * (κ * (d * u / n)) ^ 2 / (1 / (ib * (ε / (κ * u))) * (ε / (κ * u)))))) =
      4 * (ε / u) * (8 * (ω * u) / (1 / (ib * (ε / (κ * u))) * (ε / (κ * u)))) +
      4 * (ε / u) * (n * Real.sqrt (4 / (1 / (ib * (ε / (κ * u))) * (ε / (κ * u))) *
      (2 * (8 * (1 / (ib * (ε / (κ * u)))) * (ϑy * ε) ^ 4 / (ε / (κ * u) * (cc * ε) ^ 2) +
        2 * (1 / (ib * (ε / (κ * u)))) ^ 2 * (ϑy * ε) ^ 2) +
        5 * (κ * (d * u / n)) ^ 2 / (1 / (ib * (ε / (κ * u))) * (ε / (κ * u)))))) := by ring
  rw [e8]
  linarith

lemma tune_exit {ε u κ ℓ d q Lx g L₀ μ L₁ W G₀ s r c β lam : ℝ} (N : ℕ)
    (hε : 0 < ε) (hu : 0 < u) (hκ : 0 < κ) (hℓ : 0 ≤ ℓ) (hd : 0 ≤ d) (hN : 1 ≤ N)
    (hq2 : q ^ 2 = (1 + κ) * d)
    (hL₀ : L₀ = ε / u) (hμ : μ = ε / (κ * u)) (hL₁ : L₁ = ℓ / u) (hs : s = d * u / N)
    (hG₀0 : 0 ≤ G₀) (hG₀ : G₀ ≤ ε * g) (hr : 0 ≤ r) (hWr : W ≤ 3 * r / 4) (hlam0 : 0 ≤ lam)
    (hlamB : lam * (β * c + L₀ / μ * s) = 1) (hΛ : ℓ * q ^ 2 + Lx ≤ lam * r / 4)
    (hX : 32 * (g + q ^ 2) * ((N : ℝ) + 1) ^ 2 ≤ Real.exp Lx) :
    (G₀ + (1 + L₀ / μ) * L₀ * s * N) * (1 + (1 + L₀ / μ) * L₁ * s) ^ N *
      (((N : ℝ) + 1) * (Real.exp (lam * W) + ((N : ℝ) + 1) * Real.exp (lam * (r / 2 + β * c + L₀ / μ * s))) *
        Real.exp (-(lam * r))) ≤ ε / 8 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hκ' : L₀ / μ = κ := by rw [hL₀, hμ]; field_simp
  rw [hκ'] at hlamB ⊢
  have h1 : (1 + κ) * L₀ * s * N = ε * q ^ 2 := by
    rw [hL₀, hs, hq2]; field_simp
  have h2 : (1 + κ) * L₁ * s * N = ℓ * q ^ 2 := by
    rw [hL₁, hs, hq2]; field_simp
  have hg0 : 0 ≤ g := by
    by_contra h
    push Not at h
    have : ε * g < 0 := mul_neg_of_pos_of_neg hε h
    linarith
  have ht0 : 0 ≤ (1 + κ) * L₁ * s := by
    rw [hL₁, hs]; positivity
  have hpow : (1 + (1 + κ) * L₁ * s) ^ N ≤ Real.exp (ℓ * q ^ 2) := by
    have a1 : 1 + (1 + κ) * L₁ * s ≤ Real.exp ((1 + κ) * L₁ * s) := by
      linarith [Real.add_one_le_exp ((1 + κ) * L₁ * s)]
    have a2 := pow_le_pow_left₀ (by linarith) a1 N
    rw [← Real.exp_nat_mul] at a2
    have e : (N : ℝ) * ((1 + κ) * L₁ * s) = ℓ * q ^ 2 := by rw [← h2]; ring
    rw [e] at a2; exact a2
  have hG : G₀ + (1 + κ) * L₀ * s * N ≤ ε * (g + q ^ 2) := by
    rw [h1]; linarith
  have hE0 : 0 < Real.exp (-(lam * r / 4)) := Real.exp_pos _
  have hp1 : Real.exp (lam * W) * Real.exp (-(lam * r)) ≤ Real.exp (-(lam * r / 4)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have := mul_le_mul_of_nonneg_left hWr hlam0
    linarith
  have hp2 : Real.exp (lam * (r / 2 + β * c + κ * s)) * Real.exp (-(lam * r)) ≤ 3 * Real.exp (-(lam * r / 4)) := by
    have e : lam * (r / 2 + β * c + κ * s) + -(lam * r) = 1 + -(lam * r / 4) + -(lam * r / 4) := by
      have : lam * (r / 2 + β * c + κ * s) = lam * r / 2 + lam * (β * c + κ * s) := by ring
      rw [this, hlamB]; ring
    rw [← Real.exp_add, e, Real.exp_add, Real.exp_add]
    have hlr : 0 ≤ lam * r / 4 := by positivity
    have a1 : Real.exp (-(lam * r / 4)) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have a2 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have a3 : Real.exp 1 * Real.exp (-(lam * r / 4)) ≤ 3 * 1 :=
      mul_le_mul a2 a1 (Real.exp_pos _).le (by norm_num)
    have := mul_le_mul_of_nonneg_right a3 hE0.le
    linarith
  have hπ : ((N : ℝ) + 1) * (Real.exp (lam * W) + ((N : ℝ) + 1) * Real.exp (lam * (r / 2 + β * c + κ * s))) *
      Real.exp (-(lam * r)) ≤ 4 * ((N : ℝ) + 1) ^ 2 * Real.exp (-(lam * r / 4)) := by
    have e : ((N : ℝ) + 1) * (Real.exp (lam * W) + ((N : ℝ) + 1) * Real.exp (lam * (r / 2 + β * c + κ * s))) *
        Real.exp (-(lam * r)) = ((N : ℝ) + 1) * (Real.exp (lam * W) * Real.exp (-(lam * r))) +
        ((N : ℝ) + 1) ^ 2 * (Real.exp (lam * (r / 2 + β * c + κ * s)) * Real.exp (-(lam * r))) := by ring
    rw [e]
    have b1 := mul_le_mul_of_nonneg_left hp1 (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
    have b2 := mul_le_mul_of_nonneg_left hp2 (by positivity : (0 : ℝ) ≤ ((N : ℝ) + 1) ^ 2)
    have b3 : ((N : ℝ) + 1) * Real.exp (-(lam * r / 4)) ≤ ((N : ℝ) + 1) ^ 2 * Real.exp (-(lam * r / 4)) := by
      have : (N : ℝ) + 1 ≤ ((N : ℝ) + 1) ^ 2 := by
        have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ (N : ℝ) + 1) (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
        rw [sq]; linarith
      exact mul_le_mul_of_nonneg_right this hE0.le
    linarith
  have hπ0 : 0 ≤ ((N : ℝ) + 1) * (Real.exp (lam * W) + ((N : ℝ) + 1) *
      Real.exp (lam * (r / 2 + β * c + κ * s))) * Real.exp (-(lam * r)) := by positivity
  have hGm := mul_le_mul hG hpow (by positivity) (by positivity)
  have hall := mul_le_mul hGm hπ hπ0 (by positivity)
  refine hall.trans ?_
  have e : ε * (g + q ^ 2) * Real.exp (ℓ * q ^ 2) * (4 * ((N : ℝ) + 1) ^ 2 * Real.exp (-(lam * r / 4))) =
      ε / 8 * (32 * (g + q ^ 2) * ((N : ℝ) + 1) ^ 2) * Real.exp (ℓ * q ^ 2 + -(lam * r / 4)) := by
    rw [Real.exp_add]; ring
  rw [e]
  have c1 : Real.exp (ℓ * q ^ 2 + -(lam * r / 4)) ≤ Real.exp (-Lx) := by
    rw [Real.exp_le_exp]; linarith
  have c2 : 32 * (g + q ^ 2) * ((N : ℝ) + 1) ^ 2 * Real.exp (-Lx) ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hX (Real.exp_pos (-Lx)).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
    exact this
  have c3 := mul_le_mul_of_nonneg_left c1 (by positivity : (0 : ℝ) ≤ ε / 8 * (32 * (g + q ^ 2) * ((N : ℝ) + 1) ^ 2))
  have c4 := mul_le_mul_of_nonneg_left c2 (by positivity : (0 : ℝ) ≤ ε / 8)
  have e5 : ε / 8 * (32 * (g + q ^ 2) * ((N : ℝ) + 1) ^ 2) * Real.exp (-Lx) =
      ε / 8 * (32 * (g + q ^ 2) * ((N : ℝ) + 1) ^ 2 * Real.exp (-Lx)) := by ring
  linarith

lemma tune_budget {κ ℓ d q ϑx ϑy ω Lx y θi ib ia g B : ℝ} (hκ : 1 ≤ κ) (hℓ : 0 ≤ ℓ) (hd : 1 ≤ d)
    (hϑx : 0 ≤ ϑx) (hω : 0 ≤ ω) (hq0 : 0 ≤ q) (hq2 : q ^ 2 = (1 + κ) * d) (hLx : 0 ≤ Lx)
    (hy : y = q + Lx) (hθ : θi = 1024 * (1 + ℓ) * (1 + ℓ * y) ^ 2)
    (hib : ib = κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) * θi) (hia : ia = 8192 * ϑx ^ 2 + 1)
    (hg : g = (5 * q + ℓ * q ^ 2) / 12)
    (hB : B = 2 ^ 39 * (1 + κ) * (1 + ℓ * (1 + y)) ^ 4 * (d + ω + q + ϑx) *
      (ϑx ^ 2 + κ ^ 2 * (1 + y + ϑy ^ 2))) :
    64 * (1 + ℓ * g) * ω * ia ≤ B ∧ 96 * (1 + κ) * d * ia ≤ B ∧ 512 * ω * ib ≤ B ∧ 320 * κ * d * ib ≤ B ∧
      91 * ϑx * ia ≤ B ∧ 16 * (1 + κ) * ℓ * d * ia ≤ B ∧ 4608 * κ * (1 + ℓ * y) * q * ib ≤ B ∧
      768 * κ * (1 + ℓ * y) * q * (ℓ * q ^ 2 + Lx) ≤ B := by
  obtain ⟨P, hP⟩ : ∃ P, 1 + ℓ * (1 + y) = P := ⟨_, rfl⟩
  obtain ⟨F₁, hF₁⟩ : ∃ F, d + ω + q + ϑx = F := ⟨_, rfl⟩
  obtain ⟨F₂, hF₂⟩ : ∃ F, ϑx ^ 2 + κ ^ 2 * (1 + y + ϑy ^ 2) = F := ⟨_, rfl⟩
  rw [hP, hF₁, hF₂] at hB
  have hκ0 : 0 ≤ κ := by linarith
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hqy : q ≤ y := by rw [hy]; linarith
  have hℓy : 0 ≤ ℓ * y := by positivity
  have hP1 : 1 ≤ P := by
    have : 0 ≤ ℓ * (1 + y) := by positivity
    rw [← hP]; linarith
  have hP0 : 0 ≤ P := by linarith
  have hlP : 1 + ℓ ≤ P := by rw [← hP]; linarith
  have hlyP : 1 + ℓ * y ≤ P := by
    have : 0 ≤ ℓ := hℓ
    rw [← hP]; linarith
  have hly1 : 1 ≤ 1 + ℓ * y := by linarith
  have hPw1 : 1 ≤ P ^ 4 := one_le_pow₀ hP1
  have hPw2 : (1 + ℓ * y) ^ 2 ≤ P ^ 4 :=
    (pow_le_pow_left₀ (by linarith) hlyP 2).trans (pow_le_pow_right₀ hP1 (by norm_num))
  have hPw3 : (1 + ℓ) * (1 + ℓ * y) ^ 3 ≤ P ^ 4 := by
    have := mul_le_mul hlP (pow_le_pow_left₀ (by linarith) hlyP 3) (by positivity) hP0
    calc (1 + ℓ) * (1 + ℓ * y) ^ 3 ≤ P * P ^ 3 := this
      _ = P ^ 4 := by ring
  have hPw4 : (1 + ℓ) * (1 + ℓ * y) ^ 2 ≤ P ^ 4 := by
    have := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by positivity) hly1 :
      (1 + ℓ * y) ^ 2 ≤ (1 + ℓ * y) ^ 2 * (1 + ℓ * y)) (by linarith : (0 : ℝ) ≤ 1 + ℓ)
    calc (1 + ℓ) * (1 + ℓ * y) ^ 2 ≤ (1 + ℓ) * ((1 + ℓ * y) ^ 2 * (1 + ℓ * y)) := this
      _ = (1 + ℓ) * (1 + ℓ * y) ^ 3 := by ring
      _ ≤ P ^ 4 := hPw3
  have hF₁0 : 0 ≤ F₁ := by rw [← hF₁]; positivity
  have hdF : d ≤ F₁ := by rw [← hF₁]; linarith
  have hωF : ω ≤ F₁ := by rw [← hF₁]; linarith
  have hqF : q ≤ F₁ := by rw [← hF₁]; linarith
  have hϑF : ϑx ≤ F₁ := by rw [← hF₁]; linarith
  have hκ2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  have hF₂0 : 0 ≤ F₂ := by rw [← hF₂]; positivity
  have hiaB : ia ≤ 8192 * F₂ := by
    rw [hia, ← hF₂]
    have : 1 ≤ κ ^ 2 * (1 + y + ϑy ^ 2) := by
      have := mul_le_mul hκ2 (by nlinarith [sq_nonneg ϑy] : (1 : ℝ) ≤ 1 + y + ϑy ^ 2) zero_le_one (by positivity)
      linarith
    linarith
  have hYF : κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) ≤ 2 ^ 16 * F₂ := by
    rw [← hF₂]
    have : κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) ≤ κ ^ 2 * (2 ^ 16 * (1 + y + ϑy ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have : 0 ≤ 2 ^ 16 * ϑx ^ 2 := by positivity
    linarith
  have hY0 : 0 ≤ κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) := by positivity
  have hibB : ib ≤ 2 ^ 26 * P ^ 4 * F₂ := by
    rw [hib, hθ]
    have := mul_le_mul hYF hPw4 (by positivity) (by positivity)
    calc κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) * (1024 * (1 + ℓ) * (1 + ℓ * y) ^ 2) =
        1024 * (κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) * ((1 + ℓ) * (1 + ℓ * y) ^ 2)) := by ring
      _ ≤ 1024 * (2 ^ 16 * F₂ * P ^ 4) := by linarith
      _ = 2 ^ 26 * P ^ 4 * F₂ := by ring
  have hib' : (1 + ℓ * y) * ib ≤ 2 ^ 26 * P ^ 4 * F₂ := by
    rw [hib, hθ]
    have := mul_le_mul hYF hPw3 (by positivity) (by positivity)
    calc (1 + ℓ * y) * (κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) * (1024 * (1 + ℓ) * (1 + ℓ * y) ^ 2)) =
        1024 * (κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) * ((1 + ℓ) * (1 + ℓ * y) ^ 3)) := by ring
      _ ≤ 1024 * (2 ^ 16 * F₂ * P ^ 4) := by linarith
      _ = 2 ^ 26 * P ^ 4 * F₂ := by ring
  have hib0 : 0 ≤ ib := by rw [hib, hθ]; positivity
  have hia0 : 0 ≤ ia := by rw [hia]; positivity
  have hq2' : q ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hq0 hqy 2
  have hg1 : 1 + ℓ * g ≤ (1 + ℓ * y) ^ 2 := by
    have a1 : ℓ * q ≤ ℓ * y := mul_le_mul_of_nonneg_left hqy hℓ
    have a2 : ℓ * (ℓ * q ^ 2) ≤ ℓ * (ℓ * y ^ 2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hq2' hℓ) hℓ
    have e : ℓ * g = (5 * (ℓ * q) + ℓ * (ℓ * q ^ 2)) / 12 := by rw [hg]; ring
    have e2 : (1 + ℓ * y) ^ 2 = 1 + 2 * (ℓ * y) + ℓ * (ℓ * y ^ 2) := by ring
    have : 0 ≤ ℓ * q := by positivity
    have : 0 ≤ ℓ * (ℓ * q ^ 2) := by positivity
    rw [e, e2]; linarith
  have hB' : B = 2 ^ 39 * ((1 + κ) * P ^ 4 * F₁ * F₂) := by rw [hB]; ring
  have hX0 : 0 ≤ (1 + κ) * P ^ 4 * F₁ * F₂ := by positivity
  have hPF : P ^ 4 * F₁ * F₂ ≤ (1 + κ) * P ^ 4 * F₁ * F₂ := by
    have : 0 ≤ κ * (P ^ 4 * F₁ * F₂) := by positivity
    have e : (1 + κ) * P ^ 4 * F₁ * F₂ = P ^ 4 * F₁ * F₂ + κ * (P ^ 4 * F₁ * F₂) := by ring
    linarith
  have hKF : (1 + κ) * F₁ * F₂ ≤ (1 + κ) * P ^ 4 * F₁ * F₂ := by
    have h := mul_le_mul_of_nonneg_left hPw1 (by positivity : (0 : ℝ) ≤ (1 + κ) * F₁ * F₂)
    have e : (1 + κ) * F₁ * F₂ * P ^ 4 = (1 + κ) * P ^ 4 * F₁ * F₂ := by ring
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have a1 : (1 + ℓ * g) * ω ≤ P ^ 4 * F₁ :=
      mul_le_mul (hg1.trans hPw2) hωF hω (by positivity)
    have a2 := mul_le_mul a1 hiaB hia0 (by positivity)
    have e : 64 * (1 + ℓ * g) * ω * ia = 64 * ((1 + ℓ * g) * ω * ia) := by ring
    rw [e, hB']
    have e2 : P ^ 4 * F₁ * (8192 * F₂) = 8192 * (P ^ 4 * F₁ * F₂) := by ring
    linarith
  · have a1 : (1 + κ) * d * ia ≤ (1 + κ) * F₁ * (8192 * F₂) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hdF (by linarith)) hiaB hia0 (by positivity)
    have e : 96 * (1 + κ) * d * ia = 96 * ((1 + κ) * d * ia) := by ring
    have e2 : (1 + κ) * F₁ * (8192 * F₂) = 8192 * ((1 + κ) * F₁ * F₂) := by ring
    rw [e, hB']; linarith
  · have a1 := mul_le_mul hωF hibB hib0 hF₁0
    have e : 512 * ω * ib = 512 * (ω * ib) := by ring
    have e2 : F₁ * (2 ^ 26 * P ^ 4 * F₂) = 2 ^ 26 * (P ^ 4 * F₁ * F₂) := by ring
    rw [e, hB']; linarith
  · have a1 := mul_le_mul (mul_le_mul (by linarith : κ ≤ 1 + κ) hdF (by linarith) (by linarith)) hibB hib0
      (by positivity)
    have e : 320 * κ * d * ib = 320 * (κ * d * ib) := by ring
    have e2 : (1 + κ) * F₁ * (2 ^ 26 * P ^ 4 * F₂) = 2 ^ 26 * ((1 + κ) * P ^ 4 * F₁ * F₂) := by ring
    rw [e, hB']; linarith
  · have a1 := mul_le_mul hϑF hiaB hia0 hF₁0
    have e : 91 * ϑx * ia = 91 * (ϑx * ia) := by ring
    have e2 : F₁ * (8192 * F₂) = 8192 * (F₁ * F₂) := by ring
    have : F₁ * F₂ ≤ P ^ 4 * F₁ * F₂ := by
      have h := mul_le_mul_of_nonneg_left hPw1 (by positivity : (0 : ℝ) ≤ F₁ * F₂)
      have e : F₁ * F₂ * P ^ 4 = P ^ 4 * F₁ * F₂ := by ring
      linarith
    rw [e, hB']; linarith
  · have a0 : ℓ * d ≤ (1 + ℓ * y) * q := by
      have h1 : d ≤ q ^ 2 := by
        have := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ 1 + κ) (by linarith : (0 : ℝ) ≤ d)
        rw [hq2]; linarith
      have h2 : ℓ * d ≤ ℓ * q * q := by
        have := mul_le_mul_of_nonneg_left h1 hℓ
        rw [sq] at this; linarith
      have h3 : ℓ * q * q ≤ ℓ * y * q := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqy hℓ) hq0
      have e : (1 + ℓ * y) * q = q + ℓ * y * q := by ring
      rw [e]; linarith
    have a1 : ℓ * d ≤ P ^ 4 * F₁ :=
      a0.trans (mul_le_mul ((le_self_pow₀ hly1 (by norm_num : (2 : ℕ) ≠ 0)).trans hPw2) hqF hq0 (by positivity))
    have a2 := mul_le_mul (mul_le_mul_of_nonneg_left a1 (by linarith : (0 : ℝ) ≤ 1 + κ)) hiaB hia0
      (by positivity)
    have e : 16 * (1 + κ) * ℓ * d * ia = 16 * ((1 + κ) * (ℓ * d) * ia) := by ring
    have e2 : (1 + κ) * (P ^ 4 * F₁) * (8192 * F₂) = 8192 * ((1 + κ) * P ^ 4 * F₁ * F₂) := by ring
    rw [e, hB']; linarith
  · have a1 : κ * q * ((1 + ℓ * y) * ib) ≤ (1 + κ) * F₁ * (2 ^ 26 * P ^ 4 * F₂) :=
      mul_le_mul (mul_le_mul (by linarith) hqF hq0 (by linarith)) hib' (by positivity) (by positivity)
    have e : 4608 * κ * (1 + ℓ * y) * q * ib = 4608 * (κ * q * ((1 + ℓ * y) * ib)) := by ring
    have e2 : (1 + κ) * F₁ * (2 ^ 26 * P ^ 4 * F₂) = 2 ^ 26 * ((1 + κ) * P ^ 4 * F₁ * F₂) := by ring
    rw [e, hB']; linarith
  · have a0 : ℓ * q ^ 2 + Lx ≤ y * (1 + ℓ * y) := by
      have := mul_le_mul_of_nonneg_left hq2' hℓ
      have e : y * (1 + ℓ * y) = y + ℓ * y ^ 2 := by ring
      rw [e, hy]; rw [hy] at this; linarith
    have hyF : y ≤ F₂ := by
      rw [← hF₂]
      have := mul_le_mul hκ2 (by nlinarith [sq_nonneg ϑy] : y ≤ 1 + y + ϑy ^ 2) hy0 (by positivity)
      have : 0 ≤ ϑx ^ 2 := by positivity
      linarith
    have a1 : (1 + ℓ * y) * (ℓ * q ^ 2 + Lx) ≤ P ^ 4 * F₂ := by
      have := mul_le_mul_of_nonneg_left a0 (by linarith : (0 : ℝ) ≤ 1 + ℓ * y)
      have e : (1 + ℓ * y) * (y * (1 + ℓ * y)) = (1 + ℓ * y) ^ 2 * y := by ring
      have := mul_le_mul hPw2 hyF hy0 (by positivity)
      linarith
    have a2 : κ * q * ((1 + ℓ * y) * (ℓ * q ^ 2 + Lx)) ≤ (1 + κ) * F₁ * (P ^ 4 * F₂) :=
      mul_le_mul (mul_le_mul (by linarith) hqF hq0 (by linarith)) a1 (by positivity) (by positivity)
    have e : 768 * κ * (1 + ℓ * y) * q * (ℓ * q ^ 2 + Lx) = 768 * (κ * q * ((1 + ℓ * y) * (ℓ * q ^ 2 + Lx))) := by
      ring
    have e2 : (1 + κ) * F₁ * (P ^ 4 * F₂) = (1 + κ) * P ^ 4 * F₁ * F₂ := by ring
    rw [e, hB']; linarith

lemma tune_crude {κ ℓ d q ϑx ϑy ω Lx y g B m : ℝ} (hκ : 1 ≤ κ) (hℓ : 0 ≤ ℓ) (hd : 1 ≤ d) (hϑx : 0 ≤ ϑx)
    (hϑy : 0 ≤ ϑy) (hω : 0 ≤ ω) (hq0 : 0 ≤ q) (hq2 : q ^ 2 = (1 + κ) * d)
    (hLx : Lx = 40 * Real.log (2 ^ 20 * (1 + κ + d + ϑx + ϑy + ω + ℓ))) (hy : y = q + Lx)
    (hg : g = (5 * q + ℓ * q ^ 2) / 12)
    (hB : B = 2 ^ 39 * (1 + κ) * (1 + ℓ * (1 + y)) ^ 4 * (d + ω + q + ϑx) *
      (ϑx ^ 2 + κ ^ 2 * (1 + y + ϑy ^ 2)))
    (hm0 : 0 ≤ m) (hm : m ≤ B + 3) : 32 * (g + q ^ 2) * m ^ 2 ≤ Real.exp Lx := by
  obtain ⟨G, hG⟩ : ∃ G, 1 + κ + d + ϑx + ϑy + ω + ℓ = G := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, 2 ^ 20 * G = Z := ⟨_, rfl⟩
  rw [hG, hZ] at hLx
  have hG3 : 3 ≤ G := by rw [← hG]; linarith
  have hZ3 : 3 * 2 ^ 20 ≤ Z := by rw [← hZ]; linarith
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hGZ : G ≤ Z := by rw [← hZ]; linarith
  have hexp : Real.exp Lx = Z ^ 40 := by
    rw [hLx, show (40 : ℝ) * Real.log Z = ((40 : ℕ) : ℝ) * Real.log Z by norm_num, Real.exp_nat_mul,
      Real.exp_log hZ0]
  have hlog : Real.log Z ≤ Z := by linarith [Real.log_le_sub_one_of_pos hZ0]
  have hLx0 : 0 ≤ Lx := by rw [hLx]; have := Real.log_nonneg hZ1; positivity
  have hLxZ : Lx ≤ 40 * Z := by rw [hLx]; linarith
  have hκG : 1 + κ ≤ G := by rw [← hG]; linarith
  have hκG' : κ ≤ G := by linarith
  have hdG : d ≤ G := by rw [← hG]; linarith
  have hϑxG : ϑx ≤ G := by rw [← hG]; linarith
  have hϑyG : ϑy ≤ G := by rw [← hG]; linarith
  have hωG : ω ≤ G := by rw [← hG]; linarith
  have hℓG : ℓ ≤ G := by rw [← hG]; linarith
  have hG0 : 0 ≤ G := by linarith
  have hqG : q ≤ G := by
    have h1 : (1 + κ) * d ≤ G * G := mul_le_mul hκG hdG (by linarith) hG0
    rw [← pow_le_pow_iff_left₀ hq0 hG0 (two_ne_zero), hq2, sq]
    exact h1
  have hZ2 : Z ≤ Z ^ 2 := (pow_one Z).symm.le.trans (pow_le_pow_right₀ hZ1 (by norm_num))
  have hZ2' : 4 ≤ Z ^ 2 := by linarith
  have hZ3' : Z ^ 2 ≤ Z ^ 3 := pow_le_pow_right₀ hZ1 (by norm_num)
  have hZ4 : Z ^ 3 ≤ Z ^ 4 := pow_le_pow_right₀ hZ1 (by norm_num)
  have hGZ2 : G * Z = Z ^ 2 / 2 ^ 20 := by rw [← hZ]; ring
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hyZ : y ≤ 41 * Z := by rw [hy]; linarith
  have hP : 1 + ℓ * (1 + y) ≤ Z ^ 2 := by
    have h1 : ℓ * (1 + y) ≤ G * (1 + 41 * Z) := mul_le_mul hℓG (by linarith) (by linarith) hG0
    have e : G * (1 + 41 * Z) = G + 41 * (G * Z) := by ring
    rw [e, hGZ2] at h1
    linarith
  have hP4 : (1 + ℓ * (1 + y)) ^ 4 ≤ Z ^ 8 := by
    have := pow_le_pow_left₀ (by positivity) hP 4
    rw [← pow_mul] at this; exact this
  have hF1 : d + ω + q + ϑx ≤ Z := by linarith
  have hF2 : ϑx ^ 2 + κ ^ 2 * (1 + y + ϑy ^ 2) ≤ Z ^ 4 := by
    have h1 : ϑx ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hϑx hϑxG 2
    have h2 : κ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (by linarith) hκG' 2
    have h3 : ϑy ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hϑy hϑyG 2
    have h4 : κ ^ 2 * (1 + y + ϑy ^ 2) ≤ G ^ 2 * (1 + 41 * Z + G ^ 2) :=
      mul_le_mul h2 (by linarith) (by positivity) (by positivity)
    have eG : G ^ 2 = Z ^ 2 / 2 ^ 40 := by rw [← hZ]; ring
    have e : G ^ 2 * (1 + 41 * Z + G ^ 2) = Z ^ 2 / 2 ^ 40 + 41 * Z ^ 3 / 2 ^ 40 + Z ^ 4 / 2 ^ 80 := by
      rw [eG]; ring
    rw [e] at h4
    rw [eG] at h1
    linarith
  have hc : (2 : ℝ) ^ 39 ≤ Z ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num) hZ3 2
    have e : (3 * 2 ^ 20 : ℝ) ^ 2 = 9 * 2 ^ 40 := by norm_num
    linarith
  have hKZ : 1 + κ ≤ Z := by linarith
  have hBZ : B ≤ Z ^ 16 := by
    rw [hB]
    calc 2 ^ 39 * (1 + κ) * (1 + ℓ * (1 + y)) ^ 4 * (d + ω + q + ϑx) * (ϑx ^ 2 + κ ^ 2 * (1 + y + ϑy ^ 2)) ≤
        Z ^ 2 * Z * Z ^ 8 * Z * Z ^ 4 := by
          gcongr
      _ = Z ^ 16 := by ring
  have hZ16 : 1 ≤ Z ^ 16 := one_le_pow₀ hZ1
  have hmZ : m ≤ Z ^ 17 := by
    have e : Z ^ 17 = Z * Z ^ 16 := by ring
    have := mul_le_mul_of_nonneg_right hZ3 (by positivity : (0 : ℝ) ≤ Z ^ 16)
    linarith
  have hgq : g + q ^ 2 ≤ Z ^ 3 := by
    have h1 : q ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hq0 hqG 2
    have h2 : ℓ * q ^ 2 ≤ G * G ^ 2 := mul_le_mul hℓG h1 (by positivity) hG0
    have eG : G ^ 2 = Z ^ 2 / 2 ^ 40 := by rw [← hZ]; ring
    have eG3 : G * G ^ 2 = Z ^ 3 / 2 ^ 60 := by rw [← hZ]; ring
    rw [hg]
    rw [eG] at h1
    rw [eG3] at h2
    linarith
  have hgq0 : 0 ≤ g + q ^ 2 := by rw [hg]; positivity
  rw [hexp]
  calc 32 * (g + q ^ 2) * m ^ 2 ≤ Z * Z ^ 3 * (Z ^ 17) ^ 2 := by
        gcongr
        linarith
    _ = Z ^ 38 := by ring
    _ ≤ Z ^ 40 := pow_le_pow_right₀ hZ1 (by norm_num)

lemma tune_G0 {ε u κ ℓ d q L₀ μ L₁ Δ t : ℝ} (hε : 0 < ε) (hu : 0 < u) (hκ : 0 < κ) (hℓ : 0 ≤ ℓ) (hq : 0 < q)
    (hq2 : q ^ 2 = (1 + κ) * d) (hL₀ : L₀ = ε / u) (hμ : μ = ε / (κ * u)) (hL₁ : L₁ = ℓ / u)
    (hΔ : Δ ≤ d * ε * u / 32) (ht : t = q * u / (2 * (1 + κ) * (1 + ℓ * q))) :
    0 < t ∧ 2 * (1 + L₀ / μ) * L₁ * t ≤ 1 ∧
      4 / 3 * (Δ / t + (1 + L₀ / μ) * L₀ * t / 2) ≤ ε * ((5 * q + ℓ * q ^ 2) / 12) := by
  have hκ' : L₀ / μ = κ := by rw [hL₀, hμ]; field_simp
  have hA : 0 < 1 + ℓ * q := by positivity
  have ht0 : 0 < t := by rw [ht]; positivity
  refine ⟨ht0, ?_, ?_⟩
  · rw [hκ', hL₁, ht]
    have e : 2 * (1 + κ) * (ℓ / u) * (q * u / (2 * (1 + κ) * (1 + ℓ * q))) = ℓ * q / (1 + ℓ * q) := by
      field_simp
    rw [e, div_le_one hA]; linarith
  · rw [hκ']
    have h1 : Δ / t ≤ ε * (q * (1 + ℓ * q) / 16) := by
      rw [div_le_iff₀ ht0]
      have e : ε * (q * (1 + ℓ * q) / 16) * t = d * ε * u / 32 := by
        rw [ht]
        have e2 : d = q ^ 2 / (1 + κ) := by rw [hq2]; field_simp
        rw [e2]; field_simp; ring
      rw [e]; exact hΔ
    have h2 : (1 + κ) * L₀ * t / 2 ≤ ε * (q / 4) := by
      rw [hL₀, ht]
      have e : (1 + κ) * (ε / u) * (q * u / (2 * (1 + κ) * (1 + ℓ * q))) / 2 = ε * (q / 4) / (1 + ℓ * q) := by
        field_simp; ring
      rw [e, div_le_iff₀ hA]
      have : 0 ≤ ε * (q / 4) * (ℓ * q) := by positivity
      nlinarith
    have e : ε * ((5 * q + ℓ * q ^ 2) / 12) = 4 / 3 * (ε * (q * (1 + ℓ * q) / 16) + ε * (q / 4)) := by ring
    rw [e]
    have := add_le_add h1 h2
    linarith

lemma tune_misc {κ ℓ ω q Lx y ϑy θi ib x cc : ℝ} (hκ : 1 ≤ κ) (hℓ : 0 ≤ ℓ) (hω : 0 ≤ ω) (hq0 : 0 < q)
    (hLx : 0 ≤ Lx) (hy : y = q + Lx) (hθ : θi = 1024 * (1 + ℓ) * (1 + ℓ * y) ^ 2)
    (hib : ib = κ ^ 2 * (2 ^ 16 * ϑy ^ 2 + 3 * y + 1) * θi) (hx : x = 4 * ω / 3 + y / (48 * (1 + ℓ * y)))
    (hcc : cc = κ * (192 * x + 192 * ϑy ^ 2 / x + 512 * ϑy ^ 2)) :
    2 ^ 16 * κ ^ 2 * ϑy ^ 2 ≤ ib ∧ 1 ≤ ib ∧ 512 * κ * ϑy ^ 2 ≤ cc ∧ 0 < cc := by
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hA : 1 ≤ 1 + ℓ * y := by
    have : 0 ≤ ℓ * y := by positivity
    linarith
  have hθ1 : 1 ≤ θi := by
    have := one_le_mul_of_one_le_of_one_le (by linarith : (1 : ℝ) ≤ 1 + ℓ) (one_le_pow₀ (n := 2) hA)
    rw [hθ]; linarith
  have hY : 2 ^ 16 * ϑy ^ 2 ≤ 2 ^ 16 * ϑy ^ 2 + 3 * y + 1 := by linarith
  have hY1 : 1 ≤ 2 ^ 16 * ϑy ^ 2 + 3 * y + 1 := by
    have : 0 ≤ 2 ^ 16 * ϑy ^ 2 := by positivity
    linarith
  have hκ2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ
  have hx0 : 0 < x := by
    have : 0 < y := by rw [hy]; positivity
    rw [hx]; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 := mul_le_mul hY hθ1 zero_le_one (by linarith)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ κ ^ 2)
    rw [hib]; nlinarith
  · have h1 := one_le_mul_of_one_le_of_one_le hY1 hθ1
    have h2 := one_le_mul_of_one_le_of_one_le hκ2 h1
    rw [hib, mul_assoc]; exact h2
  · have : 0 ≤ κ * (192 * x + 192 * ϑy ^ 2 / x) := by positivity
    have e : cc = κ * (192 * x + 192 * ϑy ^ 2 / x) + 512 * κ * ϑy ^ 2 := by rw [hcc]; ring
    rw [e]; linarith
  · rw [hcc]
    have : 0 < 192 * x := by positivity
    have : 0 < 192 * x + 192 * ϑy ^ 2 / x + 512 * ϑy ^ 2 := by positivity
    positivity

end OracleTemplate.MinimaxLmo
