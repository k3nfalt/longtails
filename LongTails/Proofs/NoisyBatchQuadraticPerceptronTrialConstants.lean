import LongTails.Proofs.NoisyBatchQuadraticPerceptronTrials
namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialConstants
lemma gaussian_power_exp_lower (d B : ℕ) (a r A : ℝ) (ha : 0 < a)
    (hA : (B : ℝ) * ((d : ℝ) * Real.log a + r) ≤ A) :
    Real.exp (-A) ≤ ((1 / a) ^ d * Real.exp (-r)) ^ B := by
  have hp : 0 < ((1 / a) ^ d * Real.exp (-r)) ^ B := by positivity
  rw [← Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  rw [Real.log_pow, Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_pow, Real.log_div (by norm_num) ha.ne', Real.log_one, Real.log_exp]
  nlinarith
lemma common_log_bound (D M B : ℝ) (hD : 1 ≤ D) (hM : 4 ≤ M)
    (hB : 0 < B) (hBM : B ≤ 129 * M) :
    Real.log (128 * B * Real.sqrt D) ≤ 67 * D * M := by
  have hDp : 0 < D := by linarith
  have hMp : 0 < M := by linarith
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.2 hDp
  have hl : Real.log (128 * B * Real.sqrt D) ≤
      Real.log (128 * (129 * M) * Real.sqrt D) := by
    apply Real.log_le_log (by positivity)
    gcongr
  apply hl.trans
  rw [Real.log_mul (by positivity) hs.ne', Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by norm_num) hMp.ne', Real.log_sqrt hDp.le]
  have h128 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 128)
  have h129 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 129)
  have hmd := mul_le_mul_of_nonneg_left hM (by linarith : 0 ≤ D - 1)
  have hmm := mul_le_mul_of_nonneg_left hD hMp.le
  have hdm : 4 ≤ D * M := by nlinarith
  have hlogs := Real.log_le_self hMp.le
  have hlogd := Real.log_le_self hDp.le
  nlinarith
lemma centered_exponent_bound (D M B : ℝ) (hD : 1 ≤ D) (hM : 4 ≤ M)
    (hB : 0 < B) (hBM : B ≤ 129 * M) :
    B * (D * Real.log (128 * B * Real.sqrt D) + 1) ≤ 8772 * D ^ 2 * M ^ 2 := by
  have hDp : 0 ≤ D := by linarith
  have hMp : 0 ≤ M := by linarith
  have hl := common_log_bound D M B hD hM hB hBM
  have hmain : B * (D * Real.log (128 * B * Real.sqrt D) + 1) ≤
      (129 * M) * (D * (67 * D * M) + 1) := by
    calc
      _ ≤ B * (D * (67 * D * M) + 1) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right hBM (by positivity)
  have hprod : 1 ≤ D * M := by nlinarith
  have hm : M ≤ (D * M) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hD hMp
    have hh2 := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ D * M)
    nlinarith
  nlinarith
lemma good_exponent_bound (D M C : ℝ) (hD : 1 ≤ D) (hM : 4 ≤ M)
    (hC : 0 ≤ C) (hCM : C ≤ 64 * D * M) :
    D * Real.log (4 * Real.sqrt D) + C ^ 2 + 1 / 4 ≤ 4100 * D ^ 2 * M ^ 2 := by
  have hDp : 0 < D := by linarith
  have hMp : 0 ≤ M := by linarith
  rw [Real.log_mul (by norm_num) (Real.sqrt_pos.2 hDp).ne', Real.log_sqrt hDp.le]
  have hlog4 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 4)
  have hlogD := Real.log_le_self hDp.le
  have hl := mul_le_mul_of_nonneg_left (add_le_add hlog4
    (div_le_div_of_nonneg_right hlogD (by norm_num : (0 : ℝ) ≤ 2))) hDp.le
  have hc2 := sq_le_sq₀ hC (by positivity : 0 ≤ 64 * D * M) |>.2 hCM
  have hd2 : 1 ≤ D ^ 2 := by nlinarith
  have hm2 : 16 ≤ M ^ 2 := by nlinarith
  have hdm := mul_le_mul_of_nonneg_left hm2 (sq_nonneg D)
  nlinarith [sq_nonneg (D - 4)]
lemma good_probability_common (d : ℕ) (M C : ℝ) (hd : 1 ≤ (d : ℝ))
    (hM : 4 ≤ M) (hC : 0 ≤ C) (hCM : C ≤ 64 * (d : ℝ) * M) :
    Real.exp (-25000 * (d : ℝ) ^ 2 * M ^ 2) ≤
      (1 / (4 * Real.sqrt d)) ^ d * Real.exp (-C ^ 2 - 1 / 4) := by
  have he := good_exponent_bound d M C hd hM hC hCM
  have ha : 0 < 4 * Real.sqrt (d : ℝ) := by positivity
  have h := gaussian_power_exp_lower d 1 (4 * Real.sqrt d) (C ^ 2 + 1 / 4)
    (25000 * (d : ℝ) ^ 2 * M ^ 2) ha (by
      simp only [Nat.cast_one, one_mul]
      nlinarith [sq_nonneg ((d : ℝ) * M)])
  convert h using 1 <;> ring_nf
lemma centered_probability_common (d B : ℕ) (M ε : ℝ) (hd : 1 ≤ (d : ℝ))
    (hM : 4 ≤ M) (hB : 0 < (B : ℝ)) (hBM : (B : ℝ) ≤ 129 * M)
    (hε : 1 / (64 * (B : ℝ)) ≤ ε) (hε1 : ε ≤ 1) :
    Real.exp (-25000 * (d : ℝ) ^ 2 * M ^ 2) ≤
      ((ε / (2 * Real.sqrt d)) ^ d * Real.exp (-ε ^ 2)) ^ B := by
  have hdpos : 0 < (d : ℝ) := by linarith
  have hs : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdpos
  have he := centered_exponent_bound d M B hd hM hB hBM
  have ha : 0 < 128 * (B : ℝ) * Real.sqrt d := by positivity
  have h := gaussian_power_exp_lower d B (128 * (B : ℝ) * Real.sqrt d) 1
    (25000 * (d : ℝ) ^ 2 * M ^ 2) ha (by
      nlinarith [sq_nonneg ((d : ℝ) * M)])
  have hεpos : 0 < ε := lt_of_lt_of_le (by positivity) hε
  have hbase : 1 / (128 * (B : ℝ) * Real.sqrt d) ≤ ε / (2 * Real.sqrt d) := by
    calc
      _ = (1 / (64 * (B : ℝ))) / (2 * Real.sqrt d) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hε (by positivity)
  have hexp : Real.exp (-1) ≤ Real.exp (-ε ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  apply le_trans (by simpa only [neg_mul] using h)
  gcongr
lemma small_hinge_parameter_le (η R D : ℝ) (hη : 0 < η) (hR : 0 ≤ R)
    (hD : 1 ≤ D) (hsmall : η * R ≤ 1 / 16) :
    R + 4 * η * R ^ 2 ≤ Real.sqrt (48 * D) / η := by
  rw [le_div_iff₀ hη]
  have hs : 1 ≤ Real.sqrt (48 * D) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hsq : (η * R) ^ 2 ≤ (1 / 16 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by norm_num)).2 hsmall
  nlinarith
lemma hinge_center_mono (n R δ η κ H h : ℝ) (hn : 0 ≤ n) (hR : 0 < R)
    (hδ : 0 < δ) (hκ : 0 ≤ κ) (hκη : κ ≤ η) (hh : 0 ≤ h) (hhH : h ≤ H) :
    2 * κ * h + (n * h + 2 * R) / δ + h / R + 2 ≤
      2 * η * H + (n * H + 2 * R) / δ + H / R + 2 := by
  gcongr
  linarith
lemma normalized_center_bound (n κ D : ℝ) (hn : 1 ≤ n) (hκ : 1 ≤ κ) (hD : 1 ≤ D) :
    Real.sqrt (48 * D) * (2 + 8 * n * (n + 1) * κ ^ 2 + 8 * (n + 1) * κ) +
      2 * κ + 2 ≤ 64 * D * ((n + 1) ^ 2 * κ ^ 2) := by
  let M := (n + 1) ^ 2 * κ ^ 2
  have hn0 : 0 ≤ n + 1 := by linarith
  have hκ0 : 0 ≤ κ := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hκ2 : 1 ≤ κ ^ 2 := by nlinarith
  have hn2 : 4 ≤ (n + 1) ^ 2 := by nlinarith
  have hM : 4 ≤ M := by
    dsimp [M]
    nlinarith [mul_le_mul_of_nonneg_left hκ2 (sq_nonneg (n + 1))]
  have hlin : 2 * κ + 2 ≤ M := by
    have hm := mul_le_mul_of_nonneg_right hn2 (sq_nonneg κ)
    dsimp [M]
    nlinarith
  have hbracket : 2 + 8 * n * (n + 1) * κ ^ 2 + 8 * (n + 1) * κ ≤
      (17 / 2 : ℝ) * M := by
    have ht := mul_nonneg hn0 (show 0 ≤ κ ^ 2 - κ by nlinarith)
    dsimp [M] at *
    nlinarith
  have hs : Real.sqrt (48 * D) ≤ 7 * D := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hmul : Real.sqrt (48 * D) *
      (2 + 8 * n * (n + 1) * κ ^ 2 + 8 * (n + 1) * κ) ≤
      (7 * D) * ((17 / 2 : ℝ) * M) := by
    apply (mul_le_mul_of_nonneg_left hbracket (Real.sqrt_nonneg _)).trans
    exact mul_le_mul_of_nonneg_right hs (by positivity)
  have hDM := mul_le_mul_of_nonneg_right hD (show 0 ≤ M by linarith)
  change _ ≤ 64 * D * M
  nlinarith
lemma tuned_center_bound (n R δ η D : ℝ) (hn : 1 ≤ n) (hδ : 0 < δ)
    (hR : δ ≤ R) (hD : 1 ≤ D) (htune : η = δ / (8 * (n + 1) * R ^ 2)) :
    2 * η * (Real.sqrt (48 * D) / η) +
      (n * (Real.sqrt (48 * D) / η) + 2 * R) / δ +
      (Real.sqrt (48 * D) / η) / R + 2 ≤ 64 * D * ((n + 1) ^ 2 * (R / δ) ^ 2) := by
  have hRp : 0 < R := lt_of_lt_of_le hδ hR
  have hn1 : n + 1 ≠ 0 := by linarith
  have hκ : 1 ≤ R / δ := (le_div_iff₀ hδ).2 (by simpa using hR)
  have he : 2 * η * (Real.sqrt (48 * D) / η) +
      (n * (Real.sqrt (48 * D) / η) + 2 * R) / δ +
      (Real.sqrt (48 * D) / η) / R + 2 =
      Real.sqrt (48 * D) * (2 + 8 * n * (n + 1) * (R / δ) ^ 2 +
        8 * (n + 1) * (R / δ)) + 2 * (R / δ) + 2 := by
    rw [htune]
    field_simp
    ring
  rw [he]
  exact normalized_center_bound n (R / δ) D hn hκ hD
lemma tuned_block_length (n R δ η : ℝ) (hn : 1 ≤ n) (hδ : 0 < δ)
    (hR : δ ≤ R) (htune : η = δ / (8 * (n + 1) * R ^ 2)) :
    ((⌈16 * n / (η * δ)⌉₊ + 2 : ℕ) : ℝ) ≤ 129 * ((n + 1) ^ 2 * (R / δ) ^ 2) := by
  have hRp : 0 < R := lt_of_lt_of_le hδ hR
  have hnp : 0 < n + 1 := by linarith
  have hη : 0 < η := by rw [htune]; positivity
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 16 * n / (η * δ) by positivity)
  have he : 16 * n / (η * δ) = 128 * n * (n + 1) * (R / δ) ^ 2 := by
    rw [htune]
    field_simp
    ring
  rw [he] at hc
  have hk : 1 ≤ R / δ := (le_div_iff₀ hδ).2 (by simpa using hR)
  have hk2 : 1 ≤ (R / δ) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right (show 2 ≤ n + 1 by linarith) (sq_nonneg (R / δ))
  rw [he]
  push_cast
  nlinarith [mul_nonneg (show 0 ≤ n + 1 by linarith) (show 0 ≤ (R / δ) ^ 2 by positivity)]
lemma tuned_step_bounds (n R δ η : ℝ) (hn : 1 ≤ n) (hδ : 0 < δ)
    (hR : δ ≤ R) (htune : η = δ / (8 * (n + 1) * R ^ 2)) :
    0 < η ∧ η * R ≤ 1 / 16 ∧ 2 * η * R ^ 2 * (4 * n + 1) < δ := by
  have hRp : 0 < R := lt_of_lt_of_le hδ hR
  have hnp : 0 < n + 1 := by linarith
  have hη : 0 < η := by rw [htune]; positivity
  have ht : 8 * (n + 1) * η * R ^ 2 = δ := by
    rw [htune]
    field_simp
  refine ⟨hη, ?_, ?_⟩
  · have hnn := mul_nonneg (show 0 ≤ n - 1 by linarith)
      (show 0 ≤ η * R ^ 2 by positivity)
    have hh : 16 * η * R ^ 2 ≤ R := by nlinarith
    nlinarith
  · nlinarith [mul_pos hη (sq_pos_of_pos hRp)]
lemma tuned_escape_noise (n η δ : ℝ) (hn : 0 < n) (hη : 0 < η) (hδ : 0 < δ)
    (K : ℕ) (hK : K = ⌈16 * n / (η * δ)⌉₊) :
    16 * n ≤ (K : ℝ) * η * δ ∧
    ((K + 1 : ℕ) : ℝ) * (1 / (64 * ((K + 1 : ℕ) : ℝ))) ≤ 1 / 64 ∧
    1 / (64 * ((K + 1 : ℕ) : ℝ)) ≤ η * δ * n⁻¹ / 4 := by
  have hk : 16 * n / (η * δ) ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil _
  have hk' : 16 * n ≤ (K : ℝ) * η * δ := by
    have h := (div_le_iff₀ (mul_pos hη hδ)).1 hk
    nlinarith
  have hp : 0 < ((K + 1 : ℕ) : ℝ) := by positivity
  refine ⟨hk', ?_, ?_⟩
  · have he : ((K + 1 : ℕ) : ℝ) * (1 / (64 * ((K + 1 : ℕ) : ℝ))) = 1 / 64 := by
      field_simp
    exact he.le
  · rw [div_le_iff₀ (by positivity : 0 < 64 * ((K + 1 : ℕ) : ℝ))]
    apply (le_of_mul_le_mul_right ?_ hn)
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    nlinarith
lemma tuned_block_probability (d : ℕ) (n R δ η : ℝ) (hd : 1 ≤ (d : ℝ))
    (hn : 1 ≤ n) (hδ : 0 < δ) (hR : δ ≤ R)
    (htune : η = δ / (8 * (n + 1) * R ^ 2)) (K B : ℕ)
    (hK : K = ⌈16 * n / (η * δ)⌉₊) (hB : B = K + 2) :
    Real.exp (-25000 * (d : ℝ) ^ 2 * ((n + 1) ^ 2 * (R / δ) ^ 2) ^ 2) ≤
      (((1 / (64 * ((K + 1 : ℕ) : ℝ))) / (2 * Real.sqrt d)) ^ d *
        Real.exp (-(1 / (64 * ((K + 1 : ℕ) : ℝ))) ^ 2)) ^ B := by
  have hM : 4 ≤ (n + 1) ^ 2 * (R / δ) ^ 2 := by
    have hk : 1 ≤ R / δ := (le_div_iff₀ hδ).2 (by simpa using hR)
    have hn2 : 4 ≤ (n + 1) ^ 2 := by nlinarith
    have hk2 : 1 ≤ (R / δ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hk2 (sq_nonneg (n + 1))]
  apply centered_probability_common d B _ _ hd hM
  · rw [hB]; positivity
  · rw [hB, hK]
    exact tuned_block_length n R δ η hn hδ hR htune
  · rw [hB]
    gcongr
    omega
  · rw [div_le_iff₀ (by positivity : 0 < 64 * ((K + 1 : ℕ) : ℝ))]
    norm_num
    nlinarith [(show 0 ≤ (K : ℝ) by positivity)]
end LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialConstants
