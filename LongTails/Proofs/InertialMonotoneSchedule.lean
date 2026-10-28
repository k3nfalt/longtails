import LongTails.Algorithms.InertialRegularizedExtragradient
import Mathlib.NumberTheory.Harmonic.Bounds

namespace OracleTemplate.InertialMonotone

lemma horizon_lower (L R ε : ℝ) :
    (4096 : ℝ) + 2048 * L * R / ε ≤ horizon L R ε :=
  Nat.le_ceil _

lemma horizon_large {L R ε : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) :
    4096 ≤ horizon L R ε := by
  have hh := horizon_lower L R ε
  have hn : 0 ≤ 2048 * L * R / ε := by positivity
  exact_mod_cast (show (4096 : ℝ) ≤ horizon L R ε by linarith)

lemma scale_bounds {N k : ℕ} (hk : k < N) :
    129 ≤ remainingScale N k ∧ remainingScale N k ≤ N + 128 := by
  unfold remainingScale
  have hh : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k]

lemma scale_succ (N k : ℕ) : remainingScale N (k + 1) = remainingScale N k - 1 := by
  simp only [remainingScale, Nat.cast_add, Nat.cast_one]
  ring

lemma growth_formula {N k : ℕ} (hk : k < N) :
    growth N k = (4 * remainingScale N k - 2) / (remainingScale N k - 1) ^ 2 := by
  have ht := (scale_bounds hk).1
  have hd : remainingScale N k - 1 ≠ 0 := by linarith
  unfold growth
  field_simp
  ring

lemma growth_bounds {N k : ℕ} (hk : k < N) :
    0 < growth N k ∧ growth N k ≤ 5 / (remainingScale N k - 1) ∧ growth N k ≤ 1 / 16 := by
  have ht := (scale_bounds hk).1
  have hd : 0 < remainingScale N k - 1 := by linarith
  rw [growth_formula hk]
  have hu : (4 * remainingScale N k - 2) / (remainingScale N k - 1) ^ 2 ≤
      5 / (remainingScale N k - 1) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) hd).mpr
    nlinarith
  refine ⟨div_pos (by linarith) (sq_pos_of_pos hd), hu, ?_⟩
  apply hu.trans
  apply (div_le_iff₀ hd).mpr
  linarith

lemma regularization_pos {L : ℝ} (hL : 0 < L) {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) :
    0 < regularization L N k := by
  have ht : 0 < remainingScale N k := by
    have hh : (k : ℝ) ≤ N := by exact_mod_cast hk
    unfold remainingScale
    linarith
  unfold regularization
  positivity

lemma regularization_update (L : ℝ) {N k : ℕ} (hk : k < N) :
    regularization L N (k + 1) = regularization L N k * (1 + growth N k / 2) := by
  have ht := (scale_bounds hk).1
  have h0 : remainingScale N k ≠ 0 := by linarith
  have h1 : remainingScale N k - 1 ≠ 0 := by linarith
  unfold regularization growth
  rw [scale_succ]
  field_simp
  ring

lemma batchSize_pos (σ ε : ℝ) (N k : ℕ) : 0 < batchSize σ ε N k :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

lemma stepSize_pos {L : ℝ} (hL : 0 < L) {N k : ℕ} (hk : k < N) :
    0 < stepSize L N k := by
  unfold stepSize
  exact div_pos (mul_pos (by norm_num) (growth_bounds hk).1)
    (regularization_pos hL (by omega) hk.le)

lemma stepSize_mul_regularization {L : ℝ} (hL : 0 < L) {N k : ℕ} (hk : k < N) :
    stepSize L N k * regularization L N k = 2 * growth N k := by
  unfold stepSize
  exact div_mul_cancel₀ _ (ne_of_gt (regularization_pos hL (by omega) hk.le))

lemma stepSize_mul_L {L : ℝ} (hL : 0 < L) {N k : ℕ} (hk : k < N) :
    stepSize L N k * L = growth N k * remainingScale N k ^ 2 / (64 * N) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have ht := (scale_bounds hk).1
  have ht0 : remainingScale N k ≠ 0 := by linarith
  unfold stepSize regularization
  field_simp
  ring

lemma stepSize_L_bound {L : ℝ} (hL : 0 < L) {N k : ℕ} (hN : 4096 ≤ N) (hk : k < N) :
    stepSize L N k * L ≤ 1 / 4 := by
  have ht := scale_bounds hk
  have hr := growth_bounds hk
  have hNr : (4096 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : 0 < remainingScale N k - 1 := by linarith
  have hp := (le_div_iff₀ hd).mp hr.2.1
  have hs : remainingScale N k ^ 2 ≤
      2 * remainingScale N k * (remainingScale N k - 1) := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hs hr.1.le
  have h2 := mul_le_mul_of_nonneg_right hp (show 0 ≤ 2 * remainingScale N k by linarith)
  rw [stepSize_mul_L hL hk]
  apply (div_le_iff₀ (show 0 < (64 : ℝ) * N by positivity)).mpr
  nlinarith

lemma schedule_cap {L : ℝ} (hL : 0 < L) {N k : ℕ} (hN : 4096 ≤ N) (hk : k < N) :
    2 * stepSize L N k * regularization L N k +
      2 * (stepSize L N k) ^ 2 * (L + regularization L N k) ^ 2 ≤ 1 := by
  have hη := stepSize_pos hL hk
  have hμ := regularization_pos hL (by omega : 0 < N) hk.le
  have hLη := stepSize_L_bound hL hN hk
  have he := stepSize_mul_regularization hL hk
  have hr := (growth_bounds hk).2.2
  have hb : stepSize L N k * (L + regularization L N k) ≤ 3 / 8 := by nlinarith
  have hs := pow_le_pow_left₀ (show 0 ≤ stepSize L N k * (L + regularization L N k) by positivity) hb 2
  nlinarith

lemma regularization_terminal (L : ℝ) (N : ℕ) : regularization L N N = L * N / 128 := by
  unfold regularization remainingScale
  have he : (N : ℝ) + 128 - N = 128 := by ring
  rw [he]
  ring

lemma regularization_terminal_ge {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 4096 ≤ N) :
    L ≤ regularization L N N := by
  rw [regularization_terminal]
  have hn : (4096 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

lemma regularization_initial_le {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 0 < N) :
    regularization L N 0 ≤ 128 * L / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold regularization remainingScale
  simp only [Nat.cast_zero, sub_zero]
  apply (div_le_div_iff₀ (by positivity) hn).mpr
  nlinarith [mul_nonneg hL hn.le]

lemma harmonic_scale_bound {N : ℕ} (hN : 0 < N) :
    (∑ k ∈ Finset.range N, 1 / (remainingScale N k - 1)) ≤ 1 + Real.log ((N : ℝ) + 128) := by
  calc
    _ = ∑ k ∈ Finset.range N, 1 / (((N - 1 - k : ℕ) : ℝ) + 128) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      rw [Nat.cast_sub (by omega : k ≤ N - 1), Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
      unfold remainingScale
      congr 1
      ring
    _ = ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 128) := Finset.sum_range_reflect (fun k : ℕ => 1 / ((k : ℝ) + 128)) N
    _ ≤ ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro k _
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    _ = (harmonic N : ℝ) := by
      rw [harmonic]
      push_cast
      simp only [one_div]
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N
    _ ≤ 1 + Real.log ((N : ℝ) + 128) := by
      apply add_le_add_right
      apply Real.log_le_log (by exact_mod_cast hN)
      linarith

lemma log_scale_pos (N : ℕ) : 0 < 1 + Real.log ((N : ℝ) + 128) := by
  have hh : (1 : ℝ) ≤ N + 128 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hl := Real.log_nonneg hh
  linarith

lemma batch_variance_bound (σ : ℝ) {ε : ℝ} (hε : 0 < ε) {N k : ℕ} (hk : k < N) :
    σ ^ 2 / batchSize σ ε N k ≤
      ε ^ 2 * (remainingScale N k - 1) / (4096 * (1 + Real.log ((N : ℝ) + 128))) := by
  have ht := (scale_bounds hk).1
  have hH := log_scale_pos N
  have hd : 0 < remainingScale N k - 1 := by linarith
  have hb : (0 : ℝ) < batchSize σ ε N k := by exact_mod_cast batchSize_pos σ ε N k
  have hceil := Nat.le_ceil (4096 * σ ^ 2 * (1 + Real.log ((N : ℝ) + 128)) /
    (ε ^ 2 * (remainingScale N k - 1)))
  have hmax : (⌈4096 * σ ^ 2 * (1 + Real.log ((N : ℝ) + 128)) /
    (ε ^ 2 * (remainingScale N k - 1))⌉₊ : ℝ) ≤ batchSize σ ε N k := by
    simp only [batchSize]
    exact_mod_cast (le_max_right 1 _)
  have hh := hceil.trans hmax
  have he := (div_le_iff₀ (show 0 < ε ^ 2 * (remainingScale N k - 1) by positivity)).mp hh
  apply (div_le_div_iff₀ hb (show 0 < 4096 * (1 + Real.log ((N : ℝ) + 128)) by positivity)).mpr
  nlinarith

lemma noise_step_bound (σ : ℝ) {ε : ℝ} (hε : 0 < ε) {N k : ℕ} (hk : k < N) :
    (growth N k) ^ 2 * (σ ^ 2 / batchSize σ ε N k) ≤
      (25 * ε ^ 2 / (4096 * (1 + Real.log ((N : ℝ) + 128)))) * (1 / (remainingScale N k - 1)) := by
  have ht := (scale_bounds hk).1
  have hH := log_scale_pos N
  have hr := growth_bounds hk
  have hs := pow_le_pow_left₀ hr.1.le hr.2.1 2
  have hv := batch_variance_bound σ hε hk
  calc
    _ ≤ (5 / (remainingScale N k - 1)) ^ 2 *
        (ε ^ 2 * (remainingScale N k - 1) / (4096 * (1 + Real.log ((N : ℝ) + 128)))) :=
      mul_le_mul hs hv (by positivity) (by positivity)
    _ = _ := by
      have hd : remainingScale N k - 1 ≠ 0 := by linarith
      field_simp
      ring

lemma noise_sum_bound (σ : ℝ) {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 0 < N) :
    (∑ k ∈ Finset.range N, (growth N k) ^ 2 * (σ ^ 2 / batchSize σ ε N k)) ≤ 25 * ε ^ 2 / 4096 := by
  have hH := log_scale_pos N
  have hh := Finset.sum_le_sum (s := Finset.range N) (fun k hk => noise_step_bound σ hε (Finset.mem_range.mp hk))
  rw [← Finset.mul_sum] at hh
  have hs := mul_le_mul_of_nonneg_left (harmonic_scale_bound hN)
    (show 0 ≤ 25 * ε ^ 2 / (4096 * (1 + Real.log ((N : ℝ) + 128))) by positivity)
  have he : (25 * ε ^ 2 / (4096 * (1 + Real.log ((N : ℝ) + 128)))) *
      (1 + Real.log ((N : ℝ) + 128)) = 25 * ε ^ 2 / 4096 := by field_simp
  rw [he] at hs
  exact hh.trans hs

lemma calls_sum (b : ℕ → ℕ) (N : ℕ) :
    (calls b N : ℝ) = 2 * ∑ k ∈ Finset.range N, (b k : ℝ) := by
  induction N with
  | zero => simp [calls]
  | succ N ih =>
    simp only [calls, Nat.cast_add, ih, Finset.sum_range_succ]
    ring

lemma batchSize_upper (σ : ℝ) {ε : ℝ} (hε : 0 < ε) {N k : ℕ} (hk : k < N) :
    (batchSize σ ε N k : ℝ) ≤ 1 +
      (4096 * σ ^ 2 * (1 + Real.log ((N : ℝ) + 128)) / ε ^ 2) *
        (1 / (remainingScale N k - 1)) := by
  have ht := (scale_bounds hk).1
  have hd : 0 < remainingScale N k - 1 := by linarith
  have hH := log_scale_pos N
  have hA : 0 ≤ 4096 * σ ^ 2 * (1 + Real.log ((N : ℝ) + 128)) /
      (ε ^ 2 * (remainingScale N k - 1)) := by positivity
  have he : (4096 * σ ^ 2 * (1 + Real.log ((N : ℝ) + 128)) / ε ^ 2) *
      (1 / (remainingScale N k - 1)) =
      4096 * σ ^ 2 * (1 + Real.log ((N : ℝ) + 128)) /
        (ε ^ 2 * (remainingScale N k - 1)) := by field_simp
  rw [he]
  simp only [batchSize, Nat.cast_max, Nat.cast_one]
  apply max_le
  · linarith
  · linarith [Nat.ceil_lt_add_one hA]

lemma calls_bound (σ : ℝ) {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : 0 < N) :
    (calls (batchSize σ ε N) N : ℝ) ≤
      2 * N + 8192 * σ ^ 2 * (1 + Real.log ((N : ℝ) + 128)) ^ 2 / ε ^ 2 := by
  have hH := log_scale_pos N
  have hh := Finset.sum_le_sum (s := Finset.range N)
    (fun k hk => batchSize_upper σ hε (Finset.mem_range.mp hk))
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, ← Finset.mul_sum] at hh
  have hs := mul_le_mul_of_nonneg_left (harmonic_scale_bound hN)
    (show 0 ≤ 4096 * σ ^ 2 * (1 + Real.log ((N : ℝ) + 128)) / ε ^ 2 by positivity)
  rw [calls_sum]
  have he : 2 * ((4096 * σ ^ 2 * (1 + Real.log ((N : ℝ) + 128)) / ε ^ 2) *
      (1 + Real.log ((N : ℝ) + 128))) =
      8192 * σ ^ 2 * (1 + Real.log ((N : ℝ) + 128)) ^ 2 / ε ^ 2 := by ring
  linarith

lemma horizon_upper {L R ε : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) :
    (horizon L R ε : ℝ) ≤ 4097 + 2048 * L * R / ε := by
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 4096 + 2048 * L * R / ε by positivity)
  change (horizon L R ε : ℝ) < _ at hh
  linarith

lemma log_horizon_bound {L R ε : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) :
    1 + Real.log ((horizon L R ε : ℝ) + 128) ≤ 16 * Real.log (2 + L * R / ε) := by
  have hκ : 0 ≤ L * R / ε := by positivity
  have hN := horizon_upper hL hR hε
  rw [show 2048 * L * R / ε = 2048 * (L * R / ε) by ring] at hN
  have hsize : (horizon L R ε : ℝ) + 128 ≤ 2 ^ 13 * (2 + L * R / ε) := by
    norm_num
    nlinarith
  have hl := Real.log_le_log (show 0 < (horizon L R ε : ℝ) + 128 by positivity) hsize
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hl
  have h2 : Real.log 2 ≤ Real.log (2 + L * R / ε) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hhalf := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hhalf hl
  linarith

lemma calls_public_bound {L R σ ε : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) :
    calls (batchSize σ ε (horizon L R ε)) (horizon L R ε) ≤
      ⌈2 ^ 22 * (1 + L * R / ε + (σ / ε) ^ 2 * (Real.log (2 + L * R / ε)) ^ 2)⌉₊ := by
  have hN := horizon_large hL hR hε
  have hc := calls_bound σ hε (show 0 < horizon L R ε by omega)
  have hn := horizon_upper hL hR hε
  rw [show 2048 * L * R / ε = 2048 * (L * R / ε) by ring] at hn
  have hl := log_horizon_bound hL hR hε
  have hH := log_scale_pos (horizon L R ε)
  have hsq := pow_le_pow_left₀ hH.le hl 2
  have hnoise := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 8192 * σ ^ 2 / ε ^ 2 by positivity)
  have hκ : 0 ≤ L * R / ε := by positivity
  have hv : 0 ≤ (σ / ε) ^ 2 * (Real.log (2 + L * R / ε)) ^ 2 := by positivity
  have he : (8192 * σ ^ 2 / ε ^ 2) * (16 * Real.log (2 + L * R / ε)) ^ 2 =
      2097152 * ((σ / ε) ^ 2 * (Real.log (2 + L * R / ε)) ^ 2) := by ring
  rw [he] at hnoise
  have he' : (8192 * σ ^ 2 / ε ^ 2) * (1 + Real.log ((horizon L R ε : ℝ) + 128)) ^ 2 =
      8192 * σ ^ 2 * (1 + Real.log ((horizon L R ε : ℝ) + 128)) ^ 2 / ε ^ 2 := by ring
  rw [he'] at hnoise
  have hb : (calls (batchSize σ ε (horizon L R ε)) (horizon L R ε) : ℝ) ≤
      2 ^ 22 * (1 + L * R / ε + (σ / ε) ^ 2 * (Real.log (2 + L * R / ε)) ^ 2) := by
    norm_num
    nlinarith
  exact_mod_cast hb.trans (Nat.le_ceil _)

lemma initial_scale_accuracy {L R ε : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) :
    regularization L (horizon L R ε) 0 * R ≤ ε / 16 := by
  have hN := horizon_large hL hR hε
  have hn : (0 : ℝ) < horizon L R ε := by exact_mod_cast (show 0 < horizon L R ε by omega)
  have hμ := mul_le_mul_of_nonneg_right
    (regularization_initial_le hL (show 0 < horizon L R ε by omega)) hR
  have hk : 2048 * L * R / ε ≤ (horizon L R ε : ℝ) := by linarith [horizon_lower L R ε]
  have hs := (div_le_iff₀ hε).mp hk
  have he : (128 * L / (horizon L R ε : ℝ)) * R = 128 * L * R / horizon L R ε := by ring
  rw [he] at hμ
  apply hμ.trans
  apply (div_le_iff₀ hn).mpr
  nlinarith

lemma schedule_accuracy {L R σ ε : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) :
    4 * (regularization L (horizon L R ε) 0) ^ 2 * R ^ 2 +
      28 * (∑ k ∈ Finset.range (horizon L R ε), (growth (horizon L R ε) k) ^ 2 *
        (σ ^ 2 / batchSize σ ε (horizon L R ε) k)) ≤ ε ^ 2 := by
  have hN := horizon_large hL hR hε
  have hi := initial_scale_accuracy hL hR hε
  have hn : 0 ≤ regularization L (horizon L R ε) 0 * R := by
    unfold regularization
    positivity
  have his := pow_le_pow_left₀ hn hi 2
  have hs := noise_sum_bound σ hε (show 0 < horizon L R ε by omega)
  nlinarith [sq_nonneg ε]

end OracleTemplate.InertialMonotone
