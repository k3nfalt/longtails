import LongTails.Proofs.RecoveryFractalExecution
import LongTails.Proofs.FractalChebyshevWeighted
import LongTails.Proofs.FractalChebyshevParams

namespace LongTails.Proofs.RecoveryFractalSchedule

open OracleTemplate OracleTemplate.ScheduleBlock OracleTemplate.FractalChebyshev
open LongTails.Setups.SmoothHessianLipschitzGd
open LongTails.Algorithms.RecoveryFractalGd
open LongTails.Proofs.RecoveryFractalExecution
open LongTails.Proofs.FractalChebyshevWeighted

lemma step_eq (p : Params) {i : ℕ} (hi : i < blockLength p) :
    fractalStep p i = etaOf p.L (lowerCurvature p) (level p) i := by
  rw [etaOf_eq hi]
  simp only [fractalStep, Nat.mod_eq_of_lt hi]

lemma step_periodic (p : Params) (i : ℕ) :
    fractalStep p (i + blockLength p) = fractalStep p i := by
  simp [fractalStep]

lemma step_bounds (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p) (i : ℕ) :
    1 / p.L ≤ fractalStep p i ∧ fractalStep p i ≤ 1 / lowerCurvature p := by
  exact stepOf_bounds (lowerCurvature_pos p hL) (lowerCurvature_lt p hL hk) _

lemma window_eq (p : Params) (lam : ℝ) (s t : ℕ) (ht : t ≤ blockLength p) :
    win (fractalStep p) lam s t = win (etaOf p.L (lowerCurvature p) (level p)) lam s t := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [step_eq p (lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 ht)]

lemma base_prefix_bound (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p)
    {lam : ℝ} (h0 : 0 ≤ lam) (hl : lam ≤ p.L) {t : ℕ} (ht : t ≤ blockLength p) :
    |pr (fractalStep p) lam t| ≤ 1 := by
  unfold pr
  rw [window_eq p lam 0 t ht]
  exact prefix_bound (lowerCurvature_pos p hL) (lowerCurvature_lt p hL hk) (level p) h0 hl ht

lemma all_prefix_bound (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p)
    {lam : ℝ} (h0 : 0 ≤ lam) (hl : lam ≤ p.L) (t : ℕ) :
    |pr (fractalStep p) lam t| ≤ 1 := by
  exact periodic_prefix_bound _ _ _ (blockLength_pos p) (step_periodic p)
    (fun _ ht => base_prefix_bound p hL hk h0 hl ht) t

lemma all_weighted_window_bound (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p)
    {lam : ℝ} (h0 : 0 ≤ lam) (hl : lam ≤ p.L) {i t : ℕ} (hi : i < t) :
    fractalStep p i * |win (fractalStep p) lam (i + 1) t| ≤ 4 / lowerCurvature p := by
  apply periodic_weighted_window_bound _ _ _ _ (blockLength_pos p) (step_periodic p)
    (fun i => (fractalStep_pos p hL hk i).le)
    (fun _ ht => base_prefix_bound p hL hk h0 hl ht) ?_ t i hi
  intro j s hjs hs
  rw [window_eq p lam (j + 1) s hs, step_eq p (hjs.trans_le hs)]
  exact weighted_window_bound (lowerCurvature_pos p hL) (lowerCurvature_lt p hL hk)
    (level p) h0 hl hjs hs

lemma base_filter_bound (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p)
    {lam : ℝ} (hm : lowerCurvature p ≤ lam) (hl : lam ≤ p.L) :
    |pr (fractalStep p) lam (blockLength p)| ≤ 1 / 2 := by
  have hmu := lowerCurvature_pos p hL
  have hmuL := lowerCurvature_lt p hL hk
  have hx0 := x0_gt_one hmu hmuL
  have hx1 := (x_bounds hmuL (hmu.le.trans hm) hl).1
  have hx2 : (p.L + lowerCurvature p - 2 * lam) / (p.L - lowerCurvature p) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  unfold pr
  rw [window_eq p lam 0 (blockLength p) le_rfl]
  change |win (etaOf p.L (lowerCurvature p) (level p)) lam 0 (2 ^ level p)| ≤ 1 / 2
  rw [win_schedule hmu hmuL (level p) lam (Nat.zero_le _) le_rfl,
    List.drop_zero, Nat.sub_zero]
  rw [← angles_length (level p), List.take_length, prodF_angles (level p) hx0, abs_div]
  have hnum : |dbl^[level p] ((p.L + lowerCurvature p - 2 * lam) /
      (p.L - lowerCurvature p))| ≤ 1 := abs_le.mpr (abs_dbl_iterate_le _ hx1 hx2)
  have hpow : (4 : ℝ) ^ level p = (blockLength p : ℝ) ^ 2 := by
    simp only [blockLength, Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hn : (0 : ℝ) < blockLength p := by exact_mod_cast blockLength_pos p
  have hid : (blockLength p : ℝ) ^ 2 * lowerCurvature p = p.L := by
    unfold lowerCurvature
    field_simp
  have hden : 2 ≤ dbl^[level p] ((p.L + lowerCurvature p) / (p.L - lowerCurvature p)) := by
    have hg := dbl_iterate_ge hx0.le (level p)
    rw [hpow] at hg
    have he : (p.L + lowerCurvature p) / (p.L - lowerCurvature p) - 1 =
        2 * lowerCurvature p / (p.L - lowerCurvature p) := by
      field_simp [ne_of_gt (sub_pos.mpr hmuL)]
      ring
    rw [he, ← mul_div_assoc] at hg
    have hq : 1 ≤ (blockLength p : ℝ) ^ 2 * (2 * lowerCurvature p) /
        (p.L - lowerCurvature p) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [hid]
    linarith
  rw [abs_of_pos (by linarith : 0 < dbl^[level p]
    ((p.L + lowerCurvature p) / (p.L - lowerCurvature p)))]
  exact div_le_div₀ (by norm_num) hnum (by norm_num) hden

lemma repeated_prefix (p : Params) (lam : ℝ) (m : ℕ) :
    pr (fractalStep p) lam (blockLength p * m) =
      pr (fractalStep p) lam (blockLength p) ^ m := by
  induction m with
  | zero => simp [pr, win]
  | succ m ih =>
    have hn : blockLength p ≤ blockLength p * (m + 1) := by simp only [Nat.mul_succ]; omega
    have he := periodic_window_split (fractalStep p) lam (blockLength p)
      (step_periodic p) (Nat.zero_le _) hn
    change pr (fractalStep p) lam (blockLength p * (m + 1)) =
      pr (fractalStep p) lam (blockLength p) *
        pr (fractalStep p) lam (blockLength p * (m + 1) - blockLength p) at he
    rw [show blockLength p * (m + 1) - blockLength p = blockLength p * m by simp only [Nat.mul_succ]; omega,
      ih] at he
    simpa [pow_succ, mul_comm] using he

lemma epoch_filter_bound (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p)
    {lam : ℝ} (hm : lowerCurvature p ≤ lam) (hl : lam ≤ p.L) :
    |pr (fractalStep p) lam (epochLength p)| ≤ 1 / (256 * blockLength p) := by
  unfold epochLength
  rw [repeated_prefix, abs_pow]
  calc
    _ ≤ (1 / 2 : ℝ) ^ repetitions p :=
      pow_le_pow_left₀ (abs_nonneg _) (base_filter_bound p hL hk hm hl) _
    _ = 1 / (256 * blockLength p) := by
      simp only [repetitions, blockLength, Nat.cast_pow, Nat.cast_ofNat, div_pow,
        one_pow, pow_add]
      norm_num


lemma log_ratio_facts {n : ℝ} (hn : 1 < n) :
    0 < Real.log ((n + 1) / (n - 1)) ∧
    Real.cosh (Real.log ((n + 1) / (n - 1))) = (n ^ 2 + 1) / (n ^ 2 - 1) ∧
    Real.sinh (Real.log ((n + 1) / (n - 1))) = 2 * n / (n ^ 2 - 1) ∧
    1 ≤ n * Real.log ((n + 1) / (n - 1)) := by
  have hd : 0 < n - 1 := by linarith
  have hp : 0 < n + 1 := by linarith
  have hr : 1 < (n + 1) / (n - 1) := by rw [lt_div_iff₀ hd]; linarith
  have hs : n ^ 2 - 1 ≠ 0 := by nlinarith
  refine ⟨Real.log_pos hr, ?_, ?_, ?_⟩
  · rw [Real.cosh_log (by positivity)]
    field_simp
    ring
  · rw [Real.sinh_log (by positivity)]
    field_simp
    ring
  · have h := Real.one_sub_inv_le_log_of_pos (show 0 < (n + 1) / (n - 1) by positivity)
    have he : 1 - ((n + 1) / (n - 1))⁻¹ = 2 / (n + 1) := by
      field_simp
      ring
    rw [he] at h
    have hq : 1 ≤ n * (2 / (n + 1)) := by
      rw [← mul_div_assoc, le_div_iff₀ hp]
      linarith
    exact hq.trans (mul_le_mul_of_nonneg_left h (by linarith))

open OracleTemplate.FractalChebyshev OracleTemplate.ScheduleBlock Real

lemma base_sum_bounds {L : ℝ} (hL : 0 < L) (k : ℕ) (hk : 2 ≤ k) :
    1 / (2 * (L / ((2 : ℝ) ^ k) ^ 2)) ≤ ssum (etaOf L (L / ((2 : ℝ) ^ k) ^ 2) k) (2 ^ k) ∧
    ssum (etaOf L (L / ((2 : ℝ) ^ k) ^ 2) k) (2 ^ k) ≤ 1 / (L / ((2 : ℝ) ^ k) ^ 2) := by
  let n : ℝ := 2 ^ k
  let μ := L / n ^ 2
  let t := Real.log ((n + 1) / (n - 1))
  have hn4 : 4 ≤ n := by
    dsimp [n]
    have h : (2 : ℝ) ^ 2 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    norm_num at h ⊢
    exact h
  have hn : 0 < n := by linarith
  have hmu : 0 < μ := by dsimp [μ]; positivity
  have hmuL : μ < L := div_lt_self hL (by nlinarith)
  obtain ⟨ht, hc, hs, hnt⟩ := log_ratio_facts (show 1 < n by linarith)
  have hx : (L + μ) / (L - μ) = Real.cosh t := by
    rw [hc]
    dsimp [μ]
    field_simp
  have hcoeff : μ * (2 / (L - μ)) * n = Real.sinh t := by
    rw [hs]
    dsimp [μ]
    field_simp
  have hid : μ * ssum (etaOf L μ k) (2 ^ k) * Real.cosh (n * t) = Real.sinh (n * t) := by
    apply mul_left_cancel₀ hn.ne'
    calc
      n * (μ * ssum (etaOf L μ k) (2 ^ k) * Real.cosh (n * t)) =
          phiSum k (Real.cosh t) * Real.sinh t * Real.cosh (n * t) := by
        rw [ssum_etaOf hmu hmuL, hx, ← hcoeff]
        ring
      _ = n * Real.sinh (n * t) := phiSum_cosh k t ht
  have hp := Real.cosh_pos (n * t)
  have hlow := sinh_ge_half_cosh hnt
  have hhigh := Real.sinh_lt_cosh (n * t)
  have hb1 : 1 / 2 ≤ μ * ssum (etaOf L μ k) (2 ^ k) := by nlinarith
  have hb2 : μ * ssum (etaOf L μ k) (2 ^ k) ≤ 1 := by nlinarith
  change 1 / (2 * μ) ≤ _ ∧ _ ≤ 1 / μ
  constructor
  · rw [div_le_iff₀ (by positivity)]
    nlinarith
  · rw [le_div_iff₀ hmu]
    nlinarith
lemma repeated_sum (p : Params) (m : ℕ) :
    ssum (fractalStep p) (blockLength p * m) =
      m * ssum (fractalStep p) (blockLength p) := by
  induction m with
  | zero => simp [ssum]
  | succ m ih =>
    have he : blockLength p * (m + 1) = blockLength p + blockLength p * m := by simp only [Nat.mul_succ]; omega
    unfold ssum at *
    rw [he, Finset.sum_range_add]
    simp_rw [Nat.add_comm (blockLength p), step_periodic]
    rw [ih]
    push_cast
    ring

lemma actual_base_sum_bounds (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p) :
    1 / (2 * lowerCurvature p) ≤ ssum (fractalStep p) (blockLength p) ∧
    ssum (fractalStep p) (blockLength p) ≤ 1 / lowerCurvature p := by
  have he : ssum (fractalStep p) (blockLength p) =
      ssum (etaOf p.L (lowerCurvature p) (level p)) (blockLength p) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact step_eq p (Finset.mem_range.mp hi)
  rw [he]
  simpa only [lowerCurvature, blockLength, Nat.cast_pow, Nat.cast_ofNat]
    using base_sum_bounds hL (level p) hk

lemma epoch_sum_bounds (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p) :
    1 / (2 * lowerCurvature p) ≤ ssum (fractalStep p) (epochLength p) ∧
    ssum (fractalStep p) (epochLength p) ≤ repetitions p / lowerCurvature p := by
  obtain ⟨hlo, hhi⟩ := actual_base_sum_bounds p hL hk
  have hm : (1 : ℝ) ≤ repetitions p := by
    unfold repetitions
    push_cast
    have : (0 : ℝ) ≤ level p := Nat.cast_nonneg _
    linarith
  have hs : 0 ≤ ssum (fractalStep p) (blockLength p) :=
    (by have := lowerCurvature_pos p hL; positivity : 0 ≤ 1 / (2 * lowerCurvature p)).trans hlo
  unfold epochLength
  rw [repeated_sum]
  constructor
  · exact hlo.trans (by nlinarith)
  · simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hhi (by positivity : (0 : ℝ) ≤ repetitions p)

lemma epoch_periodic (p : Params) (i : ℕ) :
    fractalStep p (epochLength p + i) = fractalStep p i := by
  simp [fractalStep, epochLength, Nat.add_mod]

lemma two_epoch_filter (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p)
    {lam : ℝ} (hm : lowerCurvature p ≤ lam) (hl : lam ≤ p.L) :
    |pr (fractalStep p) lam (2 * epochLength p)| ≤ 1 / (256 * blockLength p) := by
  have he : pr (fractalStep p) lam (2 * epochLength p) =
      pr (fractalStep p) lam (epochLength p) ^ 2 := by
    unfold epochLength
    rw [show 2 * (blockLength p * repetitions p) = blockLength p * (repetitions p * 2) by ring]
    rw [repeated_prefix, repeated_prefix, pow_mul]
  rw [he, abs_pow]
  have hp := epoch_filter_bound p hL hk hm hl
  have hp1 := all_prefix_bound p hL hk ((lowerCurvature_pos p hL).le.trans hm) hl (epochLength p)
  nlinarith [abs_nonneg (pr (fractalStep p) lam (epochLength p))]

end LongTails.Proofs.RecoveryFractalSchedule
