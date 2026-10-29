import LongTails.Algorithms.GradientOnlyQuasar
import LongTails.Proofs.QuasarPowerBarrier

open Set
open scoped BigOperators

namespace OracleTemplate.GradientOnlyQuasar

open LongTails.Setups.GradientOnlyGeneralizedQuasar

lemma smoothRamp_of_nonpos {s : ℝ} (hs : s ≤ 0) : smoothRamp s = 0 := by
  simp only [smoothRamp, max_eq_left hs, max_eq_left (by linarith : s - 1 / 2 ≤ 0),
    max_eq_left (by linarith : s - 1 ≤ 0)]
  norm_num

lemma smoothRamp_of_one_le {s : ℝ} (hs : 1 ≤ s) : smoothRamp s = 1 := by
  simp only [smoothRamp, max_eq_right (by linarith : 0 ≤ s),
    max_eq_right (by linarith : 0 ≤ s - 1 / 2), max_eq_right (by linarith : 0 ≤ s - 1)]
  ring

lemma smoothRampSlope_of_nonpos {s : ℝ} (hs : s ≤ 0) : smoothRampSlope s = 0 := by
  simp only [smoothRampSlope, max_eq_left hs, max_eq_left (by linarith : s - 1 / 2 ≤ 0),
    max_eq_left (by linarith : s - 1 ≤ 0)]
  norm_num

lemma smoothRampSlope_of_one_le {s : ℝ} (hs : 1 ≤ s) : smoothRampSlope s = 0 := by
  simp only [smoothRampSlope, max_eq_right (by linarith : 0 ≤ s),
    max_eq_right (by linarith : 0 ≤ s - 1 / 2), max_eq_right (by linarith : 0 ≤ s - 1)]
  ring

lemma smoothRamp_bounds (s : ℝ) : 0 ≤ smoothRamp s ∧ smoothRamp s ≤ 1 := by
  by_cases h0 : s ≤ 0
  · rw [smoothRamp_of_nonpos h0]; norm_num
  by_cases h1 : 1 ≤ s
  · rw [smoothRamp_of_one_le h1]; norm_num
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s - 1 ≤ 0 := by linarith
  by_cases hh : s ≤ 1 / 2
  · simp only [smoothRamp, max_eq_right hs0, max_eq_left hs1,
      max_eq_left (by linarith : s - 1 / 2 ≤ 0)]
    constructor <;> nlinarith [sq_nonneg s]
  · simp only [smoothRamp, max_eq_right hs0, max_eq_left hs1,
      max_eq_right (by linarith : 0 ≤ s - 1 / 2)]
    constructor <;> nlinarith [sq_nonneg (1 - s)]

lemma smoothRampSlope_bounds (s : ℝ) :
    0 ≤ smoothRampSlope s ∧ smoothRampSlope s ≤ 2 := by
  by_cases h0 : s ≤ 0
  · rw [smoothRampSlope_of_nonpos h0]; norm_num
  by_cases h1 : 1 ≤ s
  · rw [smoothRampSlope_of_one_le h1]; norm_num
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s - 1 ≤ 0 := by linarith
  by_cases hh : s ≤ 1 / 2
  · simp only [smoothRampSlope, max_eq_right hs0, max_eq_left hs1,
      max_eq_left (by linarith : s - 1 / 2 ≤ 0)]
    constructor <;> linarith
  · simp only [smoothRampSlope, max_eq_right hs0, max_eq_left hs1,
      max_eq_right (by linarith : 0 ≤ s - 1 / 2)]
    constructor <;> linarith

lemma hasDerivAt_positivePart_square (s : ℝ) :
    HasDerivAt (fun t : ℝ => (max 0 t) ^ 2) (2 * max 0 s) s := by
  have hi : HasDerivAt (fun t : ℝ => 1 - t) (-1) s := by
    convert! (hasDerivAt_id s).const_sub (1 : ℝ) using 1
  have hh := ((hasDerivAt_barrier (1 - s)).comp s hi).const_sub (1 : ℝ)
  convert! hh using 1
  · ext t
    simp [barrier]
  · simp [barrierSlope]

lemma hasDerivAt_smoothRamp (s : ℝ) : HasDerivAt smoothRamp (smoothRampSlope s) s := by
  have h0 := hasDerivAt_positivePart_square s
  have h1 := (hasDerivAt_positivePart_square (s - 1 / 2)).comp s
    ((hasDerivAt_id s).sub_const (1 / 2))
  have h2 := (hasDerivAt_positivePart_square (s - 1)).comp s
    ((hasDerivAt_id s).sub_const 1)
  convert! ((h0.const_mul 2).sub (h1.const_mul 4)).add (h2.const_mul 2) using 1
  simp only [smoothRampSlope]
  ring

lemma continuous_smoothRamp : Continuous smoothRamp := by
  unfold smoothRamp
  fun_prop

lemma continuous_smoothRampSlope : Continuous smoothRampSlope := by
  unfold smoothRampSlope
  fun_prop

lemma momentOrder_pos (q : Params) : 0 < momentOrder q := by
  unfold momentOrder
  omega

lemma initialWeight_pos {q : Params} (hv : spec.valid q) : 0 < initialWeight q := by
  have hR := hv.2.2.1
  have hΔ := hv.2.2.2.1
  unfold initialWeight
  positivity

lemma energyLevel_pos {q : Params} (hv : spec.valid q) : 0 < energyLevel q := by
  have hR := hv.2.2.1
  unfold energyLevel
  positivity

lemma stageWeight_pos {q : Params} (hv : spec.valid q) (j : ℕ) : 0 < stageWeight q j := by
  have hi := initialWeight_pos hv
  unfold stageWeight
  positivity

lemma stageDuration_pos {q : Params} (hv : spec.valid q) (j : ℕ) :
    0 < stageDuration q j := by
  have hw := stageWeight_pos hv j
  have he := energyLevel_pos hv
  have hp := momentOrder_pos q
  have hγ := hv.2.2.2.2.1
  have hL0 := hv.1
  unfold stageDuration
  positivity

lemma stageStart_zero (q : Params) : stageStart q 0 = 0 := by simp [stageStart]

lemma stageStart_succ (q : Params) (j : ℕ) :
    stageStart q (j + 1) = stageStart q j + stageDuration q j := by
  simp [stageStart, Finset.sum_range_succ]

lemma stageStart_mono {q : Params} (hv : spec.valid q) : Monotone (stageStart q) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [stageStart_succ]
  exact le_add_of_nonneg_right (stageDuration_pos hv j).le

lemma stageStart_nonneg {q : Params} (hv : spec.valid q) (j : ℕ) : 0 ≤ stageStart q j := by
  simpa only [stageStart_zero] using stageStart_mono hv (Nat.zero_le j)

lemma sum_stageWeight (q : Params) (j : ℕ) :
    initialWeight q + ∑ i ∈ Finset.range j, stageWeight q i = stageWeight q j := by
  induction j with
  | zero => simp [stageWeight]
  | succ j ih =>
      rw [Finset.sum_range_succ, ← add_assoc, ih]
      simp only [stageWeight, pow_succ]
      ring

lemma weight_ge_initial {q : Params} (hv : spec.valid q) (t : ℝ) :
    initialWeight q ≤ weight q t := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (stageWeight_pos hv j).le
    (smoothRamp_bounds _).1)

lemma weight_pos {q : Params} (hv : spec.valid q) (t : ℝ) : 0 < weight q t :=
  (initialWeight_pos hv).trans_le (weight_ge_initial hv t)

lemma weight_of_nonpos {q : Params} (hv : spec.valid q) {t : ℝ} (ht : t ≤ 0) :
    weight q t = initialWeight q := by
  unfold weight
  have hh (j : ℕ) : smoothRamp ((t - stageStart q j) / stageDuration q j) = 0 := by
    apply smoothRamp_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg
      (by linarith [stageStart_nonneg hv j]) (stageDuration_pos hv j).le
  simp only [hh, mul_zero, Finset.sum_const_zero, add_zero]

lemma weight_after {q : Params} (hv : spec.valid q) {t : ℝ}
    (ht : stageStart q (stageCount q) ≤ t) : weight q t = stageWeight q (stageCount q) := by
  unfold weight
  rw [← sum_stageWeight q (stageCount q)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j + 1 ≤ stageCount q := Finset.mem_range.mp hj
  have ht' := (stageStart_mono hv hj').trans ht
  rw [stageStart_succ] at ht'
  rw [smoothRamp_of_one_le ((le_div_iff₀ (stageDuration_pos hv j)).2 (by linarith)), mul_one]

lemma mirrorStep_nonneg {q : Params} (hv : spec.valid q) (t : ℝ) : 0 ≤ mirrorStep q t := by
  unfold mirrorStep
  apply div_nonneg _ hv.2.2.2.2.1.le
  exact Finset.sum_nonneg (fun j _ => mul_nonneg
    (div_nonneg (stageWeight_pos hv j).le (stageDuration_pos hv j).le)
    (smoothRampSlope_bounds _).1)

lemma mirrorStep_after {q : Params} (hv : spec.valid q) {t : ℝ}
    (ht : stageStart q (stageCount q) ≤ t) : mirrorStep q t = 0 := by
  unfold mirrorStep
  have hh (j : ℕ) (hj : j ∈ Finset.range (stageCount q)) :
      stageWeight q j / stageDuration q j *
        smoothRampSlope ((t - stageStart q j) / stageDuration q j) = 0 := by
    have ht' := (stageStart_mono hv (show j + 1 ≤ stageCount q from Finset.mem_range.mp hj)).trans ht
    rw [stageStart_succ] at ht'
    rw [smoothRampSlope_of_one_le
      ((le_div_iff₀ (stageDuration_pos hv j)).2 (by linarith)), mul_zero]
  rw [Finset.sum_eq_zero hh, zero_div]

lemma continuous_weight (q : Params) : Continuous (weight q) := by
  unfold weight
  exact continuous_const.add (continuous_finsetSum _ (fun j _ =>
    continuous_const.mul (continuous_smoothRamp.comp
      ((continuous_id.sub continuous_const).div_const _))))

lemma continuous_mirrorStep (q : Params) : Continuous (mirrorStep q) := by
  unfold mirrorStep
  exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
    (continuous_smoothRampSlope.comp
      ((continuous_id.sub continuous_const).div_const _)))).div_const _

lemma hasDerivAt_weight {q : Params} (hv : spec.valid q) (t : ℝ) :
    HasDerivAt (weight q) (q.γ * mirrorStep q t) t := by
  have h (j : ℕ) : HasDerivAt
      (fun s => stageWeight q j * smoothRamp ((s - stageStart q j) / stageDuration q j))
      (stageWeight q j / stageDuration q j *
        smoothRampSlope ((t - stageStart q j) / stageDuration q j)) t := by
    have hd := ((hasDerivAt_smoothRamp ((t - stageStart q j) / stageDuration q j)).comp t
      (((hasDerivAt_id t).sub_const (stageStart q j)).div_const (stageDuration q j))).const_mul
        (stageWeight q j)
    convert! hd using 1
    ring
  have hh := (HasDerivAt.fun_sum (u := Finset.range (stageCount q)) (fun j _ => h j)).const_add
    (initialWeight q)
  convert! hh using 1
  simp only [mirrorStep]
  field_simp [ne_of_gt hv.2.2.2.2.1]

lemma ramp_finished {q : Params} (hv : spec.valid q) {t : ℝ} {i j : ℕ}
    (hij : i < j) (ht : stageStart q j ≤ t) :
    smoothRamp ((t - stageStart q i) / stageDuration q i) = 1 := by
  apply smoothRamp_of_one_le
  apply (le_div_iff₀ (stageDuration_pos hv i)).2
  have hh := (stageStart_mono hv (Nat.succ_le_of_lt hij)).trans ht
  rw [stageStart_succ] at hh
  linarith

lemma weight_ge_stage {q : Params} (hv : spec.valid q) {t : ℝ} {j : ℕ}
    (hj : j ≤ stageCount q) (ht : stageStart q j ≤ t) : stageWeight q j ≤ weight q t := by
  rw [← sum_stageWeight q j]
  unfold weight
  apply add_le_add le_rfl
  calc
    (∑ i ∈ Finset.range j, stageWeight q i) =
        ∑ i ∈ Finset.range j, stageWeight q i *
          smoothRamp ((t - stageStart q i) / stageDuration q i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ramp_finished hv (Finset.mem_range.mp hi) ht, mul_one]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
      (fun i _ _ => mul_nonneg (stageWeight_pos hv i).le (smoothRamp_bounds _).1)

lemma mirrorStep_on_stage {q : Params} (hv : spec.valid q) {t : ℝ} {j : ℕ}
    (hj : j < stageCount q) (ht0 : stageStart q j ≤ t)
    (ht1 : t ≤ stageStart q (j + 1)) :
    mirrorStep q t = stageWeight q j / stageDuration q j *
      smoothRampSlope ((t - stageStart q j) / stageDuration q j) / q.γ := by
  unfold mirrorStep
  congr 1
  apply Finset.sum_eq_single j
  · intro i _ hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · have hh := (stageStart_mono hv (Nat.succ_le_of_lt hij)).trans ht0
      rw [stageStart_succ] at hh
      rw [smoothRampSlope_of_one_le
        ((le_div_iff₀ (stageDuration_pos hv i)).2 (by linarith)), mul_zero]
    · have hh := ht1.trans (stageStart_mono hv (Nat.succ_le_of_lt hij))
      rw [smoothRampSlope_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hh) (stageDuration_pos hv i).le), mul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hj))

lemma mirrorStep_stage_bound {q : Params} (hv : spec.valid q) {t : ℝ} {j : ℕ}
    (hj : j < stageCount q) (ht0 : stageStart q j ≤ t)
    (ht1 : t ≤ stageStart q (j + 1)) :
    mirrorStep q t ≤ 2 * stageWeight q j / (q.γ * stageDuration q j) := by
  rw [mirrorStep_on_stage hv hj ht0 ht1]
  have hh := mul_le_mul_of_nonneg_left (smoothRampSlope_bounds
    ((t - stageStart q j) / stageDuration q j)).2
    (div_nonneg (stageWeight_pos hv j).le (stageDuration_pos hv j).le)
  have hs := div_le_div_of_nonneg_right hh hv.2.2.2.2.1.le
  convert hs using 1
  ring

lemma exists_active_stage {q : Params} {t : ℝ} {n : ℕ}
    (ht0 : 0 ≤ t) (ht1 : t < stageStart q n) :
    ∃ j < n, stageStart q j ≤ t ∧ t ≤ stageStart q (j + 1) := by
  induction n with
  | zero => simp only [stageStart_zero] at ht1; linarith
  | succ n ih =>
      by_cases hn : t < stageStart q n
      · obtain ⟨j, hj, hj0, hj1⟩ := ih hn
        exact ⟨j, by omega, hj0, hj1⟩
      · exact ⟨n, Nat.lt_succ_self n, le_of_not_gt hn, ht1.le⟩

lemma scalar_stage_tuning {A W L c a p : ℝ}
    (hW : 0 < W) (hWA : W ≤ A) (hL : 0 < L) (hc : 0 ≤ c)
    (ha : 0 ≤ a) (hp : 0 < p)
    (hstep : a * (128 * p * Real.sqrt (L * W + c)) ≤ W) :
    64 * p ^ 2 * (128 * (L + c / A)) * a ^ 2 ≤ A := by
  have hA : 0 < A := hW.trans_le hWA
  have hC : 0 < L * W + c := by positivity
  have hD : 0 < L * A + c := by positivity
  have hs := pow_le_pow_left₀ (show 0 ≤ a * (128 * p * Real.sqrt (L * W + c)) by positivity)
    hstep 2
  simp only [mul_pow] at hs
  rw [Real.sq_sqrt hC.le] at hs
  have hm : W ^ 2 * (L * A + c) ≤ A ^ 2 * (L * W + c) := by
    have hh := mul_nonneg (sub_nonneg.mpr hWA)
      (show 0 ≤ L * A * W + c * (A + W) by positivity)
    nlinarith
  have hscale := mul_le_mul_of_nonneg_right hs hD.le
  have hb : 8192 * p ^ 2 * a ^ 2 * (L * A + c) ≤ A ^ 2 := by
    apply (mul_le_mul_iff_left₀ hC).mp
    nlinarith [mul_nonneg (show 0 ≤ p ^ 2 * a ^ 2 * (L * A + c) by positivity) hC.le]
  apply (mul_le_mul_iff_left₀ hA).mp
  have he : 64 * p ^ 2 * (128 * (L + c / A)) * a ^ 2 * A =
      8192 * p ^ 2 * a ^ 2 * (L * A + c) := by field_simp; ring
  rw [he]
  nlinarith

lemma mirrorStep_tuning {q : Params} (hv : spec.valid q) {t : ℝ} (ht : 0 ≤ t) :
    64 * (momentOrder q : ℝ) ^ 2 * curvature q t * mirrorStep q t ^ 2 ≤ weight q t := by
  by_cases hf : stageStart q (stageCount q) ≤ t
  · rw [mirrorStep_after hv hf]
    simpa using (weight_pos hv t).le
  · obtain ⟨j, hj, ht0, ht1⟩ := exists_active_stage ht (lt_of_not_ge hf)
    have hb := mirrorStep_stage_bound hv hj ht0 ht1
    have hγ := hv.2.2.2.2.1
    have hp : (0 : ℝ) < momentOrder q := by exact_mod_cast momentOrder_pos q
    have hC : 0 < q.L0 * stageWeight q j + q.L1 ^ 2 * energyLevel q := by
      have hW := stageWeight_pos hv j
      have hE := energyLevel_pos hv
      have hL := hv.1
      positivity
    have he : 2 * stageWeight q j / (q.γ * stageDuration q j) =
        stageWeight q j /
          (128 * (momentOrder q : ℝ) * Real.sqrt (q.L0 * stageWeight q j + q.L1 ^ 2 * energyLevel q)) := by
      unfold stageDuration
      field_simp
      ring
    rw [he] at hb
    have hstep := (le_div_iff₀ (show 0 < 128 * (momentOrder q : ℝ) *
      Real.sqrt (q.L0 * stageWeight q j + q.L1 ^ 2 * energyLevel q) by positivity)).mp hb
    unfold curvature
    exact scalar_stage_tuning (stageWeight_pos hv j) (weight_ge_stage hv hj.le ht0) hv.1
      (mul_nonneg (sq_nonneg q.L1) (energyLevel_pos hv).le) (mirrorStep_nonneg hv t) hp hstep

lemma curvature_pos {q : Params} (hv : spec.valid q) (t : ℝ) : 0 < curvature q t := by
  have hw := weight_pos hv t
  have hE := energyLevel_pos hv
  have hL := hv.1
  unfold curvature
  positivity

lemma continuous_curvature {q : Params} (hv : spec.valid q) : Continuous (curvature q) := by
  unfold curvature
  exact continuous_const.mul (continuous_const.add
    (continuous_const.div (continuous_weight q) (fun t => ne_of_gt (weight_pos hv t))))

lemma mirrorStep_of_nonpos {q : Params} (hv : spec.valid q) {t : ℝ} (ht : t ≤ 0) :
    mirrorStep q t = 0 := by
  unfold mirrorStep
  have hh (j : ℕ) : smoothRampSlope ((t - stageStart q j) / stageDuration q j) = 0 := by
    apply smoothRampSlope_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg
      (by linarith [stageStart_nonneg hv j]) (stageDuration_pos hv j).le
  simp only [hh, mul_zero, Finset.sum_const_zero, zero_div]

lemma mirrorStep_tuning_all {q : Params} (hv : spec.valid q) (t : ℝ) :
    64 * (momentOrder q : ℝ) ^ 2 * curvature q t * mirrorStep q t ^ 2 ≤ weight q t := by
  by_cases ht : 0 ≤ t
  · exact mirrorStep_tuning hv ht
  · rw [mirrorStep_of_nonpos hv (le_of_not_ge ht)]
    simpa using (weight_pos hv t).le

end OracleTemplate.GradientOnlyQuasar
