import LongTails.Proofs.CountdownMarkov
import LongTails.Proofs.MixingProfiles
import Mathlib.Analysis.MeanInequalitiesPow

namespace OracleTemplate.CountdownMarkov

def averageStep (H : ℕ) (p : ℝ) (f : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then (1 - p) * f 0 + p * f H else f (i - 1)

def averageRun (H : ℕ) (p : ℝ) (f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => f
  | n + 1 => averageStep H p (averageRun H p f n)

lemma averageStep_bounds (H : ℕ) {p a b : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f : ℕ → ℝ} (hf : ∀ i ≤ H, a ≤ f i ∧ f i ≤ b) (i : ℕ) (hi : i ≤ H) :
    a ≤ averageStep H p f i ∧ averageStep H p f i ≤ b := by
  unfold averageStep
  split_ifs with hz
  · have h0 := hf 0 (Nat.zero_le H)
    have hH := hf H le_rfl
    have hq : 0 ≤ 1 - p := by linarith
    constructor
    · nlinarith [mul_nonneg hq (sub_nonneg.mpr h0.1), mul_nonneg hp (sub_nonneg.mpr hH.1)]
    · nlinarith [mul_nonneg hq (sub_nonneg.mpr h0.2), mul_nonneg hp (sub_nonneg.mpr hH.2)]
  · exact hf (i - 1) (by omega)

lemma averageRun_bounds (H : ℕ) {p a b : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f : ℕ → ℝ} (hf : ∀ i ≤ H, a ≤ f i ∧ f i ≤ b) (n i : ℕ) (hi : i ≤ H) :
    a ≤ averageRun H p f n i ∧ averageRun H p f n i ≤ b := by
  induction n generalizing i with
  | zero => exact hf i hi
  | succ n ih => exact averageStep_bounds H hp hp1 ih i hi

lemma averageRun_add (H : ℕ) (p : ℝ) (f : ℕ → ℝ) (m n : ℕ) :
    averageRun H p f (m + n) = averageRun H p (averageRun H p f n) m := by
  induction m with
  | zero => simp [averageRun]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [averageRun, ih]

lemma averageRun_no_jump_bounds (H : ℕ) {p a b : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f : ℕ → ℝ} (hf : ∀ i ≤ H, a ≤ f i ∧ f i ≤ b) (n i : ℕ) (hi : i ≤ H) :
    (1 - p) ^ n * f (i - n) + (1 - (1 - p) ^ n) * a ≤ averageRun H p f n i ∧
    averageRun H p f n i ≤ (1 - p) ^ n * f (i - n) + (1 - (1 - p) ^ n) * b := by
  have hq : 0 ≤ 1 - p := by linarith
  induction n generalizing i with
  | zero => simp [averageRun]
  | succ n ih =>
    have hc : 0 ≤ (1 - p) ^ n := pow_nonneg hq n
    rw [averageRun, averageStep]
    split_ifs with hz
    · subst i
      have h0 := ih 0 (Nat.zero_le H)
      have hH := averageRun_bounds H hp hp1 hf n H le_rfl
      simp only [Nat.zero_sub] at h0 ⊢
      rw [pow_succ]
      constructor
      · nlinarith [mul_nonneg hq (sub_nonneg.mpr h0.1), mul_nonneg hp (sub_nonneg.mpr hH.1)]
      · nlinarith [mul_nonneg hq (sub_nonneg.mpr h0.2), mul_nonneg hp (sub_nonneg.mpr hH.2)]
    · have hn := ih (i - 1) (by omega)
      have hb := hf (i - (n + 1)) (by omega)
      have he : i - 1 - n = i - (n + 1) := by omega
      rw [he] at hn
      rw [pow_succ]
      constructor
      · nlinarith only [hn.1, mul_nonneg (mul_nonneg hp hc) (sub_nonneg.mpr hb.1)]
      · nlinarith only [hn.2, mul_nonneg (mul_nonneg hp hc) (sub_nonneg.mpr hb.2)]

lemma averageRun_block_bounds (H : ℕ) {p a b : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f : ℕ → ℝ} (hf : ∀ i ≤ H, a ≤ f i ∧ f i ≤ b) (i : ℕ) (hi : i ≤ H) :
    (1 - p) ^ H * f 0 + (1 - (1 - p) ^ H) * a ≤ averageRun H p f H i ∧
    averageRun H p f H i ≤ (1 - p) ^ H * f 0 + (1 - (1 - p) ^ H) * b := by
  simpa only [Nat.sub_eq_zero_of_le hi] using averageRun_no_jump_bounds H hp hp1 hf H i hi

lemma block_failure_bounds (H : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ 1 - (1 - p) ^ H ∧ 1 - (1 - p) ^ H ≤ H * p := by
  constructor
  · exact sub_nonneg.mpr (pow_le_one₀ (by linarith) (by linarith))
  · have h := one_add_mul_le_pow (a := -p) (by linarith : -2 ≤ -p) H
    simp only [mul_neg, ← sub_eq_add_neg] at h
    linarith

lemma averageRun_range_blocks (H : ℕ) {p a b : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f : ℕ → ℝ} (hf : ∀ i ≤ H, a ≤ f i ∧ f i ≤ b) (n : ℕ) :
    ∃ l u : ℝ, (∀ i ≤ H, l ≤ averageRun H p f (n * H) i ∧
      averageRun H p f (n * H) i ≤ u) ∧ u - l ≤ (H * p) ^ n * (b - a) := by
  induction n with
  | zero =>
    refine ⟨a, b, ?_, ?_⟩
    · simpa only [Nat.zero_mul, averageRun] using hf
    · simp
  | succ n ih =>
    obtain ⟨l, u, hb, hw⟩ := ih
    let c := (1 - p) ^ H
    let f0 := averageRun H p f (n * H) 0
    refine ⟨c * f0 + (1 - c) * l, c * f0 + (1 - c) * u, ?_, ?_⟩
    · intro i hi
      rw [Nat.succ_mul, Nat.add_comm, averageRun_add]
      exact averageRun_block_bounds H hp hp1 hb i hi
    · have hlu : 0 ≤ u - l := by have h := hb 0 (Nat.zero_le H); linarith
      have hc := block_failure_bounds H hp hp1
      have hHp : 0 ≤ (H : ℝ) * p := mul_nonneg (Nat.cast_nonneg H) hp
      calc
        _ = (1 - c) * (u - l) := by ring
        _ ≤ (H * p) * (u - l) := mul_le_mul_of_nonneg_right hc.2 hlu
        _ ≤ (H * p) * ((H * p) ^ n * (b - a)) := mul_le_mul_of_nonneg_left hw hHp
        _ = (H * p) ^ (n + 1) * (b - a) := by rw [pow_succ]; ring

lemma averageRun_range (H : ℕ) {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f : ℕ → ℝ} (hf : ∀ i ≤ H, 0 ≤ f i ∧ f i ≤ 1) (t : ℕ) :
    ∃ l u : ℝ, (∀ i ≤ H, l ≤ averageRun H p f t i ∧
      averageRun H p f t i ≤ u) ∧ u - l ≤ (H * p) ^ (t / H) := by
  have hr := averageRun_bounds H hp hp1 hf (t % H)
  obtain ⟨l, u, hb, hw⟩ := averageRun_range_blocks H hp hp1 hr (t / H)
  refine ⟨l, u, ?_, by simpa using hw⟩
  intro i hi
  have he : t = t / H * H + t % H := by
    have h := Nat.mod_add_div t H
    nlinarith [h]
  rw [he, averageRun_add]
  exact hb i hi

open MeasureTheory ProbabilityTheory

lemma kernel_pow_zero_step (H n : ℕ) (p : unitInterval) :
    (kernel H p ^ (n + 1)) 0 =
      unitInterval.toNNReal p • (kernel H p ^ n) (H : ℝ) +
        unitInterval.toNNReal (unitInterval.symm p) • (kernel H p ^ n) 0 := by
  rw [pow_succ]
  change ((kernel H p ^ n) ∘ₖ kernel H p) 0 = _
  ext s hs
  rw [Kernel.comp_apply' _ _ _ hs, kernel_zero, bernoulliMeasure_def]
  simp only [lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac' _ ((kernel H p ^ n).measurable_coe hs),
    Measure.add_apply, Measure.smul_apply]

lemma kernel_pow_succ_step (H n i : ℕ) (p : unitInterval) :
    (kernel H p ^ (n + 1)) (i + 1 : ℕ) = (kernel H p ^ n) (i : ℝ) := by
  rw [pow_succ]
  change ((kernel H p ^ n) ∘ₖ kernel H p) (i + 1 : ℕ) = _
  ext s hs
  rw [Kernel.comp_apply' _ _ _ hs, kernel_succ,
    lintegral_dirac' _ ((kernel H p ^ n).measurable_coe hs)]

lemma kernel_pow_averageRun (H : ℕ) (p : unitInterval) (n i : ℕ) (s : Set ℝ) :
    ((kernel H p ^ n) (i : ℝ)).real s =
      averageRun H (p : ℝ) (fun j => (Measure.dirac (j : ℝ)).real s) n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    cases i with
    | zero =>
      rw [Nat.cast_zero, kernel_pow_zero_step, measureReal_add_apply,
        measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply]
      simp only [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
      have hz := ih 0
      rw [Nat.cast_zero] at hz
      rw [ih H, hz, averageRun, averageStep, ite_eq_left rfl]
      ring
    | succ i =>
      rw [kernel_pow_succ_step, ih]
      simp [averageRun, averageStep]

lemma weightedSum_split (H : ℕ) (p : unitInterval) (f : ℕ → ℝ) :
    ∑ i : Fin (H + 1), weight H p i * f i =
      (1 / (1 + H * (p : ℝ))) * f 0 +
        ((p : ℝ) / (1 + H * (p : ℝ))) * ∑ i : Fin H, f (i.val + 1) := by
  rw [Fin.sum_univ_succ]
  simp only [weight, ↓reduceIte, Fin.succ_ne_zero, Fin.val_zero, Fin.val_succ,
    Finset.mul_sum]

lemma weightedSum_averageStep (H : ℕ) (p : unitInterval) (f : ℕ → ℝ) :
    ∑ i : Fin (H + 1), weight H p i * averageStep H (p : ℝ) f i =
      ∑ i : Fin (H + 1), weight H p i * f i := by
  rw [weightedSum_split, weightedSum_split]
  simp only [averageStep, ↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
  have hab : 1 / (1 + H * (p : ℝ)) * p = (p : ℝ) / (1 + H * (p : ℝ)) := by ring
  have har : 1 / (1 + H * (p : ℝ)) * (1 - p) +
      (p : ℝ) / (1 + H * (p : ℝ)) = 1 / (1 + H * (p : ℝ)) := by ring
  have hh := stationary_weight_identity H _ _ _ _ hab har f
  simpa only [← Fin.sum_univ_eq_sum_range, add_comm ((1 - (p : ℝ)) * f 0)] using hh

lemma weightedSum_averageRun (H : ℕ) (p : unitInterval) (f : ℕ → ℝ) (n : ℕ) :
    ∑ i : Fin (H + 1), weight H p i * averageRun H (p : ℝ) f n i =
      ∑ i : Fin (H + 1), weight H p i * f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∑ i : Fin (H + 1), weight H p i *
      averageStep H (p : ℝ) (averageRun H (p : ℝ) f n) i) = _
    rw [weightedSum_averageStep, ih]

lemma stationaryMeasure_real (H : ℕ) (p : unitInterval) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (stationaryMeasure H p).real s =
      ∑ i : Fin (H + 1), weight H p i * (Measure.dirac (i.val : ℝ)).real s := by
  rw [measureReal_def, stationaryMeasure, Measure.sum_apply _ hs, tsum_fintype]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (measure_ne_top (Measure.dirac (i.val : ℝ)) s))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (weight_nonneg H p _), measureReal_def]

lemma stationaryMeasure_real_pow (H : ℕ) (p : unitInterval) (n : ℕ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (stationaryMeasure H p).real s =
      ∑ i : Fin (H + 1), weight H p i * ((kernel H p ^ n) (i.val : ℝ)).real s := by
  simp_rw [kernel_pow_averageRun]
  rw [weightedSum_averageRun, stationaryMeasure_real H p hs]

lemma weighted_difference_le (H : ℕ) (p : unitInterval) (f : ℕ → ℝ) (i : ℕ) :
    |f i - ∑ j : Fin (H + 1), weight H p j * f j| ≤
      ∑ j : Fin (H + 1), weight H p j * |f i - f j| := by
  have he : f i - ∑ j : Fin (H + 1), weight H p j * f j =
      ∑ j : Fin (H + 1), weight H p j * (f i - f j) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, weight_sum, one_mul]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [abs_mul, abs_of_nonneg (weight_nonneg H p j)]

lemma averageRun_pair_bound (H : ℕ) (p : unitInterval) (n i j : ℕ)
    (hi : i ≤ H) (hj : j ≤ H) {f : ℕ → ℝ} (hf : ∀ i ≤ H, 0 ≤ f i ∧ f i ≤ 1) :
    |averageRun H (p : ℝ) f n i - averageRun H (p : ℝ) f n j| ≤
      (H * (p : ℝ)) ^ (n / H) := by
  obtain ⟨l, u, hb, hw⟩ := averageRun_range H p.property.1 p.property.2 hf n
  have hbi := hb i hi
  have hbj := hb j hj
  rw [abs_le]
  constructor <;> linarith

lemma kernel_pair_bound (H : ℕ) (p : unitInterval) (n i j : ℕ)
    (hi : i ≤ H) (hj : j ≤ H) (s : Set ℝ) :
    |((kernel H p ^ n) (i : ℝ)).real s - ((kernel H p ^ n) (j : ℝ)).real s| ≤
      (H * (p : ℝ)) ^ (n / H) := by
  simp_rw [kernel_pow_averageRun]
  apply averageRun_pair_bound H p n i j hi hj
  intro k hk
  exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩

lemma kernel_stationary_bound (H : ℕ) (p : unitInterval) (n i : ℕ)
    (hi : i ≤ H) {s : Set ℝ} (hs : MeasurableSet s) :
    |((kernel H p ^ n) (i : ℝ)).real s - (stationaryMeasure H p).real s| ≤
      (H * (p : ℝ)) ^ (n / H) := by
  rw [stationaryMeasure_real_pow H p n hs]
  apply (weighted_difference_le H p (fun j => ((kernel H p ^ n) (j : ℝ)).real s) i).trans
  calc
    _ ≤ ∑ j : Fin (H + 1), weight H p j * (H * (p : ℝ)) ^ (n / H) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (kernel_pair_bound H p n i j hi (by omega) s)
        (weight_nonneg H p j)
    _ = _ := by rw [← Finset.sum_mul, weight_sum, one_mul]

lemma kernel_stationary_zero_bound (H : ℕ) (p : unitInterval) (n : ℕ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    |((kernel H p ^ n) 0).real s - (stationaryMeasure H p).real s| ≤
      (H * (p : ℝ) / (1 + H * (p : ℝ))) * (H * (p : ℝ)) ^ (n / H) := by
  rw [stationaryMeasure_real_pow H p n hs]
  have h := weighted_difference_le H p (fun j => ((kernel H p ^ n) (j : ℝ)).real s) 0
  rw [weightedSum_split H p (fun j =>
    |((kernel H p ^ n) (0 : ℕ)).real s - ((kernel H p ^ n) (j : ℝ)).real s|)] at h
  simp only [Nat.cast_zero, sub_self, abs_zero, mul_zero, zero_add] at h
  apply h.trans
  have hp : 0 ≤ (p : ℝ) := p.property.1
  calc
    _ ≤ ((p : ℝ) / (1 + H * (p : ℝ))) *
        ∑ j : Fin H, (H * (p : ℝ)) ^ (n / H) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j hj
      simpa only [Nat.cast_zero] using
        kernel_pair_bound H p n 0 (j.val + 1) (Nat.zero_le H) (by omega) s
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring

open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

lemma mixingDistance_bound (H : ℕ) (p : unitInterval) (n i : ℕ) (hi : i ≤ H) :
    mixingDistance (kernel H p) (stationaryLaw H p) n (i : ℝ) ≤
      (H * (p : ℝ)) ^ (n / H) := by
  apply ciSup_le
  intro s
  exact kernel_stationary_bound H p n i hi s.property

lemma mixingDistance_zero_bound (H : ℕ) (p : unitInterval) (n : ℕ) :
    mixingDistance (kernel H p) (stationaryLaw H p) n 0 ≤
      (H * (p : ℝ) / (1 + H * (p : ℝ))) * (H * (p : ℝ)) ^ (n / H) := by
  apply ciSup_le
  intro s
  exact kernel_stationary_zero_bound H p n s.property

lemma average_mixing_bound (H : ℕ) (p : unitInterval) (n : ℕ) :
    (∫ x, mixingDistance (kernel H p) (stationaryLaw H p) n x ∂stationaryMeasure H p) ≤
      2 * (H * (p : ℝ) / (1 + H * (p : ℝ))) * (H * (p : ℝ)) ^ (n / H) := by
  rw [integral_stationary_split]
  simp only [smul_eq_mul]
  have hp : 0 ≤ (p : ℝ) := p.property.1
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hd : 0 < 1 + H * (p : ℝ) := by positivity
  have ha : 1 / (1 + H * (p : ℝ)) ≤ 1 := (div_le_one hd).mpr (by nlinarith [mul_nonneg hH hp])
  have hs : (∑ i : Fin H, mixingDistance (kernel H p) (stationaryLaw H p) n
      ((i.val : ℝ) + 1)) ≤ H * (H * (p : ℝ)) ^ (n / H) := by
    calc
      _ ≤ ∑ i : Fin H, (H * (p : ℝ)) ^ (n / H) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Nat.cast_add, Nat.cast_one] using
          mixingDistance_bound H p n (i.val + 1) (by omega)
      _ = _ := by simp
  have h0 := mixingDistance_zero_bound H p n
  have hc : 0 ≤ (H * (p : ℝ) / (1 + H * (p : ℝ))) *
      (H * (p : ℝ)) ^ (n / H) := by positivity
  calc
    _ ≤ (1 / (1 + H * (p : ℝ))) *
        ((H * (p : ℝ) / (1 + H * (p : ℝ))) * (H * (p : ℝ)) ^ (n / H)) +
        ((p : ℝ) / (1 + H * (p : ℝ))) * (H * (H * (p : ℝ)) ^ (n / H)) :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (by positivity))
        (mul_le_mul_of_nonneg_left hs (by positivity))
    _ ≤ 1 * ((H * (p : ℝ) / (1 + H * (p : ℝ))) * (H * (p : ℝ)) ^ (n / H)) +
        ((p : ℝ) / (1 + H * (p : ℝ))) * (H * (H * (p : ℝ)) ^ (n / H)) :=
      add_le_add (mul_le_mul_of_nonneg_right ha hc) le_rfl
    _ = _ := by ring

lemma average_mixing_block_bound (H : ℕ) (p : unitInterval) (n : ℕ) :
    (∫ x, mixingDistance (kernel H p) (stationaryLaw H p) n x ∂stationaryMeasure H p) ≤
      (2 * H * (p : ℝ)) ^ (n / H + 1) := by
  apply (average_mixing_bound H p n).trans
  have hp : 0 ≤ (p : ℝ) := p.property.1
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hd : 0 < 1 + H * (p : ℝ) := by positivity
  have hq : H * (p : ℝ) / (1 + H * (p : ℝ)) ≤ H * (p : ℝ) := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (H * (p : ℝ))]
  have hc : (H * (p : ℝ)) ^ (n / H) ≤ (2 * H * (p : ℝ)) ^ (n / H) :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) _
  calc
    _ ≤ (2 * H * (p : ℝ)) * (2 * H * (p : ℝ)) ^ (n / H) := by
      apply mul_le_mul
      · nlinarith
      · exact hc
      · positivity
      · positivity
    _ = _ := by rw [pow_succ]; ring

lemma average_mixing_stretched (H : ℕ) (hH : 0 < H) (p : unitInterval)
    {τ γ : ℝ} (hτ : 0 < τ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hscale : 2 * H * (p : ℝ) ≤ Real.exp (-(((H : ℝ) / τ) ^ γ))) (n : ℕ) :
    (∫ x, mixingDistance (kernel H p) (stationaryLaw H p) n x ∂stationaryMeasure H p) ≤
      Real.exp (-(((n : ℝ) / τ) ^ γ)) := by
  apply (average_mixing_block_bound H p n).trans
  apply MixingProfiles.profile_block_bound
    (φ := fun t => Real.exp (-(((t : ℝ) / τ) ^ γ)))
    (fun _ => (Real.exp_pos _).le) _ _ _ (by have := p.property.1; positivity) hH hscale n
  · simp [Real.zero_rpow hγ.ne']
  · intro i j hij
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    apply Real.rpow_le_rpow (by positivity) _ hγ.le
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hτ.le
  · intro i j
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := Real.rpow_add_le_add_rpow
      (div_nonneg (Nat.cast_nonneg i) hτ.le)
      (div_nonneg (Nat.cast_nonneg j) hτ.le) hγ.le hγ1
    rw [← add_div, ← Nat.cast_add] at h
    linarith

end OracleTemplate.CountdownMarkov
