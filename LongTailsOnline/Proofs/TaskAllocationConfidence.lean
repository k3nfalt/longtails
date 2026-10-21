import LongTailsOnline.Algorithms.ParallelTaskAllocation
import LongTailsOnline.Proofs.TaskAllocationConcentration
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LongTailsOnline.Proofs.TaskAllocation

open LongTailsOnline.Setups.StationaryTaskAllocation
open LongTailsOnline.Algorithms.ParallelTaskAllocation

lemma noise_ge_one (p : Public) : 1 ≤ noise p := le_max_left _ _

lemma noise_ge_sigma (p : Public) : (p.σ : ℝ) ≤ noise p := le_max_right _ _

lemma confidenceLog_ge_one {p : Public} (hB : 0 < p.B) (hT : 0 < p.T) :
    1 ≤ confidenceLog p := by
  have hn : (1 : ℝ) ≤ p.k + 1 := by linarith [Nat.cast_nonneg (α := ℝ) p.k]
  have hB' : (1 : ℝ) ≤ p.B := by exact_mod_cast hB
  have hT' : (1 : ℝ) ≤ p.T := by exact_mod_cast hT
  have hσ := noise_ge_one p
  have harg : (128 : ℝ) ≤
      64 * (p.k + 1 : ℝ) * (p.B : ℝ) ^ 2 * (p.T : ℝ) ^ 3 * (1 + noise p) := by
    calc
      128 = (64 : ℝ) * 1 * 1 ^ 2 * 1 ^ 3 * (1 + 1) := by norm_num
      _ ≤ _ := by gcongr
  apply (Real.le_log_iff_exp_le (by linarith : (0 : ℝ) <
    64 * (p.k + 1 : ℝ) * (p.B : ℝ) ^ 2 * (p.T : ℝ) ^ 3 * (1 + noise p))).mpr
  exact Real.exp_one_lt_three.le.trans (by linarith)

lemma clipLevel_ge_one (p : Public) :
    1 ≤ clipLevel p := by
  have hσ := noise_ge_one p
  unfold clipLevel
  have := Real.sqrt_nonneg (2 * confidenceLog p)
  nlinarith

lemma scale_ge_one {p : Public} (hB : 0 < p.B) (hT : 0 < p.T) : 1 ≤ scale p := by
  have hH := clipLevel_ge_one p
  have ht := confidenceLog_ge_one hB hT
  unfold scale
  nlinarith [mul_nonneg (sub_nonneg.mpr hH) (sub_nonneg.mpr ht)]

lemma sample_integrable {p : Params} {P : ProbabilityMeasure (Sample p.config.k)}
    (h : Sampling p P) (i : Worker p.config.k) (j : ℕ) :
    Integrable (fun w => w (i, j)) P.toMeasure := by
  have hint := (h.subgaussian i j).integrable.add (integrable_const (p.μ i))
  convert hint using 1
  ext w
  simp

lemma clipped_bias_le {p : Params} {P : ProbabilityMeasure (Sample p.config.k)}
    (h : Sampling p P) (hB : 0 < p.config.B) (hT : 0 < p.config.T)
    (hμ : ∀ i, p.μ i ≤ 1) (i : Worker p.config.k) (j : ℕ) :
    0 ≤ p.μ i - (∫ w, clipped (clipLevel p.config) w i j ∂P.toMeasure) ∧
      p.μ i - (∫ w, clipped (clipLevel p.config) w i j ∂P.toMeasure) ≤ bias p.config := by
  let a := Real.sqrt (2 * confidenceLog p.config)
  let η := a / noise p.config
  have hσ := noise_ge_one p.config
  have hσpos : 0 < noise p.config := by linarith
  have ht := confidenceLog_ge_one hB hT
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * confidenceLog p.config := Real.sq_sqrt (by linarith)
  have ha : 1 ≤ a := by nlinarith
  have hη : 0 < η := div_pos (by linarith) hσpos
  have hmul : η * (noise p.config * a) = 2 * confidenceLog p.config := by
    dsimp only [η]
    field_simp
    nlinarith
  have hsq : ((p.config.σ : ℝ) ^ 2) ≤ noise p.config ^ 2 := by
    nlinarith [noise_ge_sigma p.config, NNReal.coe_nonneg p.config.σ]
  have hvar : (p.config.σ : ℝ) ^ 2 * η ^ 2 ≤ 2 * confidenceLog p.config := by
    calc
      _ ≤ noise p.config ^ 2 * η ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg η)
      _ = _ := by dsimp only [η]; field_simp; nlinarith
  have hexponent : -η * (clipLevel p.config - p.μ i) +
      (p.config.σ : ℝ) ^ 2 * η ^ 2 / 2 ≤ -confidenceLog p.config := by
    have hload : noise p.config * a ≤ clipLevel p.config - p.μ i := by
      change noise p.config * a ≤ 1 + noise p.config * a - p.μ i
      linarith [hμ i]
    have hload' := mul_le_mul_of_nonneg_left hload hη.le
    nlinarith
  have hb := clipped_mean_bias (H := clipLevel p.config) (sample_integrable h i j) (h.mean i j)
    (h.subgaussian i j) hη
  change 0 ≤ p.μ i - (∫ w, min (w (i, j)) (clipLevel p.config) ∂P.toMeasure) ∧ _
  refine ⟨hb.1, hb.2.trans ?_⟩
  calc
    _ ≤ Real.exp (-confidenceLog p.config) / η := by
      apply div_le_div_of_nonneg_right _ hη.le
      apply Real.exp_le_exp.mpr
      simpa only [NNReal.coe_pow] using hexponent
    _ = noise p.config / a * Real.exp (-confidenceLog p.config) := by
      dsimp only [η]
      field_simp
    _ ≤ noise p.config * Real.exp (-confidenceLog p.config) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact (div_le_self hσpos.le ha)
    _ ≤ bias p.config := by
      unfold bias
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

lemma clipped_independent {p : Params} {P : ProbabilityMeasure (Sample p.config.k)}
    (h : Sampling p P) (i : Worker p.config.k) (H : ℝ) :
    iIndepFun (fun j => fun w : Sample p.config.k => clipped H w i j) P.toMeasure := by
  exact (h.independent.precomp (show Function.Injective (fun j : ℕ => (i, j)) from
    fun _ _ he => congrArg Prod.snd he)).comp (fun _ x => min x H) (by fun_prop)

lemma radius_mono {p : Public} {u v : ℝ} (huv : u ≤ v) (N : ℕ)
    (hB : 0 < p.B) (hT : 0 < p.T) : radius p u N ≤ radius p v N := by
  have hscale := scale_ge_one hB hT
  unfold radius
  gcongr

lemma clipped_prefix_tail {p : Params} {P : ProbabilityMeasure (Sample p.config.k)}
    (h : Sampling p P) (hB : 0 < p.config.B) (hT : 0 < p.config.T)
    (hμ0 : ∀ i, 0 ≤ p.μ i) (hμ1 : ∀ i, p.μ i ≤ 1)
    (i : Worker p.config.k) {N : ℕ} (hN : 0 < N) :
    P.toMeasure.real {w | radius p.config (p.μ i) N <
      |empirical (clipLevel p.config) w i N - p.μ i|} ≤
        2 * Real.exp (-confidenceLog p.config) := by
  let Z : ℕ → Sample p.config.k → ℝ := fun j w => clipped (clipLevel p.config) w i j
  let ν : ℕ → ℝ := fun j => ∫ w, Z j w ∂P.toMeasure
  let b : ℝ := (N : ℝ) * p.μ i - ∑ j ∈ Finset.range N, ν j
  have hH := clipLevel_ge_one p.config
  have ht := confidenceLog_ge_one hB hT
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb0 : 0 ≤ b := by
    have hsum := Finset.sum_nonneg (s := Finset.range N)
      (fun j _ => (clipped_bias_le h hB hT hμ1 i j).1)
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] using hsum
  have hb1 : b ≤ (N : ℝ) * bias p.config := by
    have hsum := Finset.sum_le_sum (s := Finset.range N)
      (fun j _ => (clipped_bias_le h hB hT hμ1 i j).2)
    simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] using hsum
  have hbound (j : ℕ) : ∀ᵐ w ∂P.toMeasure, Z j w ∈ Set.Icc 0 (clipLevel p.config) := by
    filter_upwards [h.positive i j] with w hw
    exact ⟨le_min hw.le (by linarith), min_le_right _ _⟩
  have htail := bounded_sum_absolute_tail (P := P.toMeasure) (Z := Z)
    (s := Finset.range N) (fun _ => by dsimp only [Z, clipped]; fun_prop)
    (by linarith : 0 < clipLevel p.config) (hμ0 i)
    (by linarith : 0 < confidenceLog p.config) (fun j _ => hbound j)
    (fun j _ => sub_nonneg.mp (clipped_bias_le h hB hT hμ1 i j).1)
    (clipped_independent h i _)
  simp only [Finset.card_range] at htail
  have hcenter (w : Sample p.config.k) :
      (∑ j ∈ Finset.range N, (Z j w - ν j)) =
        (N : ℝ) * (empirical (clipLevel p.config) w i N - p.μ i) + b := by
    dsimp only [empirical, b, Z]
    rw [Finset.sum_sub_distrib]
    field_simp
    ring
  have hroot : Real.sqrt (((N : ℝ) * p.μ i * clipLevel p.config) *
      confidenceLog p.config) = (N : ℝ) * Real.sqrt (p.μ i * scale p.config / N) := by
    have heq : ((N : ℝ) * p.μ i * clipLevel p.config) * confidenceLog p.config =
        (N : ℝ) ^ 2 * (p.μ i * scale p.config / N) := by
      unfold scale
      field_simp
    rw [heq, Real.sqrt_mul (sq_nonneg (N : ℝ)), Real.sqrt_sq hNr.le]
  have hthreshold : (N : ℝ) * radius p.config (p.μ i) N =
      2 * Real.sqrt (((N : ℝ) * p.μ i * clipLevel p.config) * confidenceLog p.config) +
        2 * clipLevel p.config * confidenceLog p.config + (N : ℝ) * bias p.config := by
    rw [hroot]
    unfold radius scale
    field_simp
  have hsubset : {w | radius p.config (p.μ i) N <
      |empirical (clipLevel p.config) w i N - p.μ i|} ⊆
      {w | 2 * Real.sqrt (((N : ℝ) * p.μ i * clipLevel p.config) *
        confidenceLog p.config) + 2 * clipLevel p.config * confidenceLog p.config ≤
          |∑ j ∈ Finset.range N, (Z j w - ν j)|} := by
    intro w hw
    change radius p.config (p.μ i) N <
      |empirical (clipLevel p.config) w i N - p.μ i| at hw
    have htriangle : (N : ℝ) * |empirical (clipLevel p.config) w i N - p.μ i| ≤
        |∑ j ∈ Finset.range N, (Z j w - ν j)| + (N : ℝ) * bias p.config := by
      calc
        _ = |(N : ℝ) * (empirical (clipLevel p.config) w i N - p.μ i)| := by
          rw [abs_mul, abs_of_pos hNr]
        _ = |(∑ j ∈ Finset.range N, (Z j w - ν j)) - b| := by rw [hcenter]; ring_nf
        _ ≤ |∑ j ∈ Finset.range N, (Z j w - ν j)| + |b| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            abs_sub_le (∑ j ∈ Finset.range N, (Z j w - ν j)) 0 b
        _ ≤ _ := by rw [abs_of_nonneg hb0]; exact add_le_add le_rfl hb1
    have hstrict := mul_lt_mul_of_pos_left hw hNr
    rw [hthreshold] at hstrict
    exact (show 2 * Real.sqrt (((N : ℝ) * p.μ i * clipLevel p.config) *
      confidenceLog p.config) + 2 * clipLevel p.config * confidenceLog p.config ≤
        |∑ j ∈ Finset.range N, (Z j w - ν j)| by linarith)
  exact (measureReal_mono hsubset).trans htail

noncomputable def confidenceFailure (p : Params) : Set (Sample p.config.k) :=
  ⋃ i : Worker p.config.k, ⋃ j ∈ Finset.range (p.config.B * p.config.T),
    {w | radius p.config (p.μ i) (j + 1) <
      |empirical (clipLevel p.config) w i (j + 1) - p.μ i|}

lemma measurableSet_confidenceFailure (p : Params) : MeasurableSet (confidenceFailure p) := by
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.biUnion (Finset.countable_toSet _)
  intro j _
  exact measurableSet_lt measurable_const (by fun_prop)

lemma measure_confidenceFailure {p : Params} {P : ProbabilityMeasure (Sample p.config.k)}
    (h : Sampling p P) (hB : 0 < p.config.B) (hT : 0 < p.config.T)
    (hμ0 : ∀ i, 0 ≤ p.μ i) (hμ1 : ∀ i, p.μ i ≤ 1) :
    P.toMeasure.real (confidenceFailure p) ≤
      2 * (p.config.k + 1 : ℝ) * (p.config.B * p.config.T) *
        Real.exp (-confidenceLog p.config) := by
  calc
    _ ≤ ∑ i : Worker p.config.k, P.toMeasure.real
        (⋃ j ∈ Finset.range (p.config.B * p.config.T),
          {w | radius p.config (p.μ i) (j + 1) <
            |empirical (clipLevel p.config) w i (j + 1) - p.μ i|}) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Worker p.config.k, ∑ _j ∈ Finset.range (p.config.B * p.config.T),
        2 * Real.exp (-confidenceLog p.config) := by
      apply Finset.sum_le_sum
      intro i _
      exact (measureReal_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum (fun j _ => clipped_prefix_tail h hB hT hμ0 hμ1 i (by omega)))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
      ring

lemma prefix_confident {p : Params} {w : Sample p.config.k}
    (hw : w ∉ confidenceFailure p) (i : Worker p.config.k) {N : ℕ}
    (hN : 0 < N) (hmax : N ≤ p.config.B * p.config.T) :
    |empirical (clipLevel p.config) w i N - p.μ i| ≤ radius p.config (p.μ i) N := by
  by_contra hnot
  apply hw
  simp only [confidenceFailure, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_range]
  refine ⟨i, N - 1, by omega, ?_⟩
  simpa only [Nat.sub_add_cancel hN] using lt_of_not_ge hnot

lemma exp_neg_confidenceLog {p : Public} (hB : 0 < p.B) (hT : 0 < p.T) :
    Real.exp (-confidenceLog p) =
      1 / (64 * (p.k + 1 : ℝ) * (p.B : ℝ) ^ 2 * (p.T : ℝ) ^ 3 * (1 + noise p)) := by
  have hσ := noise_ge_one p
  unfold confidenceLog
  rw [Real.exp_neg, Real.exp_log (by positivity), one_div]

lemma bias_eq {p : Public} (hB : 0 < p.B) (hT : 0 < p.T) :
    bias p = 1 / (64 * (p.k + 1 : ℝ) * (p.B : ℝ) ^ 2 * (p.T : ℝ) ^ 3) := by
  have hσ := noise_ge_one p
  unfold bias
  rw [exp_neg_confidenceLog hB hT]
  field_simp

lemma imbalance_ge_two {p : Public} (hB : 0 < p.B) : 2 ≤ imbalance p := by
  have hB' : (0 : ℝ) < p.B := by exact_mod_cast hB
  have hn : (0 : ℝ) < p.k + 1 := by positivity
  have heq : imbalance p = ((p.B : ℝ) ^ 2 + (p.k + 1 : ℝ) ^ 2) /
      ((p.B : ℝ) * (p.k + 1)) := by
    unfold imbalance
    field_simp
  rw [heq]
  apply (le_div_iff₀ (mul_pos hB' hn)).mpr
  nlinarith [sq_nonneg ((p.B : ℝ) - (p.k + 1))]

lemma accuracy_pos {p : Public} (hB : 0 < p.B) (hT : 0 < p.T) : 0 < accuracy p :=
  Real.sqrt_pos.mpr (div_pos (by linarith [imbalance_ge_two hB]) (by exact_mod_cast hT))

lemma inv_horizon_le_accuracy {p : Public} (hB : 0 < p.B) (hT : 0 < p.T) :
    1 / (p.T : ℝ) ≤ accuracy p := by
  have hd := imbalance_ge_two hB
  have hT' : (1 : ℝ) ≤ p.T := by exact_mod_cast hT
  have hacc := accuracy_pos hB hT
  have hs : accuracy p ^ 2 = imbalance p / p.T := Real.sq_sqrt (by positivity)
  have hs' : ((p.T : ℝ) * accuracy p) ^ 2 = (p.T : ℝ) * imbalance p := by
    rw [mul_pow, hs]
    field_simp
  apply (div_le_iff₀ (by exact_mod_cast hT : (0 : ℝ) < p.T)).mpr
  have hnonneg : 0 ≤ (p.T : ℝ) * accuracy p := by positivity
  nlinarith

lemma confidenceFailure_cost {p : Params} {P : ProbabilityMeasure (Sample p.config.k)}
    (h : Sampling p P) (hB : 0 < p.config.B) (hT : 0 < p.config.T)
    (hμ0 : ∀ i, 0 ≤ p.μ i) (hμ1 : ∀ i, p.μ i ≤ 1) :
    (p.config.B * p.config.T : ℝ) * P.toMeasure.real (confidenceFailure p) ≤ 1 := by
  have hσ := noise_ge_one p.config
  have hT' : (1 : ℝ) ≤ p.config.T := by exact_mod_cast hT
  calc
    _ ≤ (p.config.B * p.config.T : ℝ) *
        (2 * (p.config.k + 1 : ℝ) * (p.config.B * p.config.T) *
          Real.exp (-confidenceLog p.config)) :=
      mul_le_mul_of_nonneg_left (measure_confidenceFailure h hB hT hμ0 hμ1) (by positivity)
    _ = 1 / (32 * (p.config.T : ℝ) * (1 + noise p.config)) := by
      rw [exp_neg_confidenceLog hB hT]
      field_simp
      ring
    _ ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      nlinarith

end LongTailsOnline.Proofs.TaskAllocation
