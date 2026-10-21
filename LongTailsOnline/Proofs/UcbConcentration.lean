import LongTailsOnline.Algorithms.Ucb

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LongTailsOnline.Proofs.Ucb

open LongTailsOnline.Setups.StochasticBandit LongTailsOnline.Algorithms.Ucb

lemma centered_subgaussian {p : Params} {P : ProbabilityMeasure (Sample p.k)}
    (h : Sampling p P) (i : Arm p.k) (n : ℕ) :
    HasSubgaussianMGF (fun w => w (i, n) - p.μ i) (1 / 4) P.toMeasure := by
  have hs := hasSubgaussianMGF_of_mem_Icc
    (measurable_pi_apply (i, n)).aemeasurable (h.bounded i n)
  convert hs using 1 <;> norm_num [h.mean]

lemma centered_independent {p : Params} {P : ProbabilityMeasure (Sample p.k)}
    (h : Sampling p P) (i : Arm p.k) :
    iIndepFun (fun n => fun w : Sample p.k => w (i, n) - p.μ i) P.toMeasure := by
  exact (h.independent.precomp (show Function.Injective (fun n : ℕ => (i, n)) from
    fun _ _ he => congrArg Prod.snd he)).comp (fun _ x => x - p.μ i) (by fun_prop)

lemma radius_tail {p : Params} {P : ProbabilityMeasure (Sample p.k)}
    (h : Sampling p P) (i : Arm p.k) (t : ℕ) {n : ℕ} (hn : 0 < n) :
    P.toMeasure.real {w | radius t n < |empirical w i n - p.μ i|} ≤
      2 / (t + 1 : ℝ) ^ 4 := by
  have hs := HasSubgaussianMGF.sum_of_iIndepFun (h_indep := centered_independent h i)
    (s := Finset.range n) (c := fun _ => (1 / 4 : ℝ≥0))
    (fun s _ => centered_subgaussian h i s)
  have hg : HasSubgaussianMGF (fun w => ∑ s ∈ Finset.range n, (w (i, s) - p.μ i))
      ((n : ℝ≥0) / 4) P.toMeasure := by
    simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_eq_mul_inv] using hs
  have hnR : (0 : ℝ) < n := by positivity
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hl : 0 ≤ Real.log (t + 1 : ℝ) :=
    Real.log_nonneg (by have h0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t; linarith)
  have hr : 0 ≤ radius t n := Real.sqrt_nonneg _
  have hr2 : radius t n ^ 2 = 2 * Real.log (t + 1 : ℝ) / n :=
    Real.sq_sqrt (by positivity)
  have hexp : Real.exp (-((n : ℝ) * radius t n) ^ 2 / (2 * (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ))) =
      1 / (t + 1 : ℝ) ^ 4 := by
    have he : -((n : ℝ) * radius t n) ^ 2 / (2 * (((n : ℝ≥0) / 4 : ℝ≥0) : ℝ)) =
        -(4 * Real.log (t + 1 : ℝ)) := by
      simp only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast, mul_pow, hr2]
      field_simp
    rw [he, Real.exp_neg, show (4 : ℝ) * Real.log (t + 1 : ℝ) =
      Real.log ((t + 1 : ℝ) ^ 4) by rw [Real.log_pow]; ring]
    rw [Real.exp_log (by positivity), one_div]
  have hpos := hg.measure_ge_le (mul_nonneg hnR.le hr)
  have hneg := hg.neg.measure_ge_le (mul_nonneg hnR.le hr)
  have heq (w : Sample p.k) :
      (∑ s ∈ Finset.range n, (w (i, s) - p.μ i)) =
        (empirical w i n - p.μ i) * n := by
    simp only [empirical, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    field_simp
  have hsub : {w : Sample p.k | radius t n < |empirical w i n - p.μ i|} ⊆
      {w | (n : ℝ) * radius t n ≤ ∑ s ∈ Finset.range n, (w (i, s) - p.μ i)} ∪
      {w | (n : ℝ) * radius t n ≤ -(∑ s ∈ Finset.range n, (w (i, s) - p.μ i))} := by
    intro w hw
    change radius t n < |empirical w i n - p.μ i| at hw
    change ((n : ℝ) * radius t n ≤ ∑ s ∈ Finset.range n, (w (i, s) - p.μ i)) ∨
      ((n : ℝ) * radius t n ≤ -(∑ s ∈ Finset.range n, (w (i, s) - p.μ i)))
    rw [heq]
    rcases lt_abs.mp hw with hw | hw
    · left
      nlinarith
    · right
      nlinarith
  calc
    _ ≤ P.toMeasure.real ({w | (n : ℝ) * radius t n ≤ ∑ s ∈ Finset.range n, (w (i, s) - p.μ i)} ∪
        {w | (n : ℝ) * radius t n ≤ -(∑ s ∈ Finset.range n, (w (i, s) - p.μ i))}) :=
      measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add hpos hneg
    _ = _ := by rw [hexp]; ring

noncomputable def bad (p : Params) (t : ℕ) : Set (Sample p.k) :=
  ⋃ i : Arm p.k, ⋃ n ∈ Finset.range (t + 1),
    {w | 0 < n ∧ radius t n < |empirical w i n - p.μ i|}

lemma measurableSet_bad (p : Params) (t : ℕ) : MeasurableSet (bad p t) := by
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.biUnion (Finset.countable_toSet _)
  intro n _
  exact (MeasurableSet.const (0 < n)).inter
    (measurableSet_lt measurable_const (show Measurable (fun w : Sample p.k => |empirical w i n - p.μ i|) by fun_prop))

lemma measure_bad {p : Params} {P : ProbabilityMeasure (Sample p.k)}
    (h : Sampling p P) (t : ℕ) :
    P.toMeasure.real (bad p t) ≤ 2 * (p.k + 1 : ℝ) / (t + 1 : ℝ) ^ 3 := by
  have hi (i : Arm p.k) (n : ℕ) :
      P.toMeasure.real {w | 0 < n ∧ radius t n < |empirical w i n - p.μ i|} ≤
        2 / (t + 1 : ℝ) ^ 4 := by
    by_cases hn : 0 < n
    · exact (measureReal_mono (fun _ hw => hw.2)).trans (radius_tail h i t hn)
    · simp [hn]
      positivity
  calc
    _ ≤ ∑ i : Arm p.k, P.toMeasure.real (⋃ n ∈ Finset.range (t + 1),
        {w | 0 < n ∧ radius t n < |empirical w i n - p.μ i|}) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Arm p.k, ∑ _n ∈ Finset.range (t + 1), 2 / (t + 1 : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro i _
      exact (measureReal_biUnion_finset_le (Finset.range (t + 1)) _).trans
        (Finset.sum_le_sum fun n _ => hi i n)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      field_simp

lemma sum_reciprocal_difference (T : ℕ) :
    (∑ t ∈ Finset.range T, (1 / (t + 1 : ℝ) - 1 / (t + 2 : ℝ))) =
      1 - 1 / (T + 1 : ℝ) := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma sum_inverse_cube (T : ℕ) :
    (∑ t ∈ Finset.range T, 1 / (t + 1 : ℝ) ^ 3) ≤ 2 := by
  have he (t : ℕ) : 1 / (t + 1 : ℝ) ^ 3 ≤
      2 * (1 / (t + 1 : ℝ) - 1 / (t + 2 : ℝ)) := by
    have ht : (0 : ℝ) ≤ t := by positivity
    have h1 : (0 : ℝ) < t + 1 := by positivity
    have h2 : (0 : ℝ) < t + 2 := by positivity
    calc
      _ ≤ 2 / ((t + 1 : ℝ) * (t + 2 : ℝ)) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        nlinarith [sq_nonneg (t : ℝ), mul_nonneg ht (sq_nonneg (t : ℝ))]
      _ = _ := by field_simp; ring
  calc
    _ ≤ ∑ t ∈ Finset.range T, 2 * (1 / (t + 1 : ℝ) - 1 / (t + 2 : ℝ)) :=
      Finset.sum_le_sum fun t _ => he t
    _ = 2 * (1 - 1 / (T + 1 : ℝ)) := by rw [← Finset.mul_sum, sum_reciprocal_difference]
    _ ≤ 2 := by
      have hp : 0 ≤ 1 / (T + 1 : ℝ) := by positivity
      linarith

lemma sum_measure_bad {p : Params} {P : ProbabilityMeasure (Sample p.k)}
    (h : Sampling p P) (T : ℕ) :
    (∑ t ∈ Finset.range T, P.toMeasure.real (bad p t)) ≤ 4 * (p.k + 1 : ℝ) := by
  calc
    _ ≤ ∑ t ∈ Finset.range T, 2 * (p.k + 1 : ℝ) / (t + 1 : ℝ) ^ 3 :=
      Finset.sum_le_sum fun t _ => measure_bad h t
    _ = 2 * (p.k + 1 : ℝ) * ∑ t ∈ Finset.range T, 1 / (t + 1 : ℝ) ^ 3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ 2 * (p.k + 1 : ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_inverse_cube T) (by positivity)
    _ = _ := by ring

end LongTailsOnline.Proofs.Ucb
