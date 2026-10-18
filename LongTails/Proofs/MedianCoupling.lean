import LongTails.Algorithms.MedianGradient
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.IdentDistribIndep
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

namespace LongTails.Proofs.MedianCoupling

open OracleTemplate.FiniteVariance

lemma median3_formula (a b c : ℝ) :
    median3 a b c = max (min a b) (min (max a b) c) := by
  simp only [median3, min_def, max_def]
  split_ifs <;> grind

lemma median3_sorted {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : median3 a b c = b := by
  simp [median3_formula, min_eq_left hab, max_eq_right hab, min_eq_left hbc]

lemma median3_swap (a b c : ℝ) : median3 a b c = median3 b a c := by
  simp [median3_formula, min_comm, max_comm]

lemma median3_cycle (a b c : ℝ) : median3 a b c = median3 b c a := by
  simp only [median3_formula, min_def, max_def]
  split_ifs <;> grind

lemma median3_translate (a b c t : ℝ) :
    median3 (a + t) (b + t) (c + t) = median3 a b c + t := by
  simp [median3_formula, min_add_add_right, max_add_add_right]

lemma median3_neg (a b c : ℝ) : median3 (-a) (-b) (-c) = -median3 a b c := by
  simp only [median3_formula, min_def, max_def]
  split_ifs <;> grind

lemma ordered_square {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    b ^ 2 ≤ |a * b| + |b * c| + |c * a| := by
  have h1 := le_abs_self (a * b)
  have h2 := le_abs_self (b * c)
  have h3 := abs_nonneg (c * a)
  rcases le_total 0 b with hb | hb
  · have := mul_le_mul_of_nonneg_left hbc hb
    nlinarith [abs_nonneg (a * b)]
  · have := mul_le_mul_of_nonpos_right hab hb
    nlinarith [abs_nonneg (b * c)]

lemma median3_square (a b c : ℝ) :
    median3 a b c ^ 2 ≤ |a * b| + |b * c| + |c * a| := by
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · rw [median3_sorted hab hbc]
      exact ordered_square hab hbc
    · rcases le_total a c with hac | hca
      · rw [median3_swap, median3_cycle, median3_sorted hac hcb]
        nlinarith [ordered_square hac hcb, abs_mul a b, abs_mul b a,
          abs_mul a c, abs_mul c a, abs_mul b c, abs_mul c b]
      · rw [median3_cycle, median3_cycle, median3_sorted hca hab]
        nlinarith [ordered_square hca hab]
  · rw [median3_swap]
    rcases le_total a c with hac | hca
    · rw [median3_sorted hba hac]
      nlinarith [ordered_square hba hac, abs_mul a b, abs_mul b a,
        abs_mul a c, abs_mul c a, abs_mul b c, abs_mul c b]
    · rcases le_total b c with hbc | hcb
      · rw [median3_swap, median3_cycle, median3_sorted hbc hca]
        nlinarith [ordered_square hbc hca]
      · rw [median3_cycle, median3_cycle, median3_sorted hcb hba]
        nlinarith [ordered_square hcb hba, abs_mul a b, abs_mul b a,
          abs_mul a c, abs_mul c a, abs_mul b c, abs_mul c b]

lemma median3_clamp (a b c : ℝ) :
    median3 a b c = max (min b c) (min a (max b c)) := by
  simp only [median3_formula, min_def, max_def]
  split_ifs <;> grind

lemma median3_lipschitz (b c : ℝ) : LipschitzWith 1 (fun a => median3 a b c) := by
  simp only [median3_clamp]
  exact (LipschitzWith.id.min_const _).const_max _

lemma median3_mem (a b c : ℝ) :
    min b c ≤ median3 a b c ∧ median3 a b c ≤ max b c := by
  rw [median3_clamp]
  exact ⟨le_max_left _ _, max_le (min_le_max) (min_le_right _ _)⟩

lemma median3_replace (a a' b c : ℝ) :
    (median3 a b c - median3 a' b c) ^ 2 ≤ |a - a'| * |b - c| := by
  have h₁ : |median3 a b c - median3 a' b c| ≤ |a - a'| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      (median3_lipschitz b c).dist_le_mul a a'
  have h₂ : |median3 a b c - median3 a' b c| ≤ |b - c| := by
    obtain ⟨ha, hb⟩ := median3_mem a b c
    obtain ⟨ha', hb'⟩ := median3_mem a' b c
    rw [abs_le]
    rcases le_total b c with h | h
    · simp only [min_eq_left h, max_eq_right h] at *
      rw [abs_of_nonpos (sub_nonpos.mpr h)]
      constructor <;> linarith
    · simp only [min_eq_right h, max_eq_left h] at *
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
      constructor <;> linarith
  have h := mul_le_mul h₁ h₂ (abs_nonneg _) (abs_nonneg _)
  nlinarith [sq_abs (median3 a b c - median3 a' b c)]

lemma median3_difference (a b c a' b' c' : ℝ) :
    (median3 a b c - median3 a' b' c') ^ 2 ≤
      3 * (|a - a'| * |b - c| + |b - b'| * |a' - c| +
        |c - c'| * |a' - b'|) := by
  have h₁ := median3_replace a a' b c
  have h₂ := median3_replace b b' a' c
  rw [median3_swap b a' c, median3_swap b' a' c] at h₂
  have h₃ := median3_replace c c' a' b'
  rw [median3_cycle c a' b', median3_cycle c' a' b'] at h₃
  nlinarith [sq_nonneg (median3 a b c - 2 * median3 a' b c + median3 a' b' c),
    sq_nonneg (median3 a' b c - 2 * median3 a' b' c + median3 a' b' c'),
    sq_nonneg (median3 a b c - median3 a' b c - median3 a' b' c +
      median3 a' b' c')]

open MeasureTheory ProbabilityTheory

lemma sum_abs_mul_le {d : ℕ} (a b : EuclideanSpace ℝ (Fin d)) :
    ∑ i, |a i| * |b i| ≤ ‖a‖ * ‖b‖ := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |a i|) (fun i => |b i|)
  simp only [sq_abs, ← EuclideanSpace.real_norm_sq_eq] at h
  rw [← mul_pow] at h
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp h

lemma median_norm_sq {d : ℕ} (a b c : EuclideanSpace ℝ (Fin d)) :
    ‖OracleTemplate.MedianGradient.median a b c‖ ^ 2 ≤
      ‖a‖ * ‖b‖ + ‖b‖ * ‖c‖ + ‖c‖ * ‖a‖ := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ i, (|a i| * |b i| + |b i| * |c i| + |c i| * |a i|) := by
      apply Finset.sum_le_sum
      intro i _
      change median3 (a i) (b i) (c i) ^ 2 ≤ _
      simpa only [abs_mul] using median3_square (a i) (b i) (c i)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      linarith [sum_abs_mul_le a b, sum_abs_mul_le b c, sum_abs_mul_le c a]

lemma median_replace_norm_sq {d : ℕ} (a a' b c : EuclideanSpace ℝ (Fin d)) :
    ‖OracleTemplate.MedianGradient.median a b c -
      OracleTemplate.MedianGradient.median a' b c‖ ^ 2 ≤ ‖a - a'‖ * ‖b - c‖ := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ i, |(a - a') i| * |(b - c) i| := by
      apply Finset.sum_le_sum
      intro i _
      exact median3_replace (a i) (a' i) (b i) (c i)
    _ ≤ _ := sum_abs_mul_le (a - a') (b - c)

lemma measurable_median3 {Ω : Type*} [MeasurableSpace Ω] {a b c : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable fun ω => median3 (a ω) (b ω) (c ω) :=
  (ha.min hb).max ((hb.min hc).max (hc.min ha))

lemma median_difference_norm_sq {d : ℕ} (a b c a' b' c' : EuclideanSpace ℝ (Fin d)) :
    ‖OracleTemplate.MedianGradient.median a b c -
      OracleTemplate.MedianGradient.median a' b' c'‖ ^ 2 ≤
      3 * (‖a - a'‖ * ‖b - c‖ + ‖b - b'‖ * ‖a' - c‖ +
        ‖c - c'‖ * ‖a' - b'‖) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ i, 3 * (|(a - a') i| * |(b - c) i| +
        |(b - b') i| * |(a' - c) i| + |(c - c') i| * |(a' - b') i|) := by
      apply Finset.sum_le_sum
      intro i _
      exact median3_difference (a i) (b i) (c i) (a' i) (b' i) (c' i)
    _ ≤ _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib]
      linarith [sum_abs_mul_le (a - a') (b - c), sum_abs_mul_le (b - b') (a' - c),
        sum_abs_mul_le (c - c') (a' - b')]

lemma median3_second_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {a b c : Ω → ℝ} (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hai : Integrable a P) (hbi : Integrable b P) (hci : Integrable c P)
    (hab : IndepFun a b P) (hbc : IndepFun b c P) (hca : IndepFun c a P) :
    Integrable (fun ω => median3 (a ω) (b ω) (c ω) ^ 2) P ∧
      ∫ ω, median3 (a ω) (b ω) (c ω) ^ 2 ∂P ≤
        (∫ ω, |a ω| ∂P) * (∫ ω, |b ω| ∂P) +
        (∫ ω, |b ω| ∂P) * (∫ ω, |c ω| ∂P) +
        (∫ ω, |c ω| ∂P) * (∫ ω, |a ω| ∂P) := by
  have hab' := hab.comp continuous_abs.measurable continuous_abs.measurable
  have hbc' := hbc.comp continuous_abs.measurable continuous_abs.measurable
  have hca' := hca.comp continuous_abs.measurable continuous_abs.measurable
  have hi₁ := hab'.integrable_mul hai.abs hbi.abs
  have hi₂ := hbc'.integrable_mul hbi.abs hci.abs
  have hi₃ := hca'.integrable_mul hci.abs hai.abs
  have hi := (hi₁.add hi₂).add hi₃
  have hbound : ∀ ω, median3 (a ω) (b ω) (c ω) ^ 2 ≤
      |a ω| * |b ω| + |b ω| * |c ω| + |c ω| * |a ω| := by
    intro ω
    simpa only [abs_mul] using median3_square (a ω) (b ω) (c ω)
  have hm : Integrable (fun ω => median3 (a ω) (b ω) (c ω) ^ 2) P :=
    hi.mono' ((measurable_median3 ha hb hc).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, abs_sq, Pi.add_apply,
          Pi.mul_apply, Function.comp_apply] using hbound ω)
  refine ⟨hm, (integral_mono hm hi (hbound)).trans_eq ?_⟩
  simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
  rw [integral_add (by exact hi₁.add hi₂) (by exact hi₃),
    integral_add (by exact hi₁) (by exact hi₂)]
  have e₁ := hab'.integral_fun_mul_eq_mul_integral
    hai.abs.aestronglyMeasurable hbi.abs.aestronglyMeasurable
  have e₂ := hbc'.integral_fun_mul_eq_mul_integral
    hbi.abs.aestronglyMeasurable hci.abs.aestronglyMeasurable
  have e₃ := hca'.integral_fun_mul_eq_mul_integral
    hci.abs.aestronglyMeasurable hai.abs.aestronglyMeasurable
  simp only [Function.comp_apply] at e₁ e₂ e₃
  rw [e₁, e₂, e₃]

lemma median3_integral_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (a : Fin 3 → Ω → ℝ) (hi : iIndepFun a P)
    (hs : ∀ i, IdentDistrib (a i) (fun ω => -a i ω) P P) :
    ∫ ω, median3 (a 0 ω) (a 1 ω) (a 2 ω) ∂P = 0 := by
  have hn : iIndepFun (fun i ω => -a i ω) P :=
    hi.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have hd := IdentDistrib.pi hs hi hn
  have hm : Measurable (fun v : Fin 3 → ℝ => median3 (v 0) (v 1) (v 2)) :=
    measurable_median3 (measurable_pi_apply 0) (measurable_pi_apply 1) (measurable_pi_apply 2)
  have he := (hd.comp hm).integral_eq
  simp only [Function.comp_apply, median3_neg] at he
  rw [integral_neg] at he
  linarith

lemma measurable_median {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {a b c : Ω → EuclideanSpace ℝ (Fin d)}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) :
    Measurable fun ω => OracleTemplate.MedianGradient.median (a ω) (b ω) (c ω) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  exact measurable_median3
    ((measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp ha))
    ((measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp hb))
    ((measurable_pi_apply i).comp ((WithLp.measurable_ofLp 2 _).comp hc))

lemma independent_norm_product {Ω E F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    {P : Measure Ω} {a : Ω → E} {b : Ω → F}
    (hai : Integrable a P) (hbi : Integrable b P) (hab : IndepFun a b P) :
    Integrable (fun ω => ‖a ω‖ * ‖b ω‖) P ∧
      ∫ ω, ‖a ω‖ * ‖b ω‖ ∂P = (∫ ω, ‖a ω‖ ∂P) * (∫ ω, ‖b ω‖ ∂P) := by
  have h := hab.comp continuous_norm.measurable continuous_norm.measurable
  exact ⟨h.integrable_mul hai.norm hbi.norm,
    h.integral_fun_mul_eq_mul_integral hai.norm.aestronglyMeasurable
      hbi.norm.aestronglyMeasurable⟩

lemma median_second_moment {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {a b c : Ω → EuclideanSpace ℝ (Fin d)}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hai : Integrable a P) (hbi : Integrable b P) (hci : Integrable c P)
    (hab : IndepFun a b P) (hbc : IndepFun b c P) (hca : IndepFun c a P) :
    Integrable (fun ω => ‖OracleTemplate.MedianGradient.median (a ω) (b ω) (c ω)‖ ^ 2) P ∧
      ∫ ω, ‖OracleTemplate.MedianGradient.median (a ω) (b ω) (c ω)‖ ^ 2 ∂P ≤
        (∫ ω, ‖a ω‖ ∂P) * (∫ ω, ‖b ω‖ ∂P) +
        (∫ ω, ‖b ω‖ ∂P) * (∫ ω, ‖c ω‖ ∂P) +
        (∫ ω, ‖c ω‖ ∂P) * (∫ ω, ‖a ω‖ ∂P) := by
  obtain ⟨hi₁, he₁⟩ := independent_norm_product hai hbi hab
  obtain ⟨hi₂, he₂⟩ := independent_norm_product hbi hci hbc
  obtain ⟨hi₃, he₃⟩ := independent_norm_product hci hai hca
  have hi := (hi₁.add hi₂).add hi₃
  have hm : Integrable (fun ω =>
      ‖OracleTemplate.MedianGradient.median (a ω) (b ω) (c ω)‖ ^ 2) P :=
    hi.mono' ((measurable_median ha hb hc).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, abs_sq, abs_norm, Pi.add_apply, Pi.sub_apply]
          using median_norm_sq (a ω) (b ω) (c ω))
  refine ⟨hm, (integral_mono hm hi (fun ω => median_norm_sq (a ω) (b ω) (c ω))).trans_eq ?_⟩
  simp only [Pi.add_apply]
  rw [integral_add (by exact hi₁.add hi₂) (by exact hi₃),
    integral_add (by exact hi₁) (by exact hi₂), he₁, he₂, he₃]

lemma median_coupled_second_moment {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {a b c a' b' c' : Ω → EuclideanSpace ℝ (Fin d)}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (ha' : Measurable a') (hb' : Measurable b') (hc' : Measurable c')
    (hai : Integrable a P) (hbi : Integrable b P) (hci : Integrable c P)
    (hai' : Integrable a' P) (hbi' : Integrable b' P) (hci' : Integrable c' P)
    (h₁ : IndepFun (fun ω => a ω - a' ω) (fun ω => b ω - c ω) P)
    (h₂ : IndepFun (fun ω => b ω - b' ω) (fun ω => a' ω - c ω) P)
    (h₃ : IndepFun (fun ω => c ω - c' ω) (fun ω => a' ω - b' ω) P) :
    Integrable (fun ω => ‖OracleTemplate.MedianGradient.median (a ω) (b ω) (c ω) -
      OracleTemplate.MedianGradient.median (a' ω) (b' ω) (c' ω)‖ ^ 2) P ∧
      ∫ ω, ‖OracleTemplate.MedianGradient.median (a ω) (b ω) (c ω) -
        OracleTemplate.MedianGradient.median (a' ω) (b' ω) (c' ω)‖ ^ 2 ∂P ≤
        3 * ((∫ ω, ‖a ω - a' ω‖ ∂P) * (∫ ω, ‖b ω - c ω‖ ∂P) +
          (∫ ω, ‖b ω - b' ω‖ ∂P) * (∫ ω, ‖a' ω - c ω‖ ∂P) +
          (∫ ω, ‖c ω - c' ω‖ ∂P) * (∫ ω, ‖a' ω - b' ω‖ ∂P)) := by
  obtain ⟨hi₁, he₁⟩ := independent_norm_product (hai.sub hai') (hbi.sub hci) h₁
  obtain ⟨hi₂, he₂⟩ := independent_norm_product (hbi.sub hbi') (hai'.sub hci) h₂
  obtain ⟨hi₃, he₃⟩ := independent_norm_product (hci.sub hci') (hai'.sub hbi') h₃
  have hi := ((hi₁.add hi₂).add hi₃).const_mul 3
  have hm : Integrable (fun ω => ‖OracleTemplate.MedianGradient.median (a ω) (b ω) (c ω) -
      OracleTemplate.MedianGradient.median (a' ω) (b' ω) (c' ω)‖ ^ 2) P :=
    hi.mono' (((measurable_median ha hb hc).sub
      (measurable_median ha' hb' hc')).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, abs_sq, abs_norm, Pi.add_apply, Pi.sub_apply]
          using median_difference_norm_sq (a ω) (b ω) (c ω) (a' ω) (b' ω) (c' ω))
  refine ⟨hm, (integral_mono hm hi (fun ω =>
    median_difference_norm_sq (a ω) (b ω) (c ω) (a' ω) (b' ω) (c' ω))).trans_eq ?_⟩
  simp only [Pi.add_apply]
  rw [integral_const_mul, integral_add (by exact hi₁.add hi₂) (by exact hi₃),
    integral_add (by exact hi₁) (by exact hi₂), he₁, he₂, he₃]
  simp only [Pi.sub_apply]

lemma median_translate {d : ℕ} (a b c t : EuclideanSpace ℝ (Fin d)) :
    OracleTemplate.MedianGradient.median (a + t) (b + t) (c + t) =
      OracleTemplate.MedianGradient.median a b c + t := by
  ext i
  exact median3_translate (a i) (b i) (c i) (t i)

lemma median_integrable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsFiniteMeasure P] {a b c : Ω → EuclideanSpace ℝ (Fin d)}
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c)
    (hai : Integrable a P) (hbi : Integrable b P) (hci : Integrable c P)
    (hab : IndepFun a b P) (hbc : IndepFun b c P) (hca : IndepFun c a P) :
    Integrable (fun ω => OracleTemplate.MedianGradient.median (a ω) (b ω) (c ω)) P := by
  have h₂ := (median_second_moment ha hb hc hai hbi hci hab hbc hca).1
  exact ((memLp_two_iff_integrable_sq_norm
    (measurable_median ha hb hc).aestronglyMeasurable).mpr h₂).integrable one_le_two

lemma median_integral_zero {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsFiniteMeasure P] (a : Fin 3 → Ω → EuclideanSpace ℝ (Fin d))
    (ha : ∀ j, Measurable (a j)) (hai : ∀ j, Integrable (a j) P)
    (hi : iIndepFun a P)
    (hs : ∀ j i, IdentDistrib (fun ω => a j ω i) (fun ω => -a j ω i) P P) :
    ∫ ω, OracleTemplate.MedianGradient.median (a 0 ω) (a 1 ω) (a 2 ω) ∂P = 0 := by
  have hmi := median_integrable (ha 0) (ha 1) (ha 2) (hai 0) (hai 1) (hai 2)
    (hi.indepFun (by decide : (0 : Fin 3) ≠ 1))
    (hi.indepFun (by decide : (1 : Fin 3) ≠ 2))
    (hi.indepFun (by decide : (2 : Fin 3) ≠ 0))
  ext i
  have hproj := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).integral_comp_comm hmi
  change (∫ ω, OracleTemplate.MedianGradient.median (a 0 ω) (a 1 ω) (a 2 ω) ∂P) i = 0
  simp only [EuclideanSpace.coe_proj] at hproj
  rw [← hproj]
  exact median3_integral_zero (fun j ω => a j ω i)
    (hi.comp (fun _ => (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
      (fun _ => (EuclideanSpace.proj i).continuous.measurable)) (fun j => hs j i)

end LongTails.Proofs.MedianCoupling
