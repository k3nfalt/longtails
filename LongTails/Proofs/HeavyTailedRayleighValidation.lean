import LongTails.Proofs.HeavyTailedFreshProcess
import LongTails.Algorithms.HeavyTailedRayleighMedian
import LongTails.Proofs.Execution
import LongTails.Proofs.AdaptiveEntropicCenter
import LongTails.Proofs.AdaptiveEntropicMeasurable
import Mathlib.Probability.Moments.SubGaussian
import LongTails.Proofs.RobustSampleBlocks
import LongTails.Proofs.HeavyTailedSpectralMoments

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.HeavyTailedRayleighValidation

lemma bounded_majority_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P) (hbounded : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i, (∫ ω, X i ω ∂P) ≤ 1 / 4) :
    P.real {ω | (n : ℝ) / 2 ≤ ∑ i, X i ω} ≤ Real.exp (-(n : ℝ) / 8) := by
  let Y := fun i ω => X i ω - ∫ z, X i z ∂P
  have hY : iIndepFun Y P := hind.comp (fun i z => z - ∫ ω, X i ω ∂P)
    (fun _ => measurable_id.sub_const _)
  have hsg (i : Fin n) : HasSubgaussianMGF (Y i) (1 / 4) P := by
    have hh := hasSubgaussianMGF_of_mem_Icc (μ := P) (hX i).aemeasurable
      (Filter.Eventually.of_forall (hbounded i))
    norm_num only [sub_zero, nnnorm_one, one_div, inv_pow, one_pow] at hh
    convert hh using 1
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY
    (s := Finset.univ) (fun i _ => hsg i)
    (show 0 ≤ (n : ℝ) / 4 by positivity)
  have hsum : (∑ i, ∫ ω, X i ω ∂P) ≤ (n : ℝ) / 4 := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hmean i)
    simpa [div_eq_mul_inv] using hh
  have hsub : {ω | (n : ℝ) / 2 ≤ ∑ i, X i ω} ⊆
      {ω | (n : ℝ) / 4 ≤ ∑ i, Y i ω} := by
    intro ω hω
    change (n : ℝ) / 2 ≤ ∑ i, X i ω at hω
    change (n : ℝ) / 4 ≤ ∑ i, (X i ω - ∫ z, X i z ∂P)
    rw [Finset.sum_sub_distrib]
    linarith
  have hh := (measureReal_mono (μ := P) hsub).trans htail
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  convert hh using 1
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  field_simp
  ring


lemma moment_tail_probability {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → E} {p t K : ℝ} (hp : 0 ≤ p) (ht : 0 < t)
    (hi : Integrable (fun ω => ‖X ω‖ ^ p) P)
    (hb : (∫ ω, ‖X ω‖ ^ p ∂P) ≤ K) :
    P.real {ω | t < ‖X ω‖} ≤ K / t ^ p := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => Real.rpow_nonneg (norm_nonneg (X ω)) p)) hi (t ^ p)
  have hsub : {ω | t < ‖X ω‖} ⊆ {ω | t ^ p ≤ ‖X ω‖ ^ p} := by
    intro ω hω
    exact Real.rpow_le_rpow ht.le (le_of_lt hω) hp
  apply (le_div_iff₀ (Real.rpow_pos_of_pos ht p)).mpr
  have hh := mul_le_mul_of_nonneg_left (measureReal_mono (μ := P) hsub)
    (Real.rpow_nonneg ht.le p)
  nlinarith [hm.trans hb]


lemma countP_real_sum {α : Type*} (l : List α) (b : α → Bool) :
    (l.countP b : ℝ) = (l.map (fun x => if b x then (1 : ℝ) else 0)).sum := by
  induction l with
  | nil => simp
  | cons x l ih => cases hb : b x <;> simp [hb, ih, add_comm]

lemma scalar_median_accuracy (l : List ℝ) (μ R : ℝ)
    (hg : l.length < 2 * l.countP (fun x => decide (|x - μ| ≤ R))) :
    |(l.mergeSort (· ≤ ·)).getD (l.length / 2) 0 - μ| ≤ R := by
  have hp := List.mergeSort_perm l (· ≤ ·)
  have heq (x : ℝ) : (|x - μ| ≤ R) ↔ (μ - R ≤ x ∧ x ≤ μ + R) := by
    rw [abs_le]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hc := hp.countP_eq (fun x => decide (μ - R ≤ x ∧ x ≤ μ + R))
  have hh := OracleTemplate.AdaptiveHeavyTailSimplex.sorted_middle_interval
    (l.mergeSort (· ≤ ·)) List.sortedLE_mergeSort (μ - R) (μ + R)
    (by
      rw [List.length_mergeSort, hc]
      simpa only [← heq] using hg)
  simp only [List.length_mergeSort] at hh
  exact abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩

lemma median_bad_half {n : ℕ} (Y : Fin n → ℝ) (μ R : ℝ)
    (hbad : R < |((List.ofFn Y).mergeSort (· ≤ ·)).getD (n / 2) 0 - μ|) :
    (n : ℝ) / 2 ≤ ∑ i, if R < |Y i - μ| then (1 : ℝ) else 0 := by
  classical
  let l := List.ofFn Y
  let good := fun x : ℝ => decide (|x - μ| ≤ R)
  have hnot : ¬l.length < 2 * l.countP good := by
    intro h
    have hh := scalar_median_accuracy l μ R h
    simp only [l, List.length_ofFn] at hh
    linarith
  have hc := List.length_eq_countP_add_countP good (l := l)
  have hc' : l.length = l.countP good + l.countP (fun x => !good x) := by
    have he : (fun x => decide (¬good x = true)) = (fun x => !good x) := by
      funext x
      cases good x <;> rfl
    rw [he] at hc
    exact hc
  have hb : l.length ≤ 2 * l.countP (fun x => !good x) := by omega
  have hr : (l.length : ℝ) ≤ 2 * (l.countP (fun x => !good x) : ℝ) := by exact_mod_cast hb
  rw [countP_real_sum] at hr
  simpa [l, good, List.map_ofFn, List.sum_ofFn, not_le] using (show
    (l.length : ℝ) / 2 ≤ (l.map (fun x => if !good x then (1 : ℝ) else 0)).sum by linarith)


lemma independent_median_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    (Y : Fin n → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (μ R : ℝ) (hb : ∀ i, P.real {ω | R < |Y i ω - μ|} ≤ 1 / 4) :
    P.real {ω | R < |((List.ofFn (fun i => Y i ω)).mergeSort (· ≤ ·)).getD (n / 2) 0 - μ|} ≤
      Real.exp (-(n : ℝ) / 8) := by
  classical
  let b : ℝ → ℝ := fun y => if R < |y - μ| then 1 else 0
  have hbm : Measurable b := Measurable.ite
    (measurableSet_lt measurable_const (continuous_abs.measurable.comp (measurable_id.sub_const μ)))
    measurable_const measurable_const
  let X := fun i ω => b (Y i ω)
  have hX (i : Fin n) : Measurable (X i) := hbm.comp (hY i)
  have hXi : iIndepFun X P := hind.comp (fun _ => b) (fun _ => hbm)
  have hXbounded (i : Fin n) (ω : Ω) : X i ω ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [X, b]
    split_ifs <;> norm_num
  have hXmean (i : Fin n) : (∫ ω, X i ω ∂P) ≤ 1 / 4 := by
    have heq : X i = {ω | R < |Y i ω - μ|}.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      rfl
    have hset : MeasurableSet {ω | R < |Y i ω - μ|} :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp ((hY i).sub_const μ))
    rw [heq]
    change (∫ ω, {ω | R < |Y i ω - μ|}.indicator 1 ω ∂P) ≤ 1 / 4
    rw [integral_indicator_one hset]
    exact hb i
  have hh := bounded_majority_probability P hn X hX hXi hXbounded hXmean
  apply (measureReal_mono (μ := P) ?_).trans hh
  intro ω hω
  exact median_bad_half (fun i => Y i ω) μ R hω


lemma small_moment_bad_probability {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → E} {p γ : ℝ} (hp : 1 ≤ p) (hγ : 0 < γ)
    (hi : Integrable (fun ω => ‖X ω‖ ^ p) P)
    (hb : (∫ ω, ‖X ω‖ ^ p ∂P) ≤ (γ / 8) ^ p) :
    P.real {ω | γ / 2 < ‖X ω‖} ≤ 1 / 4 := by
  have hh := moment_tail_probability P (by linarith : 0 ≤ p)
    (show 0 < γ / 2 by positivity) hi hb
  have heq : (γ / 8) ^ p / (γ / 2) ^ p = (1 / 4 : ℝ) ^ p := by
    rw [← Real.div_rpow (by positivity : 0 ≤ γ / 8) (by positivity : 0 ≤ γ / 2)]
    congr 1
    field_simp
    ring
  rw [heq] at hh
  have hpow := Real.rpow_le_rpow_of_exponent_ge
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) ≤ 1) hp
  simpa only [Real.rpow_one] using hh.trans hpow


lemma rayleigh_indexed_values (values : ℕ → ℝ) (K : ℕ) :
    ((fun sc : List ℝ × ℕ => (values sc.2 :: sc.1, sc.2 + 1))^[K] ([], 0)) =
      (((List.range K).map values).reverse, K) := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [List.range_succ]


lemma execute_rayleigh_median
    (p : LongTails.Setups.HeavyTailedHessianVector.Params)
    (x v : LongTails.Setups.HeavyTailedHessianVector.Space p) (n m K : ℕ)
    (g : LongTails.Setups.HeavyTailedHessianVector.Space p → p.Ω →
      LongTails.Setups.HeavyTailedHessianVector.Space p)
    (H : LongTails.Setups.HeavyTailedHessianVector.Space p → p.Ω →
      LongTails.Setups.HeavyTailedHessianVector.Space p →L[ℝ]
        LongTails.Setups.HeavyTailedHessianVector.Space p)
    (P : ProbabilityMeasure (ℕ → p.Ω)) (ξ : ℕ → p.Ω) :
    let O : OracleTemplate.Oracle
      (LongTails.Setups.HeavyTailedHessianVector.Space p ×
        Option (LongTails.Setups.HeavyTailedHessianVector.Space p))
      (LongTails.Setups.HeavyTailedHessianVector.Space p) :=
      { Seed := fun _ => p.Ω
        law := P
        answer := fun _ (_, y, w) ω => match w with | none => g y ω | some u => H y ω u }
    OracleTemplate.execute O (LongTails.Algorithms.HeavyTailedRayleighMedian.algorithm p x v n m)
      (fun _ => K) () ξ =
      LongTails.Algorithms.HeavyTailedRayleighMedian.output n m
        ((List.range K).map (fun k => inner ℝ v (H x (ξ k) v))) := by
  intro O
  let A := LongTails.Algorithms.HeavyTailedRayleighMedian.algorithm p x v n m
  have hh := OracleTemplate.execute_indexed_of_answer O A K () ξ
    (fun k (_, y, w) => match w with | none => g y (ξ k) | some u => H y (ξ k) u)
    (by intro history query; rfl)
  rw [hh]
  change LongTails.Algorithms.HeavyTailedRayleighMedian.output n m
    (((fun sc : List ℝ × ℕ => (inner ℝ v (H x (ξ sc.2) v) :: sc.1, sc.2 + 1))^[K]
      ([], 0)).1.reverse) = _
  rw [rayleigh_indexed_values (fun k => inner ℝ v (H x (ξ k) v)) K]
  simp


lemma batch_count_tuning {p σ e : ℝ} (hp : 1 < p) (hσ : 0 ≤ σ) (he : 0 < e) :
    let n := max 1 ⌈(6 * σ ^ p / e ^ p) ^ (1 / (p - 1))⌉₊
    0 < n ∧ 6 * σ ^ p / (n : ℝ) ^ (p - 1) ≤ e ^ p := by
  intro n
  have hn : 1 ≤ n := Nat.le_max_left _ _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 ≤ 6 * σ ^ p / e ^ p := by positivity
  have hbase : (6 * σ ^ p / e ^ p) ^ (1 / (p - 1)) ≤ (n : ℝ) := by
    exact (Nat.le_ceil _).trans (by
      exact_mod_cast (Nat.le_max_right 1 ⌈(6 * σ ^ p / e ^ p) ^ (1 / (p - 1))⌉₊))
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg ha _) hbase (by linarith : 0 ≤ p - 1)
  rw [← Real.rpow_mul ha, one_div_mul_cancel (by linarith : p - 1 ≠ 0), Real.rpow_one] at hpow
  refine ⟨hn, ?_⟩
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hn0 (p - 1))).mpr
  have hh := (div_le_iff₀ (Real.rpow_pos_of_pos he p)).mp hpow
  nlinarith

lemma finite_batch_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (e : Ω → ℝ) (he : Measurable e)
    {p κ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : Integrable e P) (hm : (∫ ω, e ω ∂P) = 0)
    (hpi : Integrable (fun ω => ‖e ω‖ ^ p) P)
    (hb : (∫ ω, ‖e ω‖ ^ p ∂P) ≤ κ) (n : ℕ) (hn : 0 < n) :
    Integrable (fun η : Fin n → Ω => ‖(n : ℝ)⁻¹ * ∑ k : Fin n, e (η k)‖ ^ p)
      (Measure.pi fun _ : Fin n => P) ∧
    (∫ η : Fin n → Ω, ‖(n : ℝ)⁻¹ * ∑ k : Fin n, e (η k)‖ ^ p
      ∂Measure.pi (fun _ : Fin n => P)) ≤ 6 * κ / (n : ℝ) ^ (p - 1) := by
  let F := fun η : Fin n → Ω => ‖(n : ℝ)⁻¹ * ∑ k : Fin n, e (η k)‖ ^ p
  have hF : Measurable F := by
    dsimp only [F]
    fun_prop
  have hprefix := OracleTemplate.StochasticGeneralized.prefix_preserving P n
  have hh := HeavyTailedFreshProcess.iid_batch_moment P he hp hp2 hi hm hpi hb n hn
  have heq (ξ : ℕ → Ω) : F (fun k => ξ k) =
      ‖(n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, e (ξ k)‖ ^ p := by
    simp only [F, Fin.sum_univ_eq_sum_range (fun k => e (ξ k)), smul_eq_mul]
  have hfi : Integrable (fun ξ : ℕ → Ω => F (fun k => ξ k))
      (Measure.infinitePi fun _ : ℕ => P) := by simpa only [heq] using hh.1
  refine ⟨(hprefix.integrable_comp hF.aestronglyMeasurable).mp hfi, ?_⟩
  change (∫ η, F η ∂Measure.pi (fun _ : Fin n => P)) ≤ _
  rw [← hprefix.map_eq, integral_map hprefix.measurable.aemeasurable hF.aestronglyMeasurable]
  simpa only [heq] using hh.2

lemma grouped_median_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n m : ℕ) (hm : 0 < m)
    (A : (Fin n → Ω) → ℝ) (hA : Measurable A) (μ R : ℝ)
    (hb : (Measure.pi fun _ : Fin n => P).real {η | R < |A η - μ|} ≤ 1 / 4) :
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => P).real
      {η | R < |((List.ofFn (fun j : Fin m => A (η j))).mergeSort (· ≤ ·)).getD (m / 2) 0 - μ|} ≤
      Real.exp (-(m : ℝ) / 8) := by
  let Q := Measure.pi fun _ : Fin n => P
  have hY (j : Fin m) : Measurable (fun η : Fin m → Fin n → Ω => A (η j)) :=
    hA.comp (measurable_pi_apply j)
  have hind : iIndepFun (fun (j : Fin m) (η : Fin m → Fin n → Ω) => A (η j))
      (Measure.pi fun _ : Fin m => Q) := iIndepFun_pi (fun _ => hA.aemeasurable)
  apply independent_median_probability (Measure.pi fun _ : Fin m => Q) hm _ hY hind μ R
  intro j
  have hset : MeasurableSet {η | R < |A η - μ|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hA.sub_const μ))
  have he := (measurePreserving_eval (fun _ : Fin m => Q) j).measure_preimage hset.nullMeasurableSet
  change (Measure.pi fun _ : Fin m => Q).real ((fun η => η j) ⁻¹' {η | R < |A η - μ|}) ≤ _
  rw [measureReal_def, he]
  exact hb

lemma stream_median_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n m : ℕ) (hm : 0 < m)
    (A : (Fin n → Ω) → ℝ) (hA : Measurable A) (μ R : ℝ)
    (hb : (Measure.pi fun _ : Fin n => P).real {η | R < |A η - μ|} ≤ 1 / 4) :
    (Measure.infinitePi fun _ : ℕ => P).real
      {ξ | R < |((List.ofFn (fun j : Fin m => A (fun k : Fin n => ξ (j.val * n + k.val)))).mergeSort
        (· ≤ ·)).getD (m / 2) 0 - μ|} ≤ Real.exp (-(m : ℝ) / 8) := by
  let V := fun η : Fin m → Fin n → Ω =>
    ((List.ofFn (fun j : Fin m => A (η j))).mergeSort (· ≤ ·)).getD (m / 2) 0
  have hV : Measurable V :=
    (OracleTemplate.AdaptiveList.measurable_getD (m / 2) 0).comp
      (OracleTemplate.AdaptiveHeavyTailSimplex.measurable_mergeSort.comp
        ((OracleTemplate.AdaptiveList.measurable_ofFn m).comp
          (measurable_pi_iff.mpr (fun j => hA.comp (measurable_pi_apply j)))))
  have hset : MeasurableSet {η | R < |V η - μ|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hV.sub_const μ))
  have he := (OracleTemplate.RobustGradient.stream_groups_preserving P m n).measure_preimage
    hset.nullMeasurableSet
  have ht := grouped_median_probability P n m hm A hA μ R hb
  change (Measure.infinitePi fun _ : ℕ => P).real
    ((fun ξ (j : Fin m) (k : Fin n) => ξ (j.val * n + k.val)) ⁻¹' {η | R < |V η - μ|}) ≤ _
  rw [measureReal_def, he]
  exact ht

lemma finite_mean_centered {Ω : Type*} (a : Ω → ℝ) (μ : ℝ)
    (n : ℕ) (hn : 0 < n) (η : Fin n → Ω) :
    (n : ℝ)⁻¹ * (∑ k : Fin n, a (η k)) - μ =
      (n : ℝ)⁻¹ * ∑ k : Fin n, (a (η k) - μ) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma finite_mean_bad_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (a : Ω → ℝ) (ha : Measurable a)
    {p κ μ γ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hγ : 0 < γ)
    (hi : Integrable a P) (hm : (∫ ω, a ω ∂P) = μ)
    (hpi : Integrable (fun ω => ‖a ω - μ‖ ^ p) P)
    (hb : (∫ ω, ‖a ω - μ‖ ^ p ∂P) ≤ κ) (n : ℕ) (hn : 0 < n)
    (htune : 6 * κ / (n : ℝ) ^ (p - 1) ≤ (γ / 8) ^ p) :
    (Measure.pi fun _ : Fin n => P).real
      {η | γ / 2 < |(n : ℝ)⁻¹ * ∑ k : Fin n, a (η k) - μ|} ≤ 1 / 4 := by
  have hemean : (∫ ω, a ω - μ ∂P) = 0 := by
    rw [integral_sub hi (integrable_const _), hm]
    simp
  have hh := finite_batch_moment P (fun ω => a ω - μ) (ha.sub_const μ) hp hp2
    (hi.sub (integrable_const _)) hemean hpi hb n hn
  have heq (η : Fin n → Ω) := finite_mean_centered a μ n hn η
  have htail := small_moment_bad_probability (Measure.pi fun _ : Fin n => P) hp hγ hh.1 (hh.2.trans htune)
  simpa only [← heq, Real.norm_eq_abs] using htail

lemma groupMean_indexed (values : ℕ → ℝ) (n m : ℕ) (j : Fin m) :
    LongTails.Algorithms.HeavyTailedRayleighMedian.groupMean n
      ((List.range (n * m)).map values) j.val =
      (n : ℝ)⁻¹ * ∑ k : Fin n, values (j.val * n + k.val) := by
  unfold LongTails.Algorithms.HeavyTailedRayleighMedian.groupMean
  rw [Fin.sum_univ_eq_sum_range (fun k => values (j.val * n + k))]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n := Finset.mem_range.mp hk
  have hj := Nat.mul_le_mul_right n (Nat.succ_le_of_lt j.isLt)
  have hindex : j.val * n + k < n * m := by
    rw [Nat.succ_mul] at hj
    nlinarith
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hindex,
    Option.map_some, Option.getD_some]

lemma output_indexed_groups (values : ℕ → ℝ) (n m : ℕ) :
    LongTails.Algorithms.HeavyTailedRayleighMedian.output n m
      ((List.range (n * m)).map values) =
      ((List.ofFn (fun j : Fin m => (n : ℝ)⁻¹ * ∑ k : Fin n,
        values (j.val * n + k.val))).mergeSort (· ≤ ·)).getD (m / 2) 0 := by
  unfold LongTails.Algorithms.HeavyTailedRayleighMedian.output
  simp only [groupMean_indexed]

lemma scalar_output_probability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (a : Ω → ℝ) (ha : Measurable a)
    {p κ μ γ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hγ : 0 < γ)
    (hi : Integrable a P) (hm : (∫ ω, a ω ∂P) = μ)
    (hpi : Integrable (fun ω => ‖a ω - μ‖ ^ p) P)
    (hb : (∫ ω, ‖a ω - μ‖ ^ p ∂P) ≤ κ) (n m : ℕ) (hn : 0 < n) (hmpos : 0 < m)
    (htune : 6 * κ / (n : ℝ) ^ (p - 1) ≤ (γ / 8) ^ p) :
    (Measure.infinitePi fun _ : ℕ => P).real
      {ξ | γ / 2 < |LongTails.Algorithms.HeavyTailedRayleighMedian.output n m
        ((List.range (n * m)).map (fun k => a (ξ k))) - μ|} ≤ Real.exp (-(m : ℝ) / 8) := by
  have hA : Measurable (fun η : Fin n → Ω => (n : ℝ)⁻¹ * ∑ k : Fin n, a (η k)) := by fun_prop
  have hblock := finite_mean_bad_probability P a ha hp hp2 hγ hi hm hpi hb n hn htune
  have ht := stream_median_probability P n m hmpos _ hA μ (γ / 2) hblock
  simpa only [output_indexed_groups] using ht

lemma rayleigh_scalar_moments {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → E →L[ℝ] E) (A : E →L[ℝ] E) (v : E) (hv : ‖v‖ = 1)
    {p κ : ℝ} (hp : 0 ≤ p)
    (hi : Integrable (fun ω => B ω v) P) (hm : (∫ ω, B ω v ∂P) = A v)
    (hpi : Integrable (fun ω => ‖B ω v - A v‖ ^ p) P)
    (hb : (∫ ω, ‖B ω v - A v‖ ^ p ∂P) ≤ κ) :
    Integrable (fun ω => inner ℝ v (B ω v)) P ∧
    (∫ ω, inner ℝ v (B ω v) ∂P) = inner ℝ v (A v) ∧
    Integrable (fun ω => ‖inner ℝ v (B ω v) - inner ℝ v (A v)‖ ^ p) P ∧
    (∫ ω, ‖inner ℝ v (B ω v) - inner ℝ v (A v)‖ ^ p ∂P) ≤ κ := by
  have hemean : (∫ ω, B ω v - A v ∂P) = 0 := by
    rw [integral_sub hi (integrable_const _), hm]
    simp
  have hh := HeavyTailedSpectralMoments.projection_moment_control (P := P) v hp
    (by norm_num : (0 : ℝ) ≤ 1) hv.le (hi.sub (integrable_const _)) hemean hpi hb
  refine ⟨hi.const_inner v, ?_, ?_, ?_⟩
  · rw [integral_inner hi, hm]
  · simpa only [Pi.sub_apply, inner_sub_right] using hh.2.2.1
  · simpa only [Pi.sub_apply, inner_sub_right, Real.one_rpow, one_mul] using hh.2.2.2

lemma actual_rayleigh_probability
    (p : LongTails.Setups.HeavyTailedHessianVector.Params)
    (x v : LongTails.Setups.HeavyTailedHessianVector.Space p) (hv : ‖v‖ = 1)
    (g : LongTails.Setups.HeavyTailedHessianVector.Space p → p.Ω →
      LongTails.Setups.HeavyTailedHessianVector.Space p)
    (H : LongTails.Setups.HeavyTailedHessianVector.Space p → p.Ω →
      LongTails.Setups.HeavyTailedHessianVector.Space p →L[ℝ]
        LongTails.Setups.HeavyTailedHessianVector.Space p)
    (A : LongTails.Setups.HeavyTailedHessianVector.Space p →L[ℝ]
      LongTails.Setups.HeavyTailedHessianVector.Space p) (hH : Measurable (H x))
    (P0 : ProbabilityMeasure p.Ω) (P : ProbabilityMeasure (ℕ → p.Ω))
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k (ξ : ℕ → p.Ω) => ξ k) (P0 : Measure p.Ω) (P : Measure (ℕ → p.Ω)))
    (hp : 1 ≤ p.p) (hp2 : p.p ≤ 2) (γ : ℝ) (hγ : 0 < γ)
    (hi : Integrable (fun ω => H x ω v) (P0 : Measure p.Ω))
    (hm : (∫ ω, H x ω v ∂(P0 : Measure p.Ω)) = A v)
    (hpi : Integrable (fun ω => ‖H x ω v - A v‖ ^ p.p) (P0 : Measure p.Ω))
    (hb : (∫ ω, ‖H x ω v - A v‖ ^ p.p ∂(P0 : Measure p.Ω)) ≤ p.σh ^ p.p)
    (n m : ℕ) (hn : 0 < n) (hmpos : 0 < m)
    (htune : 6 * p.σh ^ p.p / (n : ℝ) ^ (p.p - 1) ≤ (γ / 8) ^ p.p) :
    let O : OracleTemplate.Oracle
      (LongTails.Setups.HeavyTailedHessianVector.Space p ×
        Option (LongTails.Setups.HeavyTailedHessianVector.Space p))
      (LongTails.Setups.HeavyTailedHessianVector.Space p) :=
      { Seed := fun _ => p.Ω
        law := P
        answer := fun _ (_, y, w) ω => match w with | none => g y ω | some u => H y ω u }
    (P : Measure (ℕ → p.Ω)).real {ξ | γ / 2 <
      |OracleTemplate.execute O (LongTails.Algorithms.HeavyTailedRayleighMedian.algorithm p x v n m)
        (fun _ => n * m) () ξ - inner ℝ v (A v)|} ≤ Real.exp (-(m : ℝ) / 8) := by
  intro O
  have hlaw : (P : Measure (ℕ → p.Ω)) = Measure.infinitePi (fun _ : ℕ => (P0 : Measure p.Ω)) := by
    have hh := hIID.stream_law.map_eq
    change Measure.map id (P : Measure (ℕ → p.Ω)) = _ at hh
    simpa only [Measure.map_id] using hh
  have hscalar := rayleigh_scalar_moments (P0 : Measure p.Ω) (H x) A v hv (by linarith : 0 ≤ p.p)
    hi hm hpi hb
  have hmeas : Measurable (fun ω => inner ℝ v (H x ω v)) := by fun_prop
  have ht := scalar_output_probability (P0 : Measure p.Ω) _ hmeas hp hp2 hγ
    hscalar.1 hscalar.2.1 hscalar.2.2.1 hscalar.2.2.2 n m hn hmpos htune
  have heq (ξ : ℕ → p.Ω) :
      OracleTemplate.execute O (LongTails.Algorithms.HeavyTailedRayleighMedian.algorithm p x v n m)
        (fun _ => n * m) () ξ = LongTails.Algorithms.HeavyTailedRayleighMedian.output n m
          ((List.range (n * m)).map (fun k => inner ℝ v (H x (ξ k) v))) :=
    execute_rayleigh_median p x v n m (n * m) g H P ξ
  simp only [heq, hlaw]
  exact ht

lemma validation_group_tuning (R : ℕ) (hR : 0 < R) (δ : ℝ) (hδ : 0 < δ) :
    Real.exp (-((2 * ⌈4 * Real.log (2 * R / δ)⌉₊ + 1 : ℕ) : ℝ) / 8) ≤ δ / (2 * R) := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hceil := Nat.le_ceil (4 * Real.log (2 * R / δ))
  have hexponent : -((2 * ⌈4 * Real.log (2 * R / δ)⌉₊ + 1 : ℕ) : ℝ) / 8 ≤
      -Real.log (2 * R / δ) := by
    push_cast
    linarith
  have he := Real.exp_le_exp.mpr hexponent
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 2 * (R : ℝ) / δ)] at he
  simpa only [inv_div] using he

end LongTails.Proofs.HeavyTailedRayleighValidation
