import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import LongTails.Setups.HeavyTailedMarkovSmoothAndConvex
import LongTails.Setups.PolynomialMixingHeavyTailedConvex
import LongTails.Includes
import LongTails.TemplateLowerBound
import LongTails.Proofs.HeavyTailedMarkovLaw
import LongTails.Proofs.ExecutionHistory

namespace LongTails.Proofs.PolynomialMixingLowerBound

open MeasureTheory ProbabilityTheory unitInterval
open scoped ENNReal
open Function Preorder

noncomputable def refreshKernel {Ω : Type*} [MeasurableSpace Ω]
    (π : ProbabilityMeasure Ω) (r : unitInterval) : Kernel Ω Ω where
  toFun z := toNNReal (σ r) • Measure.dirac z + toNNReal r • (π : Measure Ω)
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.add_apply, Measure.smul_apply]
    exact (measurable_const.mul ((Measure.measurable_coe hs).comp Measure.measurable_dirac)).add measurable_const

instance refreshKernel_isMarkov {Ω : Type*} [MeasurableSpace Ω]
    (π : ProbabilityMeasure Ω) (r : unitInterval) : IsMarkovKernel (refreshKernel π r) where
  isProbabilityMeasure z := ⟨by
    simp [refreshKernel, Measure.add_apply, Measure.smul_apply, ← ENNReal.coe_add]⟩

lemma refreshKernel_comp_probability {Ω : Type*} [MeasurableSpace Ω]
    (π μ : ProbabilityMeasure Ω) (r : unitInterval) :
    refreshKernel π r ∘ₘ (μ : Measure Ω) =
      toNNReal (σ r) • (μ : Measure Ω) + toNNReal r • (π : Measure Ω) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [refreshKernel, Kernel.coe_mk, Measure.add_apply, Measure.smul_apply]
  change (∫⁻ z, (toNNReal (σ r) : ℝ≥0∞) * Measure.dirac z s +
    (toNNReal r : ℝ≥0∞) * (π : Measure Ω) s ∂(μ : Measure Ω)) =
    (toNNReal (σ r) : ℝ≥0∞) * (μ : Measure Ω) s +
    (toNNReal r : ℝ≥0∞) * (π : Measure Ω) s
  rw [lintegral_add_left]
  · rw [lintegral_const_mul]
    · have hid : (∫⁻ z, Measure.dirac z s ∂(μ : Measure Ω)) = (μ : Measure Ω) s := by
        simp only [Measure.dirac_apply' _ hs]
        simpa using lintegral_indicator_one hs
      rw [hid]
      simp
    · exact ((Measure.measurable_coe hs).comp Measure.measurable_dirac)
  · exact measurable_const.mul ((Measure.measurable_coe hs).comp Measure.measurable_dirac)

lemma refreshKernel_stationary {Ω : Type*} [MeasurableSpace Ω]
    (π : ProbabilityMeasure Ω) (r : unitInterval) :
    refreshKernel π r ∘ₘ (π : Measure Ω) = (π : Measure Ω) := by
  rw [refreshKernel_comp_probability, ← add_smul]
  simp

lemma refreshKernel_pow_markov {Ω : Type*} [MeasurableSpace Ω]
    (π : ProbabilityMeasure Ω) (r : unitInterval) (n : ℕ) :
    IsMarkovKernel (refreshKernel π r ^ n) := by
  induction n with
  | zero => change IsMarkovKernel (Kernel.id); infer_instance
  | succ n ih =>
    let :=  ih
    rw [pow_succ']
    change IsMarkovKernel (refreshKernel π r ∘ₖ (refreshKernel π r ^ n))
    infer_instance

lemma refreshKernel_pow_succ {Ω : Type*} [MeasurableSpace Ω]
    (π : ProbabilityMeasure Ω) (r : unitInterval) (n : ℕ) (z : Ω) :
    (refreshKernel π r ^ (n + 1)) z =
      toNNReal (σ r) • (refreshKernel π r ^ n) z + toNNReal r • (π : Measure Ω) := by
  let :=  refreshKernel_pow_markov π r n
  rw [pow_succ']
  exact refreshKernel_comp_probability π ⟨(refreshKernel π r ^ n) z, inferInstance⟩ r

lemma refreshKernel_pow_real {Ω : Type*} [MeasurableSpace Ω]
    (π : ProbabilityMeasure Ω) (r : unitInterval) (n : ℕ) (z : Ω) (s : Set Ω) :
    ((refreshKernel π r ^ n) z).real s =
      (1 - (r : ℝ)) ^ n * (Measure.dirac z).real s +
      (1 - (1 - (r : ℝ)) ^ n) * (π : Measure Ω).real s := by
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, sub_self, zero_mul, add_zero]
    rfl
  | succ n ih =>
    let := refreshKernel_pow_markov π r n
    rw [refreshKernel_pow_succ, measureReal_add_apply,
      measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply, ih]
    simp only [coe_toNNReal, coe_symm_eq, pow_succ]
    ring

lemma refreshKernel_pow_deviation {Ω : Type*} [MeasurableSpace Ω]
    (π : ProbabilityMeasure Ω) (r : unitInterval) (n : ℕ) (z : Ω) (s : Set Ω) :
    |((refreshKernel π r ^ n) z).real s - (π : Measure Ω).real s| =
      (1 - (r : ℝ)) ^ n * |(Measure.dirac z).real s - (π : Measure Ω).real s| := by
  rw [refreshKernel_pow_real]
  have heq : (1 - (r : ℝ)) ^ n * (Measure.dirac z).real s +
      (1 - (1 - (r : ℝ)) ^ n) * (π : Measure Ω).real s - (π : Measure Ω).real s =
      (1 - (r : ℝ)) ^ n * ((Measure.dirac z).real s - (π : Measure Ω).real s) := by ring
  rw [heq, abs_mul, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr r.2.2) n)]

lemma bernoulli_deviation_first {Ω : Type*} [MeasurableSpace Ω]
    (a b : Ω) (p : unitInterval) (s : Set Ω) (hs : MeasurableSet s) :
    |(Measure.dirac a).real s - (bernoulliMeasure a b p).real s| ≤ 1 - (p : ℝ) := by
  classical
  rw [bernoulliMeasure_real_apply p hs]
  simp only [measureReal_def, Measure.dirac_apply' _ hs, coe_toNNReal, coe_symm_eq]
  split_ifs <;> simp_all [abs_of_nonneg (sub_nonneg.mpr p.2.2), abs_of_nonpos (sub_nonpos.mpr p.2.2)]
  all_goals linarith [p.2.1, p.2.2]

lemma bernoulli_deviation_second {Ω : Type*} [MeasurableSpace Ω]
    (a b : Ω) (p : unitInterval) (s : Set Ω) (hs : MeasurableSet s) :
    |(Measure.dirac b).real s - (bernoulliMeasure a b p).real s| ≤ (p : ℝ) := by
  classical
  rw [bernoulliMeasure_real_apply p hs]
  simp only [measureReal_def, Measure.dirac_apply' _ hs, coe_toNNReal, coe_symm_eq]
  split_ifs <;> simp_all [abs_of_nonneg p.2.1]
  all_goals linarith [p.2.1, p.2.2]

lemma refresh_bernoulli_mixing_first {Ω : Type} [MeasurableSpace Ω]
    (a b : Ω) (p r : unitInterval) (n : ℕ) :
    LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.mixingDistance
      (refreshKernel ⟨bernoulliMeasure a b p, inferInstance⟩ r)
      ⟨bernoulliMeasure a b p, inferInstance⟩ n a ≤
      (1 - (r : ℝ)) ^ n * (1 - (p : ℝ)) := by
  apply ciSup_le
  intro s
  exact (refreshKernel_pow_deviation (⟨bernoulliMeasure a b p, inferInstance⟩ : ProbabilityMeasure Ω)
    r n a s.val).le.trans (mul_le_mul_of_nonneg_left
      (bernoulli_deviation_first a b p s.val s.property)
      (pow_nonneg (sub_nonneg.mpr r.2.2) n))

lemma refresh_bernoulli_mixing_second {Ω : Type} [MeasurableSpace Ω]
    (a b : Ω) (p r : unitInterval) (n : ℕ) :
    LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.mixingDistance
      (refreshKernel ⟨bernoulliMeasure a b p, inferInstance⟩ r)
      ⟨bernoulliMeasure a b p, inferInstance⟩ n b ≤
      (1 - (r : ℝ)) ^ n * (p : ℝ) := by
  apply ciSup_le
  intro s
  exact (refreshKernel_pow_deviation (⟨bernoulliMeasure a b p, inferInstance⟩ : ProbabilityMeasure Ω)
    r n b s.val).le.trans (mul_le_mul_of_nonneg_left
      (bernoulli_deviation_second a b p s.val s.property)
      (pow_nonneg (sub_nonneg.mpr r.2.2) n))

lemma ae_dirac_eq_of_measurable_singleton {Ω : Type*} [MeasurableSpace Ω]
    (a : Ω) (ha : MeasurableSet ({a} : Set Ω)) :
    ∀ᵐ z ∂Measure.dirac a, z = a := by
  exact (ae_dirac_iff ha).2 rfl

lemma integrable_two_atoms {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] (a b : Ω) (ha : MeasurableSet ({a} : Set Ω))
    (hb : MeasurableSet ({b} : Set Ω)) (p : unitInterval) (f : Ω → F) :
    Integrable f (bernoulliMeasure a b p) := by
  have hi (z : Ω) (hz : MeasurableSet ({z} : Set Ω)) : Integrable f (Measure.dirac z) := by
    apply (integrable_const (f z)).congr
    filter_upwards [ae_dirac_eq_of_measurable_singleton z hz] with x hx
    simp [hx]
  rw [bernoulliMeasure_def]
  exact ((hi a ha).smul_measure_nnreal).add_measure ((hi b hb).smul_measure_nnreal)

lemma integral_two_atoms {Ω F : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (a b : Ω) (ha : MeasurableSet ({a} : Set Ω))
    (hb : MeasurableSet ({b} : Set Ω)) (p : unitInterval) (f : Ω → F) :
    (∫ z, f z ∂bernoulliMeasure a b p) = (p : ℝ) • f a + (1 - (p : ℝ)) • f b := by
  have hi (z : Ω) (hz : MeasurableSet ({z} : Set Ω)) : Integrable f (Measure.dirac z) := by
    apply (integrable_const (f z)).congr
    filter_upwards [ae_dirac_eq_of_measurable_singleton z hz] with x hx
    simp [hx]
  have he (z : Ω) (hz : MeasurableSet ({z} : Set Ω)) :
      (∫ x, f x ∂Measure.dirac z) = f z := by
    calc
      _ = ∫ _, f z ∂Measure.dirac z := integral_congr_ae (by
        filter_upwards [ae_dirac_eq_of_measurable_singleton z hz] with x hx
        simp [hx])
      _ = _ := by simp
  rw [bernoulliMeasure_def, integral_add_measure
    ((hi a ha).smul_measure_nnreal) ((hi b hb).smul_measure_nnreal)]
  simp [NNReal.smul_def, he a ha, he b hb]

lemma refresh_bernoulli_mixing_integrable {Ω : Type} [MeasurableSpace Ω]
    (a b : Ω) (ha : MeasurableSet ({a} : Set Ω)) (hb : MeasurableSet ({b} : Set Ω))
    (p r : unitInterval) (n : ℕ) :
    Integrable (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.mixingDistance
      (refreshKernel ⟨bernoulliMeasure a b p, inferInstance⟩ r)
      ⟨bernoulliMeasure a b p, inferInstance⟩ n) (bernoulliMeasure a b p) :=
  integrable_two_atoms a b ha hb p _

lemma refresh_bernoulli_average_mixing {Ω : Type} [MeasurableSpace Ω]
    (a b : Ω) (ha : MeasurableSet ({a} : Set Ω)) (hb : MeasurableSet ({b} : Set Ω))
    (p r : unitInterval) (n : ℕ) :
    (∫ z, LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.mixingDistance
      (refreshKernel ⟨bernoulliMeasure a b p, inferInstance⟩ r)
      ⟨bernoulliMeasure a b p, inferInstance⟩ n z ∂bernoulliMeasure a b p) ≤
      2 * (p : ℝ) * (1 - (p : ℝ)) * (1 - (r : ℝ)) ^ n := by
  rw [integral_two_atoms a b ha hb p]
  simp only [smul_eq_mul]
  have ha := mul_le_mul_of_nonneg_left (refresh_bernoulli_mixing_first a b p r n) p.2.1
  have hb := mul_le_mul_of_nonneg_left (refresh_bernoulli_mixing_second a b p r n)
    (sub_nonneg.mpr p.2.2)
  nlinarith

lemma polynomial_le_exponential (x β : ℝ) (hx : 0 ≤ x) (hβ : 0 ≤ β) :
    (1 + x) ^ β ≤ Real.exp (β * x) := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < 1 + x)]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)
  nlinarith [mul_le_mul_of_nonneg_right hlog hβ]

lemma refresh_decay_le_exponential (r : unitInterval) (n : ℕ) :
    (1 - (r : ℝ)) ^ n ≤ Real.exp (-(r : ℝ) * n) := by
  have h := Real.add_one_le_exp (-(r : ℝ))
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr r.2.2) (by linarith : 1 - (r : ℝ) ≤ Real.exp (-(r : ℝ))) n
  simpa [← Real.exp_nat_mul, mul_comm] using hp

lemma exponential_polynomial_envelope (a x β : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 ≤ x) (hβ : 0 ≤ β) :
    a ^ β * Real.exp (-β * a * x) ≤ (1 + x) ^ (-β) := by
  have hx1 : 0 < 1 + x := by linarith
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hx1, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_le_sub_one_of_pos (mul_pos ha hx1)
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt hx1)] at hlog
  have h : Real.log a + Real.log (1 + x) ≤ a * x := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h hβ]

lemma refresh_polynomial_envelope (p r : unitInterval) (a τ β : ℝ) (n : ℕ)
    (ha : 0 < a) (ha1 : a ≤ 1) (hτ : 0 < τ) (hβ : 0 ≤ β)
    (hp : 2 * (p : ℝ) ≤ a ^ β) (hr : (r : ℝ) = β * a / τ) :
    2 * (p : ℝ) * (1 - (p : ℝ)) * (1 - (r : ℝ)) ^ n ≤
      (1 + (n : ℝ) / τ) ^ (-β) := by
  have hc : 2 * (p : ℝ) * (1 - (p : ℝ)) ≤ a ^ β := by
    nlinarith [p.2.1, sq_nonneg (p : ℝ)]
  have hnon : 0 ≤ 2 * (p : ℝ) * (1 - (p : ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) p.2.1) (sub_nonneg.mpr p.2.2)
  have h1 := mul_le_mul_of_nonneg_left (refresh_decay_le_exponential r n) hnon
  have h2 := mul_le_mul_of_nonneg_right hc (Real.exp_pos (-(r : ℝ) * n)).le
  apply (h1.trans h2).trans
  rw [hr]
  have he : -(β * a / τ) * (n : ℝ) = -β * a * ((n : ℝ) / τ) := by ring
  rw [he]
  exact exponential_polynomial_envelope a ((n : ℝ) / τ) β ha ha1 (by positivity) hβ

lemma polynomial_scale_bounds (p β : ℝ) (hp : 0 < p) (hp1 : p ≤ 1 / 4)
    (hβ : 0 < β) :
    0 < (4 * p) ^ (1 / β) ∧ (4 * p) ^ (1 / β) ≤ 1 ∧
      2 * p ≤ ((4 * p) ^ (1 / β)) ^ β := by
  have hbase : 0 ≤ 4 * p := by positivity
  refine ⟨Real.rpow_pos_of_pos (by positivity) _, ?_, ?_⟩
  · exact Real.rpow_le_one hbase (by linarith) (by positivity)
  · rw [one_div, Real.rpow_inv_rpow hbase (ne_of_gt hβ)]
    linarith

lemma stationary_transition_probability {Ω : Type} [MeasurableSpace Ω]
    (κ : Kernel Ω Ω) [IsMarkovKernel κ] (π : ProbabilityMeasure Ω)
    (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω))
    (b : Ω) (hb : MeasurableSet ({b} : Set Ω)) (t : Set Ω) (ht : MeasurableSet t)
    (k : ℕ) :
    (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ π : Measure (ℕ → Ω))
      {ξ | ξ k = b ∧ ξ (k + 1) ∈ t} = (π : Measure Ω) {b} * κ b t := by
  let P : Measure (ℕ → Ω) := LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ π
  let B : Set (Finset.Iic k → Ω) := {h | h ⟨k, Finset.mem_Iic.mpr le_rfl⟩ = b}
  have hB : MeasurableSet B := by
    have hm : Measurable (fun h : Finset.Iic k → Ω => h ⟨k, Finset.mem_Iic.mpr le_rfl⟩) := by fun_prop
    exact hm hb
  have hj := OracleTemplate.HeavyTailedMarkovGradient.pathLaw_prefix_future κ π k 1
  have he := congrArg (fun μ : Measure ((Finset.Iic k → Ω) × Ω) => μ (B ×ˢ t)) hj
  rw [Measure.map_apply (by fun_prop) (hB.prod ht), Measure.compProd_apply_prod hB ht] at he
  simp only [pow_one, Kernel.comap_apply] at he
  change (∫⁻ h in B, κ (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩) t ∂P.map (frestrictLe k)) =
    P {ξ | ξ k = b ∧ ξ (k + 1) ∈ t} at he
  have hi : (∫⁻ h in B, κ (h ⟨k, Finset.mem_Iic.mpr le_rfl⟩) t ∂P.map (frestrictLe k)) =
      κ b t * P.map (frestrictLe k) B := by
    calc
      _ = ∫⁻ _ in B, κ b t ∂P.map (frestrictLe k) := by
        apply setLIntegral_congr_fun hB
        intro h hh
        exact congrArg (fun z => κ z t) hh
      _ = _ := by rw [setLIntegral_const]
  have hm : P.map (frestrictLe k) B = (π : Measure Ω) {b} := by
    rw [Measure.map_apply (by fun_prop) hB]
    have hm := OracleTemplate.HeavyTailedMarkovGradient.pathLaw_stationary_marginal κ π hπ k
    have hx := congrArg (fun μ : Measure Ω => μ {b}) hm
    rw [Measure.map_apply (by fun_prop) hb] at hx
    exact hx
  rw [hi, hm] at he
  exact he.symm.trans (mul_comm _ _)

noncomputable def twoAtomLaw {Ω : Type*} [MeasurableSpace Ω]
    (a b : Ω) (p : unitInterval) : ProbabilityMeasure Ω :=
  ⟨bernoulliMeasure a b p, inferInstance⟩

lemma refresh_exit_probability {Ω : Type} [MeasurableSpace Ω]
    (a b : Ω) (hab : a ≠ b) (hb : MeasurableSet ({b} : Set Ω))
    (p r : unitInterval) (k : ℕ) :
    (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
      (refreshKernel (twoAtomLaw a b p) r)
      (twoAtomLaw a b p) : Measure (ℕ → Ω)).real
      {ξ | ξ k = b ∧ ξ (k + 1) ≠ b} = (1 - (p : ℝ)) * (r : ℝ) * (p : ℝ) := by
  have he := stationary_transition_probability
    (refreshKernel (twoAtomLaw a b p) r)
    (twoAtomLaw a b p)
    (refreshKernel_stationary _ _) b hb ({b}ᶜ) hb.compl k
  have ha : a ∉ ({b} : Set Ω) := hab
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at he
  rw [measureReal_def, he]
  simp [twoAtomLaw, refreshKernel, Measure.add_apply, Measure.smul_apply,
    hb, ha, Measure.dirac_apply' _ hb.compl]
  change ((toNNReal r : ℝ≥0∞) * ((toNNReal (σ p) : ℝ≥0∞) * (toNNReal p : ℝ≥0∞))).toReal = _
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, coe_toNNReal, coe_symm_eq]
  ring

def commonPrefix {Ω : Type*} (b : Ω) (n : ℕ) : Set (ℕ → Ω) :=
  {ξ | ∀ k ≤ n, ξ k = b}

lemma measurableSet_commonPrefix {Ω : Type*} [MeasurableSpace Ω]
    (b : Ω) (hb : MeasurableSet ({b} : Set Ω)) (n : ℕ) :
    MeasurableSet (commonPrefix b n) := by
  unfold commonPrefix
  simpa only [Set.preimage, Set.mem_singleton_iff, Set.ofPred_forall] using
    (MeasurableSet.iInter fun (k : ℕ) => MeasurableSet.iInter fun (_ : k ≤ n) =>
      (measurable_pi_apply k) hb)

lemma commonPrefix_succ {Ω : Type*} (b : Ω) (n : ℕ) :
    commonPrefix b (n + 1) = commonPrefix b n ∩ {ξ | ξ (n + 1) = b} := by
  ext ξ
  simp only [commonPrefix, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h _ le_rfl⟩
  · rintro ⟨h, hn⟩ k hk
    by_cases he : k = n + 1
    · simpa [he] using hn
    · exact h k (by omega)

lemma first_exit_cover {Ω : Type*} (b : Ω) (n : ℕ) (ξ : ℕ → Ω)
    (h : ξ ∉ commonPrefix b n) :
    ξ 0 ≠ b ∨ ∃ k < n, ξ k = b ∧ ξ (k + 1) ≠ b := by
  classical
  induction n with
  | zero =>
    left
    simpa [commonPrefix] using h
  | succ n ih =>
    by_cases hc : ξ ∈ commonPrefix b n
    · right
      refine ⟨n, by omega, hc n le_rfl, ?_⟩
      intro hn
      exact h (by rw [commonPrefix_succ]; exact ⟨hc, hn⟩)
    · rcases ih hc with h0 | ⟨k, hk, he, hn⟩
      · exact Or.inl h0
      · exact Or.inr ⟨k, by omega, he, hn⟩

lemma commonPrefix_probability_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure (ℕ → Ω)) (b : Ω) (hb : MeasurableSet ({b} : Set Ω)) (n : ℕ) :
    1 - (P : Measure (ℕ → Ω)).real {ξ : ℕ → Ω | ξ 0 ≠ b} -
      ∑ k : Fin n, (P : Measure (ℕ → Ω)).real {ξ : ℕ → Ω | ξ k = b ∧ ξ (k + 1) ≠ b} ≤
      (P : Measure (ℕ → Ω)).real (commonPrefix b n) := by
  have hsub : (commonPrefix b n)ᶜ ⊆ {ξ : ℕ → Ω | ξ 0 ≠ b} ∪
      ⋃ k : Fin n, {ξ : ℕ → Ω | ξ k = b ∧ ξ (k + 1) ≠ b} := by
    intro ξ hξ
    rcases first_exit_cover b n ξ hξ with h0 | ⟨k, hk, he, hn⟩
    · exact Or.inl h0
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨k, hk⟩, he, hn⟩)
  have hu := (measureReal_mono (μ := (P : Measure (ℕ → Ω))) hsub).trans
    (measureReal_union_le _ _)
  have hs := measureReal_iUnion_fintype_le (μ := (P : Measure (ℕ → Ω)))
    (fun k : Fin n => {ξ : ℕ → Ω | ξ k = b ∧ ξ (k + 1) ≠ b})
  have hc := measureReal_add_measureReal_compl (μ := (P : Measure (ℕ → Ω)))
    (measurableSet_commonPrefix b hb n)
  have hone : (P : Measure (ℕ → Ω)).real Set.univ = 1 := by simp [measureReal_def]
  rw [hone] at hc
  linarith

lemma refresh_initial_noncommon {Ω : Type} [MeasurableSpace Ω]
    (a b : Ω) (hab : a ≠ b) (hb : MeasurableSet ({b} : Set Ω)) (p r : unitInterval) :
    (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
      (refreshKernel (twoAtomLaw a b p) r) (twoAtomLaw a b p) : Measure (ℕ → Ω)).real
      {ξ | ξ 0 ≠ b} = (p : ℝ) := by
  classical
  have hm := OracleTemplate.HeavyTailedMarkovGradient.pathLaw_map_zero
    (refreshKernel (twoAtomLaw a b p) r) (twoAtomLaw a b p)
  have he := congrArg (fun μ : Measure Ω => μ ({b}ᶜ)) hm
  rw [Measure.map_apply (by fun_prop) hb.compl] at he
  calc
    _ = ((twoAtomLaw a b p : Measure Ω) ({b}ᶜ)).toReal := congrArg ENNReal.toReal he
    _ = (p : ℝ) := by simp [twoAtomLaw, bernoulliMeasure_apply p hb.compl, hab]

lemma refresh_commonPrefix_lower {Ω : Type} [MeasurableSpace Ω]
    (a b : Ω) (hab : a ≠ b) (hb : MeasurableSet ({b} : Set Ω))
    (p r : unitInterval) (n : ℕ) :
    1 - (p : ℝ) - (n : ℝ) * (p : ℝ) * (r : ℝ) ≤
    (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
      (refreshKernel (twoAtomLaw a b p) r) (twoAtomLaw a b p) : Measure (ℕ → Ω)).real
      (commonPrefix b n) := by
  have h := commonPrefix_probability_lower
    (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
      (refreshKernel (twoAtomLaw a b p) r) (twoAtomLaw a b p)) b hb n
  rw [refresh_initial_noncommon a b hab hb p r] at h
  simp_rw [refresh_exit_probability a b hab hb p r] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hp := p.2.1
  have hr := r.2.1
  have hcross : 0 ≤ (n : ℝ) * (p : ℝ) * (p : ℝ) * (r : ℝ) := by positivity
  nlinarith

def sampledOracle {Query Reply : Type*} {Ω : Type} [MeasurableSpace Ω]
    (g : Query → Ω → Reply) (P : ProbabilityMeasure (ℕ → Ω)) :
    OracleTemplate.Oracle Query Reply where
  Seed := fun _ => Ω
  law := P
  answer := fun _ q z => g q.2 z

lemma execute_commonPrefix {Query Reply Output : Type*} {Ω : Type} [MeasurableSpace Ω]
    (g₁ g₂ : Query → Ω → Reply) (P₁ P₂ : ProbabilityMeasure (ℕ → Ω))
    (b : Ω) (hcommon : ∀ x, g₁ x b = g₂ x b)
    (A : OracleTemplate.Algorithm Query Reply Output) (seed : A.Seed)
    (ξ : ℕ → Ω) (N : ℕ) (hξ : ξ ∈ commonPrefix b N) :
    OracleTemplate.execute (sampledOracle g₁ P₁) A (fun _ => N) seed ξ =
      OracleTemplate.execute (sampledOracle g₂ P₂) A (fun _ => N) seed ξ := by
  have hist : ∀ k, k ≤ N →
      OracleTemplate.executeIndexedState (sampledOracle g₁ P₁) A seed ξ k =
        OracleTemplate.executeIndexedState (sampledOracle g₂ P₂) A seed ξ k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      simp only [OracleTemplate.executeIndexedState]
      rw [congrArg Prod.fst hp, congrArg Prod.snd hp]
      simp only [sampledOracle, OracleTemplate.executeIndexedState_length]
      rw [hξ k (by omega), hcommon]
  unfold OracleTemplate.execute
  erw [OracleTemplate.executeWithTrace_eq_executeIndexedState,
    OracleTemplate.executeWithTrace_eq_executeIndexedState, hist N le_rfl]

lemma refresh_commonPrefix_half {Ω : Type} [MeasurableSpace Ω]
    (a b : Ω) (hab : a ≠ b) (hb : MeasurableSet ({b} : Set Ω))
    (p r : unitInterval) (n : ℕ) (hp : (p : ℝ) ≤ 1 / 4)
    (hn : (n : ℝ) * (p : ℝ) * (r : ℝ) ≤ 1 / 4) :
    1 / 2 ≤
    (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
      (refreshKernel (twoAtomLaw a b p) r) (twoAtomLaw a b p) : Measure (ℕ → Ω)).real
      (commonPrefix b n) := by
  have h := refresh_commonPrefix_lower a b hab hb p r n
  linarith

lemma integral_pair_lower {W : Type*} [MeasurableSpace W]
    (P : ProbabilityMeasure W) (S : Set W) (hS : MeasurableSet S)
    (f g : W → ℝ) (hf : Integrable f (P : Measure W))
    (hg : Integrable g (P : Measure W))
    (hf0 : ∀ w, 0 ≤ f w) (hg0 : ∀ w, 0 ≤ g w)
    (c : ℝ) (hpair : ∀ w ∈ S, c ≤ f w + g w) :
    c * (P : Measure W).real S ≤ (∫ w, f w ∂(P : Measure W)) +
      (∫ w, g w ∂(P : Measure W)) := by
  classical
  have hi : Integrable (S.indicator (fun _ : W => c)) (P : Measure W) :=
    (integrable_const c).indicator hS
  have h := integral_mono hi (hf.add hg) (fun w => show
      S.indicator (fun _ : W => c) w ≤ f w + g w from by
    by_cases hw : w ∈ S
    · simpa only [Set.indicator_of_mem hw] using hpair w hw
    · simp only [Set.indicator_of_notMem hw]
      exact add_nonneg (hf0 w) (hg0 w))
  simp only [Pi.add_apply] at h
  rw [integral_add hf hg] at h
  simpa [integral_indicator hS, measureReal_def, mul_comm] using h

lemma execution_pair_lower {Q R O : Type*} {Ω : Type} [MeasurableSpace Ω]
    (g₁ g₂ : Q → Ω → R) (P : ProbabilityMeasure (ℕ → Ω))
    (b : Ω) (hb : MeasurableSet ({b} : Set Ω)) (hcommon : ∀ x, g₁ x b = g₂ x b)
    (A : OracleTemplate.Algorithm Q R O) (N : ℕ)
    (F₁ F₂ : O → ℝ) (hF₁ : ∀ x, 0 ≤ F₁ x) (hF₂ : ∀ x, 0 ≤ F₂ x)
    (c : ℝ) (hsep : ∀ x, c ≤ F₁ x + F₂ x)
    (hi₁ : Integrable (fun w : A.Seed × (ℕ → Ω) =>
      F₁ (OracleTemplate.execute (sampledOracle g₁ P) A (fun _ => N) w.1 w.2))
      ((A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω))))
    (hi₂ : Integrable (fun w : A.Seed × (ℕ → Ω) =>
      F₂ (OracleTemplate.execute (sampledOracle g₂ P) A (fun _ => N) w.1 w.2))
      ((A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω)))) :
    c * (P : Measure (ℕ → Ω)).real (commonPrefix b N) ≤
      (∫ w : A.Seed × (ℕ → Ω),
        F₁ (OracleTemplate.execute (sampledOracle g₁ P) A (fun _ => N) w.1 w.2)
        ∂((A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω)))) +
      (∫ w : A.Seed × (ℕ → Ω),
        F₂ (OracleTemplate.execute (sampledOracle g₂ P) A (fun _ => N) w.1 w.2)
        ∂((A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω)))) := by
  let joint : ProbabilityMeasure (A.Seed × (ℕ → Ω)) :=
    ⟨(A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω)), inferInstance⟩
  have h := integral_pair_lower joint (Set.univ ×ˢ commonPrefix b N)
    (MeasurableSet.univ.prod (measurableSet_commonPrefix b hb N))
    _ _ hi₁ hi₂ (fun w => hF₁ _) (fun w => hF₂ _) c (by
      intro w hw
      erw [execute_commonPrefix g₁ g₂ P P b hcommon A w.1 w.2 N hw.2]
      exact hsep _)
  change c * ((A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω))).real
    (Set.univ ×ˢ commonPrefix b N) ≤ _ at h
  rw [measureReal_prod_prod] at h
  simpa [measureReal_def, joint] using h

lemma sqrt_profile_derivative (h t : ℝ) (hh : 0 < h) :
    HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 + h ^ 2))
      (t / Real.sqrt (t ^ 2 + h ^ 2)) t := by
  have hp : 0 < t ^ 2 + h ^ 2 := by nlinarith [sq_nonneg t]
  have hd : HasDerivAt (fun x : ℝ => x ^ 2 + h ^ 2) (2 * t) t := by
    convert! ((hasDerivAt_id t).pow 2).add (hasDerivAt_const t (h ^ 2)) using 1; simp
  convert hd.sqrt (ne_of_gt hp) using 1; ring

lemma sqrt_profile_slope_bound (h t : ℝ) (hh : 0 < h) :
    |t / Real.sqrt (t ^ 2 + h ^ 2)| ≤ 1 := by
  have hp : 0 < t ^ 2 + h ^ 2 := by nlinarith [sq_nonneg t]
  rw [abs_div, abs_of_pos (Real.sqrt_pos.2 hp), div_le_one (Real.sqrt_pos.2 hp)]
  calc
    |t| = Real.sqrt (t ^ 2) := (Real.sqrt_sq_eq_abs t).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg h])

lemma sqrt_profile_slope_derivative (h t : ℝ) (hh : 0 < h) :
    HasDerivAt (fun x : ℝ => x / Real.sqrt (x ^ 2 + h ^ 2))
      (h ^ 2 / (Real.sqrt (t ^ 2 + h ^ 2)) ^ 3) t := by
  have hp : 0 < t ^ 2 + h ^ 2 := by nlinarith [sq_nonneg t]
  have hs := Real.sqrt_pos.2 hp
  have he := Real.sq_sqrt hp.le
  convert! (hasDerivAt_id t).div (sqrt_profile_derivative h t hh) (ne_of_gt hs) using 1
  simp only [id_eq]
  field_simp
  nlinarith

lemma sqrt_profile_slope_derivative_bounds (h t : ℝ) (hh : 0 < h) :
    0 ≤ h ^ 2 / (Real.sqrt (t ^ 2 + h ^ 2)) ^ 3 ∧
      h ^ 2 / (Real.sqrt (t ^ 2 + h ^ 2)) ^ 3 ≤ 1 / h := by
  have hp : 0 < t ^ 2 + h ^ 2 := by nlinarith [sq_nonneg t]
  have hs := Real.sqrt_pos.2 hp
  have he := Real.sq_sqrt hp.le
  have hle : h ≤ Real.sqrt (t ^ 2 + h ^ 2) := by nlinarith [sq_nonneg t]
  constructor
  · positivity
  · apply (div_le_div_iff₀ (pow_pos hs 3) hh).2
    nlinarith [mul_le_mul_of_nonneg_left hle (sq_nonneg h)]

lemma sqrt_profile_slope_lipschitz (h : ℝ) (hh : 0 < h) (x y : ℝ) :
    |x / Real.sqrt (x ^ 2 + h ^ 2) - y / Real.sqrt (y ^ 2 + h ^ 2)| ≤
      (1 / h) * |x - y| := by
  have hb (t : ℝ) : ‖h ^ 2 / (Real.sqrt (t ^ 2 + h ^ 2)) ^ 3‖ ≤ 1 / h := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sqrt_profile_slope_derivative_bounds h t hh).1]
    exact (sqrt_profile_slope_derivative_bounds h t hh).2
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (sqrt_profile_slope_derivative h t hh).hasDerivWithinAt)
      (fun t _ => hb t) (Set.mem_univ y) (Set.mem_univ x)

lemma sqrt_profile_convex (h : ℝ) (hh : 0 < h) :
    ConvexOn ℝ Set.univ (fun x : ℝ => Real.sqrt (x ^ 2 + h ^ 2)) := by
  have hm : Monotone (fun x : ℝ => x / Real.sqrt (x ^ 2 + h ^ 2)) :=
    monotone_of_deriv_nonneg
      (fun t => (sqrt_profile_slope_derivative h t hh).differentiableAt)
      (fun t => by rw [(sqrt_profile_slope_derivative h t hh).deriv]
                   exact (sqrt_profile_slope_derivative_bounds h t hh).1)
  apply Monotone.convexOn_univ_of_deriv
    (fun t => (sqrt_profile_derivative h t hh).differentiableAt)
  intro x y hxy
  rw [(sqrt_profile_derivative h x hh).deriv, (sqrt_profile_derivative h y hh).deriv]
  exact hm hxy

lemma shifted_sqrt_separation (t R h m : ℝ) (hm : 0 ≤ m) :
    2 * m * (R - h) ≤
      m * (Real.sqrt ((t - R) ^ 2 + h ^ 2) - h) +
      m * (Real.sqrt ((t + R) ^ 2 + h ^ 2) - h) := by
  have hs (x : ℝ) : |x| ≤ Real.sqrt (x ^ 2 + h ^ 2) := by
    calc
      |x| = Real.sqrt (x ^ 2) := (Real.sqrt_sq_eq_abs x).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg h])
  have hleft := (neg_le_abs (t - R)).trans (hs (t - R))
  have hright := (le_abs_self (t + R)).trans (hs (t + R))
  nlinarith [mul_nonneg hm (show 0 ≤ Real.sqrt ((t - R) ^ 2 + h ^ 2) +
    Real.sqrt ((t + R) ^ 2 + h ^ 2) - 2 * R by linarith)]

section Ridge

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def sqrtRidge (v : E) (c h m : ℝ) (x : E) : ℝ :=
  m * Real.sqrt ((⟪v, x⟫ - c) ^ 2 + h ^ 2)

lemma sqrtRidge_gradient (v : E) (c h m : ℝ) (hh : 0 < h) (x : E) :
    HasGradientAt (sqrtRidge v c h m)
      ((m * ((⟪v, x⟫ - c) / Real.sqrt ((⟪v, x⟫ - c) ^ 2 + h ^ 2))) • v) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hd := ((sqrt_profile_derivative h (⟪v, x⟫ - c) hh).comp_hasFDerivAt x
    ((innerSL ℝ v).hasFDerivAt.sub_const c)).const_mul m
  convert! hd using 1
  ext y
  simp [mul_assoc]

omit [CompleteSpace E] in
lemma sqrtRidge_convex (v : E) (c h m : ℝ) (hh : 0 < h) (hm : 0 ≤ m) :
    ConvexOn ℝ Set.univ (sqrtRidge v c h m) := by
  have hc := (sqrt_profile_convex h hh).comp_affineMap
    ((innerSL ℝ v).toLinearMap.toAffineMap - AffineMap.const ℝ E c)
  convert! hc.smul hm using 1

lemma sqrtRidge_gradient_norm (v : E) (hv : ‖v‖ = 1) (c h m : ℝ)
    (hh : 0 < h) (hm : 0 ≤ m) (x : E) : ‖gradient (sqrtRidge v c h m) x‖ ≤ m := by
  rw [(sqrtRidge_gradient v c h m hh x).gradient, norm_smul, hv, mul_one,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg hm]
  exact (mul_le_mul_of_nonneg_left (sqrt_profile_slope_bound h (⟪v, x⟫ - c) hh) hm).trans_eq
    (mul_one m)

lemma sqrtRidge_smooth (v : E) (hv : ‖v‖ = 1) (c h m : ℝ)
    (hh : 0 < h) (hm : 0 ≤ m) (x y : E) :
    ‖gradient (sqrtRidge v c h m) x - gradient (sqrtRidge v c h m) y‖ ≤
      (m / h) * ‖x - y‖ := by
  rw [(sqrtRidge_gradient v c h m hh x).gradient,
    (sqrtRidge_gradient v c h m hh y).gradient, ← sub_smul,
    norm_smul, hv, mul_one, Real.norm_eq_abs, ← mul_sub,
    abs_mul, abs_of_nonneg hm]
  have hinner : |(⟪v, x⟫ - c) - (⟪v, y⟫ - c)| ≤ ‖x - y‖ := by
    simpa [sub_sub_sub_cancel_right, ← inner_sub_right, hv] using
      abs_real_inner_le_norm v (x - y)
  calc
    _ ≤ m * ((1 / h) * |(⟪v, x⟫ - c) - (⟪v, y⟫ - c)|) :=
      mul_le_mul_of_nonneg_left (sqrt_profile_slope_lipschitz h hh _ _) hm
    _ ≤ m * ((1 / h) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner (by positivity)) hm
    _ = _ := by ring

lemma sqrtRidge_gradient_measurable [MeasurableSpace E] [BorelSpace E]
    (v : E) (hv : ‖v‖ = 1) (c h m : ℝ) (hh : 0 < h) (hm : 0 ≤ m) :
    Measurable (gradient (sqrtRidge v c h m)) := by
  have hc : 0 ≤ m / h := div_nonneg hm hh.le
  apply (LipschitzWith.of_dist_le_mul (K := (m / h).toNNReal) (fun x y => ?_)).continuous.measurable
  convert! sqrtRidge_smooth v hv c h m hh hm x y using 1 <;> simp [dist_eq_norm, Real.coe_toNNReal _ hc]

omit [CompleteSpace E] in
lemma sqrtRidge_min (v : E) (c h m : ℝ) (hh : 0 < h) (hm : 0 ≤ m)
    (xstar : E) (hx : ⟪v, xstar⟫ = c) : IsMinOn (sqrtRidge v c h m) Set.univ xstar := by
  intro x _
  simp only [sqrtRidge, hx, sub_self, zero_pow (by decide : 2 ≠ 0), zero_add,
    Real.sqrt_sq_eq_abs, abs_of_pos hh]
  apply mul_le_mul_of_nonneg_left _ hm
  calc
    h = Real.sqrt (h ^ 2) := (Real.sqrt_sq hh.le).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (⟪v, x⟫ - c)])

omit [CompleteSpace E] in
lemma sqrtRidge_at_center (v : E) (hv : ‖v‖ = 1) (x0 : E) (R h m : ℝ)
    (hh : 0 < h) :
    sqrtRidge v (⟪v, x0⟫ + R) h m (x0 + R • v) = m * h := by
  simp [sqrtRidge, inner_add_right, inner_smul_right, hv,
    Real.sqrt_sq hh.le]

omit [CompleteSpace E] in
lemma sqrtRidge_center_min (v : E) (hv : ‖v‖ = 1) (x0 : E) (R h m : ℝ)
    (hh : 0 < h) (hm : 0 ≤ m) :
    IsMinOn (sqrtRidge v (⟪v, x0⟫ + R) h m) Set.univ (x0 + R • v) := by
  apply sqrtRidge_min v _ h m hh hm
  simp [inner_add_right, inner_smul_right, hv]

omit [CompleteSpace E] in
lemma sqrtRidge_center_distance (v : E) (hv : ‖v‖ = 1) (x0 : E) (R : ℝ) :
    ‖x0 - (x0 + R • v)‖ = |R| := by simp [norm_smul, hv, Real.norm_eq_abs]

omit [CompleteSpace E] in
lemma sqrtRidge_pair_separation (v x0 x : E) (R h m : ℝ) (hm : 0 ≤ m) :
    2 * m * (R - h) ≤
      (sqrtRidge v (⟪v, x0⟫ + R) h m x - m * h) +
      (sqrtRidge v (⟪v, x0⟫ - R) h m x - m * h) := by
  have hs := shifted_sqrt_separation (⟪v, x⟫ - ⟪v, x0⟫) R h m hm
  convert hs using 1; dsimp [sqrtRidge]; ring_nf

end Ridge

lemma rare_moment_weight (p α : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (hα : 1 ≤ α) :
    p * (p⁻¹ - 1) ^ α + (1 - p) ≤ 2 * p ^ (1 - α) := by
  have hinv : 1 ≤ p⁻¹ := (one_le_inv₀ hp).2 hp1
  have hb := Real.rpow_le_rpow (by linarith : 0 ≤ p⁻¹ - 1)
    (by linarith : p⁻¹ - 1 ≤ p⁻¹) (by linarith : 0 ≤ α)
  have he : p * (p⁻¹) ^ α = p ^ (1 - α) := by
    rw [Real.inv_rpow hp.le, ← Real.rpow_neg hp.le]
    calc
      p * p ^ (-α) = p ^ (1 : ℝ) * p ^ (-α) := by rw [Real.rpow_one]
      _ = p ^ (1 - α) := by rw [← Real.rpow_add hp]; congr 1
  have ho := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp hp1
    (by linarith : 1 - α ≤ 0)
  have hm := mul_le_mul_of_nonneg_left hb hp.le
  rw [he] at hm
  linarith

noncomputable def rareOracle {Q F Ω : Type*} [Zero F] [SMul ℝ F]
    (a : Ω) (p : ℝ) (G : Q → F) (x : Q) (z : Ω) : F := by
  classical
  exact if z = a then p⁻¹ • G x else 0

lemma rareOracle_mean {Q F Ω : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (a b : Ω) (hab : a ≠ b) (ha : MeasurableSet ({a} : Set Ω))
    (hb : MeasurableSet ({b} : Set Ω)) (p : unitInterval) (hp : 0 < (p : ℝ))
    (G : Q → F) (x : Q) :
    (∫ z, rareOracle a p G x z ∂bernoulliMeasure a b p) = G x := by
  rw [integral_two_atoms a b ha hb p]
  simp [rareOracle, Ne.symm hab, smul_smul, ne_of_gt hp]

lemma rareOracle_measurable {Q F Ω : Type*} [MeasurableSpace Q] [MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (a : Ω) (ha : MeasurableSet ({a} : Set Ω)) (p : ℝ)
    (G : Q → F) (hG : Measurable G) :
    Measurable (Function.uncurry (rareOracle a p G)) := by
  classical
  unfold Function.uncurry rareOracle
  apply Measurable.ite (ha.preimage measurable_snd)
  · exact (hG.comp measurable_fst).const_smul _
  · exact measurable_const

lemma rareOracle_moment {Q F Ω : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b : Ω) (hab : a ≠ b) (ha : MeasurableSet ({a} : Set Ω))
    (hb : MeasurableSet ({b} : Set Ω)) (p : unitInterval) (hp : 0 < (p : ℝ))
    (α : ℝ) (hα : 1 ≤ α) (G : Q → F) (x : Q) :
    (∫ z, ‖rareOracle a p G x z - G x‖ ^ α ∂bernoulliMeasure a b p) ≤
      2 * (p : ℝ) ^ (1 - α) * ‖G x‖ ^ α := by
  classical
  have hinv : 0 ≤ (p : ℝ)⁻¹ - 1 := sub_nonneg.mpr ((one_le_inv₀ hp).2 p.2.2)
  have hr : rareOracle a p G x a - G x = ((p : ℝ)⁻¹ - 1) • G x := by
    simp [rareOracle, sub_smul]
  have hc : rareOracle a p G x b - G x = -G x := by
    simp [rareOracle, Ne.symm hab]
  rw [integral_two_atoms a b ha hb p, hr, hc, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hinv, Real.mul_rpow hinv (norm_nonneg _)]
  simp only [smul_eq_mul]
  calc
    _ = ((p : ℝ) * ((p : ℝ)⁻¹ - 1) ^ α + (1 - (p : ℝ))) * ‖G x‖ ^ α := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (rare_moment_weight p α hp p.2.2 hα)
      (Real.rpow_nonneg (norm_nonneg _) _)

lemma ridge_admissible
    (q : LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.Params)
    (hq : LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.spec.valid q)
    (v : q.E) (hv : ‖v‖ = 1) (a b : q.Ω) (hab : a ≠ b)
    (ha : MeasurableSet ({a} : Set q.Ω)) (hb : MeasurableSet ({b} : Set q.Ω))
    (p r : unitInterval) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) ≤ 1 / 4)
    (hr : (r : ℝ) = q.β * (4 * (p : ℝ)) ^ (1 / q.β) / q.τ)
    (d h m : ℝ) (hd : |d| ≤ q.R) (hh : 0 < h) (hm : 0 ≤ m)
    (hsmooth : m / h ≤ q.L)
    (hnoise : 2 * (p : ℝ) ^ (1 - q.α) * m ^ q.α ≤ q.σ ^ q.α) :
    LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.spec.admissible q
      (sqrtRidge v (inner ℝ v q.x0 + d) h m)
      (sampledOracle (rareOracle a p (gradient (sqrtRidge v (inner ℝ v q.x0 + d) h m)))
        (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
          (refreshKernel (twoAtomLaw a b p) r) (twoAtomLaw a b p))) := by
  rcases hq with ⟨hL, hR, hσ, hα, hα2, hτ, hβ, hε⟩
  refine ⟨rareOracle a p (gradient (sqrtRidge v (inner ℝ v q.x0 + d) h m)),
    refreshKernel (twoAtomLaw a b p) r, inferInstance, twoAtomLaw a b p,
    rfl, refreshKernel_stationary _ _, ?_, ?_, sqrtRidge_convex v _ h m hh hm,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact refresh_bernoulli_mixing_integrable a b ha hb p r n
  · intro n
    have hav := refresh_bernoulli_average_mixing a b ha hb p r n
    have hbds := polynomial_scale_bounds p q.β hp hp1 hβ
    exact hav.trans (refresh_polynomial_envelope p r _ q.τ q.β n
      hbds.1 hbds.2.1 hτ hβ.le hbds.2.2 hr)
  · intro x
    rw [(sqrtRidge_gradient v _ h m hh x).gradient]
    exact sqrtRidge_gradient v _ h m hh x
  · intro x y
    exact (sqrtRidge_smooth v hv _ h m hh hm x y).trans
      (mul_le_mul_of_nonneg_right hsmooth (norm_nonneg _))
  · refine ⟨q.x0 + d • v, sqrtRidge_center_min v hv q.x0 d h m hh hm, ?_⟩
    rw [sqrtRidge_center_distance v hv]
    exact hd
  · exact rareOracle_measurable a ha p _ (sqrtRidge_gradient_measurable v hv _ h m hh hm)
  · intro x
    exact integrable_two_atoms a b ha hb p _
  · intro x
    exact rareOracle_mean a b hab ha hb p hp _ x
  · intro x
    exact integrable_two_atoms a b ha hb p _
  · intro x
    have hbnd := rareOracle_moment a b hab ha hb p hp q.α hα.le
      (gradient (sqrtRidge v (inner ℝ v q.x0 + d) h m)) x
    apply hbnd.trans
    apply le_trans _ hnoise
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (sqrtRidge_gradient_norm v hv _ h m hh hm x)
        (by linarith)) (by positivity)

lemma successful_gap_at_minimizer
    (q : LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.Params)
    (f : q.E → ℝ) {W : Type} [MeasurableSpace W] (output : W → q.E)
    (P : ProbabilityMeasure W) (xstar : q.E) (hmin : IsMinOn f Set.univ xstar)
    (hs : LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.spec.successful q f output P) :
    Integrable (fun w => f (output w) - f xstar) (P : Measure W) ∧
      (∫ w, f (output w) - f xstar ∂(P : Measure W)) ≤ q.ε := by
  rcases hs with ⟨_, ystar, hy, hi, he⟩
  have hval : f ystar = f xstar := le_antisymm (hy (Set.mem_univ xstar))
    (hmin (Set.mem_univ ystar))
  simpa only [hval] using And.intro hi he

lemma ridge_pair_not_successful
    (q : LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.Params)
    (v : q.E) (hv : ‖v‖ = 1) (a b : q.Ω) (hab : a ≠ b)
    (hb : MeasurableSet ({b} : Set q.Ω)) (p r : unitInterval)
    (hp1 : (p : ℝ) ≤ 1 / 4) (N : ℕ)
    (hN : (N : ℝ) * (p : ℝ) * (r : ℝ) ≤ 1 / 4)
    (h m : ℝ) (hh : 0 < h) (hm : 0 ≤ m)
    (hε : 0 < q.ε) (hgap : 2 * q.ε < m * (q.R - h))
    (A : OracleTemplate.Algorithm q.E q.E q.E) :
    let f₁ := sqrtRidge v (inner ℝ v q.x0 + q.R) h m
    let f₂ := sqrtRidge v (inner ℝ v q.x0 - q.R) h m
    let P := LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
      (refreshKernel (twoAtomLaw a b p) r) (twoAtomLaw a b p)
    let O₁ := sampledOracle (rareOracle a p (gradient f₁)) P
    let O₂ := sampledOracle (rareOracle a p (gradient f₂)) P
    let joint : ProbabilityMeasure (A.Seed × (ℕ → q.Ω)) :=
      ⟨(A.law : Measure A.Seed).prod (P : Measure (ℕ → q.Ω)), inferInstance⟩
    ¬ (LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.spec.successful q f₁
      (fun w : A.Seed × (ℕ → q.Ω) => OracleTemplate.execute O₁ A (fun _ => N) w.1 w.2) joint ∧
      LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.spec.successful q f₂
      (fun w : A.Seed × (ℕ → q.Ω) => OracleTemplate.execute O₂ A (fun _ => N) w.1 w.2) joint) := by
  dsimp only
  intro hs
  have hmin₁ := sqrtRidge_center_min v hv q.x0 q.R h m hh hm
  have hmin₂ : IsMinOn (sqrtRidge v (inner ℝ v q.x0 - q.R) h m) Set.univ
      (q.x0 + (-q.R) • v) := by
    simpa only [sub_eq_add_neg] using sqrtRidge_center_min v hv q.x0 (-q.R) h m hh hm
  have hval₁ := sqrtRidge_at_center v hv q.x0 q.R h m hh
  have hval₂ : sqrtRidge v (inner ℝ v q.x0 - q.R) h m (q.x0 + (-q.R) • v) = m * h := by
    simpa only [sub_eq_add_neg] using sqrtRidge_at_center v hv q.x0 (-q.R) h m hh
  have h₁ := successful_gap_at_minimizer q _ _ _ _ hmin₁ hs.1
  have h₂ := successful_gap_at_minimizer q _ _ _ _ hmin₂ hs.2
  rw [hval₁] at h₁
  rw [hval₂] at h₂
  have hn₁ (x : q.E) : 0 ≤ sqrtRidge v (inner ℝ v q.x0 + q.R) h m x - m * h := by
    have hx := hmin₁ (Set.mem_univ x)
    rw [hval₁] at hx
    exact sub_nonneg.mpr hx
  have hn₂ (x : q.E) : 0 ≤ sqrtRidge v (inner ℝ v q.x0 - q.R) h m x - m * h := by
    have hx := hmin₂ (Set.mem_univ x)
    rw [hval₂] at hx
    exact sub_nonneg.mpr hx
  have hpair := execution_pair_lower _ _ _ b hb
    (fun x => by simp [rareOracle, Ne.symm hab]) A N _ _ hn₁ hn₂
    (2 * m * (q.R - h)) (fun x => sqrtRidge_pair_separation v q.x0 x q.R h m hm) h₁.1 h₂.1
  have hprob := refresh_commonPrefix_half a b hab hb p r N hp1 hN
  have hc : 0 ≤ 2 * m * (q.R - h) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hprob hc
  have hbound := hpair.trans (add_le_add h₁.2 h₂.2)
  have hend := hmul.trans hbound
  nlinarith only [hend, hgap]

lemma calibrated_mass_noise (m noise α : ℝ) (hm : 0 < m) (hnoise : 0 < noise) (hα : 1 < α) :
    let p := (2 * (m / noise) ^ α) ^ (1 / (α - 1))
    0 < p ∧ 2 * p ^ (1 - α) * m ^ α = noise ^ α := by
  let p := (2 * (m / noise) ^ α) ^ (1 / (α - 1))
  have ht : 0 < 2 * (m / noise) ^ α := by positivity
  have hp : 0 < p := Real.rpow_pos_of_pos ht _
  have he : p ^ (α - 1) = 2 * (m / noise) ^ α := by
    dsimp [p]
    rw [one_div, Real.rpow_inv_rpow ht.le (by linarith)]
  have hi : p ^ (1 - α) = (2 * (m / noise) ^ α)⁻¹ := by
    rw [show 1 - α = -(α - 1) by ring, Real.rpow_neg hp.le, he]
  refine ⟨hp, ?_⟩
  change 2 * p ^ (1 - α) * m ^ α = noise ^ α
  rw [hi, Real.div_rpow hm.le hnoise.le]
  have hm' := Real.rpow_pos_of_pos hm α
  have hnoise' := Real.rpow_pos_of_pos hnoise α
  field_simp

lemma calibrated_mass_quarter (m noise α : ℝ) (hm : 0 < m) (hnoise : 0 < noise) (hα : 1 < α)
    (hsmall : 2 * (m / noise) ^ α ≤ (1 / 4 : ℝ) ^ (α - 1)) :
    (2 * (m / noise) ^ α) ^ (1 / (α - 1)) ≤ 1 / 4 := by
  have ht : 0 ≤ 2 * (m / noise) ^ α := by positivity
  have hb := Real.rpow_le_rpow ht hsmall (by positivity : 0 ≤ 1 / (α - 1))
  have he : ((1 / 4 : ℝ) ^ (α - 1)) ^ (1 / (α - 1)) = 1 / 4 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    have hx : (α - 1) * (1 / (α - 1)) = 1 := by
      field_simp [ne_of_gt (sub_pos.mpr hα)]
    rw [hx, Real.rpow_one]
  exact hb.trans_eq he

lemma floor_budget_no_hit (p r B : ℝ) (hp : 0 < p) (hr : 0 < r)
    (hB : B = 1 / (4 * p * r)) (N : ℕ) (hN : N ≤ ⌊B⌋₊) :
    (N : ℝ) * p * r ≤ 1 / 4 := by
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hn : (N : ℝ) ≤ B := (Nat.cast_le.mpr hN).trans (Nat.floor_le hB0)
  rw [hB] at hn
  have hm := mul_le_mul_of_nonneg_right hn (show 0 ≤ p * r by positivity)
  have he : (1 / (4 * p * r)) * (p * r) = 1 / 4 := by field_simp
  rw [he] at hm
  simpa only [mul_assoc] using hm

lemma hard_tuning (R ε L : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (hL : 16 ≤ L * R ^ 2 / ε) :
    0 < R / 4 ∧ 0 < 4 * ε / R ∧ (4 * ε / R) / (R / 4) ≤ L ∧
      2 * ε < (4 * ε / R) * (R - R / 4) := by
  have hbase : 16 * ε ≤ L * R ^ 2 := (le_div_iff₀ hε).mp hL
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · have he : (4 * ε / R) / (R / 4) = 16 * ε / R ^ 2 := by ring
    rw [he]
    exact (div_le_iff₀ (sq_pos_of_pos hR)).2 hbase
  · have he : (4 * ε / R) * (R - R / 4) = 3 * ε := by field_simp; ring
    rw [he]
    linarith

lemma four_tail_power_identity (α : ℝ) :
    (4 : ℝ) ^ (α - 1) * 2 * (4 : ℝ) ^ α = (2 : ℝ) ^ (4 * α - 1) := by
  have hf (t : ℝ) : (4 : ℝ) ^ t = (2 : ℝ) ^ (2 * t) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hf, hf]
  calc
    _ = (2 : ℝ) ^ (2 * (α - 1)) * (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (2 * α) := by
      rw [Real.rpow_one]
    _ = (2 : ℝ) ^ (4 * α - 1) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

lemma normalized_mass_small (z α : ℝ) (hz : 0 < z)
    (hlarge : (2 : ℝ) ^ (4 * α - 1) ≤ z ^ α) :
    2 * (4 / z) ^ α ≤ (1 / 4 : ℝ) ^ (α - 1) := by
  have hzpow := Real.rpow_pos_of_pos hz α
  have hfour := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) (α - 1)
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 4) hz.le]
  rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4)]
  apply (mul_le_mul_iff_right₀ hfour).mp
  calc
    _ = (2 : ℝ) ^ (4 * α - 1) / z ^ α := by
      rw [← four_tail_power_identity α]
      ring
    _ ≤ 1 := (div_le_one hzpow).2 hlarge
    _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt hfour)]

lemma normalized_mass_identity (z α : ℝ) (hz : 0 < z) (hα : 1 < α) :
    4 * (2 * (4 / z) ^ α) ^ (1 / (α - 1)) =
      ((2 : ℝ) ^ (4 * α - 1) / z ^ α) ^ (1 / (α - 1)) := by
  have ht : 0 < 2 * (4 / z) ^ α := by positivity
  apply (Real.rpow_left_inj (by positivity) (by positivity)
    (ne_of_gt (sub_pos.mpr hα))).mp
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity), one_div,
    Real.rpow_inv_rpow ht.le (ne_of_gt (sub_pos.mpr hα)),
    Real.rpow_inv_rpow (by positivity) (ne_of_gt (sub_pos.mpr hα)),
    Real.div_rpow (by norm_num : (0 : ℝ) ≤ 4) hz.le,
    ← four_tail_power_identity α]
  ring

lemma refresh_budget_identity (w t β τ : ℝ) (hw : 0 < w) (ht : 0 < t)
    (hβ : 0 < β) (hτ : 0 < τ) :
    τ / β * (w⁻¹) ^ ((β + 1) / (β * t)) =
      1 / (w ^ (1 / t) * (β * (w ^ (1 / t)) ^ (1 / β) / τ)) := by
  have he : w ^ (1 / t) * (w ^ (1 / t)) ^ (1 / β) =
      w ^ ((β + 1) / (β * t)) := by
    rw [← Real.rpow_mul hw.le, ← Real.rpow_add hw]
    congr 1
    field_simp
  rw [Real.inv_rpow hw.le]
  have hd : w ^ (1 / t) * (β * (w ^ (1 / t)) ^ (1 / β) / τ) =
      β / τ * w ^ ((β + 1) / (β * t)) := by
    rw [← he]
    ring
  rw [hd]
  have hw' := Real.rpow_pos_of_pos hw ((β + 1) / (β * t))
  field_simp

lemma refresh_root_identity (w t β : ℝ) (hw : 0 ≤ w) :
    (w ^ (1 / t)) ^ (1 / β) = w ^ (1 / (β * t)) := by
  rw [← Real.rpow_mul hw]
  congr 1
  ring

lemma setup_calibration (q : LongTails.Setups.PolynomialMixingHeavyTailedConvex.Params)
    (hq : LongTails.Setups.PolynomialMixingHeavyTailedConvex.spec.valid q) :
    ∃ p r : unitInterval, 0 < (p : ℝ) ∧ (p : ℝ) ≤ 1 / 4 ∧ 0 < (r : ℝ) ∧
      (r : ℝ) = q.β * (4 * (p : ℝ)) ^ (1 / q.β) / q.τ ∧
      2 * (p : ℝ) ^ (1 - q.α) * (4 * q.ε / q.R) ^ q.α = q.σ ^ q.α ∧
      q.τ / q.β * ((q.σ * q.R / q.ε) ^ q.α / (2 : ℝ) ^ (4 * q.α - 1)) ^
        ((q.β + 1) / (q.β * (q.α - 1))) = 1 / (4 * (p : ℝ) * (r : ℝ)) := by
  rcases hq with ⟨hbase, hR, hnoise, _, _, _, _, hlarge, hmix⟩
  rcases hbase with ⟨_, _, _, hα, _, hτ, hβ, hε⟩
  let z := q.σ * q.R / q.ε
  let m := 4 * q.ε / q.R
  let p0 := (2 * (m / q.σ) ^ q.α) ^ (1 / (q.α - 1))
  let w := (2 : ℝ) ^ (4 * q.α - 1) / z ^ q.α
  have hz : 0 < z := by dsimp [z]; positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have hw : 0 < w := by dsimp [w]; positivity
  have hratio : m / q.σ = 4 / z := by dsimp [m, z]; field_simp
  have hcal := calibrated_mass_noise m q.σ q.α hm hnoise hα
  have hp0 : 0 < p0 := hcal.1
  have hp1 : p0 ≤ 1 / 4 := by
    apply calibrated_mass_quarter m q.σ q.α hm hnoise hα
    rw [hratio]
    exact normalized_mass_small z q.α hz hlarge
  have hfour : 4 * p0 = w ^ (1 / (q.α - 1)) := by
    dsimp [p0]
    rw [hratio]
    exact normalized_mass_identity z q.α hz hα
  have hroot : (4 * p0) ^ (1 / q.β) = w ^ (1 / (q.β * (q.α - 1))) := by
    rw [hfour, refresh_root_identity w (q.α - 1) q.β hw.le]
  let r0 := q.β * (4 * p0) ^ (1 / q.β) / q.τ
  have hr0 : 0 < r0 := by dsimp [r0]; positivity
  have hr1 : r0 ≤ 1 := by
    dsimp [r0]
    rw [hroot]
    exact (div_le_one hτ).2 hmix
  let p : unitInterval := ⟨p0, hp0.le, hp1.trans (by norm_num)⟩
  let r : unitInterval := ⟨r0, hr0.le, hr1⟩
  refine ⟨p, r, hp0, hp1, hr0, rfl, hcal.2, ?_⟩
  have hi : w⁻¹ = z ^ q.α / (2 : ℝ) ^ (4 * q.α - 1) := by simp [w]
  change q.τ / q.β * (z ^ q.α / (2 : ℝ) ^ (4 * q.α - 1)) ^
    ((q.β + 1) / (q.β * (q.α - 1))) = 1 / (4 * p0 * r0)
  rw [← hi, refresh_budget_identity w (q.α - 1) q.β q.τ hw (sub_pos.mpr hα) hβ hτ,
    ← hfour]

lemma polynomialMixing_lower : OracleTemplate.NonConvergence
    LongTails.Setups.PolynomialMixingHeavyTailedConvex.spec
    (fun q _ => ⌊q.τ / q.β * ((q.σ * q.R / q.ε) ^ q.α / (2 : ℝ) ^ (4 * q.α - 1)) ^
      ((q.β + 1) / (q.β * (q.α - 1)))⌋₊) := by
  classical
  intro q hq A _ budget hbudget
  obtain ⟨p, r, hp, hp1, hr, hreq, hnoise, hB⟩ := setup_calibration q hq
  rcases hq with ⟨hbase, hR, _, ⟨v, hv⟩, ⟨a, b, hab, ha, hb⟩, hT, _, _, _⟩
  have hε : 0 < q.ε := hbase.2.2.2.2.2.2.2
  have htune := hard_tuning q.R q.ε q.L hR hε hT
  have hN := floor_budget_no_hit p r _ hp hr hB (budget 0) (hbudget 0)
  have hbconst : budget = fun _ => budget 0 := by
    funext i
    congr 1
    exact Subsingleton.elim i 0
  let objective (d : ℝ) := sqrtRidge v (inner ℝ v q.x0 + d) (q.R / 4) (4 * q.ε / q.R)
  let P := LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw
    (refreshKernel (twoAtomLaw a b p) r) (twoAtomLaw a b p)
  let O (d : ℝ) := sampledOracle (rareOracle a p (gradient (objective d))) P
  let joint : ProbabilityMeasure (A.Seed × (ℕ → q.Ω)) :=
    ⟨(A.law : Measure A.Seed).prod (P : Measure (ℕ → q.Ω)), inferInstance⟩
  have hadm (d : ℝ) (hd : |d| ≤ q.R) :
      LongTails.Setups.PolynomialMixingHeavyTailedConvex.spec.admissible q (objective d) (O d) :=
    ridge_admissible q hbase v hv a b hab ha hb p r hp hp1 hreq d (q.R / 4)
      (4 * q.ε / q.R) hd htune.1 htune.2.1.le htune.2.2.1 hnoise.le
  by_contra hn
  have hs (d : ℝ) (hd : |d| ≤ q.R) :
      LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.spec.successful q (objective d)
        (fun w : A.Seed × (ℕ → q.Ω) => OracleTemplate.execute (O d) A budget w.1 w.2) joint := by
    by_contra hfail
    exact hn ⟨objective d, O d, hadm d hd, hfail⟩
  have hpair := ridge_pair_not_successful q v hv a b hab hb p r hp1 (budget 0) hN
    (q.R / 4) (4 * q.ε / q.R) htune.1 htune.2.1.le hε htune.2.2.2 A
  apply hpair
  constructor
  · have hsplus := hs q.R (by rw [abs_of_pos hR])
    rw [hbconst] at hsplus
    simpa only [objective, O, P, joint] using hsplus
  · have hsminus := hs (-q.R) (by rw [abs_neg, abs_of_pos hR])
    rw [hbconst] at hsminus
    dsimp only [O] at hsminus
    have he : objective (-q.R) =
        sqrtRidge v (inner ℝ v q.x0 - q.R) (q.R / 4) (4 * q.ε / q.R) := by
      simp only [objective, sub_eq_add_neg]
    erw [he] at hsminus
    simpa only [P, joint] using hsminus

lemma polynomialMixing_inclusion :
    OracleTemplate.Includes LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.spec
      LongTails.Setups.PolynomialMixingHeavyTailedConvex.spec := by
  refine ⟨{
    numOracles_eq := rfl
    mapParams := id
    mapPublic := id
    instance_eq := fun _ => rfl
    query_eq := fun _ => rfl
    reply_eq := fun _ => rfl
    output_eq := fun _ => rfl
    public_eq := fun _ => rfl
    valid := fun _ h => h.1
    admissible := ?_
    successful := ?_
    allowedAlgorithm := ?_ }⟩
  · intro p hp I O h
    exact h
  · intro p hp I O h Ω _ output P hs
    exact hs
  · intro q A h
    exact h

lemma common_path_probability_lower (p r : ℝ) (N : ℕ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    1 - p - (N : ℝ) * p * r ≤ (1 - p) * (1 - p * r) ^ N := by
  have hprod : p * r ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hr1 hp]
  have hpow := one_add_mul_sub_le_pow (a := 1 - p * r) (by linarith : -1 ≤ 1 - p * r) N
  have hmul := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ 1 - p)
  have hcross : 0 ≤ (N : ℝ) * p * p * r := by positivity
  nlinarith

lemma common_path_probability_half (p r : ℝ) (N : ℕ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1 / 4) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hN : (N : ℝ) * p * r ≤ 1 / 4) :
    1 / 2 ≤ (1 - p) * (1 - p * r) ^ N := by
  have h := common_path_probability_lower p r N hp (by linarith) hr hr1
  linarith

end LongTails.Proofs.PolynomialMixingLowerBound
