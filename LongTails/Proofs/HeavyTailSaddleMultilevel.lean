import LongTails.Proofs.ScalarSearchBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import LongTails.Proofs.StochasticQuasarWorkTail
import LongTails.Proofs.HeavyTailedClipping
import LongTails.Proofs.HeavyTailedMomentBounds
import LongTails.Proofs.HeavyTailedProductProcess
import LongTails.Proofs.HeavyTailedFreshProcess
import LongTails.Proofs.HeavyTailSaddleGeometry
import LongTails.Algorithms.HeavyTailSaddleEstimator
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Algebra.Order.Field.GeomSum

open MeasureTheory
open scoped ENNReal

namespace LongTails.Proofs.HeavyTailSaddleMultilevel

open LongTails.Algorithms.HeavyTailSaddleEstimator

lemma level_weight_formula (J : ℕ) (j : Fin (J + 1)) :
    levelWeight J j = ((2 : ℝ)⁻¹) ^ j.val /
      ∑ i : Fin (J + 1), ((2 : ℝ)⁻¹) ^ i.val := by
  unfold levelWeight levelPMF
  rw [PMF.normalize_apply, ENNReal.toReal_mul, ENNReal.toReal_inv, tsum_fintype]
  rw [ENNReal.toReal_sum (by intro i hi; finiteness)]
  simp [div_eq_mul_inv]

lemma level_weight_pos (J : ℕ) (j : Fin (J + 1)) : 0 < levelWeight J j := by
  rw [level_weight_formula]
  apply div_pos (by positivity)
  apply Finset.sum_pos'
  · intro i hi
    positivity
  · exact ⟨0, Finset.mem_univ _, by simp⟩

lemma level_weight_sum (J : ℕ) : ∑ j : Fin (J + 1), levelWeight J j = 1 := by
  simp_rw [level_weight_formula]
  rw [← Finset.sum_div]
  apply div_self
  have h : 0 < ∑ i : Fin (J + 1), ((2 : ℝ)⁻¹) ^ i.val := by
    apply Finset.sum_pos'
    · intro i hi
      positivity
    · exact ⟨0, Finset.mem_univ _, by simp⟩
  exact h.ne'

lemma level_normalizer_bounds (J : ℕ) :
    1 ≤ ∑ i : Fin (J + 1), ((2 : ℝ)⁻¹) ^ i.val ∧
      ∑ i : Fin (J + 1), ((2 : ℝ)⁻¹) ^ i.val ≤ 2 := by
  constructor
  · simpa using Finset.single_le_sum (f := fun i : Fin (J + 1) =>
      ((2 : ℝ)⁻¹) ^ i.val) (fun i hi => by positivity) (Finset.mem_univ 0)
  · rw [Fin.sum_univ_eq_sum_range]
    have h := geom_sum_mul ((2 : ℝ)⁻¹) (J + 1)
    norm_num at h ⊢
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (J + 1)]

lemma level_weight_bounds (J : ℕ) (j : Fin (J + 1)) :
    ((2 : ℝ)⁻¹) ^ j.val / 2 ≤ levelWeight J j ∧
      levelWeight J j ≤ ((2 : ℝ)⁻¹) ^ j.val := by
  have h := level_normalizer_bounds J
  have hp : 0 < ∑ i : Fin (J + 1), ((2 : ℝ)⁻¹) ^ i.val := by linarith
  rw [level_weight_formula]
  constructor
  · exact div_le_div_of_nonneg_left (by positivity) hp h.2
  · exact (div_le_iff₀ hp).mpr (by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) j.val])

lemma weighted_level_work (J : ℕ) :
    ∑ j : Fin (J + 1), levelWeight J j * (2 : ℝ) ^ (j.val + 1) ≤ 2 * (J + 1) := by
  calc
    _ ≤ ∑ _j : Fin (J + 1), (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ ((2 : ℝ)⁻¹) ^ j.val * 2 ^ (j.val + 1) :=
          mul_le_mul_of_nonneg_right (level_weight_bounds J j).2 (by positivity)
        _ = 2 := by rw [pow_succ, inv_pow]; field_simp
    _ = _ := by simp; ring

lemma reply_calls_formula (h : ℕ) {J : ℕ} (j : Fin (J + 1)) :
    replyCalls h j = (h + 1) * (1 + 3 * 2 ^ j.val) := by
  simp [replyCalls, levelCalls, pow_succ]
  ring

lemma reply_calls_max (h J : ℕ) (j : Fin (J + 1)) :
    replyCalls h j ≤ (h + 1) * (1 + 3 * 2 ^ J) := by
  rw [reply_calls_formula]
  have hj : j.val ≤ J := by omega
  gcongr

lemma weighted_reply_work (h J : ℕ) :
    ∑ j : Fin (J + 1), levelWeight J j * (replyCalls h j : ℝ) ≤
      (h + 1) * (1 + 3 * (J + 1)) := by
  have hb : ∑ j : Fin (J + 1), levelWeight J j * (2 : ℝ) ^ j.val ≤ J + 1 := by
    have ht := weighted_level_work J
    simp_rw [pow_succ, ← mul_assoc] at ht
    rw [← Finset.sum_mul] at ht
    linarith
  have heq : (∑ j : Fin (J + 1), levelWeight J j * (replyCalls h j : ℝ)) =
      (h + 1) * ((∑ j : Fin (J + 1), levelWeight J j) +
        3 * ∑ j : Fin (J + 1), levelWeight J j * (2 : ℝ) ^ j.val) := by
    simp only [reply_calls_formula, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      Nat.cast_pow]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq, level_weight_sum]
  gcongr

lemma level_profile_coordinate (batch depth : ℕ → ℕ) (j : ℕ) :
    MeasurePreserving (fun s : (k : ℕ) → Fin (batch k) → Fin (depth k + 1) => s j)
      (levelProfileLaw batch depth : Measure _)
      (Measure.pi (fun _ : Fin (batch j) => (levelLaw (depth j) : Measure _))) :=
  measurePreserving_eval_infinitePi _ j

lemma level_law_singleton (J : ℕ) (j : Fin (J + 1)) :
    (levelLaw J : Measure _).real {j} = levelWeight J j := by
  rw [measureReal_def]
  change ((levelPMF J).toMeasure {j}).toReal = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rfl

lemma integral_reply_work (h J : ℕ) :
    (∫ j : Fin (J + 1), (replyCalls h j : ℝ) ∂(levelLaw J : Measure _)) ≤
      (h + 1) * (1 + 3 * (J + 1)) := by
  rw [integral_fintype (Integrable.of_finite)]
  simpa only [level_law_singleton, smul_eq_mul] using weighted_reply_work h J

lemma reply_work_tail (h J k : ℕ) (t : ℝ) :
    (Measure.pi fun _ : Fin k => (levelLaw J : Measure (Fin (J + 1))))
      {samples | 2 * k * ((h + 1) * (1 + 3 * (J + 1)) : ℝ) +
        ((h + 1) * (1 + 3 * (2 : ℝ) ^ J)) * t <
          ∑ i, (replyCalls h (samples i) : ℝ)} ≤ ENNReal.ofReal (Real.exp (-t)) := by
  refine OracleTemplate.StochasticQuasar.bounded_cost_sum_tail
    (μ := (levelLaw J : Measure (Fin (J + 1))))
    (W := fun j : Fin (J + 1) => (replyCalls h j : ℝ))
    (M := (h + 1) * (1 + 3 * (2 : ℝ) ^ J))
    (C := (h + 1) * (1 + 3 * (J + 1))) (by positivity)
    (measurable_of_finite _) ?_ (integral_reply_work h J) k t
  intro j
  refine ⟨Nat.cast_nonneg _, ?_⟩
  exact_mod_cast reply_calls_max h J j

lemma reply_work_cap (h J k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    let C := ⌈2 * k * ((h + 1) * (1 + 3 * (J + 1)) : ℝ) +
      ((h + 1) * (1 + 3 * (2 : ℝ) ^ J)) * Real.log (1 / δ)⌉₊
    (Measure.pi fun _ : Fin k => (levelLaw J : Measure (Fin (J + 1))))
      {samples | C < ∑ i, replyCalls h (samples i)} ≤ ENNReal.ofReal δ := by
  intro C
  have hsub : {samples : Fin k → Fin (J + 1) | C < ∑ i, replyCalls h (samples i)} ⊆
      {samples | 2 * k * ((h + 1) * (1 + 3 * (J + 1)) : ℝ) +
        ((h + 1) * (1 + 3 * (2 : ℝ) ^ J)) * Real.log (1 / δ) <
          ∑ i, (replyCalls h (samples i) : ℝ)} := by
    intro samples hs
    have hc : 2 * k * ((h + 1) * (1 + 3 * (J + 1)) : ℝ) +
        ((h + 1) * (1 + 3 * (2 : ℝ) ^ J)) * Real.log (1 / δ) ≤ (C : ℝ) :=
      Nat.le_ceil _
    have hh : (C : ℝ) < ∑ i, (replyCalls h (samples i) : ℝ) := by exact_mod_cast hs
    exact lt_of_le_of_lt hc hh
  have ht := (measure_mono hsub).trans (reply_work_tail h J k (Real.log (1 / δ)))
  have he : Real.exp (-Real.log (1 / δ)) = δ := by
    rw [Real.log_div one_ne_zero hδ.ne', Real.log_one]
    simpa using Real.exp_log hδ
  simpa only [he] using ht

lemma reply_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {J : ℕ} (base : E) (fine coarse : Fin (J + 1) → E) :
    (∫ j, reply base fine coarse j ∂(levelLaw J : Measure _)) =
      base + ∑ j, (fine j - coarse j) := by
  rw [integral_fintype (Integrable.of_finite)]
  simp_rw [level_law_singleton, reply, smul_add, smul_smul,
    mul_inv_cancel₀ (level_weight_pos J _).ne', one_smul]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, level_weight_sum, one_smul]

lemma reply_integral_telescope {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {J : ℕ} (v : Fin (J + 2) → E) :
    (∫ j, reply (v 0) (fun j => v j.succ) (fun j => v j.castSucc) j
      ∂(levelLaw J : Measure _)) = v (Fin.last (J + 1)) := by
  rw [reply_integral, Finset.sum_sub_distrib, ← add_sub_assoc,
    ← Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  abel

lemma random_reply_mean {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {J : ℕ} {base : Ω → E} {fine coarse : Fin (J + 1) → Ω → E}
    (hb : Measurable base) (hf : Measurable (Function.uncurry fine))
    (hc : Measurable (Function.uncurry coarse))
    (hbi : Integrable base P) (hfi : ∀ j, Integrable (fine j) P)
    (hci : ∀ j, Integrable (coarse j) P) (v : Fin (J + 2) → E)
    (hbm : (∫ ω, base ω ∂P) = v 0)
    (hfm : ∀ j, (∫ ω, fine j ω ∂P) = v j.succ)
    (hcm : ∀ j, (∫ ω, coarse j ω ∂P) = v j.castSucc) :
    let R := fun z : Fin (J + 1) × Ω =>
      reply (base z.2) (fun j => fine j z.2) (fun j => coarse j z.2) z.1
    Integrable R ((levelLaw J : Measure _).prod P) ∧
      (∫ z, R z ∂(levelLaw J : Measure _).prod P) = v (Fin.last (J + 1)) := by
  intro R
  have hw : Measurable (fun j : Fin (J + 1) => (levelWeight J j)⁻¹) :=
    measurable_of_countable _
  have hR : Measurable R := (hb.comp measurable_snd).add
    ((hw.comp measurable_fst).smul (hf.sub hc))
  have hRi (j : Fin (J + 1)) : Integrable (fun ω => R (j, ω)) P :=
    hbi.add (((hfi j).sub (hci j)).smul ((levelWeight J j)⁻¹))
  have hprod : Integrable R ((levelLaw J : Measure _).prod P) := by
    apply (integrable_prod_iff hR.aestronglyMeasurable).mpr
    exact ⟨Filter.Eventually.of_forall hRi, Integrable.of_finite⟩
  refine ⟨hprod, ?_⟩
  rw [integral_prod R hprod]
  have hm (j : Fin (J + 1)) : (∫ ω, R (j, ω) ∂P) =
      reply (v 0) (fun j => v j.succ) (fun j => v j.castSucc) j := by
    dsimp [R, reply]
    have hscaled : Integrable (fun ω => (levelWeight J j)⁻¹ • (fine j ω - coarse j ω)) P :=
      ((hfi j).sub (hci j)).smul ((levelWeight J j)⁻¹)
    rw [integral_add hbi hscaled, integral_smul,
      integral_sub (hfi j) (hci j), hbm, hfm, hcm]
  simp_rw [hm]
  exact reply_integral_telescope v

lemma trajectory_lyapunov {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {step : S → Ω → S} {W : S → ℝ}
    (hs : Measurable (Function.uncurry step)) (hW : Measurable W)
    (hW0 : ∀ s, 0 ≤ W s) {q B : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hi : ∀ s, Integrable (fun ω => W (step s ω)) P)
    (hb : ∀ s, (∫ ω, W (step s ω) ∂P) ≤ q * W s + B) (n : ℕ) (s : S) :
    Integrable (fun ξ => W (HeavyTailedProductProcess.trajectory step n s ξ))
      (Measure.infinitePi fun _ : ℕ => P) ∧
    (∫ ξ, W (HeavyTailedProductProcess.trajectory step n s ξ)
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤
      q ^ n * W s + B / (1 - q) * (1 - q ^ n) := by
  induction n generalizing s with
  | zero => simp [HeavyTailedProductProcess.trajectory]
  | succ n ih =>
    let F : Ω × (ℕ → Ω) → ℝ := fun z =>
      W (HeavyTailedProductProcess.trajectory step n (step s z.1) z.2)
    have hF : Measurable F := hW.comp
      ((HeavyTailedProductProcess.trajectory_measurable hs n).comp
        (((hs.comp measurable_prodMk_left).comp measurable_fst).prodMk measurable_snd))
    have hcontrol := WeakGradientConvolution.nonnegative_fiber_integral_bound
      hF.stronglyMeasurable (fun z => hW0 _)
      (Filter.Eventually.of_forall (fun ω => (ih (step s ω)).1))
      (((hi s).const_mul (q ^ n)).add (integrable_const (B / (1 - q) * (1 - q ^ n))))
      (Filter.Eventually.of_forall (fun ω => (ih (step s ω)).2))
    have hsplit := HeavyTailedProductProcess.head_tail_preserving P
    have heq : (fun ξ => W (HeavyTailedProductProcess.trajectory step (n + 1) s ξ)) =
        F ∘ (fun ξ : ℕ → Ω => (ξ 0, fun k => ξ (k + 1))) := rfl
    rw [heq]
    refine ⟨hsplit.integrable_comp_of_integrable hcontrol.1, ?_⟩
    have heint := integral_map (μ := Measure.infinitePi fun _ : ℕ => P)
      hsplit.measurable.aemeasurable hF.aestronglyMeasurable
    rw [hsplit.map_eq] at heint
    change (∫ ξ, F (ξ 0, fun k => ξ (k + 1)) ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ _
    rw [← heint]
    simp only [Pi.add_apply] at hcontrol
    rw [integral_add ((hi s).const_mul _) (integrable_const _),
      integral_const_mul, integral_const] at hcontrol
    simp only [probReal_univ, smul_eq_mul, one_mul] at hcontrol
    calc
      _ ≤ q ^ n * (q * W s + B) + B / (1 - q) * (1 - q ^ n) :=
        hcontrol.2.trans (add_le_add
          (mul_le_mul_of_nonneg_left (hb s) (pow_nonneg hq n)) le_rfl)
      _ = _ := by
        have hd : 1 - q ≠ 0 := by linarith
        rw [pow_succ]
        field_simp
        ring

lemma contractive_noise_step {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : E → E} {x y : E}
    {e : Ω → E} {q p V : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hq : 0 ≤ q)
    (hT : ‖T x - T y‖ ≤ q * ‖x - y‖)
    (he : Integrable e P) (hep : Integrable (fun ω => ‖e ω‖ ^ p) P)
    (hmean : ∫ ω, e ω ∂P = 0) (hV : (∫ ω, ‖e ω‖ ^ p ∂P) ≤ V) :
    (∫ ω, ‖T x + e ω - T y‖ ^ p ∂P) ≤ q ^ p * ‖x - y‖ ^ p + 6 * V := by
  have hn := HeavyTailedMomentBounds.integral_norm_add_rpow_le hp hp2 he hep hmean
    (w := T x - T y)
  have hc := Real.rpow_le_rpow (norm_nonneg _) hT (by linarith : 0 ≤ p)
  rw [Real.mul_rpow hq (norm_nonneg _)] at hc
  have hid : (fun ω => ‖T x + e ω - T y‖ ^ p) =
      (fun ω => ‖T x - T y + e ω‖ ^ p) := by
    funext ω
    congr 2
    abel
  rw [hid]
  linarith

lemma contractive_moment_uniform {a : ℕ → ℝ} {q V : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (hV : 0 ≤ V) (hzero : a 0 = 0)
    (hstep : ∀ n, a (n + 1) ≤ q * a n + V) (n : ℕ) :
    a n ≤ V / (1 - q) := by
  have hd : 0 < 1 - q := by linarith
  induction n with
  | zero => rw [hzero]; positivity
  | succ n ih =>
    calc
      a (n + 1) ≤ q * a n + V := hstep n
      _ ≤ q * (V / (1 - q)) + V := by gcongr
      _ = V / (1 - q) := by field_simp; ring

lemma coupled_trajectory_moment {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {T : E → E} {e : E → Ω → E}
    (hT : Measurable T) (he : Measurable (Function.uncurry e))
    {q p V : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hq : 0 ≤ q) (hq1 : q < 1)
    (hV0 : 0 ≤ V) (hc : ∀ x y, ‖T x - T y‖ ≤ q * ‖x - y‖)
    (hei : ∀ x, Integrable (e x) P)
    (hepi : ∀ x, Integrable (fun ω => ‖e x ω‖ ^ p) P)
    (hmean : ∀ x, ∫ ω, e x ω ∂P = 0)
    (hV : ∀ x, (∫ ω, ‖e x ω‖ ^ p ∂P) ≤ V) (n : ℕ) (x : E) :
    let step := fun (z : E × E) ω => (T z.1 + e z.1 ω, T z.2)
    let error := fun ξ =>
      let z := HeavyTailedProductProcess.trajectory step n (x, x) ξ
      ‖z.1 - z.2‖ ^ p
    Integrable error (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, error ξ ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 6 * V / (1 - q ^ p) := by
  intro step error
  let W : E × E → ℝ := fun z => ‖z.1 - z.2‖ ^ p
  have hs : Measurable (Function.uncurry step) := by
    exact ((hT.comp measurable_fst.fst).add
      (he.comp (measurable_fst.fst.prodMk measurable_snd))).prodMk
        (hT.comp measurable_fst.snd)
  have hWi (z : E × E) : Integrable (fun ω => W (step z ω)) P := by
    have h := HeavyTailedMomentBounds.integrable_norm_add_rpow (T z.1 - T z.2)
      (by linarith : 0 < p) (hei z.1).aestronglyMeasurable (hepi z.1)
    convert h using 1
    funext ω
    dsimp [W, step]
    congr 2
    abel
  have hb (z : E × E) : (∫ ω, W (step z ω) ∂P) ≤ q ^ p * W z + 6 * V :=
    contractive_noise_step hp hp2 hq (hc z.1 z.2) (hei z.1) (hepi z.1)
      (hmean z.1) (hV z.1)
  have hqp : 0 ≤ q ^ p := Real.rpow_nonneg hq p
  have hqp1 : q ^ p < 1 := Real.rpow_lt_one hq hq1 (by linarith)
  have h := trajectory_lyapunov P (W := W) hs (by dsimp [W]; fun_prop)
    (fun z => Real.rpow_nonneg (norm_nonneg _) _) hqp hqp1 hWi hb n (x, x)
  have hzero : W (x, x) = 0 := by simp [W, Real.zero_rpow (by linarith : p ≠ 0)]
  rw [hzero, mul_zero, zero_add] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hK : 0 ≤ 6 * V / (1 - q ^ p) := by positivity
  nlinarith [mul_nonneg hK (pow_nonneg hqp n)]

lemma centered_batch_properties {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {e : Ω → E}
    (he : Measurable e) {p V : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : Integrable e P) (hm : (∫ ω, e ω ∂P) = 0)
    (hpi : Integrable (fun ω => ‖e ω‖ ^ p) P)
    (hb : (∫ ω, ‖e ω‖ ^ p ∂P) ≤ V) (n : ℕ) (hn : 0 < n) :
    let Q := Measure.infinitePi fun _ : ℕ => P
    let b := fun ξ : ℕ → Ω => (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, e (ξ k)
    Integrable b Q ∧ (∫ ξ, b ξ ∂Q) = 0 ∧ Integrable (fun ξ => ‖b ξ‖ ^ p) Q ∧
      (∫ ξ, ‖b ξ‖ ^ p ∂Q) ≤ 6 * V / (n : ℝ) ^ (p - 1) := by
  intro Q b
  have hi' (k : ℕ) : Integrable (fun ξ : ℕ → Ω => e (ξ k)) Q :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => P) k).integrable_comp_of_integrable hi
  have hm' (k : ℕ) : (∫ ξ : ℕ → Ω, e (ξ k) ∂Q) = 0 := by
    have hh := measurePreserving_eval_infinitePi (fun _ : ℕ => P) k
    rw [← integral_map_of_stronglyMeasurable hh.measurable he.stronglyMeasurable,
      hh.map_eq, hm]
  refine ⟨(integrable_finsetSum _ (fun k _ => hi' k)).smul _, ?_,
    HeavyTailedFreshProcess.iid_batch_moment P he hp hp2 hi hm hpi hb n hn⟩
  dsimp [b]
  rw [integral_smul, integral_finsetSum _ (fun k _ => hi' k)]
  simp_rw [hm']
  simp

lemma batch_oracle_properties {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {oracle : Ω → E} {g : E}
    (ho : Measurable oracle) {p V : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : Integrable oracle P) (hm : (∫ ω, oracle ω ∂P) = g)
    (hpi : Integrable (fun ω => ‖oracle ω - g‖ ^ p) P)
    (hb : (∫ ω, ‖oracle ω - g‖ ^ p ∂P) ≤ V) (n : ℕ) (hn : 0 < n) :
    let Q := Measure.infinitePi fun _ : ℕ => P
    let b := fun ξ : ℕ → Ω => (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, oracle (ξ k)
    Integrable b Q ∧ (∫ ξ, b ξ ∂Q) = g ∧
      Integrable (fun ξ => ‖b ξ - g‖ ^ p) Q ∧
      (∫ ξ, ‖b ξ - g‖ ^ p ∂Q) ≤ 6 * V / (n : ℝ) ^ (p - 1) := by
  intro Q b
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let e := fun ω => oracle ω - g
  have hemean : (∫ ω, e ω ∂P) = 0 := by
    dsimp [e]
    rw [integral_sub hi (integrable_const _), hm, integral_const]
    simp
  have h := centered_batch_properties P (e := e) (ho.sub measurable_const) hp hp2
    (hi.sub (integrable_const g)) hemean hpi hb n hn
  have heq (ξ : ℕ → Ω) :
      (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, e (ξ k) = b ξ - g := by
    dsimp [e, b]
    rw [Finset.sum_sub_distrib, smul_sub]
    simp [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hn0]
  dsimp only at h
  simp_rw [heq] at h
  have hbi : Integrable b Q := by
    convert h.1.add (integrable_const g) using 1
    funext ξ
    simp only [Pi.add_apply, sub_add_cancel]
  refine ⟨hbi, ?_, h.2.2⟩
  have hh := h.2.1
  rw [integral_sub hbi (integrable_const g), integral_const] at hh
  simpa using sub_eq_zero.mp hh

lemma finite_batch_oracle_properties {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {oracle : Ω → E} {g : E}
    (ho : Measurable oracle) {p V : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : Integrable oracle P) (hm : (∫ ω, oracle ω ∂P) = g)
    (hpi : Integrable (fun ω => ‖oracle ω - g‖ ^ p) P)
    (hb : (∫ ω, ‖oracle ω - g‖ ^ p ∂P) ≤ V) (n : ℕ) (hn : 0 < n) :
    let Q := Measure.pi fun _ : Fin n => P
    let b := fun ξ : Fin n → Ω => (n : ℝ)⁻¹ • ∑ k : Fin n, oracle (ξ k)
    Integrable b Q ∧ (∫ ξ, b ξ ∂Q) = g ∧
      Integrable (fun ξ => ‖b ξ - g‖ ^ p) Q ∧
      (∫ ξ, ‖b ξ - g‖ ^ p ∂Q) ≤ 6 * V / (n : ℝ) ^ (p - 1) := by
  intro Q b
  let R := Measure.infinitePi fun _ : ℕ => P
  let restrict := fun ξ : ℕ → Ω => fun i : Fin n => ξ i
  have hr : MeasurePreserving restrict R Q := by
    have hIID := OracleTemplate.StochasticGeneralized.infinitePi_iid P
    have hh := (measurePreserving_eval_infinitePi
      (fun _ : ℕ => Measure.pi fun _ : Fin n => P) 0).comp
      (OracleTemplate.FiniteVariance.infinite_block_law P R
        hIID.independent hIID.marginal n)
    simpa [Function.comp_def, restrict] using hh
  have hbm : Measurable b := by dsimp [b]; fun_prop
  have hpm : Measurable (fun ξ => ‖b ξ - g‖ ^ p) :=
    (hbm.sub measurable_const).norm.pow_const p
  have heq (ξ : ℕ → Ω) : b (restrict ξ) =
      (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, oracle (ξ k) := by
    dsimp [b, restrict]
    rw [Fin.sum_univ_eq_sum_range (fun k => oracle (ξ k))]
  have h := batch_oracle_properties P ho hp hp2 hi hm hpi hb n hn
  dsimp only at h
  simp_rw [← heq] at h
  refine ⟨(hr.integrable_comp hbm.aestronglyMeasurable).mp h.1, ?_,
    (hr.integrable_comp hpm.aestronglyMeasurable).mp h.2.2.1, ?_⟩
  · rw [← hr.map_eq, integral_map_of_stronglyMeasurable hr.measurable hbm.stronglyMeasurable]
    exact h.2.1
  · rw [← hr.map_eq, integral_map_of_stronglyMeasurable hr.measurable hpm.stronglyMeasurable]
    exact h.2.2.2

lemma fast_moment_factor {p : ℝ} (hp : 1 ≤ p) :
    6 / (1 - (31 / 32 : ℝ) ^ p) ≤ 192 := by
  have hq := Real.rpow_le_self_of_le_one (by norm_num : (0 : ℝ) ≤ 31 / 32)
    (by norm_num : (31 / 32 : ℝ) ≤ 1) hp
  have hd : 0 < 1 - (31 / 32 : ℝ) ^ p := by linarith
  apply (div_le_iff₀ hd).mpr
  linarith

lemma coupled_gradient_moment {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {field : E → E} {oracle : E → Ω → E}
    (hf : Measurable field) (ho : Measurable (Function.uncurry oracle))
    {L p V : ℝ} (hL : 0 < L) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hV0 : 0 ≤ V)
    (hm : ∀ x y, L / 4 * ‖x - y‖ ^ 2 ≤ inner ℝ (field x - field y) (x - y))
    (hl : ∀ x y, ‖field x - field y‖ ≤ L * ‖x - y‖)
    (hoi : ∀ x, Integrable (oracle x) P)
    (hop : ∀ x, Integrable (fun ω => ‖oracle x ω - field x‖ ^ p) P)
    (homean : ∀ x, ∫ ω, oracle x ω ∂P = field x)
    (hoV : ∀ x, (∫ ω, ‖oracle x ω - field x‖ ^ p ∂P) ≤ V) (n : ℕ) (x : E) :
    let η := 1 / (4 * L)
    let step := fun (z : E × E) ω => (z.1 - η • oracle z.1 ω, z.2 - η • field z.2)
    let error := fun ξ =>
      let z := HeavyTailedProductProcess.trajectory step n (x, x) ξ
      ‖z.1 - z.2‖ ^ p
    Integrable error (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, error ξ ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 192 * η ^ p * V := by
  intro η step error
  have hη : 0 ≤ η := by dsimp [η]; positivity
  let T := fun z => z - η • field z
  let e := fun z ω => (-η) • (oracle z ω - field z)
  have hei (z : E) : Integrable (e z) P :=
    ((hoi z).sub (integrable_const _)).smul _
  have hnorm (z : E) (ω : Ω) : ‖e z ω‖ ^ p = η ^ p * ‖oracle z ω - field z‖ ^ p := by
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hη,
      Real.mul_rpow hη (norm_nonneg _)]
  have hepi (z : E) : Integrable (fun ω => ‖e z ω‖ ^ p) P := by
    simp_rw [hnorm]
    exact (hop z).const_mul _
  have hemean (z : E) : (∫ ω, e z ω ∂P) = 0 := by
    dsimp [e]
    rw [integral_smul, integral_sub (hoi z) (integrable_const _), homean,
      integral_const]
    simp
  have heV (z : E) : (∫ ω, ‖e z ω‖ ^ p ∂P) ≤ η ^ p * V := by
    simp_rw [hnorm]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hoV z) (Real.rpow_nonneg hη p)
  have hc : ∀ a b, ‖T a - T b‖ ≤ (31 / 32 : ℝ) * ‖a - b‖ := fun a b =>
    HeavyTailSaddleGeometry.fast_step_contraction hL a b (hm a b) (hl a b)
  have h := coupled_trajectory_moment P (T := T) (e := e) (by dsimp [T]; fun_prop)
    (by dsimp [e]; fun_prop) hp hp2 (by norm_num) (by norm_num)
    (mul_nonneg (Real.rpow_nonneg hη p) hV0) hc hei hepi hemean heV n x
  have heq : (fun (z : E × E) ω => (T z.1 + e z.1 ω, T z.2)) = step := by
    funext z ω
    dsimp [T, e, step]
    congr 1
    module
  dsimp only at h
  rw [heq] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hb := mul_le_mul_of_nonneg_right (fast_moment_factor hp)
    (mul_nonneg (Real.rpow_nonneg hη p) hV0)
  convert hb using 1 <;> ring

lemma coupled_batched_gradient_moment {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Measure (ℕ → Ω)) [IsProbabilityMeasure S]
    (hIID : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
      (fun k ξ => ξ k) P S) {field : E → E} {oracle : E → Ω → E}
    (hf : Measurable field) (ho : Measurable (Function.uncurry oracle))
    {L p V : ℝ} (hL : 0 < L) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hV0 : 0 ≤ V)
    (hm : ∀ x y, L / 4 * ‖x - y‖ ^ 2 ≤ inner ℝ (field x - field y) (x - y))
    (hl : ∀ x y, ‖field x - field y‖ ≤ L * ‖x - y‖)
    (hoi : ∀ x, Integrable (oracle x) P)
    (hop : ∀ x, Integrable (fun ω => ‖oracle x ω - field x‖ ^ p) P)
    (homean : ∀ x, ∫ ω, oracle x ω ∂P = field x)
    (hoV : ∀ x, (∫ ω, ‖oracle x ω - field x‖ ^ p ∂P) ≤ V)
    (batch : ℕ) (hbatch : 0 < batch) (n : ℕ) (x : E) :
    let B := fun z (ξ : Fin batch → Ω) =>
      (batch : ℝ)⁻¹ • ∑ k : Fin batch, oracle z (ξ k)
    let η := 1 / (4 * L)
    let step := fun (z : E × E) ξ => (z.1 - η • B z.1 ξ, z.2 - η • field z.2)
    let error := fun ξ =>
      let z := HeavyTailedProductProcess.trajectory step n (x, x)
        (fun k (i : Fin batch) => ξ (k * batch + i.val))
      ‖z.1 - z.2‖ ^ p
    Integrable error S ∧
      (∫ ξ, error ξ ∂S) ≤
        192 * η ^ p * (6 * V / (batch : ℝ) ^ (p - 1)) := by
  intro B η step error
  let Q := Measure.pi fun _ : Fin batch => P
  have hB (z : E) := finite_batch_oracle_properties P
    (ho.comp (measurable_const.prodMk measurable_id)) hp hp2
    (hoi z) (homean z) (hop z) (hoV z) batch hbatch
  have hBm : Measurable (Function.uncurry B) := by
    dsimp [B, Function.uncurry]
    fun_prop
  have h := coupled_gradient_moment Q hf hBm hL hp hp2 (by positivity) hm hl
    (fun z => (hB z).1) (fun z => (hB z).2.2.1)
    (fun z => (hB z).2.1) (fun z => (hB z).2.2.2) n x

  have hs : Measurable (Function.uncurry step) := by
    dsimp [step]
    fun_prop
  have ht : Measurable (fun ξ : ℕ → Fin batch → Ω =>
      HeavyTailedProductProcess.trajectory step n (x, x) ξ) :=
    (HeavyTailedProductProcess.trajectory_measurable hs n).comp
      (measurable_const.prodMk measurable_id)
  have he : Measurable (fun ξ : ℕ → Fin batch → Ω =>
      let z := HeavyTailedProductProcess.trajectory step n (x, x) ξ
      ‖z.1 - z.2‖ ^ p) := (ht.fst.sub ht.snd).norm.pow_const p
  have hmap := OracleTemplate.FiniteVariance.infinite_block_law P S
    hIID.independent hIID.marginal batch
  refine ⟨hmap.integrable_comp_of_integrable h.1, ?_⟩
  have heq := integral_map_of_stronglyMeasurable (μ := S) hmap.measurable he.stronglyMeasurable
  rw [hmap.map_eq] at heq
  exact heq.symm.trans_le h.2

lemma fresh_output_moment {E F Ω Ψ : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (P : Measure Ω) (Q : Measure Ψ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {field : E → F} {oracle : E → Ω → F} {U : Ψ → E} {u : E}
    (ho : Measurable (Function.uncurry oracle)) (hU : Measurable U)
    {L p V W : ℝ} (hL : 0 ≤ L) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hl : ∀ x, ‖field x - field u‖ ≤ L * ‖x - u‖)
    (hoi : ∀ x, Integrable (oracle x) P)
    (hop : ∀ x, Integrable (fun ω => ‖oracle x ω - field x‖ ^ p) P)
    (homean : ∀ x, ∫ ω, oracle x ω ∂P = field x)
    (hoV : ∀ x, (∫ ω, ‖oracle x ω - field x‖ ^ p ∂P) ≤ V)
    (hUi : Integrable (fun ξ => ‖U ξ - u‖ ^ p) Q)
    (hUW : (∫ ξ, ‖U ξ - u‖ ^ p ∂Q) ≤ W) :
    let error := fun z : Ψ × Ω => ‖oracle (U z.1) z.2 - field u‖ ^ p
    Integrable error (Q.prod P) ∧ (∫ z, error z ∂Q.prod P) ≤ L ^ p * W + 6 * V := by
  intro error
  have hp0 : 0 < p := by linarith
  have heq (ξ : Ψ) (ω : Ω) : oracle (U ξ) ω - field u =
      (field (U ξ) - field u) + (oracle (U ξ) ω - field (U ξ)) := by abel
  have hni (ξ : Ψ) := (hoi (U ξ)).sub (integrable_const (field (U ξ)))
  have hnm (ξ : Ψ) : (∫ ω, oracle (U ξ) ω - field (U ξ) ∂P) = 0 := by
    rw [integral_sub (hoi (U ξ)) (integrable_const _), homean, integral_const]
    simp
  have hEi (ξ : Ψ) : Integrable (fun ω => error (ξ, ω)) P := by
    dsimp [error]
    simp_rw [heq]
    exact HeavyTailedMomentBounds.integrable_norm_add_rpow _ hp0
      (hni ξ).aestronglyMeasurable (hop (U ξ))
  have hEb (ξ : Ψ) : (∫ ω, error (ξ, ω) ∂P) ≤
      L ^ p * ‖U ξ - u‖ ^ p + 6 * V := by
    dsimp [error]
    simp_rw [heq]
    have hh := HeavyTailedMomentBounds.integral_norm_add_rpow_le
      (w := field (U ξ) - field u) hp hp2
      (hni ξ) (hop (U ξ)) (hnm ξ)
    have hc := Real.rpow_le_rpow (norm_nonneg _) (hl (U ξ)) hp0.le
    rw [Real.mul_rpow hL (norm_nonneg _)] at hc
    exact hh.trans (add_le_add hc (mul_le_mul_of_nonneg_left (hoV (U ξ)) (by norm_num)))
  have hE : Measurable error := by
    exact ((ho.comp ((hU.comp measurable_fst).prodMk measurable_snd)).sub
      measurable_const).norm.pow_const p
  have h := WeakGradientConvolution.nonnegative_fiber_integral_bound
    hE.stronglyMeasurable (fun z => Real.rpow_nonneg (norm_nonneg _) _)
    (Filter.Eventually.of_forall hEi)
    ((hUi.const_mul (L ^ p)).add (integrable_const (6 * V)))
    (Filter.Eventually.of_forall hEb)
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [Pi.add_apply]
  rw [integral_add (hUi.const_mul _) (integrable_const _), integral_const_mul, integral_const]
  simp only [smul_eq_mul, probReal_univ, one_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hUW (Real.rpow_nonneg hL p)) le_rfl

lemma norm_sum_power_le {E : Type*} [NormedAddCommGroup E] (x y : E)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ‖x + y‖ ^ p ≤ 2 * (‖x‖ ^ p + ‖y‖ ^ p) := by
  have hsum : (‖x‖ + ‖y‖) ^ p ≤ (2 : ℝ) ^ (p - 1) * (‖x‖ ^ p + ‖y‖ ^ p) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
      (⟨‖x‖, norm_nonneg _⟩ : NNReal) (⟨‖y‖, norm_nonneg _⟩ : NNReal) hp
  have htwo : (2 : ℝ) ^ (p - 1) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one _
  exact (Real.rpow_le_rpow (norm_nonneg _) (norm_add_le x y) (by linarith)).trans
    (hsum.trans (mul_le_mul_of_nonneg_right htwo (by positivity)))

lemma mean_error_power_le {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → E} (hi : Integrable X P) (θ : E) {p : ℝ} (hp : 1 < p)
    (hpi : Integrable (fun ω => ‖X ω - θ‖ ^ p) P) :
    ‖(∫ ω, X ω ∂P) - θ‖ ^ p ≤ ∫ ω, ‖X ω - θ‖ ^ p ∂P := by
  have hx := hi.sub (integrable_const θ)
  have hh := (norm_integral_le_integral_norm (fun ω => X ω - θ)).trans
    (HeavyTailedMomentBounds.integral_norm_le_root_moment hp hx.aestronglyMeasurable hpi)
  have hc := Real.rpow_le_rpow (norm_nonneg _) hh (by linarith : 0 ≤ p)
  rw [integral_sub hi (integrable_const θ), integral_const] at hc
  simp only [probReal_univ, one_smul] at hc
  have hn : 0 ≤ ∫ ω, ‖X ω - θ‖ ^ p ∂P :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  rw [← Real.rpow_mul hn, one_div_mul_cancel (by linarith : p ≠ 0), Real.rpow_one] at hc
  exact hc

lemma moment_mean_bound {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → E} (hX : AEStronglyMeasurable X P) (θ : E) {p M : ℝ} (hp : 1 < p)
    (hpi : Integrable (fun ω => ‖X ω - θ‖ ^ p) P)
    (hM : (∫ ω, ‖X ω - θ‖ ^ p ∂P) ≤ M) :
    Integrable X P ∧ ‖(∫ ω, X ω ∂P) - θ‖ ≤ M ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hXp : MemLp (fun ω => X ω - θ) (ENNReal.ofReal p) P := by
    apply (integrable_norm_rpow_iff (hX.sub aestronglyMeasurable_const)
      (by simp [hp0]) (by simp)).mp
    simpa only [ENNReal.toReal_ofReal hp0.le, Pi.sub_apply] using hpi
  have hq : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  have hxi : Integrable (fun ω => X ω - θ) P :=
    memLp_one_iff_integrable.mp (hXp.mono_exponent hq)
  have hi : Integrable X P := by
    convert hxi.add (integrable_const θ) using 1
    funext ω
    simp only [Pi.add_apply, sub_add_cancel]
  refine ⟨hi, ?_⟩
  have hh := (norm_integral_le_integral_norm (fun ω => X ω - θ)).trans
    (HeavyTailedMomentBounds.integral_norm_le_root_moment hp hxi.aestronglyMeasurable hpi)
  rw [integral_sub hi (integrable_const θ), integral_const] at hh
  simp only [probReal_univ, one_smul] at hh
  exact hh.trans (Real.rpow_le_rpow
    (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)) hM (by positivity))

lemma centered_moment_le {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → E} (hi : Integrable X P) (θ : E) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (hpi : Integrable (fun ω => ‖X ω - θ‖ ^ p) P) :
    Integrable (fun ω => ‖X ω - ∫ z, X z ∂P‖ ^ p) P ∧
      (∫ ω, ‖X ω - ∫ z, X z ∂P‖ ^ p ∂P) ≤
        4 * ∫ ω, ‖X ω - θ‖ ^ p ∂P := by
  let m := ∫ z, X z ∂P
  have heq (ω : Ω) : X ω - m = (θ - m) + (X ω - θ) := by abel
  have hi' : Integrable (fun ω => ‖X ω - m‖ ^ p) P := by
    simp_rw [heq]
    exact HeavyTailedMomentBounds.integrable_norm_add_rpow _ (by linarith)
      (hi.sub (integrable_const θ)).aestronglyMeasurable hpi
  refine ⟨hi', ?_⟩
  have hb := integral_mono hi'
    (((integrable_const (‖θ - m‖ ^ p)).add hpi).const_mul 2)
    (fun ω => by rw [heq]; exact norm_sum_power_le _ _ hp.le hp2)
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_add (integrable_const _) hpi, integral_const] at hb
  simp only [probReal_univ, one_smul, norm_sub_rev θ m] at hb
  have hm := mean_error_power_le P hi θ hp hpi
  change ‖m - θ‖ ^ p ≤ _ at hm
  dsimp only [m] at hb
  linarith

lemma weighted_moment_term {a w V p : ℝ} (ha : 0 ≤ a) (hw : 0 < w)
    (h : a ^ p ≤ V * w ^ (p - 1)) : w * (a / w) ^ p ≤ V := by
  rw [Real.div_rpow ha hw.le]
  rw [Real.rpow_sub_one hw.ne'] at h
  have hp : 0 < w ^ p := Real.rpow_pos_of_pos hw p
  have hh := (le_div_iff₀ hw).mp (show a ^ p ≤ V * w ^ p / w by simpa [mul_div_assoc] using h)
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hp).mpr (by simpa [mul_comm] using hh)

lemma weighted_moment_sum {ι : Type*} (s : Finset ι) (a w : ι → ℝ) (V p : ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hw : ∀ i ∈ s, 0 < w i)
    (h : ∀ i ∈ s, a i ^ p ≤ V * w i ^ (p - 1)) :
    ∑ i ∈ s, w i * (a i / w i) ^ p ≤ s.card * V := by
  calc
    _ ≤ ∑ _i ∈ s, V := Finset.sum_le_sum fun i hi =>
      weighted_moment_term (ha i hi) (hw i hi) (h i hi)
    _ = _ := by simp [nsmul_eq_mul]

lemma random_level_moment {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {J : ℕ} {D : Fin (J + 1) → Ω → E} {p A : ℝ}
    (hD : Measurable (Function.uncurry D))
    (hi : ∀ j, Integrable (fun ω => ‖D j ω‖ ^ p) P)
    (hb : ∀ j, (∫ ω, ‖D j ω‖ ^ p ∂P) ≤ A * (levelWeight J j) ^ (p - 1)) :
    let F := fun z : Fin (J + 1) × Ω => ‖(levelWeight J z.1)⁻¹ • D z.1 z.2‖ ^ p
    Integrable F ((levelLaw J : Measure _).prod P) ∧
      (∫ z, F z ∂(levelLaw J : Measure _).prod P) ≤ (J + 1) * A := by
  intro F
  have hscale (j : Fin (J + 1)) (ω : Ω) :
      F (j, ω) = (levelWeight J j)⁻¹ ^ p * ‖D j ω‖ ^ p := by
    dsimp [F]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (level_weight_pos J j).le),
      Real.mul_rpow (inv_nonneg.mpr (level_weight_pos J j).le) (norm_nonneg _)]
  have hFi (j : Fin (J + 1)) : Integrable (fun ω => F (j, ω)) P := by
    simp_rw [hscale]
    exact (hi j).const_mul _
  have hF : Measurable F := by
    have hw : Measurable (fun j : Fin (J + 1) => (levelWeight J j)⁻¹) :=
      measurable_of_countable _
    exact (((hw.comp measurable_fst).smul hD).norm).pow_const p
  have hprod := WeakGradientConvolution.nonnegative_fiber_integral_bound
    hF.stronglyMeasurable (fun z => Real.rpow_nonneg (norm_nonneg _) _)
    (Filter.Eventually.of_forall hFi)
    (show Integrable (fun j => ∫ ω, F (j, ω) ∂P) (levelLaw J : Measure _) from
      Integrable.of_finite)
    (Filter.Eventually.of_forall (fun j => le_refl (∫ ω, F (j, ω) ∂P)))
  refine ⟨hprod.1, hprod.2.trans ?_⟩
  rw [integral_fintype (Integrable.of_finite)]
  simp only [level_law_singleton, smul_eq_mul]
  calc
    _ ≤ ∑ _j : Fin (J + 1), A := by
      apply Finset.sum_le_sum
      intro j hj
      simp_rw [hscale]
      rw [integral_const_mul, Real.inv_rpow (level_weight_pos J j).le]
      have h := hb j
      rw [Real.rpow_sub_one (level_weight_pos J j).ne'] at h
      have hh : (levelWeight J j) * (∫ ω, ‖D j ω‖ ^ p ∂P) ≤
          A * (levelWeight J j) ^ p := by
        have h' := (le_div_iff₀ (level_weight_pos J j)).mp
          (show (∫ ω, ‖D j ω‖ ^ p ∂P) ≤ A * (levelWeight J j) ^ p / levelWeight J j by
            simpa [mul_div_assoc] using h)
        simpa [mul_comm] using h'
      have hp : 0 < (levelWeight J j) ^ p := Real.rpow_pos_of_pos (level_weight_pos J j) p
      apply (div_le_iff₀ hp).mpr hh |>.trans_eq'
      ring
    _ = _ := by simp

lemma dyadic_moment_weight {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (J : ℕ) (j : Fin (J + 1)) :
    1 / ((2 : ℝ) ^ j.val) ^ (p - 1) ≤ 2 * (levelWeight J j) ^ (p - 1) := by
  have hbase : ((2 : ℝ) ^ j.val)⁻¹ ≤ 2 * levelWeight J j := by
    have h := (level_weight_bounds J j).1
    rw [inv_pow] at h
    linarith
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ ((2 : ℝ) ^ j.val)⁻¹)
    hbase (show 0 ≤ p - 1 by linarith)
  rw [Real.inv_rpow (by positivity), Real.mul_rpow (by norm_num) (level_weight_pos J j).le] at hh
  have hc : (2 : ℝ) ^ (p - 1) ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show p - 1 ≤ 1 by linarith)
  simpa only [one_div] using hh.trans
    (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (level_weight_pos J j).le _))

lemma difference_moment {E Ω : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y) (θ : E)
    {p U V : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hXi : Integrable (fun ω => ‖X ω - θ‖ ^ p) P)
    (hYi : Integrable (fun ω => ‖Y ω - θ‖ ^ p) P)
    (hU : (∫ ω, ‖X ω - θ‖ ^ p ∂P) ≤ U)
    (hV : (∫ ω, ‖Y ω - θ‖ ^ p ∂P) ≤ V) :
    Integrable (fun ω => ‖X ω - Y ω‖ ^ p) P ∧
      (∫ ω, ‖X ω - Y ω‖ ^ p ∂P) ≤ 2 * (U + V) := by
  have heq (ω : Ω) : X ω - Y ω = (X ω - θ) + -(Y ω - θ) := by abel
  have hneg : Integrable (fun ω => ‖-(Y ω - θ)‖ ^ p) P := by simpa only [norm_neg] using hYi
  have hi : Integrable (fun ω => ‖X ω - Y ω‖ ^ p) P := by
    simp_rw [heq]
    exact HeavyTailedMomentBounds.integrable_norm_sum_rpow (by linarith)
      (hX.sub measurable_const).aestronglyMeasurable
      (hY.sub measurable_const).neg.aestronglyMeasurable hXi hneg
  refine ⟨hi, ?_⟩
  have hb := integral_mono hi ((hXi.add hYi).const_mul 2) (fun ω => ?_)
  · simp only [Pi.add_apply] at hb
    rw [integral_const_mul, integral_add hXi hYi] at hb
    linarith
  · rw [heq]
    simpa only [norm_neg, Pi.add_apply] using norm_sum_power_le (X ω - θ) (-(Y ω - θ)) hp hp2

lemma random_reply_moment {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {J : ℕ} {base : Ω → E} {D : Fin (J + 1) → Ω → E} (θ : E)
    (hb : Measurable base) (hD : Measurable (Function.uncurry D))
    {p A B : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hbi : Integrable (fun ω => ‖base ω - θ‖ ^ p) P)
    (hbB : (∫ ω, ‖base ω - θ‖ ^ p ∂P) ≤ B)
    (hDi : ∀ j, Integrable (fun ω => ‖D j ω‖ ^ p) P)
    (hDA : ∀ j, (∫ ω, ‖D j ω‖ ^ p ∂P) ≤ A * (levelWeight J j) ^ (p - 1)) :
    let R := fun z : Fin (J + 1) × Ω => base z.2 + (levelWeight J z.1)⁻¹ • D z.1 z.2
    Integrable (fun z => ‖R z - θ‖ ^ p) ((levelLaw J : Measure _).prod P) ∧
      (∫ z, ‖R z - θ‖ ^ p ∂(levelLaw J : Measure _).prod P) ≤
        2 * (B + (J + 1) * A) := by
  intro R
  have hcor := random_level_moment P hD hDi hDA
  dsimp only at hcor
  let C := fun z : Fin (J + 1) × Ω => ‖(levelWeight J z.1)⁻¹ • D z.1 z.2‖ ^ p
  let V := fun z : Fin (J + 1) × Ω => 2 * (‖base z.2 - θ‖ ^ p + C z)
  have hCi : Integrable C ((levelLaw J : Measure _).prod P) := hcor.1
  have hBi : Integrable (fun z : Fin (J + 1) × Ω => ‖base z.2 - θ‖ ^ p)
      ((levelLaw J : Measure _).prod P) := hbi.comp_snd _
  have hsum : Integrable (fun z => ‖base z.2 - θ‖ ^ p + C z)
      ((levelLaw J : Measure _).prod P) := hBi.add hCi
  have hVi : Integrable V ((levelLaw J : Measure _).prod P) := hsum.const_mul 2
  have hw : Measurable (fun j : Fin (J + 1) => (levelWeight J j)⁻¹) :=
    measurable_of_countable _
  have hR : Measurable (fun z => ‖R z - θ‖ ^ p) :=
    (((hb.comp measurable_snd).add ((hw.comp measurable_fst).smul hD)).sub
      measurable_const).norm.pow_const p
  have hbnd (z : Fin (J + 1) × Ω) : ‖R z - θ‖ ^ p ≤ V z := by
    have heq : R z - θ = (base z.2 - θ) + (levelWeight J z.1)⁻¹ • D z.1 z.2 := by
      dsimp [R]
      abel
    rw [heq]
    exact norm_sum_power_le _ _ hp hp2
  have hRi : Integrable (fun z => ‖R z - θ‖ ^ p) ((levelLaw J : Measure _).prod P) := by
    apply hVi.mono' hR.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hbnd z
  refine ⟨hRi, (integral_mono hRi hVi hbnd).trans ?_⟩
  dsimp [V]
  rw [integral_const_mul, integral_add hBi hCi,
    integral_fun_snd (fun ω => ‖base ω - θ‖ ^ p)]
  simp only [probReal_univ, one_smul]
  exact mul_le_mul_of_nonneg_left (add_le_add hbB hcor.2) (by norm_num)

lemma dyadic_reply_moments {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {J : ℕ} {base : Ω → E} {fine coarse : Fin (J + 1) → Ω → E} (θ : E)
    (hb : Measurable base) (hf : Measurable (Function.uncurry fine))
    (hc : Measurable (Function.uncurry coarse)) {p B : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hB : 0 ≤ B)
    (hbi : Integrable (fun ω => ‖base ω - θ‖ ^ p) P)
    (hbB : (∫ ω, ‖base ω - θ‖ ^ p ∂P) ≤ B)
    (hfi : ∀ j, Integrable (fun ω => ‖fine j ω - θ‖ ^ p) P)
    (hci : ∀ j, Integrable (fun ω => ‖coarse j ω - θ‖ ^ p) P)
    (hfB : ∀ j, (∫ ω, ‖fine j ω - θ‖ ^ p ∂P) ≤ B / ((2 : ℝ) ^ j.val) ^ (p - 1))
    (hcB : ∀ j, (∫ ω, ‖coarse j ω - θ‖ ^ p ∂P) ≤ B / ((2 : ℝ) ^ j.val) ^ (p - 1)) :
    let Q := (levelLaw J : Measure _).prod P
    let R := fun z : Fin (J + 1) × Ω =>
      reply (base z.2) (fun j => fine j z.2) (fun j => coarse j z.2) z.1
    Integrable R Q ∧
      Integrable (fun z => ‖R z - θ‖ ^ p) Q ∧
      (∫ z, ‖R z - θ‖ ^ p ∂Q) ≤ 18 * (J + 1) * B ∧
      Integrable (fun z => ‖R z - ∫ w, R w ∂Q‖ ^ p) Q ∧
      (∫ z, ‖R z - ∫ w, R w ∂Q‖ ^ p ∂Q) ≤ 72 * (J + 1) * B := by
  intro Q R
  have hd (j : Fin (J + 1)) := difference_moment P
    (hf.comp (measurable_const.prodMk measurable_id))
    (hc.comp (measurable_const.prodMk measurable_id)) θ hp.le hp2
    (hfi j) (hci j) (hfB j) (hcB j)
  have hD (j : Fin (J + 1)) : (∫ ω, ‖fine j ω - coarse j ω‖ ^ p ∂P) ≤
      (8 * B) * (levelWeight J j) ^ (p - 1) := by
    have hw := mul_le_mul_of_nonneg_left (dyadic_moment_weight hp.le hp2 J j)
      (show 0 ≤ 4 * B by positivity)
    have hh : (∫ ω, ‖fine j ω - coarse j ω‖ ^ p ∂P) ≤
        2 * (B / ((2 : ℝ) ^ j.val) ^ (p - 1) + B / ((2 : ℝ) ^ j.val) ^ (p - 1)) := (hd j).2
    simp only [div_eq_mul_inv] at hh hw ⊢
    nlinarith only [hh, hw]
  have hraw := random_reply_moment P θ hb (hf.sub hc) hp.le hp2 hbi hbB
    (fun j => (hd j).1) hD
  change Integrable (fun z => ‖R z - θ‖ ^ p) Q ∧
    (∫ z, ‖R z - θ‖ ^ p ∂Q) ≤ 2 * (B + (J + 1) * (8 * B)) at hraw
  have hw : Measurable (fun j : Fin (J + 1) => (levelWeight J j)⁻¹) :=
    measurable_of_countable _
  have hRm : Measurable R := (hb.comp measurable_snd).add
    ((hw.comp measurable_fst).smul (hf.sub hc))
  have hri := (moment_mean_bound Q hRm.aestronglyMeasurable θ hp hraw.1 hraw.2).1
  have hcenter := centered_moment_le Q hri θ hp hp2 hraw.1
  have hrawB : (∫ z, ‖R z - θ‖ ^ p ∂Q) ≤ 18 * (J + 1) * B := by
    have hJB : 0 ≤ (J : ℝ) * B := mul_nonneg (Nat.cast_nonneg _) hB
    nlinarith [hraw.2]
  exact ⟨hri, hraw.1, hrawB, hcenter.1, by linarith [hcenter.2]⟩

lemma clipping_second_from_bias {C p V : ℝ} (hC : 0 < C) (hp : 1 ≤ p) (hV : 0 ≤ V) :
    2 * (2 * C) ^ (2 - p) * V ≤ 4 * C * (V / (C / 2) ^ (p - 1)) := by
  have hh := Real.rpow_le_rpow (show 0 ≤ C / 2 by positivity)
    (show C / 2 ≤ 2 * C by linarith) (show 0 ≤ p - 1 by linarith)
  have hprod : (2 * C) ^ (2 - p) * (C / 2) ^ (p - 1) ≤ 2 * C := by
    calc
      _ ≤ (2 * C) ^ (2 - p) * (2 * C) ^ (p - 1) :=
        mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by positivity) _)
      _ = 2 * C := by
        rw [← Real.rpow_add (by positivity), show (2 - p) + (p - 1) = 1 by ring, Real.rpow_one]
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr
  have h := mul_le_mul_of_nonneg_right hprod (show 0 ≤ 2 * V by positivity)
  nlinarith only [h]

lemma clipped_error_bounds {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P) (u θ : E)
    (hmean : (∫ ω, X ω ∂P) = u) {C p V d : ℝ}
    (hC : 0 < C) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hV : 0 ≤ V)
    (hu : ‖u‖ ≤ C / 2) (hθ : ‖θ‖ ≤ C / 2) (hd : ‖u - θ‖ ≤ d)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P)
    (hpV : (∫ ω, ‖X ω - u‖ ^ p ∂P) ≤ V) :
    let error := fun ω => OracleTemplate.clip C (X ω) - θ
    Integrable error P ∧ Integrable (fun ω => ‖error ω‖ ^ 2) P ∧
      (∀ ω, ‖error ω‖ ≤ 3 * C / 2) ∧
      ‖∫ ω, error ω ∂P‖ ≤ d + V / (C / 2) ^ (p - 1) ∧
      (∫ ω, ‖error ω‖ ^ 2 ∂P) ≤ 2 * (2 * C) ^ (2 - p) * V + 2 * d ^ 2 := by
  intro error
  have hp0 : p ≠ 0 := by linarith
  have hvpow : (V ^ p⁻¹) ^ p = V := Real.rpow_inv_rpow hV hp0
  have hraw : (∫ ω, ‖X ω - u‖ ^ p ∂P) ≤ (V ^ p⁻¹) ^ p := by
    simpa only [hvpow] using hpV
  have hclip := OracleTemplate.integrable_clip (P := P) hX hC.le
  have hcm := (OracleTemplate.measurable_clip C).comp hX
  have hei : Integrable error P := hclip.sub (integrable_const θ)
  have heb (ω : Ω) : ‖error ω‖ ≤ 3 * C / 2 := by
    exact (norm_sub_le _ _).trans (by linarith [OracleTemplate.norm_clip_le hC.le (X ω)])
  have he2i : Integrable (fun ω => ‖error ω‖ ^ 2) P := by
    apply Integrable.of_bound ((hcm.sub_const θ).norm.pow_const 2).aestronglyMeasurable
      ((3 * C / 2) ^ 2)
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (heb ω) 2
  have hb := OracleTemplate.clipped_bias_bound hX hXi hmean hC hp hu hpi hraw
  rw [hvpow] at hb
  have hm : ‖∫ ω, error ω ∂P‖ ≤ d + V / (C / 2) ^ (p - 1) := by
    change ‖∫ ω, OracleTemplate.clip C (X ω) - θ ∂P‖ ≤ _
    rw [integral_sub hclip (integrable_const θ), integral_const]
    simp only [probReal_univ, one_smul]
    exact (norm_sub_le_norm_sub_add_norm_sub _ u θ).trans (by linarith)
  have hcenter : Integrable (fun ω => ‖OracleTemplate.clip C (X ω) - u‖ ^ 2) P := by
    apply Integrable.of_bound ((hcm.sub_const u).norm.pow_const 2).aestronglyMeasurable
      ((C + ‖u‖) ^ 2)
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖OracleTemplate.clip C (X ω) - u‖ ^ 2 ≤ (C + ‖u‖) ^ 2
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (add_le_add (OracleTemplate.norm_clip_le hC.le (X ω)) le_rfl)
  have hs := OracleTemplate.clipped_second_moment_bound hX hC.le
    (show 0 ≤ p by linarith) hp2 (show ‖u‖ ≤ C by linarith) hpi hraw
  rw [hvpow] at hs
  have hi := integral_mono he2i
    ((hcenter.add (integrable_const (‖u - θ‖ ^ 2))).const_mul 2) (fun ω => ?_)
  · simp only [Pi.add_apply] at hi
    rw [integral_const_mul, integral_add hcenter (integrable_const _), integral_const] at hi
    simp only [probReal_univ, smul_eq_mul, one_mul] at hi
    have hdsq := pow_le_pow_left₀ (norm_nonneg _) hd 2
    exact ⟨hei, he2i, heb, hm, by linarith⟩
  · have heq : error ω = (OracleTemplate.clip C (X ω) - u) + (u - θ) := by
      dsimp [error]
      abel
    rw [heq]
    simpa only [Real.rpow_two, Pi.add_apply] using
      norm_sum_power_le (OracleTemplate.clip C (X ω) - u) (u - θ)
        (by norm_num : (1 : ℝ) ≤ 2) le_rfl

lemma clipped_batch_error_bounds {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P) (u θ : E)
    (hmean : (∫ ω, X ω ∂P) = u) {C p V d : ℝ}
    (hC : 0 < C) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hV : 0 ≤ V)
    (hu : ‖u‖ ≤ C / 2) (hθ : ‖θ‖ ≤ C / 2) (hd : ‖u - θ‖ ≤ d)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P)
    (hpV : (∫ ω, ‖X ω - u‖ ^ p ∂P) ≤ V) (n : ℕ) (hn : 0 < n) :
    let Q := Measure.pi fun _ : Fin n => P
    let v := 6 * V / (n : ℝ) ^ (p - 1)
    let error := fun ξ : Fin n → Ω =>
      OracleTemplate.clip C ((n : ℝ)⁻¹ • ∑ i : Fin n, X (ξ i)) - θ
    Integrable error Q ∧ Integrable (fun ξ => ‖error ξ‖ ^ 2) Q ∧
      (∀ ξ, ‖error ξ‖ ≤ 3 * C / 2) ∧
      ‖∫ ξ, error ξ ∂Q‖ ≤ d + v / (C / 2) ^ (p - 1) ∧
      (∫ ξ, ‖error ξ‖ ^ 2 ∂Q) ≤ 2 * (2 * C) ^ (2 - p) * v + 2 * d ^ 2 := by
  intro Q v error
  have hb := finite_batch_oracle_properties P hX hp hp2 hXi hmean hpi hpV n hn
  have hm : Measurable (fun ξ : Fin n → Ω => (n : ℝ)⁻¹ • ∑ i : Fin n, X (ξ i)) := by
    fun_prop
  exact clipped_error_bounds Q hm hb.1 u θ hb.2.1 hC hp hp2 (by dsimp [v]; positivity)
    hu hθ hd hb.2.2.1 hb.2.2.2
lemma transferred_clipped_batch_bounds {E Ω Ψ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Measure Ψ)
    {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P) (u θ : E)
    (hmean : (∫ ω, X ω ∂P) = u) {C p V d : ℝ}
    (hC : 0 < C) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hV : 0 ≤ V)
    (hu : ‖u‖ ≤ C / 2) (hθ : ‖θ‖ ≤ C / 2) (hd : ‖u - θ‖ ≤ d)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P)
    (hpV : (∫ ω, ‖X ω - u‖ ^ p ∂P) ≤ V) (n : ℕ) (hn : 0 < n)
    {Y : Ψ → E} (hYbound : ∀ ω, ‖Y ω‖ ≤ C)
    (hD : ProbabilityTheory.IdentDistrib Y
      (fun ξ : Fin n → Ω => OracleTemplate.clip C ((n : ℝ)⁻¹ • ∑ i : Fin n, X (ξ i)))
      S (Measure.pi fun _ : Fin n => P)) :
    let v := 6 * V / (n : ℝ) ^ (p - 1)
    let error := fun ω => Y ω - θ
    Integrable error S ∧ Integrable (fun ω => ‖error ω‖ ^ 2) S ∧
      (∀ ω, ‖error ω‖ ≤ 3 * C / 2) ∧
      ‖∫ ω, error ω ∂S‖ ≤ d + v / (C / 2) ^ (p - 1) ∧
      (∫ ω, ‖error ω‖ ^ 2 ∂S) ≤ 2 * (2 * C) ^ (2 - p) * v + 2 * d ^ 2 := by
  intro v error
  have hb := clipped_batch_error_bounds P hX hXi u θ hmean hC hp hp2 hV hu hθ hd hpi hpV n hn
  have he := hD.comp (measurable_id.sub_const θ)
  have h2 := he.comp (measurable_norm.pow_const (2 : ℕ))
  refine ⟨he.integrable_iff.mpr hb.1, h2.integrable_iff.mpr hb.2.1, ?_, ?_, ?_⟩
  · intro ω
    exact (norm_sub_le _ _).trans (by linarith [hYbound ω])
  · have heq : (∫ ω, error ω ∂S) = ∫ ξ : Fin n → Ω,
        OracleTemplate.clip C ((n : ℝ)⁻¹ • ∑ i : Fin n, X (ξ i)) - θ
          ∂(Measure.pi fun _ : Fin n => P) := he.integral_eq
    rw [heq]
    exact hb.2.2.2.1
  · exact h2.integral_eq.trans_le hb.2.2.2.2


lemma clipping_batch_tuning {p V a b : ℝ} (hp : 1 < p) (hV : 0 ≤ V)
    (ha : 0 < a) (hb : 0 < b) :
    let n := 1 + ⌈((2 : ℝ) ^ 36 * V / (a * b ^ (p - 1))) ^ (1 / (p - 1))⌉₊
    0 < n ∧ (139968 * V / (n : ℝ) ^ (p - 1)) / (16 * b) ^ (p - 1) ≤ a / 262144 := by
  intro n
  have hn : 0 < n := by dsimp [n]; omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he : ((2 : ℝ) ^ 36 * V / (a * b ^ (p - 1))) ^ (1 / (p - 1)) ≤ (n : ℝ) := by
    have hh := Nat.le_ceil (((2 : ℝ) ^ 36 * V / (a * b ^ (p - 1))) ^ (1 / (p - 1)))
    dsimp [n]
    push_cast
    linarith
  have hbase : 0 ≤ (2 : ℝ) ^ 36 * V / (a * b ^ (p - 1)) := by positivity
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hbase _) he (show 0 ≤ p - 1 by linarith)
  rw [one_div, Real.rpow_inv_rpow hbase (by linarith : p - 1 ≠ 0)] at hpow
  have hpb : 0 < b ^ (p - 1) := Real.rpow_pos_of_pos hb _
  have hpc : 0 < (16 * b) ^ (p - 1) := Real.rpow_pos_of_pos (by positivity) _
  have hpn : 0 < (n : ℝ) ^ (p - 1) := Real.rpow_pos_of_pos hn0 _
  have hmul := (div_le_iff₀ (mul_pos ha hpb)).mp hpow
  have hbc : b ^ (p - 1) ≤ (16 * b) ^ (p - 1) := by
    apply Real.rpow_le_rpow hb.le (by linarith) (by linarith)
  have hh := mul_le_mul_of_nonneg_left hbc (mul_nonneg hpn.le ha.le)
  have hcost : (2 : ℝ) ^ 36 * V ≤ a * (n : ℝ) ^ (p - 1) * (16 * b) ^ (p - 1) := by
    nlinarith only [hmul, hh]
  refine ⟨hn, ?_⟩
  apply (div_le_iff₀ hpc).mpr
  apply (div_le_iff₀ hpn).mpr
  norm_num at hcost
  nlinarith only [hcost, hV]

lemma depth_bias_tuning {p σ a : ℝ} (hp : 1 < p) (hσ : 0 ≤ σ) (ha : 0 < a) :
    let J := ⌈Real.logb 2 (max 1 (((2 : ℝ) ^ 24 * σ / a) ^ (p / (p - 1))))⌉₊
    (324 * σ ^ p / ((2 : ℝ) ^ (J + 1)) ^ (p - 1)) ^ (1 / p) ≤ a / 8192 := by
  intro J
  have hp0 : 0 < p := by linarith
  have hs : 0 < p - 1 := by linarith
  have hr : 0 ≤ (2 : ℝ) ^ 24 * σ / a := by positivity
  have hn := OracleTemplate.ScalarHeavyTailEstimator.dyadic_ceil_lower
    (((2 : ℝ) ^ 24 * σ / a) ^ (p / (p - 1)))
  change ((2 : ℝ) ^ 24 * σ / a) ^ (p / (p - 1)) ≤ (2 : ℝ) ^ J at hn
  have hn' : ((2 : ℝ) ^ 24 * σ / a) ^ (p / (p - 1)) ≤ (2 : ℝ) ^ (J + 1) :=
    hn.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hr _) hn' hs.le
  rw [← Real.rpow_mul hr, div_mul_cancel₀ _ hs.ne'] at hpow
  have hscale : (a / 8192) ^ p * ((2 : ℝ) ^ 24 * σ / a) ^ p = (2048 : ℝ) ^ p * σ ^ p := by
    rw [← Real.mul_rpow (by positivity) hr, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2048) hσ]
    congr 1
    field_simp
    ring
  have h2048 : (324 : ℝ) ≤ (2048 : ℝ) ^ p := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2048) hp.le
    norm_num at hh
    linarith
  have hcoef := mul_le_mul_of_nonneg_right h2048 (Real.rpow_nonneg hσ p)
  have hprod := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ (a / 8192) ^ p from Real.rpow_nonneg (by positivity) p)
  rw [hscale] at hprod
  have hmoment : 324 * σ ^ p / ((2 : ℝ) ^ (J + 1)) ^ (p - 1) ≤ (a / 8192) ^ p :=
    (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr (hcoef.trans hprod)
  have hh := Real.rpow_le_rpow (by positivity) hmoment (show 0 ≤ 1 / p by positivity)
  rw [one_div, Real.rpow_rpow_inv (by positivity) hp0.ne'] at hh
  simpa only [one_div] using hh

lemma horizon_bias_tuning {ell m : ℝ} (hm : 0 < m) :
    let h := ⌈Real.logb (32 / 31) (max 1 ((2 : ℝ) ^ 18 * ell / m))⌉₊
    ell * (31 / 32 : ℝ) ^ h ≤ m / 262144 := by
  intro h
  have ht : 0 < max 1 ((2 : ℝ) ^ 18 * ell / m) := by positivity
  have hh := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 32 / 31) ht).mp
    (Nat.le_ceil (Real.logb (32 / 31) (max 1 ((2 : ℝ) ^ 18 * ell / m))))
  rw [Real.rpow_natCast] at hh
  have hb : (2 : ℝ) ^ 18 * ell / m ≤ (32 / 31 : ℝ) ^ h :=
    (le_max_right _ _).trans hh
  have hp := mul_le_mul_of_nonneg_right hb (pow_nonneg (by norm_num : (0 : ℝ) ≤ 31 / 32) h)
  have he : (32 / 31 : ℝ) ^ h * (31 / 32 : ℝ) ^ h = 1 := by
    rw [← mul_pow]
    norm_num
  rw [he] at hp
  have hd : ((2 : ℝ) ^ 18 * (ell * (31 / 32 : ℝ) ^ h)) / m ≤ 1 := by
    convert hp using 1; ring
  have hf := (div_le_one hm).mp hd
  norm_num at hf
  linarith

lemma clipping_calibration {a b p v : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a ≤ b)
    (hp : 1 ≤ p) (hv : 0 ≤ v) (hclip : v / (16 * b) ^ (p - 1) ≤ a / 262144) :
    a / 4096 + v / (16 * b) ^ (p - 1) ≤ a / 1024 ∧
      2 * (64 * b) ^ (2 - p) * v + 2 * (a / 4096) ^ 2 ≤ a * b / 512 := by
  have hh := clipping_second_from_bias (C := 32 * b) (by positivity) hp hv
  rw [show 2 * (32 * b) = 64 * b by ring, show 32 * b / 2 = 16 * b by ring] at hh
  have hc := mul_le_mul_of_nonneg_left hclip (show 0 ≤ 128 * b by positivity)
  have hab' := mul_nonneg ha (sub_nonneg.mpr hab)
  constructor
  · linarith
  · nlinarith only [hh, hc, hab']

lemma kernel_bias_bound {E : Type*} [NormedAddCommGroup E]
    {p σ Lfast m B D : ℝ} (hp : 1 < p) (hσ : 0 ≤ σ) (hm : 0 < m) (hB : 0 < B)
    (hD : 0 ≤ D) (hD2 : m * D ^ 2 ≤ 16 * B) (mean θ target : E)
    (hdet : ‖θ - target‖ ≤ Lfast * (31 / 32 : ℝ) ^ kernelHorizon Lfast m * D)
    (hmean : ‖mean - θ‖ ≤
      (324 * σ ^ p / ((2 : ℝ) ^ (kernelDepth p σ m B + 1)) ^ (p - 1)) ^ (1 / p)) :
    ‖mean - target‖ ≤ Real.sqrt (m * B) / 4096 := by
  have ha : 0 < Real.sqrt (m * B) := Real.sqrt_pos.mpr (mul_pos hm hB)
  have ha2 := Real.sq_sqrt (mul_pos hm hB).le
  have hmul := mul_le_mul_of_nonneg_left hD2 hm.le
  have hdist : m * D ≤ 4 * Real.sqrt (m * B) := by
    nlinarith [mul_nonneg hm.le hD]
  have hh := horizon_bias_tuning (ell := Lfast) hm
  change Lfast * (31 / 32 : ℝ) ^ kernelHorizon Lfast m ≤ m / 262144 at hh
  have hscaled := mul_le_mul_of_nonneg_right hh hD
  have hdet' : ‖θ - target‖ ≤ Real.sqrt (m * B) / 65536 := by
    nlinarith only [hdet, hscaled, hdist]
  have hj := depth_bias_tuning hp hσ ha
  change (324 * σ ^ p / ((2 : ℝ) ^ (kernelDepth p σ m B + 1)) ^ (p - 1)) ^ (1 / p) ≤
    Real.sqrt (m * B) / 8192 at hj
  exact (norm_sub_le_norm_sub_add_norm_sub mean θ target).trans (by linarith)

lemma kernel_error_bounds {E Ω Ψ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] [MeasurableSpace Ψ] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Measure Ψ) {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P) (u θ : E)
    (hmean : (∫ ω, X ω ∂P) = u) {p σ m H B : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hm : 0 < m) (hmH : m ≤ H) (hB : 0 < B)
    (hθ : ‖θ‖ ≤ 9 * Real.sqrt (H * B))
    (hbias : ‖u - θ‖ ≤ Real.sqrt (m * B) / 4096) (J : ℕ)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P)
    (hpV : (∫ ω, ‖X ω - u‖ ^ p ∂P) ≤ 23328 * (J + 1) * σ ^ p)
    {Y : Ψ → E} (hYbound : ∀ ω, ‖Y ω‖ ≤ 32 * Real.sqrt (H * B))
    (hD : ProbabilityTheory.IdentDistrib Y
      (fun ξ : Fin (kernelBatch p σ m H B J) → Ω =>
        OracleTemplate.clip (32 * Real.sqrt (H * B))
          ((kernelBatch p σ m H B J : ℝ)⁻¹ • ∑ i, X (ξ i)))
      S (Measure.pi fun _ : Fin (kernelBatch p σ m H B J) => P)) :
    let error := fun ω => Y ω - θ
    Integrable error S ∧ Integrable (fun ω => ‖error ω‖ ^ 2) S ∧
      (∀ ω, ‖error ω‖ ≤ 48 * Real.sqrt (H * B)) ∧
      ‖∫ ω, error ω ∂S‖ ≤ Real.sqrt (m * B) / 1024 ∧
      (∫ ω, ‖error ω‖ ^ 2 ∂S) ≤ Real.sqrt (m * B) * Real.sqrt (H * B) / 512 := by
  intro error
  let a := Real.sqrt (m * B)
  let b := Real.sqrt (H * B)
  let n := kernelBatch p σ m H B J
  let V := (J + 1 : ℝ) * σ ^ p
  let v := 139968 * V / (n : ℝ) ^ (p - 1)
  have hH : 0 < H := lt_of_lt_of_le hm hmH
  have ha : 0 < a := Real.sqrt_pos.mpr (mul_pos hm hB)
  have hb : 0 < b := Real.sqrt_pos.mpr (mul_pos hH hB)
  have hab : a ≤ b := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hmH hB.le)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have ht := clipping_batch_tuning hp hV ha hb
  change 0 < n ∧ v / (16 * b) ^ (p - 1) ≤ a / 262144 at ht
  have hu : ‖u‖ ≤ (32 * b) / 2 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub u θ 0
    simp only [sub_zero] at hh
    change ‖u - θ‖ ≤ a / 4096 at hbias
    change ‖θ‖ ≤ 9 * b at hθ
    linarith
  have hθ' : ‖θ‖ ≤ (32 * b) / 2 := by change ‖θ‖ ≤ 9 * b at hθ; linarith
  have herr := transferred_clipped_batch_bounds P S hX hXi u θ hmean
    (show 0 < 32 * b by positivity) hp.le hp2
    (show 0 ≤ 23328 * (J + 1 : ℝ) * σ ^ p by positivity) hu hθ' hbias hpi hpV n ht.1 hYbound hD
  have he : 6 * (23328 * (J + 1 : ℝ) * σ ^ p) / (n : ℝ) ^ (p - 1) = v := by dsimp [v, V]; ring
  dsimp only at herr
  rw [he, show 32 * b / 2 = 16 * b by ring,
    show 2 * (32 * b) = 64 * b by ring] at herr
  have hc := clipping_calibration ha.le hb hab hp.le (by dsimp [v]; positivity) ht.2
  refine ⟨herr.1, herr.2.1, ?_, herr.2.2.2.1.trans hc.1, herr.2.2.2.2.trans hc.2⟩
  intro ω
  have hh := herr.2.2.1 ω
  dsimp [b] at hh
  linarith

lemma joint_component_moments {E F Ω : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace Ω] (P : Measure Ω) {X : Ω → E} {Y : Ω → F}
    (hX : Measurable X) (hY : Measurable Y) {p V : ℝ} (hp : 0 ≤ p)
    (hi : Integrable (fun ω => (Real.sqrt (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2)) ^ p) P)
    (hv : (∫ ω, (Real.sqrt (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2)) ^ p ∂P) ≤ V) :
    Integrable (fun ω => ‖X ω‖ ^ p) P ∧ (∫ ω, ‖X ω‖ ^ p ∂P) ≤ V ∧
      Integrable (fun ω => ‖Y ω‖ ^ p) P ∧ (∫ ω, ‖Y ω‖ ^ p ∂P) ≤ V := by
  have hx (ω : Ω) : ‖X ω‖ ^ p ≤ (Real.sqrt (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2)) ^ p := by
    apply Real.rpow_le_rpow (norm_nonneg _) _ hp
    have hh := Real.sq_sqrt (add_nonneg (sq_nonneg ‖X ω‖) (sq_nonneg ‖Y ω‖))
    have hn := Real.sqrt_nonneg (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2)
    nlinarith [norm_nonneg (X ω), sq_nonneg ‖Y ω‖]
  have hy (ω : Ω) : ‖Y ω‖ ^ p ≤ (Real.sqrt (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2)) ^ p := by
    apply Real.rpow_le_rpow (norm_nonneg _) _ hp
    have hh := Real.sq_sqrt (add_nonneg (sq_nonneg ‖X ω‖) (sq_nonneg ‖Y ω‖))
    have hn := Real.sqrt_nonneg (‖X ω‖ ^ 2 + ‖Y ω‖ ^ 2)
    nlinarith [norm_nonneg (Y ω), sq_nonneg ‖X ω‖]
  have hxi : Integrable (fun ω => ‖X ω‖ ^ p) P := hi.mono'
    (hX.norm.pow_const p).aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hx ω))
  have hyi : Integrable (fun ω => ‖Y ω‖ ^ p) P := hi.mono'
    (hY.norm.pow_const p).aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hy ω))
  exact ⟨hxi, (integral_mono hxi hi hx).trans hv, hyi, (integral_mono hyi hi hy).trans hv⟩

lemma heterogeneous_exp_sum_moment {ι : Type*} [Fintype ι] {S : ι → Type*}
    [∀ i, MeasurableSpace (S i)] (P : (i : ι) → Measure (S i))
    [∀ i, IsProbabilityMeasure (P i)] (W : (i : ι) → S i → ℝ) (C : ι → ℝ)
    (hi : ∀ i, Integrable (fun s => Real.exp (W i s)) (P i))
    (hmean : ∀ i, (∫ s, Real.exp (W i s) ∂P i) ≤ Real.exp (2 * C i)) :
    Integrable (fun samples : (i : ι) → S i => Real.exp (∑ i, W i (samples i))) (Measure.pi P) ∧
    (∫ samples : (i : ι) → S i, Real.exp (∑ i, W i (samples i)) ∂Measure.pi P)
      ≤ Real.exp (2 * (∑ i, C i)) := by
  constructor
  · simp only [Real.exp_sum]
    exact Integrable.fintype_prod_dep hi
  · simp only [Real.exp_sum]
    rw [integral_fintype_prod_eq_prod (μ := P) (fun i s => Real.exp (W i s))]
    have hh : (∏ i, (∫ s, Real.exp (W i s) ∂P i)) ≤ ∏ i, Real.exp (2 * C i) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact integral_nonneg (fun s => (Real.exp_pos _).le)
      · intro i _
        exact hmean i
    simpa only [← Real.exp_sum, ← Finset.mul_sum] using hh

lemma prefix_exp_sum_moment {S : Type*} [MeasurableSpace S]
    (P : Measure S) [IsProbabilityMeasure P] (W : ℕ → S → ℝ) (C : ℕ → ℝ) (K : ℕ)
    (hi : ∀ j < K, Integrable (fun s => Real.exp (W j s)) P)
    (hmean : ∀ j < K, (∫ s, Real.exp (W j s) ∂P) ≤ Real.exp (2 * C j)) :
    let R := Measure.infinitePi fun _ : ℕ => P
    Integrable (fun ξ : ℕ → S => Real.exp (∑ j ∈ Finset.range K, W j (ξ j))) R ∧
    (∫ ξ : ℕ → S, Real.exp (∑ j ∈ Finset.range K, W j (ξ j)) ∂R)
      ≤ Real.exp (2 * (∑ j ∈ Finset.range K, C j)) := by
  intro R
  have hIID := OracleTemplate.StochasticGeneralized.infinitePi_iid P
  have hind := hIID.independent.precomp (g := fun i : Fin K => i.val) Fin.val_injective
  have hp : MeasurePreserving (fun ξ : ℕ → S => fun i : Fin K => ξ i) R
      (Measure.pi fun _ : Fin K => P) := by
    refine ⟨by fun_prop, ?_⟩
    simpa only [hIID.marginal] using hind.map_fun_eq_pi_map
      (fun i : Fin K => (hIID.measurable i.val).aemeasurable)
  have hh := heterogeneous_exp_sum_moment (fun _ : Fin K => P)
    (fun i s => W i s) (fun i => C i) (fun i => hi i i.isLt) (fun i => hmean i i.isLt)
  have hcomp := hp.integrable_comp_of_integrable hh.1
  have he := hp.hasLaw.integral_comp hh.1.aestronglyMeasurable
  have hsum (ξ : ℕ → S) : (∑ i : Fin K, W i (ξ i)) = ∑ j ∈ Finset.range K, W j (ξ j) :=
    Fin.sum_univ_eq_sum_range (fun j => W j (ξ j)) K
  constructor
  · simpa only [Function.comp_def, hsum] using hcomp
  · have hb := he.trans_le hh.2
    simpa only [Function.comp_def, hsum, Fin.sum_univ_eq_sum_range] using hb

lemma heterogeneous_exp_sum_tail {ι : Type*} [Fintype ι] {S : ι → Type*}
    [∀ i, MeasurableSpace (S i)] (P : (i : ι) → Measure (S i))
    [∀ i, IsProbabilityMeasure (P i)] (W : (i : ι) → S i → ℝ) (C : ι → ℝ)
    (hi : ∀ i, Integrable (fun s => Real.exp (W i s)) (P i))
    (hmean : ∀ i, (∫ s, Real.exp (W i s) ∂P i) ≤ Real.exp (2 * C i)) (t : ℝ) :
    (Measure.pi P) {samples | 2 * (∑ i, C i) + t < ∑ i, W i (samples i)} ≤
      ENNReal.ofReal (Real.exp (-t)) := by
  have hi : Integrable (fun samples : (i : ι) → S i => Real.exp (∑ i, W i (samples i)))
      (Measure.pi P) := by
    simp only [Real.exp_sum]
    exact Integrable.fintype_prod_dep hi
  have hi' := hi.const_mul (Real.exp (-(2 * (∑ i, C i) + t)))
  have hh := hi'.measure_le_integral
    (Filter.Eventually.of_forall (fun _ => by positivity))
    (s := {samples | 2 * (∑ i, C i) + t < ∑ i, W i (samples i)}) (by
      intro samples hs
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by change 2 * (∑ i, C i) + t < ∑ i, W i (samples i) at hs; linarith))
  rw [integral_const_mul] at hh
  have hprod : (∫ samples : (i : ι) → S i, Real.exp (∑ i, W i (samples i)) ∂Measure.pi P) =
      ∏ i, (∫ s, Real.exp (W i s) ∂P i) := by
    simp only [Real.exp_sum]
    exact integral_fintype_prod_eq_prod (μ := P) (fun i s => Real.exp (W i s))
  rw [hprod] at hh
  refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have hp : (∏ i, (∫ s, Real.exp (W i s) ∂P i)) ≤ ∏ i, Real.exp (2 * C i) := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact integral_nonneg (fun s => (Real.exp_pos _).le)
    · intro i _
      exact hmean i
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_pos (-(2 * (∑ i, C i) + t))).le
  convert hm using 1
  rw [← Real.exp_sum, ← Real.exp_add, ← Finset.mul_sum]
  congr 1
  ring

lemma heterogeneous_unit_work_tail {ι : Type*} [Fintype ι] {S : ι → Type*}
    [∀ i, MeasurableSpace (S i)] (P : (i : ι) → Measure (S i))
    [∀ i, IsProbabilityMeasure (P i)] (W : (i : ι) → S i → ℝ) (C : ι → ℝ)
    (hW : ∀ i, Measurable (W i)) (hb : ∀ i s, 0 ≤ W i s ∧ W i s ≤ 1)
    (hmean : ∀ i, (∫ s, W i s ∂P i) ≤ C i) (t : ℝ) :
    (Measure.pi P) {samples | 2 * (∑ i, C i) + t < ∑ i, W i (samples i)} ≤
      ENNReal.ofReal (Real.exp (-t)) := by
  exact heterogeneous_exp_sum_tail P W C
    (fun i => OracleTemplate.StochasticQuasar.bounded_work_exp_integrable (hW i) (hb i))
    (fun i => OracleTemplate.StochasticQuasar.bounded_work_exp_moment (hW i) (hb i) (hmean i)) t

lemma heterogeneous_work_tail {ι : Type*} [Fintype ι] {S : ι → Type*}
    [∀ i, MeasurableSpace (S i)] (P : (i : ι) → Measure (S i))
    [∀ i, IsProbabilityMeasure (P i)] (W : (i : ι) → S i → ℝ) (C : ι → ℝ)
    {M : ℝ} (hM : 0 < M) (hW : ∀ i, Measurable (W i))
    (hb : ∀ i s, 0 ≤ W i s ∧ W i s ≤ M)
    (hmean : ∀ i, (∫ s, W i s ∂P i) ≤ C i) (t : ℝ) :
    (Measure.pi P) {samples | 2 * (∑ i, C i) + M * t < ∑ i, W i (samples i)} ≤
      ENNReal.ofReal (Real.exp (-t)) := by
  have hn (i : ι) (s : S i) : 0 ≤ W i s / M ∧ W i s / M ≤ 1 :=
    ⟨div_nonneg (hb i s).1 hM.le, (div_le_one hM).mpr (hb i s).2⟩
  have hm (i : ι) : (∫ s, W i s / M ∂P i) ≤ C i / M := by
    rw [integral_div]
    exact div_le_div_of_nonneg_right (hmean i) hM.le
  have hh := heterogeneous_unit_work_tail P (fun i s => W i s / M) (fun i => C i / M)
    (fun i => (hW i).div_const M) hn hm t
  have he (samples : (i : ι) → S i) :
      2 * (∑ i, C i / M) + t < ∑ i, W i (samples i) / M ↔
      2 * (∑ i, C i) + M * t < ∑ i, W i (samples i) := by
    rw [← Finset.sum_div, ← Finset.sum_div, lt_div_iff₀ hM]
    have ha : (2 * ((∑ i, C i) / M) + t) * M = 2 * (∑ i, C i) + M * t := by field_simp
    rw [ha]
  simpa only [he] using hh

lemma finite_batch_calls (h J n : ℕ) (v : Fin n → Fin (J+1)) :
    (batchCalls h (extendLevels v) n : ℝ) = ∑ i : Fin n, (replyCalls h (v i) : ℝ) := by
  simp only [batchCalls, Nat.cast_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  simp [extendLevels]

lemma batch_work_exp_moment (h J n : ℕ) {M : ℝ} (hM : 0 < M)
    (hmax : (h+1 : ℝ) * (1 + 3 * (2 : ℝ)^J) ≤ M) :
    let Q := Measure.pi fun _ : Fin n => (levelLaw J : Measure (Fin (J+1)))
    let W := fun v : Fin n → Fin (J+1) => (batchCalls h (extendLevels v) n : ℝ) / M
    Integrable (fun v => Real.exp (W v)) Q ∧
    (∫ v, Real.exp (W v) ∂Q) ≤ Real.exp (2 * (n : ℝ) * ((h+1)*(1+3*(J+1))) / M) := by
  intro Q W
  have hb (j : Fin (J+1)) : 0 ≤ (replyCalls h j : ℝ) / M ∧ (replyCalls h j : ℝ) / M ≤ 1 := by
    refine ⟨by positivity, (div_le_one hM).mpr ?_⟩
    have hh : (replyCalls h j : ℝ) ≤ (h+1 : ℝ) * (1+3*(2 : ℝ)^J) := by
      exact_mod_cast reply_calls_max h J j
    exact hh.trans hmax
  have hm : (∫ j, (replyCalls h j : ℝ) / M ∂(levelLaw J : Measure (Fin (J+1)))) ≤
      ((h+1)*(1+3*(J+1)) : ℝ) / M := by
    rw [integral_div]
    exact div_le_div_of_nonneg_right (integral_reply_work h J) hM.le
  have hi := OracleTemplate.StochasticQuasar.bounded_work_exp_integrable
    (μ := (levelLaw J : Measure (Fin (J+1)))) (measurable_of_finite _) hb
  have he := OracleTemplate.StochasticQuasar.bounded_work_exp_moment
    (μ := (levelLaw J : Measure (Fin (J+1)))) (measurable_of_finite _) hb hm
  have hh := heterogeneous_exp_sum_moment (fun _ : Fin n => (levelLaw J : Measure (Fin (J+1))))
    (fun _ j => (replyCalls h j : ℝ) / M)
    (fun _ => ((h+1)*(1+3*(J+1)) : ℝ) / M) (fun _ => hi) (fun _ => he)
  have hw (v : Fin n → Fin (J+1)) : (∑ i : Fin n, (replyCalls h (v i) : ℝ) / M) = W v := by
    rw [← Finset.sum_div, ← finite_batch_calls]
  simpa only [hw, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_div_assoc, mul_assoc] using hh

lemma exponential_work_tail {S : Type*} [MeasurableSpace S]
    (P : Measure S) (W : S → ℝ) {M C : ℝ} (hM : 0 < M)
    (hi : Integrable (fun s => Real.exp (W s / M)) P)
    (hm : (∫ s, Real.exp (W s / M) ∂P) ≤ Real.exp (2 * C / M)) (t : ℝ) :
    P {s | 2 * C + M * t < W s} ≤ ENNReal.ofReal (Real.exp (-t)) := by
  have hp := (hi.const_mul (Real.exp (-(2 * C / M + t)))).measure_le_integral
    (Filter.Eventually.of_forall (fun _ => by positivity))
    (s := {s | 2 * C + M * t < W s}) (by
      intro s hs
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have he : (2 * C / M + t) * M = 2 * C + M * t := by field_simp
      have hh : 2 * C / M + t < W s / M := (lt_div_iff₀ hM).mpr (by rwa [he])
      linarith)
  rw [integral_const_mul] at hp
  refine hp.trans (ENNReal.ofReal_le_ofReal ?_)
  have hh := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-(2 * C / M + t))).le
  convert hh using 1
  rw [← Real.exp_add]
  congr 1
  ring

lemma affine_oracle_statistics {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → E} {a : E} {p V s : ℝ} (hs : |s| = 1) (c : E)
    (hX : Integrable X P) (hm : ∫ ω, X ω ∂P = a)
    (hpi : Integrable (fun ω => ‖X ω-a‖^p) P)
    (hpV : (∫ ω, ‖X ω-a‖^p ∂P) ≤ V) :
    Integrable (fun ω => s • X ω+c) P ∧
    (∫ ω, s • X ω+c ∂P) = s • a+c ∧
    Integrable (fun ω => ‖(s • X ω+c)-(s • a+c)‖^p) P ∧
    (∫ ω, ‖(s • X ω+c)-(s • a+c)‖^p ∂P) ≤ V := by
  have he (ω : Ω) : ‖(s • X ω+c)-(s • a+c)‖^p = ‖X ω-a‖^p := by
    rw [add_sub_add_right_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, hs, one_mul]
  have hsi : Integrable (fun ω => s • X ω) P := hX.smul s
  refine ⟨hsi.add (integrable_const c), ?_, ?_, ?_⟩
  · rw [integral_add hsi (integrable_const c), integral_smul, hm, integral_const]
    simp
  · simpa only [he] using hpi
  · simpa only [he] using hpV

lemma proximal_corrected_oracle {E F Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (gx : E × F → E) (gy : E × F → F) (ox : E × F → Ω → E) (oy : E × F → Ω → F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy))
    (hxi : ∀ z, Integrable (ox z) P) (hyi : ∀ z, Integrable (oy z) P)
    (hxm : ∀ z, ∫ ω, ox z ω ∂P = gx z) (hym : ∀ z, ∫ ω, oy z ω ∂P = gy z)
    {p V : ℝ} (hp : 0 ≤ p)
    (hpi : ∀ z, Integrable (fun ω => (Real.sqrt (‖ox z ω-gx z‖^2+‖oy z ω-gy z‖^2))^p) P)
    (hpV : ∀ z, (∫ ω, (Real.sqrt (‖ox z ω-gx z‖^2+‖oy z ω-gy z‖^2))^p ∂P) ≤ V)
    (L lam : ℝ) (center : E) (shift : F) :
    let a := fun v x ω => ox (x,v) ω+(2*L) • (x-center)
    let b := fun v x ω => -oy (x,v) ω+(lam • v-shift)
    let field := fun v x => gx (x,v)+(2*L) • (x-center)
    let dualField := fun v x => -gy (x,v)+(lam • v-shift)
    (∀ v, Measurable (Function.uncurry (a v))) ∧
    (∀ v, Measurable (Function.uncurry (b v))) ∧
    (∀ v x, Integrable (a v x) P) ∧ (∀ v x, Integrable (b v x) P) ∧
    (∀ v x, ∫ ω, a v x ω ∂P = field v x) ∧
    (∀ v x, ∫ ω, b v x ω ∂P = dualField v x) ∧
    (∀ v x, Integrable (fun ω => ‖a v x ω-field v x‖^p) P) ∧
    (∀ v x, Integrable (fun ω => ‖b v x ω-dualField v x‖^p) P) ∧
    (∀ v x, (∫ ω, ‖a v x ω-field v x‖^p ∂P) ≤ V) ∧
    (∀ v x, (∫ ω, ‖b v x ω-dualField v x‖^p ∂P) ≤ V) := by
  intro a b field dualField
  have hcomp (z : E × F) := joint_component_moments P
    ((hox.comp (measurable_const.prodMk measurable_id)).sub measurable_const)
    ((hoy.comp (measurable_const.prodMk measurable_id)).sub measurable_const) hp (hpi z) (hpV z)
  have hx (v : F) (x : E) : Integrable (a v x) P ∧ (∫ ω, a v x ω ∂P) = field v x ∧
      Integrable (fun ω => ‖a v x ω-field v x‖^p) P ∧
      (∫ ω, ‖a v x ω-field v x‖^p ∂P) ≤ V := by
    simpa only [one_smul] using affine_oracle_statistics P (s := 1) (by norm_num)
      ((2*L) • (x-center)) (hxi (x,v)) (hxm (x,v)) (hcomp (x,v)).1 (hcomp (x,v)).2.1
  have hy (v : F) (x : E) : Integrable (b v x) P ∧ (∫ ω, b v x ω ∂P) = dualField v x ∧
      Integrable (fun ω => ‖b v x ω-dualField v x‖^p) P ∧
      (∫ ω, ‖b v x ω-dualField v x‖^p ∂P) ≤ V := by
    simpa only [neg_one_smul] using affine_oracle_statistics P (s := -1) (by norm_num)
      (lam • v-shift) (hyi (x,v)) (hym (x,v)) (hcomp (x,v)).2.2.1 (hcomp (x,v)).2.2.2
  refine ⟨?_, ?_, fun v x => (hx v x).1, fun v x => (hy v x).1,
    fun v x => (hx v x).2.1, fun v x => (hy v x).2.1,
    fun v x => (hx v x).2.2.1, fun v x => (hy v x).2.2.1,
    fun v x => (hx v x).2.2.2, fun v x => (hy v x).2.2.2⟩
  · intro v
    have hm : Measurable (fun w : E × Ω => ox (w.1,v) w.2) :=
      hox.comp (show Measurable (fun w : E × Ω => ((w.1,v),w.2)) by fun_prop)
    exact hm.add (by fun_prop)
  · intro v
    have hm : Measurable (fun w : E × Ω => oy (w.1,v) w.2) :=
      hoy.comp (show Measurable (fun w : E × Ω => ((w.1,v),w.2)) by fun_prop)
    exact hm.neg.add measurable_const

end LongTails.Proofs.HeavyTailSaddleMultilevel
