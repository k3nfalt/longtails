import LongTails.Proofs.EscapeChainRegularity
import LongTails.Proofs.EscapeChainCoin
import Mathlib.Algebra.Order.Chebyshev

open MeasureTheory

namespace LongTails.Proofs.EscapeChainOracle

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus EscapeChainFunction
open EscapeChainCoordinates EscapeChainCount EscapeChainBounds EscapeChainJets EscapeChainSmooth
open EscapeChainCertificate EscapeChainRegularity EscapeChainCoin ThirdOrderJetDifference
open LongTails.Proofs.AbcHardOracle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

variable {K : ℕ} {u v : ℕ → E}

noncomputable def smask (K : ℕ) (u v : ℕ → E) (l : ℕ) (y : E) : ℝ :=
  RelativeHessianCutoffSpatial.value (radius K) y * saddle u v l y

noncomputable def mvec (K : ℕ) (u v : ℕ → E) (l : ℕ) (y : E) : E := gradient (smask K u v l) y

noncomputable def prob (K : ℕ) (A : ℝ) (u v : ℕ → E) (l : ℕ) (y : E) : ℝ :=
  ‖mvec K u v l y‖ ^ 2 / A

noncomputable def start (K : ℕ) (A : ℝ) (u v : ℕ → E) (l : ℕ) (y : E) : ℝ :=
  ∑ m ∈ Finset.range l, prob K A u v m y

noncomputable def answerN (K : ℕ) (A : ℝ) (u v : ℕ → E) (y : E) (U : ℝ) : E :=
  gradient (objective K (radius K) u v) y +
    ∑ l ∈ Finset.range K, (icoin (start K A u v l y) (prob K A u v l y) U - 1) • mvec K u v l y

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma smask_smooth (K : ℕ) (u v : ℕ → E) (l : ℕ) : ContDiff ℝ 3 (smask K u v l) :=
  (RelativeHessianCutoffSpatial.smooth _).mul (saddle_smooth u v l)

lemma mvec_eq (K : ℕ) (u v : ℕ → E) (l : ℕ) (y : E) :
    mvec K u v l y = RelativeHessianCutoffSpatial.value (radius K) y • gradient (saddle u v l) y +
      saddle u v l y • gradient (RelativeHessianCutoffSpatial.value (radius K)) y :=
  ProductCompositionJets.product_gradient (RelativeHessianCutoffSpatial.smooth _) (saddle_smooth u v l) y

lemma mvec_bound (fr : Frame K u v) {l : ℕ} (hl : l < K) (y : E) :
    ‖mvec K u v l y‖ ≤ 2 * sadConst u v y l := by
  obtain ⟨c0, c1, -, -⟩ := cut_bounds K y
  have hj := saddle_jet fr hl y 0 0
  have hc1 : ‖gradient (RelativeHessianCutoffSpatial.value (radius K)) y‖ ≤ 1 := by
    refine c1.trans ?_
    rw [div_le_one (by have := sqrt_succ_ge K; positivity)]
    have := sqrt_succ_ge K; nlinarith
  rw [mvec_eq]
  calc _ ≤ ‖RelativeHessianCutoffSpatial.value (radius K) y • gradient (saddle u v l) y‖ +
        ‖saddle u v l y • gradient (RelativeHessianCutoffSpatial.value (radius K)) y‖ := norm_add_le _ _
    _ ≤ 1 * sadConst u v y l + sadConst u v y l * 1 :=
        add_le_add (smul_le c0 hj.grad (by norm_num)) (smul_le hj.val hc1 (by
          unfold sadConst; split_ifs <;> norm_num))
    _ = _ := by ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma sadConst_le (u v : ℕ → E) (y : E) (l : ℕ) : sadConst u v y l ≤ 2 ^ 49 := by
  unfold sadConst; split_ifs <;> norm_num

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma sadConst_nonneg (u v : ℕ → E) (y : E) (l : ℕ) : 0 ≤ sadConst u v y l := by
  unfold sadConst; split_ifs <;> norm_num

lemma mvec_zero (fr : Frame K u v) {l : ℕ} (hl : l < K) (y : E) (h : ¬ active u v y l) :
    mvec K u v l y = 0 := by
  classical
  have hb := mvec_bound fr hl y
  rw [show sadConst u v y l = 0 by unfold sadConst; rw [ite_eq_right h], mul_zero] at hb
  exact norm_le_zero_iff.1 hb

omit [FiniteDimensional ℝ E] in
lemma prob_nonneg {A : ℝ} (hA : 0 < A) (l : ℕ) (y : E) : 0 ≤ prob K A u v l y := by
  unfold prob; positivity

omit [FiniteDimensional ℝ E] in
lemma start_nonneg {A : ℝ} (hA : 0 < A) (l : ℕ) (y : E) : 0 ≤ start K A u v l y :=
  Finset.sum_nonneg fun m _ => prob_nonneg hA m y

lemma prob_sum (fr : Frame K u v) {A : ℝ} (hA : 45 * 2 ^ 102 ≤ A) (y : E) :
    ∑ l ∈ Finset.range K, prob K A u v l y ≤ 1 := by
  classical
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hterm : ∀ l ∈ Finset.range K, prob K A u v l y ≤ (if active u v y l then 1 / 45 else 0) := by
    intro l hl
    have hlK := Finset.mem_range.1 hl
    split_ifs with h
    · unfold prob
      rw [div_le_iff₀ hA0]
      have hb : ‖mvec K u v l y‖ ≤ 2 ^ 50 :=
        (mvec_bound fr hlK y).trans (by linarith [sadConst_le u v y l])
      have hb' : ‖mvec K u v l y‖ ^ 2 ≤ (2 ^ 50) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      norm_num at hb'
      linarith
    · unfold prob; simp [mvec_zero fr hlK y h]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have := active_card fr y K le_rfl
  have : (((Finset.range K).filter (active u v y)).card : ℝ) ≤ 45 := by exact_mod_cast this
  nlinarith

lemma interval_fits (fr : Frame K u v) {A : ℝ} (hA : 45 * 2 ^ 102 ≤ A) {l : ℕ} (hl : l < K)
    (y : E) : start K A u v l y + prob K A u v l y ≤ 1 := by
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have h := prob_sum fr hA y
  unfold start
  rw [← Finset.sum_range_succ]
  refine le_trans ?_ h
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    (fun m _ _ => prob_nonneg hA0 m y)

omit [FiniteDimensional ℝ E] in
lemma coef_integrable (K : ℕ) (A : ℝ) (u v : ℕ → E) (l : ℕ) (y : E) :
    Integrable (fun U => icoin (start K A u v l y) (prob K A u v l y) U - 1) unif :=
  (icoin_integrable _ _).sub (integrable_const _)

lemma coef_integral (fr : Frame K u v) {A : ℝ} (hA : 45 * 2 ^ 102 ≤ A) {l : ℕ} (hl : l < K)
    (y : E) :
    (∫ U, (icoin (start K A u v l y) (prob K A u v l y) U - 1) ∂unif) • mvec K u v l y = 0 := by
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  rcases eq_or_lt_of_le (prob_nonneg (K := K) (u := u) (v := v) hA0 l y) with h0 | hpos
  · have : mvec K u v l y = 0 := by
      have h := h0.symm
      unfold prob at h
      rw [div_eq_zero_iff] at h
      rcases h with h | h
      · exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h)
      · linarith
    rw [this, smul_zero]
  · rw [integral_sub (icoin_integrable _ _) (integrable_const _),
      icoin_integral (start_nonneg hA0 l y) hpos (interval_fits fr hA hl y), integral_const,
      probReal_univ, one_smul, sub_self, zero_smul]

omit [FiniteDimensional ℝ E] in
lemma answer_integrable (K : ℕ) (A : ℝ) (u v : ℕ → E) (y : E) :
    Integrable (answerN K A u v y) unif := by
  unfold answerN
  refine (integrable_const _).add ?_
  exact integrable_finsetSum _ fun l _ => (coef_integrable K A u v l y).smul_const _

lemma answer_mean (fr : Frame K u v) {A : ℝ} (hA : 45 * 2 ^ 102 ≤ A) (y : E) :
    ∫ U, answerN K A u v y U ∂unif = gradient (objective K (radius K) u v) y := by
  unfold answerN
  rw [integral_add (integrable_const _)
    (integrable_finsetSum _ fun l _ => (coef_integrable K A u v l y).smul_const _),
    integral_const, probReal_univ, one_smul,
    integral_finsetSum _ fun l _ => (coef_integrable K A u v l y).smul_const _]
  rw [Finset.sum_eq_zero, add_zero]
  intro l hl
  rw [integral_smul_const]
  exact coef_integral fr hA (Finset.mem_range.1 hl) y

omit [FiniteDimensional ℝ E] in
lemma answer_dev (K : ℕ) (A : ℝ) (u v : ℕ → E) (y : E) (U : ℝ) :
    answerN K A u v y U - gradient (objective K (radius K) u v) y =
      ∑ l ∈ Finset.range K, (icoin (start K A u v l y) (prob K A u v l y) U - 1) • mvec K u v l y := by
  unfold answerN; abel

lemma dev_pointwise (fr : Frame K u v) (y : E) (U : ℝ) (A : ℝ) :
    ‖answerN K A u v y U - gradient (objective K (radius K) u v) y‖ ^ 2 ≤
      45 * ∑ l ∈ Finset.range K, (icoin (start K A u v l y) (prob K A u v l y) U - 1) ^ 2 *
        ‖mvec K u v l y‖ ^ 2 := by
  classical
  rw [answer_dev]
  set S := (Finset.range K).filter (active u v y)
  have hsplit : ∑ l ∈ Finset.range K, (icoin (start K A u v l y) (prob K A u v l y) U - 1) •
      mvec K u v l y = ∑ l ∈ S, (icoin (start K A u v l y) (prob K A u v l y) U - 1) • mvec K u v l y := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun l hl => ?_
    split_ifs with h
    · rfl
    · rw [mvec_zero fr (Finset.mem_range.1 hl) y h, smul_zero]
  rw [hsplit]
  have hcard : (S.card : ℝ) ≤ 45 := by exact_mod_cast active_card fr y K le_rfl
  have hcs := sq_sum_le_card_mul_sum_sq (s := S)
    (f := fun l => ‖(icoin (start K A u v l y) (prob K A u v l y) U - 1) • mvec K u v l y‖)
  have hnorm := norm_sum_le S (fun l => (icoin (start K A u v l y) (prob K A u v l y) U - 1) •
    mvec K u v l y)
  have hsq : ‖∑ l ∈ S, (icoin (start K A u v l y) (prob K A u v l y) U - 1) • mvec K u v l y‖ ^ 2 ≤
      (∑ l ∈ S, ‖(icoin (start K A u v l y) (prob K A u v l y) U - 1) • mvec K u v l y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hterm : ∀ l, ‖(icoin (start K A u v l y) (prob K A u v l y) U - 1) • mvec K u v l y‖ ^ 2 =
      (icoin (start K A u v l y) (prob K A u v l y) U - 1) ^ 2 * ‖mvec K u v l y‖ ^ 2 := by
    intro l; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [hterm] at hcs
  have hsub : ∑ l ∈ S, (icoin (start K A u v l y) (prob K A u v l y) U - 1) ^ 2 * ‖mvec K u v l y‖ ^ 2 ≤
      ∑ l ∈ Finset.range K, (icoin (start K A u v l y) (prob K A u v l y) U - 1) ^ 2 *
        ‖mvec K u v l y‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
  have h0 : 0 ≤ ∑ l ∈ S, (icoin (start K A u v l y) (prob K A u v l y) U - 1) ^ 2 * ‖mvec K u v l y‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  nlinarith

lemma dev_integrable [MeasurableSpace E] [BorelSpace E] (K : ℕ) (A : ℝ) (u v : ℕ → E) (y : E) :
    Integrable (fun U => ‖answerN K A u v y U - gradient (objective K (radius K) u v) y‖ ^ 2) unif := by
  have hm : Measurable fun U => answerN K A u v y U - gradient (objective K (radius K) u v) y := by
    unfold answerN
    refine (measurable_const.add ?_).sub measurable_const
    exact Finset.measurable_sum _ fun l _ => ((icoin_measurable _ _).sub measurable_const).smul_const _
  have hbd : ∀ U, ‖answerN K A u v y U - gradient (objective K (radius K) u v) y‖ ≤
      ∑ l ∈ Finset.range K, (|1 / prob K A u v l y| + 1) * ‖mvec K u v l y‖ := by
    intro U
    rw [answer_dev]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine (abs_sub _ _).trans ?_
    rw [abs_one]
    have hc : |icoin (start K A u v l y) (prob K A u v l y) U| ≤ |1 / prob K A u v l y| := by
      unfold icoin; split_ifs <;> simp
    linarith
  refine Integrable.of_bound (C := (∑ l ∈ Finset.range K, (|1 / prob K A u v l y| + 1) *
    ‖mvec K u v l y‖) ^ 2) (hm.norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards with U
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbd U) 2

lemma answer_variance [MeasurableSpace E] [BorelSpace E] (fr : Frame K u v) {A : ℝ} (hA : 45 * 2 ^ 102 ≤ A) (y : E) :
    ∫ U, ‖answerN K A u v y U - gradient (objective K (radius K) u v) y‖ ^ 2 ∂unif ≤ 45 ^ 2 * A := by
  classical
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hint : Integrable (fun U => 45 * ∑ l ∈ Finset.range K,
      (icoin (start K A u v l y) (prob K A u v l y) U - 1) ^ 2 * ‖mvec K u v l y‖ ^ 2) unif :=
    (integrable_finsetSum _ fun l _ => (icoin_sq_integrable _ _).mul_const _).const_mul _
  refine (integral_mono (dev_integrable K A u v y) hint fun U => dev_pointwise fr y U A).trans ?_
  rw [integral_const_mul, integral_finsetSum _ fun l _ => (icoin_sq_integrable _ _).mul_const _]
  have hterm : ∀ l ∈ Finset.range K, ∫ U, (icoin (start K A u v l y) (prob K A u v l y) U - 1) ^ 2 *
      ‖mvec K u v l y‖ ^ 2 ∂unif ≤ if active u v y l then A else 0 := by
    intro l hl
    have hlK := Finset.mem_range.1 hl
    rw [integral_mul_const]
    by_cases hact : active u v y l
    · rw [ite_eq_left hact]
      rcases eq_or_lt_of_le (prob_nonneg (K := K) (u := u) (v := v) hA0 l y) with h0 | hpos
      · have hm : ‖mvec K u v l y‖ ^ 2 = 0 := by
          have h := h0.symm; unfold prob at h; rw [div_eq_zero_iff] at h
          rcases h with h | h
          · exact h
          · linarith
        rw [hm, mul_zero]; exact hA0.le
      · rw [icoin_sq_integral (start_nonneg hA0 l y) hpos (interval_fits fr hA hlK y)]
        have hp : prob K A u v l y = ‖mvec K u v l y‖ ^ 2 / A := rfl
        have hm0 : 0 < ‖mvec K u v l y‖ ^ 2 := by
          rw [hp] at hpos; exact (div_pos_iff_of_pos_right hA0).1 hpos
        rw [hp, one_div_div, sub_mul, div_mul_cancel₀ _ hm0.ne']
        linarith
    · rw [ite_eq_right hact, mvec_zero fr hlK y hact]; simp
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by norm_num)).trans ?_
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : (((Finset.range K).filter (active u v y)).card : ℝ) ≤ 45 := by
    exact_mod_cast active_card fr y K le_rfl
  nlinarith

end LongTails.Proofs.EscapeChainOracle
