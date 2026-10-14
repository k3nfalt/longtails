import LongTails.Proofs.AdaptiveEntropicInnovation
import LongTails.Proofs.AdaptiveEntropicDynamics
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def pairScore {S Ω : Type*} (X : S → Ω → Ω → ℝ)
    (n : ℕ) (s : S) (b : Fin n → Ω) : ℝ :=
  if h : n = 2 then X s (b (Fin.cast h.symm 0)) (b (Fin.cast h.symm 1)) else 0

lemma measurable_pairScore {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {X : S → Ω → Ω → ℝ} (hX : Measurable (fun w : S × (Ω × Ω) => X w.1 w.2.1 w.2.2))
    (n : ℕ) : Measurable (Function.uncurry (pairScore X n)) := by
  by_cases hn : n = 2
  · subst n
    have hm : Measurable (fun w : S × (Fin 2 → Ω) => (w.1, (w.2 0, w.2 1))) := by fun_prop
    change Measurable (fun w : S × (Fin 2 → Ω) => X w.1 (w.2 0) (w.2 1))
    exact hX.comp hm
  · change Measurable (fun w : S × (Fin n → Ω) =>
      if h : n = 2 then X w.1 (w.2 (Fin.cast h.symm 0)) (w.2 (Fin.cast h.symm 1)) else 0)
    simp only [dite_eq_right hn]
    exact measurable_const

lemma pairScore_unit {S Ω : Type*} {X : S → Ω → Ω → ℝ}
    (hb : ∀ s a b, 0 ≤ X s a b ∧ X s a b ≤ 1) (n : ℕ) (s : S) (b : Fin n → Ω) :
    0 ≤ pairScore X n s b ∧ pairScore X n s b ≤ 1 := by
  unfold pairScore
  split_ifs
  · exact hb _ _ _
  · norm_num

lemma integral_pairScore {S Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : S → Ω → Ω → ℝ) (s : S) :
    (∫ b, pairScore X 2 s b ∂Measure.pi (fun _ : Fin 2 => P)) =
      ∫ w : Ω × Ω, X s w.1 w.2 ∂P.prod P := by
  change (∫ b : Fin 2 → Ω, X s (b 0) (b 1) ∂Measure.pi (fun _ => P)) = _
  exact (measurePreserving_finTwoArrow P).integral_comp' (fun w : Ω × Ω => X s w.1 w.2)

lemma bounded_centered_second_le_pair {E Ω : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → E} (hZ : Measurable Z)
    {U : ℝ} (hb : ∀ ω, ‖Z ω‖ ≤ U) :
    (∫ ω, ‖Z ω - ∫ z, Z z ∂P‖ ^ 2 ∂P) ≤
      ∫ b : Fin 2 → Ω, ‖Z (b 0) - Z (b 1)‖ ^ 2 ∂Measure.pi (fun _ => P) := by
  have hi : Integrable Z P := Integrable.of_bound hZ.aestronglyMeasurable U
    (Filter.Eventually.of_forall hb)
  have hm : ‖∫ z, Z z ∂P‖ ≤ U := by
    have h := norm_integral_le_integral_norm (μ := P) Z
    have hle := integral_mono hi.norm (integrable_const U) hb
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using h.trans hle
  have hdiff (a b : Ω) : ‖Z a - Z b‖ ≤ 2 * U :=
    (norm_sub_le _ _).trans (by linarith [hb a, hb b])
  have hcent (ω : Ω) : ‖Z ω - ∫ z, Z z ∂P‖ ≤ 2 * U :=
    (norm_sub_le _ _).trans (by linarith [hb ω])
  have hpair : Integrable (fun w : Ω × Ω => ‖Z w.1 - Z w.2‖ ^ 2) (P.prod P) := by
    apply Integrable.of_bound (((hZ.comp measurable_fst).sub
      (hZ.comp measurable_snd)).norm.pow_const 2).aestronglyMeasurable (4 * U ^ 2)
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖Z w.1 - Z w.2‖ ^ 2 ≤ 4 * U ^ 2
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) (hdiff w.1 w.2) 2]
  have hci : Integrable (fun ω => ‖Z ω - ∫ z, Z z ∂P‖ ^ 2) P := by
    apply Integrable.of_bound ((hZ.sub_const _).norm.pow_const 2).aestronglyMeasurable (4 * U ^ 2)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) (hcent ω) 2]
  have hj (ω : Ω) : ‖Z ω - ∫ z, Z z ∂P‖ ^ 2 ≤ ∫ z, ‖Z ω - Z z‖ ^ 2 ∂P := by
    have hdi : Integrable (fun z => Z ω - Z z) P := (integrable_const _).sub hi
    have hdi2 : Integrable (fun z => ‖Z ω - Z z‖ ^ 2) P := by
      apply Integrable.of_bound ((measurable_const.sub hZ).norm.pow_const 2).aestronglyMeasurable (4 * U ^ 2)
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      change ‖Z ω - Z z‖ ^ 2 ≤ 4 * U ^ 2
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) (hdiff ω z) 2]
    have h := GeneralNormClipping.norm_integral_sq_le hdi hdi2
    simpa only [integral_sub (integrable_const _) hi, integral_const,
      probReal_univ, one_smul] using h
  have h := integral_mono hci hpair.integral_prod_left hj
  rw [← integral_prod _ hpair] at h
  have he := (measurePreserving_finTwoArrow P).integral_comp'
    (fun w : Ω × Ω => ‖Z w.1 - Z w.2‖ ^ 2)
  exact he.symm ▸ h

def boundedActive (q : Public) (μ : simplex q.d → Vector q.d) (σ A : ℝ)
    (T : ℕ) (s : State q) : Prop := cappedActive q μ σ A s ∧ s.completed < T

noncomputable def weightedResidual (q : Public) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (s : State q) (g : Vector q.d) : Fin q.d → ℝ := by
  classical
  exact if boundedActive q μ σ A T s then
    ((s.completed + 1 : ℕ) : ℝ) • (fun i => (clippedReply (clippingThreshold q s)
      (historyCenter q s) g - historyCenter q s) i) else 0

lemma measurableSet_boundedActive (q : Public) {μ : simplex q.d → Vector q.d}
    (hμ : Measurable μ) (σ A : ℝ) (T : ℕ) :
    MeasurableSet {s | boundedActive q μ σ A T s} :=
  (measurableSet_cappedActive q hμ σ A).inter
    (measurableSet_lt (measurable_completed q) measurable_const)

lemma measurable_weightedResidual (q : Public) {μ : simplex q.d → Vector q.d}
    (hμ : Measurable μ) (σ A : ℝ) (T : ℕ) :
    Measurable (Function.uncurry (weightedResidual q μ σ A T)) := by
  apply Measurable.ite ((measurableSet_boundedActive q hμ σ A T).preimage measurable_fst)
  · have hc := (measurable_historyCenter q).comp
      (measurable_fst : Measurable (fun w : State q × Vector q.d => w.1))
    have hz := (measurable_clippedReply ((measurable_clippingThreshold q).comp measurable_fst)
      hc measurable_snd).sub hc
    have hp : Measurable (fun w : State q × Vector q.d => fun i =>
        (clippedReply (clippingThreshold q w.1) (historyCenter q w.1) w.2 - historyCenter q w.1) i) := by
      apply measurable_pi_iff.mpr
      intro i
      exact (PiLp.continuous_apply 2 (fun _ : Fin q.d => ℝ) i).measurable.comp hz
    have ht : Measurable (fun w : State q × Vector q.d => ((w.1.completed + 1 : ℕ) : ℝ)) := by fun_prop
    exact ht.smul hp
  · exact measurable_const

lemma weightedResidual_range (q : Public) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T : ℕ) (s : State q) (g : Vector q.d) :
    ‖weightedResidual q μ σ A T s g‖ ≤ 24 * q.L * window q (T + 1) + A := by
  classical
  by_cases hs : boundedActive q μ σ A T s
  · have hlambda := clippingThreshold_nonneg q hL s hs.1.2.1
    have ht : (0 : ℝ) < ((s.completed + 1 : ℕ) : ℝ) := by positivity
    have hn := GeneralNormClipping.norm_le hlambda (fun i => (g - historyCenter q s) i)
    have he : ((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s =
        24 * q.L * window q (s.completed + 1) + empiricalQuantile q s := by
      unfold clippingThreshold driftRadius
      push_cast
      have ht0 : (s.completed : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    have hk : (window q (s.completed + 1) : ℝ) ≤ window q (T + 1) := by
      exact_mod_cast window_mono q (show s.completed + 1 ≤ T + 1 by have := hs.2; omega)
    calc
      _ = ((s.completed + 1 : ℕ) : ℝ) * ‖clip (clippingThreshold q s)
          (fun i => (g - historyCenter q s) i)‖ := by
        rw [weightedResidual, ite_eq_left hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.le,
          clippedReply_coordinates]
      _ ≤ ((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s :=
        mul_le_mul_of_nonneg_left hn ht.le
      _ = _ := he
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ 24 * q.L by positivity)
        linarith [hs.1.2.2]
  · simp only [weightedResidual, ite_eq_right hs, norm_zero]
    positivity

lemma weightedResidual_difference (q : Public) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (s : State q) (g h : Vector q.d)
    (hs : boundedActive q μ σ A T s) :
    ‖weightedResidual q μ σ A T s g - weightedResidual q μ σ A T s h‖ ^ 2 =
      ((s.completed + 1 : ℕ) : ℝ) ^ 2 *
        dualNorm (clippedReply (clippingThreshold q s) (historyCenter q s) g -
          clippedReply (clippingThreshold q s) (historyCenter q s) h) ^ 2 := by
  classical
  have he : weightedResidual q μ σ A T s g - weightedResidual q μ σ A T s h =
      ((s.completed + 1 : ℕ) : ℝ) • (fun i =>
        (clippedReply (clippingThreshold q s) (historyCenter q s) g -
          clippedReply (clippingThreshold q s) (historyCenter q s) h) i) := by
    simp only [weightedResidual, ite_eq_left hs]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, PiLp.sub_apply]
    ring
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), mul_pow]
  rfl

lemma weightedResidual_pair_range (q : Public) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T : ℕ)
    (s : State q) (g h : Vector q.d) :
    ‖weightedResidual q μ σ A T s g - weightedResidual q μ σ A T s h‖ ^ 2 ≤
      4 * (24 * q.L * window q (T + 1) + A) ^ 2 := by
  have hU : 0 ≤ 24 * q.L * window q (T + 1) + A := by positivity
  have hd := (norm_sub_le (weightedResidual q μ σ A T s g)
    (weightedResidual q μ σ A T s h)).trans (add_le_add
      (weightedResidual_range q μ σ hA hL T s g)
      (weightedResidual_range q μ σ hA hL T s h))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
  nlinarith [hs]

lemma weightedResidual_centered_second_le_pair (q : Public) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T : ℕ) (s : State q) :
    (∫ ω, ‖weightedResidual q μ σ A T s (g (queryPoint q s) ω) -
      ∫ z, weightedResidual q μ σ A T s (g (queryPoint q s) z) ∂P‖ ^ 2 ∂P) ≤
      ∫ b : Fin 2 → Ω,
        ‖weightedResidual q μ σ A T s (g (queryPoint q s) (b 0)) -
          weightedResidual q μ σ A T s (g (queryPoint q s) (b 1))‖ ^ 2
        ∂Measure.pi (fun _ => P) := by
  have hgs : Measurable (g (queryPoint q s)) :=
    hg.comp (measurable_const.prodMk measurable_id)
  have hZ : Measurable (fun ω => weightedResidual q μ σ A T s (g (queryPoint q s) ω)) :=
    (measurable_weightedResidual q hμ σ A T).comp (measurable_const.prodMk hgs)
  exact bounded_centered_second_le_pair hZ
    (fun ω => weightedResidual_range q μ σ hA hL T s _)

lemma bounded_square_moment {v a U p : ℝ} (hv : 0 ≤ v)
    (hU : 0 < U) (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (hb : v ≤ 2 * U) (hd : v ≤ 2 * a) :
    v ^ 2 ≤ 4 * U ^ (2 - p) * a ^ p := by
  have hc := GeneralNormClipping.capped_square_le_rpow
    (show 0 ≤ v / 2 by positivity) hU hp hp2
  have hratio : (v / 2) ^ 2 / U ^ 2 ≤ 1 := by
    apply (div_le_one₀ (sq_pos_of_pos hU)).mpr
    exact pow_le_pow_left₀ (by positivity) (by linarith : v / 2 ≤ U) 2
  have he : U ^ 2 * min 1 ((v / 2) ^ 2 / U ^ 2) = (v / 2) ^ 2 := by
    rw [min_eq_right hratio]
    field_simp
  rw [he] at hc
  have hm := Real.rpow_le_rpow (show 0 ≤ v / 2 by positivity)
    (show v / 2 ≤ a by linarith) hp
  have hm' := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hU.le (2 - p))
  nlinarith

lemma weightedResidual_pair_moment (q : Public) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) {A p : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (T : ℕ)
    (hU : 0 < 24 * q.L * window q (T + 1) + A)
    (s : State q) (g h : Vector q.d) :
    ‖weightedResidual q μ σ A T s g - weightedResidual q μ σ A T s h‖ ^ 2 ≤
      8 * (24 * q.L * window q (T + 1) + A) ^ (2 - p) *
        ((s.completed + 1 : ℕ) : ℝ) ^ p *
          (dualNorm (g - μ (queryPoint q s)) ^ p +
            dualNorm (h - μ (queryPoint q s)) ^ p) := by
  classical
  by_cases hs : boundedActive q μ σ A T s
  · have ht : 0 ≤ ((s.completed + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have he : ‖weightedResidual q μ σ A T s g - weightedResidual q μ σ A T s h‖ =
        ((s.completed + 1 : ℕ) : ℝ) *
          dualNorm (clippedReply (clippingThreshold q s) (historyCenter q s) g -
            clippedReply (clippingThreshold q s) (historyCenter q s) h) := by
      have he : weightedResidual q μ σ A T s g - weightedResidual q μ σ A T s h =
          ((s.completed + 1 : ℕ) : ℝ) • (fun i =>
            (clippedReply (clippingThreshold q s) (historyCenter q s) g -
              clippedReply (clippingThreshold q s) (historyCenter q s) h) i) := by
        simp only [weightedResidual, ite_eq_left hs]
        funext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, PiLp.sub_apply]
        ring
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
      rfl
    have hd : ‖weightedResidual q μ σ A T s g - weightedResidual q μ σ A T s h‖ ≤
        2 * (((s.completed + 1 : ℕ) : ℝ) * dualNorm (g - h)) := by
      rw [he]
      have hh := mul_le_mul_of_nonneg_left
        (clippedReply_difference (clippingThreshold_nonneg q hL s hs.1.2.1)
          (historyCenter q s) g h) ht
      nlinarith
    have hb : ‖weightedResidual q μ σ A T s g - weightedResidual q μ σ A T s h‖ ≤
        2 * (24 * q.L * window q (T + 1) + A) := by
      have hg := weightedResidual_range q μ σ hA hL T s g
      have hh := weightedResidual_range q μ σ hA hL T s h
      exact (norm_sub_le _ _).trans (by linarith)
    have hdual : 0 ≤ dualNorm (g - h) := norm_nonneg _
    have hh := bounded_square_moment (norm_nonneg _)
      hU (show 0 ≤ p by linarith) hp2 hb hd
    rw [Real.mul_rpow ht hdual] at hh
    have hm := mul_le_mul_of_nonneg_left
      (dualNorm_difference_moment hp hp2 g h (μ (queryPoint q s)))
      (show 0 ≤ 4 * (24 * q.L * window q (T + 1) + A) ^ (2 - p) *
        ((s.completed + 1 : ℕ) : ℝ) ^ p by positivity)
    nlinarith
  · simp only [weightedResidual, ite_eq_right hs, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    unfold dualNorm
    positivity

lemma weightedResidual_pair_mean (q : Public) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {σ A p : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (T : ℕ) (hU : 0 < 24 * q.L * window q (T + 1) + A) (s : State q) :
    (∫ b : Fin 2 → Ω,
      ‖weightedResidual q μ σ A T s (g (queryPoint q s) (b 0)) -
        weightedResidual q μ σ A T s (g (queryPoint q s) (b 1))‖ ^ 2
      ∂Measure.pi (fun _ => P)) ≤
        16 * (24 * q.L * window q (T + 1) + A) ^ (2 - p) *
          ((s.completed + 1 : ℕ) : ℝ) ^ p * σ ^ p := by
  let Z := fun ω => weightedResidual q μ σ A T s (g (queryPoint q s) ω)
  let F := fun ω => dualNorm (g (queryPoint q s) ω - μ (queryPoint q s)) ^ p
  let C := 8 * (24 * q.L * window q (T + 1) + A) ^ (2 - p) *
    ((s.completed + 1 : ℕ) : ℝ) ^ p
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hF : Integrable F P := hi _
  have hZ : Measurable Z := (measurable_weightedResidual q hμ σ A T).comp
    (measurable_const.prodMk (hg.comp measurable_prodMk_left))
  have hpair : Integrable (fun w : Ω × Ω => ‖Z w.1 - Z w.2‖ ^ 2) (P.prod P) := by
    apply Integrable.of_bound (((hZ.comp measurable_fst).sub
      (hZ.comp measurable_snd)).norm.pow_const 2).aestronglyMeasurable
      (4 * (24 * q.L * window q (T + 1) + A) ^ 2)
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact weightedResidual_pair_range q μ σ hA hL T s _ _
  have hdom : Integrable (fun w : Ω × Ω => C * (F w.1 + F w.2)) (P.prod P) :=
    ((hF.comp_fst P).add (hF.comp_snd P)).const_mul C
  have hb : ∀ w : Ω × Ω, ‖Z w.1 - Z w.2‖ ^ 2 ≤ C * (F w.1 + F w.2) := by
    intro w
    exact weightedResidual_pair_moment q μ σ hA hL hp hp2 T hU s _ _
  have hbound := integral_mono hpair hdom hb
  rw [integral_const_mul, integral_add (hF.comp_fst P) (hF.comp_snd P),
    integral_fun_fst, integral_fun_snd] at hbound
  simp only [probReal_univ, one_smul] at hbound
  have hh := mul_le_mul_of_nonneg_left (hm (queryPoint q s)) hC
  calc
    _ = ∫ w : Ω × Ω, ‖Z w.1 - Z w.2‖ ^ 2 ∂P.prod P :=
      (measurePreserving_finTwoArrow P).integral_comp' (fun w : Ω × Ω => ‖Z w.1 - Z w.2‖ ^ 2)
    _ ≤ C * ((∫ ω, F ω ∂P) + ∫ ω, F ω ∂P) := hbound
    _ ≤ 16 * (24 * q.L * window q (T + 1) + A) ^ (2 - p) *
        ((s.completed + 1 : ℕ) : ℝ) ^ p * σ ^ p := by
      dsimp [C, F] at *
      nlinarith

noncomputable def weightedNoise (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (P : Measure Ω) (s : State q) (ω : Ω) : Fin q.d → ℝ :=
  weightedResidual q μ σ A T s (g (queryPoint q s) ω) -
    ∫ z, weightedResidual q μ σ A T s (g (queryPoint q s) z) ∂P

lemma measurable_weightedNoise (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ A : ℝ) (T : ℕ) (P : Measure Ω) [SFinite P] :
    Measurable (Function.uncurry (weightedNoise q g μ σ A T P)) := by
  have hZ : Measurable (fun w : State q × Ω =>
      weightedResidual q μ σ A T w.1 (g (queryPoint q w.1) w.2)) :=
    (measurable_weightedResidual q hμ σ A T).comp
      (measurable_fst.prodMk (hg.comp (((measurable_queryPoint q).comp measurable_fst).prodMk
        measurable_snd)))
  have hm : Measurable (fun s : State q =>
      ∫ z, weightedResidual q μ σ A T s (g (queryPoint q s) z) ∂P) :=
    hZ.stronglyMeasurable.integral_prod_right.measurable
  exact hZ.sub (hm.comp measurable_fst)

lemma weightedNoise_range (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T : ℕ) (s : State q) (ω : Ω) :
    ‖weightedNoise q g μ σ A T P s ω‖ ≤ 2 * (24 * q.L * window q (T + 1) + A) := by
  let Z := fun ω => weightedResidual q μ σ A T s (g (queryPoint q s) ω)
  let U := 24 * q.L * window q (T + 1) + A
  have hZ : Measurable Z := (measurable_weightedResidual q hμ σ A T).comp
    (measurable_const.prodMk (hg.comp measurable_prodMk_left))
  have hb : ∀ ω, ‖Z ω‖ ≤ U := fun ω => weightedResidual_range q μ σ hA hL T s _
  have hi : Integrable Z P := Integrable.of_bound hZ.aestronglyMeasurable U
    (Filter.Eventually.of_forall hb)
  have hm : ‖∫ z, Z z ∂P‖ ≤ U := by
    have hh := integral_mono hi.norm (integrable_const U) hb
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    exact (norm_integral_le_integral_norm Z).trans hh
  exact (norm_sub_le (Z ω) (∫ z, Z z ∂P)).trans (by linarith [hb ω])

lemma integral_weightedNoise_eq_zero (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T : ℕ) (s : State q) :
    (∫ ω, weightedNoise q g μ σ A T P s ω ∂P) = 0 := by
  have hZ : Measurable (fun ω => weightedResidual q μ σ A T s (g (queryPoint q s) ω)) :=
    (measurable_weightedResidual q hμ σ A T).comp
      (measurable_const.prodMk (hg.comp measurable_prodMk_left))
  have hi : Integrable (fun ω => weightedResidual q μ σ A T s (g (queryPoint q s) ω)) P :=
    Integrable.of_bound hZ.aestronglyMeasurable (24 * q.L * window q (T + 1) + A)
      (Filter.Eventually.of_forall (fun ω => weightedResidual_range q μ σ hA hL T s _))
  simp only [weightedNoise, integral_sub hi (integrable_const _), integral_const,
    probReal_univ, one_smul, sub_self]

lemma weightedResidual_local_range (q : Public) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (s : State q) (g : Vector q.d) (hL : 0 ≤ q.L)
    (hs : boundedActive q μ σ A T s) :
    ‖weightedResidual q μ σ A T s g‖ ≤
      ((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s := by
  classical
  have ht : 0 ≤ ((s.completed + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlambda := clippingThreshold_nonneg q hL s hs.1.2.1
  rw [weightedResidual, ite_eq_left hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
    clippedReply_coordinates]
  exact mul_le_mul_of_nonneg_left (GeneralNormClipping.norm_le hlambda _) ht

lemma weightedNoise_inactive (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (P : Measure Ω) (s : State q) (ω : Ω)
    (hs : ¬ boundedActive q μ σ A T s) : weightedNoise q g μ σ A T P s ω = 0 := by
  classical
  simp [weightedNoise, weightedResidual, hs]

lemma weightedNoise_local_range (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ A : ℝ) (T : ℕ) (s : State q) (ω : Ω) (hL : 0 ≤ q.L)
    (hs : boundedActive q μ σ A T s) :
    ‖weightedNoise q g μ σ A T P s ω‖ ≤
      2 * (((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s) := by
  let Z := fun ω => weightedResidual q μ σ A T s (g (queryPoint q s) ω)
  let C := ((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s
  have hZ : Measurable Z := (measurable_weightedResidual q hμ σ A T).comp
    (measurable_const.prodMk (hg.comp measurable_prodMk_left))
  have hb : ∀ ω, ‖Z ω‖ ≤ C := fun ω => weightedResidual_local_range q μ σ A T s _ hL hs
  have hi : Integrable Z P := Integrable.of_bound hZ.aestronglyMeasurable C
    (Filter.Eventually.of_forall hb)
  have hm : ‖∫ z, Z z ∂P‖ ≤ C := by
    have hh := integral_mono hi.norm (integrable_const C) hb
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    exact (norm_integral_le_integral_norm Z).trans hh
  exact (norm_sub_le (Z ω) (∫ z, Z z ∂P)).trans (by linarith [hb ω])

lemma weighted_clippingThreshold_le_cap (q : Public) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (s : State q) (hL : 0 ≤ q.L)
    (hs : boundedActive q μ σ A T s) :
    ((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s ≤
      24 * q.L * window q (T + 1) + A := by
  rw [weighted_clippingThreshold]
  have hk : (window q (s.completed + 1) : ℝ) ≤ window q (T + 1) := by
    exact_mod_cast window_mono q (show s.completed + 1 ≤ T + 1 by have := hs.2; omega)
  have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ 24 * q.L by positivity)
  linarith [hs.1.2.2]

lemma weightedNoise_quadratic_range (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (T : ℕ) (s : State q) (ω : Ω) (hL : 0 < q.L)
    (hH : 2 ≤ confidence q) :
    ‖weightedNoise q g μ σ A T P s ω‖ ^ 2 / regularization q s ≤
      (24 * q.L * window q (T + 1) + A) * geometry q / trimCount q := by
  classical
  have hB := regularization_pos q hL hH s
  have hD := geometry_pos q
  have hKn : 0 < trimCount q := by unfold trimCount; omega
  have hK : 0 < (trimCount q : ℝ) := by exact_mod_cast hKn
  by_cases hs : boundedActive q μ σ A T s
  · have hc : 0 ≤ ((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s :=
      mul_nonneg (Nat.cast_nonneg _) (clippingThreshold_nonneg q hL.le s hs.1.2.1)
    have hu := weighted_clippingThreshold_le_cap q μ σ A T s hL.le hs
    have hn := pow_le_pow_left₀ (norm_nonneg _)
      (weightedNoise_local_range (P := P) q hg hμ σ A T s ω hL.le hs) 2
    have hw : ‖weightedNoise q g μ σ A T P s ω‖ ^ 2 ≤
        4 * (((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s) ^ 2 := by nlinarith
    exact normalized_quadratic_range hc hu hB hD.le hK hw
      (weighted_clippingThreshold_le_regularization q hL.le s)
  · rw [weightedNoise_inactive q g μ σ A T P s ω hs, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_div]
    exact div_nonneg (mul_nonneg (by positivity) hD.le) hK.le

lemma weightedResidual_pair_local_range (q : Public) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (s : State q) (g h : Vector q.d) (hL : 0 ≤ q.L)
    (hs : boundedActive q μ σ A T s) :
    ‖weightedResidual q μ σ A T s g - weightedResidual q μ σ A T s h‖ ^ 2 ≤
      4 * (((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s) ^ 2 := by
  have h1 := weightedResidual_local_range q μ σ A T s g hL hs
  have h2 := weightedResidual_local_range q μ σ A T s h hL hs
  have hd : ‖weightedResidual q μ σ A T s g - weightedResidual q μ σ A T s h‖ ≤
      2 * (((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s) :=
    (norm_sub_le _ _).trans (by linarith)
  have hp := pow_le_pow_left₀ (norm_nonneg _) hd 2
  nlinarith

end OracleTemplate.AdaptiveHeavyTailSimplex
