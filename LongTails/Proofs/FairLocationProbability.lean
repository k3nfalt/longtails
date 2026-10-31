import LongTails.Proofs.FairLocationExistence
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.Pi

namespace OracleTemplate.RadialFairLocation

open MeasureTheory ProbabilityTheory Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def centralIndices {n : ℕ} (r : ℝ) (a : Fin n → E) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => ‖a i‖ ≤ r)

def goodBlock {n : ℕ} (r : ℝ) (a : Fin n → E) : Prop :=
  3 * n ≤ 4 * (centralIndices r a).card

noncomputable def idealNoise {n : ℕ} (r : ℝ) (a : Fin n → E) : E := by
  classical
  exact if goodBlock r a then location r a else 0

omit [InnerProductSpace ℝ E] in
lemma goodBlock_neg {n : ℕ} (r : ℝ) (a : Fin n → E) :
    goodBlock r (fun i => -a i) ↔ goodBlock r a := by
  simp only [goodBlock, centralIndices, norm_neg]

lemma idealNoise_norm [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (a : Fin n → E) : ‖idealNoise r a‖ ≤ 3 * r := by
  classical
  unfold idealNoise
  split_ifs with h
  · exact central_cluster_bound hn hr a (location r a) (centralIndices r a) h
      (fun i hi => (Finset.mem_filter.mp hi).2) (location_equation hn hr a)
  · simp only [norm_zero]
    positivity

lemma idealNoise_neg [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (a : Fin n → E) :
    idealNoise r (fun i => -a i) = -idealNoise r a := by
  classical
  by_cases h : goodBlock r a
  · simp only [idealNoise, (goodBlock_neg r a).mpr h, h, ite_eq_left, location_neg hn hr a]
  · have hn' : ¬ goodBlock r (fun i => -a i) := mt (goodBlock_neg r a).mp h
    simp [idealNoise, hn', h]

lemma idealNoise_good_difference [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (a b : Fin n → E)
    (ha : goodBlock r a) (hb : goodBlock r b) :
    (n : ℝ) * ‖idealNoise r a - idealNoise r b‖ ≤
      2048 * r * ∑ i, ‖a i - b i‖ / (r + ‖a i‖ + ‖b i‖) := by
  have hna := idealNoise_norm hn hr a
  have hnb := idealNoise_norm hn hr b
  simp only [idealNoise, ha, hb, ite_true] at hna hnb ⊢
  exact relative_cluster_root_stability hr a b _ _ (centralIndices r a) ha
    (fun i hi => (Finset.mem_filter.mp hi).2) hna hnb
    (location_equation hn hr a) (location_equation hn hr b)

lemma idealNoise_good_difference_sq [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (a b : Fin n → E)
    (ha : goodBlock r a) (hb : goodBlock r b) :
    ‖idealNoise r a - idealNoise r b‖ ^ 2 ≤
      (2048 * r) ^ 2 / n * ∑ i, (‖a i - b i‖ / (r + ‖a i‖ + ‖b i‖)) ^ 2 := by
  have h := idealNoise_good_difference hn hr a b ha hb
  have hsum : 0 ≤ ∑ i, ‖a i - b i‖ / (r + ‖a i‖ + ‖b i‖) := by
    exact Finset.sum_nonneg (fun i _ => by positivity)
  have hs := (sq_le_sq₀ (by positivity) (by positivity)).mpr h
  have hc := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun i : Fin n => ‖a i - b i‖ / (r + ‖a i‖ + ‖b i‖))
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  have hm := mul_le_mul_of_nonneg_left hc (sq_nonneg (2048 * r))
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [div_mul_eq_mul_div, le_div_iff₀ hn']
  nlinarith [mul_pow (n : ℝ) ‖idealNoise r a - idealNoise r b‖ 2,
    mul_pow (2048 * r) (∑ i, ‖a i - b i‖ / (r + ‖a i‖ + ‖b i‖)) 2]

lemma idealNoise_difference_sq [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (a b : Fin n → E) :
    ‖idealNoise r a - idealNoise r b‖ ^ 2 ≤
      (2048 * r) ^ 2 / n * ∑ i, (‖a i - b i‖ / (r + ‖a i‖ + ‖b i‖)) ^ 2 +
        if goodBlock r a ∧ goodBlock r b then 0 else 36 * r ^ 2 := by
  by_cases h : goodBlock r a ∧ goodBlock r b
  · simpa [h] using
      idealNoise_good_difference_sq hn hr a b h.1 h.2
  · rw [ite_eq_right h]
    have hnrm : ‖idealNoise r a - idealNoise r b‖ ≤ 6 * r :=
      (norm_sub_le _ _).trans (by linarith [idealNoise_norm hn hr a, idealNoise_norm hn hr b])
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnrm
    have ht : 0 ≤ (2048 * r) ^ 2 / (n : ℝ) *
        ∑ i, (‖a i - b i‖ / (r + ‖a i‖ + ‖b i‖)) ^ 2 := by positivity
    nlinarith

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma measurable_centralCount {n : ℕ} (r : ℝ) :
    Measurable (fun a : Fin n → E => (centralIndices r a).card) := by
  classical
  simp only [centralIndices, Finset.card_filter]
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_le (measurable_pi_apply i).norm measurable_const)
    measurable_const measurable_const

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma measurableSet_goodBlock {n : ℕ} (r : ℝ) :
    MeasurableSet {a : Fin n → E | goodBlock r a} :=
  measurableSet_le measurable_const ((measurable_centralCount r).const_mul 4)

lemma measurable_idealNoise [CompleteSpace E] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) : Measurable (idealNoise (E := E) (n := n) r) := by
  classical
  exact Measurable.ite (measurableSet_goodBlock r) (continuous_location hn hr).measurable
    measurable_const

lemma quarter_failure_probability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {A : Set Ω} (hA : MeasurableSet A)
    (hp : P.real A ≤ 1 / 64) (k : ℕ) :
    (Measure.pi fun _ : Fin (4 * k) => P)
      {ξ | k ≤ (Finset.univ.filter (fun i => ξ i ∈ A)).card} ≤
      ENNReal.ofReal ((1 / 4 : ℝ) ^ k) := by
  classical
  let F : Ω → ℝ := fun ω => if ω ∈ A then 64 else 1
  have hFm : Measurable F := Measurable.ite hA measurable_const measurable_const
  have hFi : Integrable F P := Integrable.of_bound hFm.aestronglyMeasurable 64
    (Filter.Eventually.of_forall (fun ω => by dsimp [F]; split_ifs <;> norm_num))
  have hFe : (∫ ω, F ω ∂P) = 1 + 63 * P.real A := by
    have he : F = fun ω => 1 + 63 * A.indicator (fun _ => (1 : ℝ)) ω := by
      ext ω
      by_cases h : ω ∈ A <;> norm_num [F, h]
    rw [he, integral_add (integrable_const 1)
      (((integrable_const 1).indicator hA).const_mul 63), integral_const_mul]
    change (∫ a, (1 : ℝ) ∂P) + 63 * (∫ a, A.indicator 1 a ∂P) = _
    rw [integral_indicator_one hA]
    simp
  have hFnonneg : 0 ≤ ∫ ω, F ω ∂P :=
    integral_nonneg (fun ω => by dsimp [F]; split_ifs <;> norm_num)
  have hFbound : (∫ ω, F ω ∂P) ≤ 2 := by rw [hFe]; linarith
  let W : (Fin (4 * k) → Ω) → ℝ := fun ξ => ∏ i, F (ξ i)
  have hWm : Measurable W := by dsimp [W]; fun_prop
  have hWnonneg (ξ : Fin (4 * k) → Ω) : 0 ≤ W ξ := by
    apply Finset.prod_nonneg
    intro i _
    dsimp [F]
    split_ifs <;> norm_num
  have hWbound (ξ : Fin (4 * k) → Ω) : W ξ ≤ 64 ^ (4 * k) := by
    calc
      _ ≤ ∏ _i : Fin (4 * k), (64 : ℝ) := Finset.prod_le_prod₀
        (fun i _ => by dsimp [F]; split_ifs <;> norm_num)
        (fun i _ => by dsimp [F]; split_ifs <;> norm_num)
      _ = _ := by simp
  have hWi : Integrable W (Measure.pi fun _ : Fin (4 * k) => P) :=
    Integrable.of_bound hWm.aestronglyMeasurable (64 ^ (4 * k))
      (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg ξ)]
        exact hWbound ξ))
  have hWe (ξ : Fin (4 * k) → Ω) : W ξ =
      64 ^ (Finset.univ.filter (fun i => ξ i ∈ A)).card := by
    simp only [W, F, ← Finset.prod_filter, Finset.prod_const]
  have h := (hWi.div_const (64 ^ k)).measure_le_integral
    (Filter.Eventually.of_forall (fun ξ => div_nonneg (hWnonneg ξ) (by positivity)))
    (s := {ξ | k ≤ (Finset.univ.filter (fun i => ξ i ∈ A)).card}) (by
      intro ξ hξ
      apply (one_le_div (by positivity : (0 : ℝ) < 64 ^ k)).mpr
      rw [hWe]
      exact pow_le_pow_right₀ (by norm_num) hξ)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div, show W = fun ξ => ∏ i : Fin (4 * k), F (ξ i) from rfl,
    integral_fintype_prod_eq_pow, Fintype.card_fin]
  calc
    _ ≤ 2 ^ (4 * k) / 64 ^ k := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hFnonneg hFbound (4 * k)) (by positivity)
    _ = _ := by rw [pow_mul, ← div_pow]; norm_num

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma goodBlock_failure_probability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → E} (hX : Measurable X)
    (r : ℝ) (hp : P.real {ω | r < ‖X ω‖} ≤ 1 / 64) (k : ℕ) :
    (Measure.pi fun _ : Fin (4 * k) => P)
      {ξ | ¬goodBlock r (fun i => X (ξ i))} ≤ ENNReal.ofReal ((1 / 4 : ℝ) ^ k) := by
  apply (measure_mono ?_).trans (quarter_failure_probability
    (measurableSet_lt measurable_const hX.norm) hp k)
  intro ξ hξ
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (4 * k)))) (p := fun i => ‖X (ξ i)‖ ≤ r)
  simp only [Finset.card_univ, Fintype.card_fin, not_le] at hc
  change ¬3 * (4 * k) ≤ 4 * (Finset.univ.filter (fun i => ‖X (ξ i)‖ ≤ r)).card at hξ
  change k ≤ (Finset.univ.filter (fun i => r < ‖X (ξ i)‖)).card
  omega

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma goodBlock_failure_real {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → E} (hX : Measurable X)
    (r : ℝ) (hp : P.real {ω | r < ‖X ω‖} ≤ 1 / 64) (k : ℕ) :
    (Measure.pi fun _ : Fin (4 * k) => P).real
      {ξ | ¬goodBlock r (fun i => X (ξ i))} ≤ (1 / 4 : ℝ) ^ k := by
  have hh := ENNReal.toReal_mono (by finiteness) (goodBlock_failure_probability hX r hp k)
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ (1 / 4 : ℝ) ^ k)] using hh

omit [InnerProductSpace ℝ E] [SecondCountableTopology E] in
lemma goodBlock_pair_failure_real {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X Y : Ω → E}
    (hX : Measurable X) (hY : Measurable Y) (r : ℝ)
    (hpX : P.real {ω | r < ‖X ω‖} ≤ 1 / 64)
    (hpY : P.real {ω | r < ‖Y ω‖} ≤ 1 / 64) (k : ℕ) :
    (Measure.pi fun _ : Fin (4 * k) => P).real
      {ξ | ¬(goodBlock r (fun i => X (ξ i)) ∧ goodBlock r (fun i => Y (ξ i)))} ≤
        2 * (1 / 4 : ℝ) ^ k := by
  have he : {ξ : Fin (4 * k) → Ω |
      ¬(goodBlock r (fun i => X (ξ i)) ∧ goodBlock r (fun i => Y (ξ i)))} =
      {ξ | ¬goodBlock r (fun i => X (ξ i))} ∪
      {ξ | ¬goodBlock r (fun i => Y (ξ i))} := by ext; simp only [Set.mem_ofPred_eq, Set.mem_union, not_and_or]
  rw [he]
  have hh := measureReal_union_le (μ := Measure.pi fun _ : Fin (4 * k) => P)
    {ξ | ¬goodBlock r (fun i => X (ξ i))} {ξ | ¬goodBlock r (fun i => Y (ξ i))}
  linarith [goodBlock_failure_real hX r hpX k, goodBlock_failure_real hY r hpY k]

lemma integrable_idealNoise [CompleteSpace E] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) {A : Ω → Fin n → E} (hA : Measurable A) :
    Integrable (fun ω => idealNoise r (A ω)) P :=
  Integrable.of_bound ((measurable_idealNoise hn hr).comp hA).aestronglyMeasurable (3 * r)
    (Filter.Eventually.of_forall (fun ω => idealNoise_norm hn hr (A ω)))

lemma integral_idealNoise_zero [CompleteSpace E] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    {A : Ω → Fin n → E} (hs : IdentDistrib A (fun ω i => -A ω i) P P) :
    ∫ ω, idealNoise r (A ω) ∂P = 0 := by
  have he := (hs.comp (measurable_idealNoise hn hr)).integral_eq
  simp only [Function.comp_apply, idealNoise_neg hn hr, integral_neg] at he
  have ht : (2 : ℝ) • (∫ ω, idealNoise r (A ω) ∂P) = 0 := by
    rw [two_smul]
    calc
      _ = -(∫ ω, idealNoise r (A ω) ∂P) + (∫ ω, idealNoise r (A ω) ∂P) :=
        congrArg (fun z => z + (∫ ω, idealNoise r (A ω) ∂P)) he
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

lemma integral_idealNoise_zero_independent [CompleteSpace E]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (A : Fin n → Ω → E) (hi : iIndepFun A P)
    (hs : ∀ i, IdentDistrib (A i) (fun ω => -A i ω) P P) :
    ∫ ω, idealNoise r (fun i => A i ω) ∂P = 0 := by
  apply integral_idealNoise_zero hn hr
  exact IdentDistrib.pi hs hi (hi.comp (fun _ => Neg.neg) (fun _ => measurable_neg))

lemma integral_idealNoise_zero_product [CompleteSpace E]
    {Ω : Type*} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) {X : Ω → E}
    (hX : Measurable X) (hs : p.map X = p.map (fun ω => -X ω)) :
    ∫ ξ, idealNoise r (fun i => X (ξ i)) ∂(Measure.pi fun _ : Fin n => p) = 0 := by
  apply integral_idealNoise_zero hn hr
  refine ⟨(Measurable.of_eval (fun i => hX.comp (measurable_pi_apply i))).aemeasurable,
    (Measurable.of_eval (fun i => (hX.comp (measurable_pi_apply i)).neg)).aemeasurable, ?_⟩
  rw [Measure.pi_map_pi (fun _ => hX.aemeasurable),
    Measure.pi_map_pi (f := fun _ ω => -X ω) (fun _ => hX.neg.aemeasurable)]
  simp only [hs]

end OracleTemplate.RadialFairLocation
