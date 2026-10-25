import LongTails.Algorithms.FairVarianceReduction
import LongTails.Proofs.FairRelativeEnergy
import LongTails.Proofs.FairClippingTransfer

namespace OracleTemplate.FairVarianceReduction

open MeasureTheory ProbabilityTheory RadialFairLocation Classical

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma refresh_good {n : ℕ} (hn : 0 < n) {R G : ℝ} (hR : 0 < R)
    (a : Fin n → E) (u : E) (hu : ‖u‖ ≤ G) (ha : goodBlock R a) :
    refresh R G (fun i => a i + u) = idealNoise R a + u := by
  have hnorm := idealNoise_norm hn hR a
  simp only [idealNoise, ha, ite_true] at hnorm ⊢
  rw [refresh, location_translate hn hR, clip_eq_self]
  exact (norm_add_le _ _).trans (by linarith)

lemma refresh_discrepancy {n : ℕ} (hn : 0 < n) {R G : ℝ} (hR : 0 < R)
    (a : Fin n → E) (u : E) (hu : ‖u‖ ≤ G) :
    ‖refresh R G (fun i => a i + u) - (idealNoise R a + u)‖ ≤
      if goodBlock R a then 0 else 2 * G + 3 * R := by
  by_cases ha : goodBlock R a
  · rw [ite_eq_left ha, refresh_good hn hR a u hu ha, sub_self, norm_zero]
  · rw [ite_eq_right ha]
    simp only [idealNoise, ha, ite_false, zero_add]
    have hG : 0 ≤ G := (norm_nonneg u).trans hu
    exact (norm_sub_le _ _).trans (by
      have hh := norm_clip_le (by positivity : 0 ≤ G + 3 * R)
        (location R (fun i => a i + u))
      change ‖refresh R G (fun i => a i + u)‖ ≤ G + 3 * R at hh
      linarith)

lemma increment_good {n : ℕ} (hn : 0 < n) {R B : ℝ} (hR : 0 < R)
    (a b : Fin n → E) (u v : E) (ha : goodBlock R a) (hb : goodBlock R b) :
    increment R B (fun i => a i + u) (fun i => b i + v) =
      clip B ((u - v) + (idealNoise R a - idealNoise R b)) := by
  simp only [increment, location_translate hn hR, idealNoise, ha, hb, ite_true]
  congr 1
  abel

noncomputable def idealIncrement {n : ℕ} (R : ℝ) (a b : Fin n → E) (u v : E) : E :=
  (u - v) + (idealNoise R a - idealNoise R b)

lemma raw_increment_good {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
    (a b : Fin n → E) (u v : E) (ha : goodBlock R a) (hb : goodBlock R b) :
    location R (fun i => a i + u) - location R (fun i => b i + v) =
      idealIncrement R a b u v := by
  simp only [location_translate hn hR, idealIncrement, idealNoise, ha, hb, ite_true]
  abel

omit [CompleteSpace E] in
lemma idealIncrement_error {n : ℕ} (R : ℝ) (a b : Fin n → E) (u v : E) :
    idealIncrement R a b u v - (u - v) = idealNoise R a - idealNoise R b := by
  simp [idealIncrement]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_refresh {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R) (G : ℝ) :
    Measurable (refresh (E := E) (m := n) R G) :=
  (measurable_clip _).comp (continuous_location hn hR).measurable

lemma measurable_increment {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R) (B : ℝ) :
    Measurable (fun ab : (Fin n → E) × (Fin n → E) => increment R B ab.1 ab.2) :=
  (measurable_clip _).comp (((continuous_location hn hR).measurable.comp measurable_fst).sub
    ((continuous_location hn hR).measurable.comp measurable_snd))

lemma refresh_bias {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {R G : ℝ} (hR : 0 < R)
    {A : Ω → Fin n → E} (hA : Measurable A)
    (hs : IdentDistrib A (fun ω i => -A ω i) P P) (u : E) (hu : ‖u‖ ≤ G) :
    ‖(∫ ω, refresh R G (fun i => A ω i + u) ∂P) - u‖ ≤
      (2 * G + 3 * R) * P.real {ω | ¬goodBlock R (A ω)} := by
  let S : Set Ω := {ω | ¬goodBlock R (A ω)}
  have hS : MeasurableSet S := ((measurableSet_goodBlock R).preimage hA).compl
  have hG : 0 ≤ G := (norm_nonneg u).trans hu
  have hm : Measurable (fun ω i => A ω i + u) :=
    Measurable.of_eval (fun i => ((measurable_pi_apply i).comp hA).add measurable_const)
  have hi : Integrable (fun ω => refresh R G (fun i => A ω i + u)) P :=
    GeneralNormClipping.integrable_clip ((continuous_location hn hR).measurable.comp hm)
      (by positivity)
  have hNi := integrable_idealNoise (P := P) hn hR hA
  have hmean : (∫ ω, idealNoise R (A ω) + u ∂P) = u := by
    rw [integral_add hNi (integrable_const u), integral_idealNoise_zero hn hR hs]
    simp
  have hb : ∀ ω, ‖refresh R G (fun i => A ω i + u) - (idealNoise R (A ω) + u)‖ ≤
      S.indicator (fun _ => 2 * G + 3 * R) ω := by
    intro ω
    have hh := refresh_discrepancy hn hR (A ω) u hu
    by_cases hw : ω ∈ S
    · simpa only [Set.indicator_of_mem hw, ite_eq_right hw] using hh
    · have hg : goodBlock R (A ω) := not_not.mp hw
      simpa only [Set.indicator_of_notMem hw, hg, ite_true] using hh
  have he := norm_integral_le_of_norm_le (μ := P)
    ((integrable_const (2 * G + 3 * R)).indicator hS) (Filter.Eventually.of_forall hb)
  rw [integral_sub (g := fun ω => idealNoise R (A ω) + u) hi
      (hNi.add (integrable_const u)), hmean,
    integral_indicator_const _ hS, smul_eq_mul, mul_comm] at he
  exact he

lemma refresh_second_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {R G : ℝ} (hR : 0 < R)
    {A : Ω → Fin n → E} (hA : Measurable A) (u : E) (hu : ‖u‖ ≤ G) :
    Integrable (fun ω => ‖refresh R G (fun i => A ω i + u) - u‖ ^ 2) P ∧
    (∫ ω, ‖refresh R G (fun i => A ω i + u) - u‖ ^ 2 ∂P) ≤
      9 * R ^ 2 + (2 * G + 3 * R) ^ 2 * P.real {ω | ¬goodBlock R (A ω)} := by
  let S : Set Ω := {ω | ¬goodBlock R (A ω)}
  have hS : MeasurableSet S := ((measurableSet_goodBlock R).preimage hA).compl
  have hG : 0 ≤ G := (norm_nonneg u).trans hu
  have hm : Measurable (fun ω i => A ω i + u) :=
    Measurable.of_eval (fun i => ((measurable_pi_apply i).comp hA).add measurable_const)
  have hbound (ω : Ω) : ‖refresh R G (fun i => A ω i + u) - u‖ ≤ 2 * G + 3 * R := by
    have hh := norm_clip_le (by positivity : 0 ≤ G + 3 * R)
      (location R (fun i => A ω i + u))
    change ‖refresh R G (fun i => A ω i + u)‖ ≤ G + 3 * R at hh
    exact (norm_sub_le _ _).trans (by linarith)
  have hi : Integrable (fun ω => ‖refresh R G (fun i => A ω i + u) - u‖ ^ 2) P := by
    apply Integrable.of_bound
      ((((measurable_refresh hn hR G).comp hm).sub measurable_const).norm.pow_const 2).aestronglyMeasurable ((2 * G + 3 * R) ^ 2)
    filter_upwards [] with ω
    change |‖refresh R G (fun i => A ω i + u) - u‖ ^ 2| ≤ _
    rw [abs_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbound ω) 2
  refine ⟨hi, ?_⟩
  have hI := (integrable_const (μ := P) ((2 * G + 3 * R) ^ 2)).indicator hS
  have hb (ω : Ω) : ‖refresh R G (fun i => A ω i + u) - u‖ ^ 2 ≤
      9 * R ^ 2 + S.indicator (fun _ => (2 * G + 3 * R) ^ 2) ω := by
    by_cases hw : ω ∈ S
    · rw [Set.indicator_of_mem hw]
      have hh := pow_le_pow_left₀ (norm_nonneg _) (hbound ω) 2
      nlinarith [sq_nonneg R]
    · have hg : goodBlock R (A ω) := not_not.mp hw
      rw [Set.indicator_of_notMem hw, add_zero, refresh_good hn hR _ u hu hg, add_sub_cancel_right]
      have hh := pow_le_pow_left₀ (norm_nonneg _) (idealNoise_norm hn hR (A ω)) 2
      nlinarith
  have he := integral_mono hi ((integrable_const (9 * R ^ 2)).add hI) hb
  simp only [Pi.add_apply] at he
  rw [integral_add (integrable_const _) hI, integral_const, integral_indicator_const _ hS] at he
  simpa only [probReal_univ, one_smul, smul_eq_mul, one_mul, mul_comm (P.real S)] using he

lemma measurable_idealIncrement {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (hn : 0 < n) {R : ℝ} (hR : 0 < R) {A B : Ω → Fin n → E}
    (hA : Measurable A) (hB : Measurable B) (u v : E) :
    Measurable (fun ω => idealIncrement R (A ω) (B ω) u v) :=
  measurable_const.add (((measurable_idealNoise hn hR).comp hA).sub
    ((measurable_idealNoise hn hR).comp hB))

lemma integrable_idealIncrement {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
    {A B : Ω → Fin n → E} (hA : Measurable A) (hB : Measurable B) (u v : E) :
    Integrable (fun ω => idealIncrement R (A ω) (B ω) u v) P :=
  (integrable_const (u - v)).add
    ((integrable_idealNoise hn hR hA).sub (integrable_idealNoise hn hR hB))

lemma integral_idealIncrement {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {R : ℝ} (hR : 0 < R)
    {A B : Ω → Fin n → E} (hA : Measurable A) (hB : Measurable B)
    (hsA : IdentDistrib A (fun ω i => -A ω i) P P)
    (hsB : IdentDistrib B (fun ω i => -B ω i) P P) (u v : E) :
    ∫ ω, idealIncrement R (A ω) (B ω) u v ∂P = u - v := by
  have hiA := integrable_idealNoise (P := P) hn hR hA
  have hiB := integrable_idealNoise (P := P) hn hR hB
  simp only [idealIncrement]
  rw [integral_add (f := fun _ => u - v) (g := fun ω => idealNoise R (A ω) - idealNoise R (B ω))
    (integrable_const _) (hiA.sub hiB), integral_sub hiA hiB,
    integral_idealNoise_zero hn hR hsA, integral_idealNoise_zero hn hR hsB]
  simp

lemma increment_bias {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {R K : ℝ} (hR : 0 < R) (hK : 0 < K)
    {A B : Ω → Fin n → E} (hA : Measurable A) (hB : Measurable B)
    (hsA : IdentDistrib A (fun ω i => -A ω i) P P)
    (hsB : IdentDistrib B (fun ω i => -B ω i) P P) (u v : E) (huv : ‖u - v‖ ≤ K / 2) :
    ‖(∫ ω, increment R K (fun i => A ω i + u) (fun i => B ω i + v) ∂P) - (u - v)‖ ≤
      2 / K * (∫ ω, ‖idealNoise R (A ω) - idealNoise R (B ω)‖ ^ 2 ∂P) +
        2 * K * P.real {ω | ¬(goodBlock R (A ω) ∧ goodBlock R (B ω))} := by
  let S : Set Ω := {ω | ¬(goodBlock R (A ω) ∧ goodBlock R (B ω))}
  have hS : MeasurableSet S :=
    (((measurableSet_goodBlock R).preimage hA).inter
      ((measurableSet_goodBlock R).preimage hB)).compl
  have hmA : Measurable (fun ω i => A ω i + u) :=
    Measurable.of_eval (fun i => ((measurable_pi_apply i).comp hA).add measurable_const)
  have hmB : Measurable (fun ω i => B ω i + v) :=
    Measurable.of_eval (fun i => ((measurable_pi_apply i).comp hB).add measurable_const)
  have hX := ((continuous_location hn hR).measurable.comp hmA).sub
    ((continuous_location hn hR).measurable.comp hmB)
  have hi2 : Integrable (fun ω => ‖idealIncrement R (A ω) (B ω) u v - (u - v)‖ ^ 2) P := by
    simp only [idealIncrement_error]
    exact integrable_idealNoise_difference_sq hn hR hA hB
  have he := FairClippingTransfer.integral_bias_transfer hX
    (measurable_idealIncrement hn hR hA hB u v) (integrable_idealIncrement hn hR hA hB u v)
    (integral_idealIncrement hn hR hA hB hsA hsB u v) hi2 hS hK huv (by
      intro ω hω
      have hg : goodBlock R (A ω) ∧ goodBlock R (B ω) := not_not.mp hω
      exact raw_increment_good hn hR _ _ u v hg.1 hg.2)
  simpa only [increment, S, Pi.sub_apply, Function.comp_apply, idealIncrement_error] using he

lemma increment_second_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    {A B : Ω → Fin n → E} (hA : Measurable A) (hB : Measurable B)
    (u v : E) (huv : ‖u - v‖ ≤ K) :
    Integrable (fun ω => ‖increment R K (fun i => A ω i + u) (fun i => B ω i + v) - (u - v)‖ ^ 2) P ∧
    (∫ ω, ‖increment R K (fun i => A ω i + u) (fun i => B ω i + v) - (u - v)‖ ^ 2 ∂P) ≤
      (∫ ω, ‖idealNoise R (A ω) - idealNoise R (B ω)‖ ^ 2 ∂P) +
        4 * K ^ 2 * P.real {ω | ¬(goodBlock R (A ω) ∧ goodBlock R (B ω))} := by
  let S : Set Ω := {ω | ¬(goodBlock R (A ω) ∧ goodBlock R (B ω))}
  have hS : MeasurableSet S :=
    (((measurableSet_goodBlock R).preimage hA).inter
      ((measurableSet_goodBlock R).preimage hB)).compl
  have hmA : Measurable (fun ω i => A ω i + u) :=
    Measurable.of_eval (fun i => ((measurable_pi_apply i).comp hA).add measurable_const)
  have hmB : Measurable (fun ω i => B ω i + v) :=
    Measurable.of_eval (fun i => ((measurable_pi_apply i).comp hB).add measurable_const)
  have hX := ((continuous_location hn hR).measurable.comp hmA).sub
    ((continuous_location hn hR).measurable.comp hmB)
  have hi2 : Integrable (fun ω => ‖idealIncrement R (A ω) (B ω) u v - (u - v)‖ ^ 2) P := by
    simp only [idealIncrement_error]
    exact integrable_idealNoise_difference_sq hn hR hA hB
  refine ⟨FairClippingTransfer.integrable_clipped_error_sq hX hK (u - v), ?_⟩
  have he := FairClippingTransfer.integral_error_sq hX hi2 hS hK huv (by
    intro ω hω
    have hg : goodBlock R (A ω) ∧ goodBlock R (B ω) := not_not.mp hω
    exact raw_increment_good hn hR _ _ u v hg.1 hg.2)
  simpa only [increment, S, Pi.sub_apply, Function.comp_apply, idealIncrement_error] using he

end OracleTemplate.FairVarianceReduction
