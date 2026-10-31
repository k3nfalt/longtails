import LongTails.Proofs.FairLocationProbability

namespace OracleTemplate.RadialFairLocation

open MeasureTheory ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E]

lemma relative_ratio_nonneg {r : ℝ} (hr : 0 ≤ r) (a b : E) :
    0 ≤ ‖a - b‖ / (r + ‖a‖ + ‖b‖) := by positivity

lemma relative_ratio_le_one {r : ℝ} (hr : 0 ≤ r) (a b : E) :
    ‖a - b‖ / (r + ‖a‖ + ‖b‖) ≤ 1 := by
  have hd : 0 ≤ r + ‖a‖ + ‖b‖ := by positivity
  rcases eq_or_lt_of_le hd with h | h
  · rw [← h, div_zero]
    norm_num
  · apply (div_le_one h).mpr
    linarith [norm_sub_le a b]

lemma relative_ratio_radius {r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R) (a b : E) :
    ‖a - b‖ / (R + ‖a‖ + ‖b‖) ≤ ‖a - b‖ / (r + ‖a‖ + ‖b‖) := by
  have hd : 0 ≤ r + ‖a‖ + ‖b‖ := by positivity
  rcases eq_or_lt_of_le hd with h | h
  · have ha : a = 0 := norm_eq_zero.mp (by linarith [norm_nonneg a, norm_nonneg b])
    have hb : b = 0 := norm_eq_zero.mp (by linarith [norm_nonneg a, norm_nonneg b])
    simp [ha, hb]
  · exact div_le_div_of_nonneg_left (norm_nonneg _) h (by linarith)

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma integrable_relative_ratio_sq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {r : ℝ} (hr : 0 ≤ r)
    {A B : Ω → E} (hA : Measurable A) (hB : Measurable B) :
    Integrable (fun ω => (‖A ω - B ω‖ / (r + ‖A ω‖ + ‖B ω‖)) ^ 2) P := by
  apply Integrable.of_bound
    (((hA.sub hB).norm.div ((measurable_const.add hA.norm).add hB.norm)).pow_const 2).aestronglyMeasurable 1
  filter_upwards [] with ω
  change |(‖A ω - B ω‖ / (r + ‖A ω‖ + ‖B ω‖)) ^ 2| ≤ 1
  rw [abs_sq]
  nlinarith [relative_ratio_nonneg hr (A ω) (B ω), relative_ratio_le_one hr (A ω) (B ω)]

lemma integral_relative_ratio_radius {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {r R : ℝ} (hr : 0 ≤ r) (hR : r ≤ R)
    {A B : Ω → E} (hA : Measurable A) (hB : Measurable B) :
    (∫ ω, (‖A ω - B ω‖ / (R + ‖A ω‖ + ‖B ω‖)) ^ 2 ∂P) ≤
      ∫ ω, (‖A ω - B ω‖ / (r + ‖A ω‖ + ‖B ω‖)) ^ 2 ∂P := by
  apply integral_mono (integrable_relative_ratio_sq (hr.trans hR) hA hB)
    (integrable_relative_ratio_sq hr hA hB)
  intro ω
  exact pow_le_pow_left₀ (relative_ratio_nonneg (hr.trans hR) _ _)
    (relative_ratio_radius hr hR _ _) 2

variable [InnerProductSpace ℝ E] [CompleteSpace E]

lemma integrable_idealNoise_difference_sq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) {A B : Ω → Fin n → E}
    (hA : Measurable A) (hB : Measurable B) :
    Integrable (fun ω => ‖idealNoise r (A ω) - idealNoise r (B ω)‖ ^ 2) P := by
  apply Integrable.of_bound
    ((((measurable_idealNoise hn hr).comp hA).sub
      ((measurable_idealNoise hn hr).comp hB)).norm.pow_const 2).aestronglyMeasurable (36 * r ^ 2)
  filter_upwards [] with ω
  have hh : ‖idealNoise r (A ω) - idealNoise r (B ω)‖ ≤ 6 * r :=
    (norm_sub_le _ _).trans (by linarith [idealNoise_norm hn hr (A ω), idealNoise_norm hn hr (B ω)])
  change |‖idealNoise r (A ω) - idealNoise r (B ω)‖ ^ 2| ≤ _
  rw [abs_sq]
  nlinarith [(sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh]

lemma integral_idealNoise_difference_sq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) {A B : Ω → Fin n → E}
    (hA : Measurable A) (hB : Measurable B) {v δ : ℝ}
    (hv : ∀ i, (∫ ω, (‖A ω i - B ω i‖ / (r + ‖A ω i‖ + ‖B ω i‖)) ^ 2 ∂P) ≤ v)
    (hδ : P.real {ω | ¬(goodBlock r (A ω) ∧ goodBlock r (B ω))} ≤ δ) :
    (∫ ω, ‖idealNoise r (A ω) - idealNoise r (B ω)‖ ^ 2 ∂P) ≤
      (2048 * r) ^ 2 * v + 36 * r ^ 2 * δ := by
  classical
  let S : Set Ω := {ω | ¬(goodBlock r (A ω) ∧ goodBlock r (B ω))}
  have hS : MeasurableSet S :=
    ((measurableSet_goodBlock r).preimage hA |>.inter
      ((measurableSet_goodBlock r).preimage hB)).compl
  let Z : Ω → ℝ := fun ω => ‖idealNoise r (A ω) - idealNoise r (B ω)‖ ^ 2
  let V : Fin n → Ω → ℝ := fun i ω =>
    (‖A ω i - B ω i‖ / (r + ‖A ω i‖ + ‖B ω i‖)) ^ 2
  have hVi (i : Fin n) : Integrable (V i) P :=
    integrable_relative_ratio_sq hr.le ((measurable_pi_apply i).comp hA)
      ((measurable_pi_apply i).comp hB)
  have hZi : Integrable Z P := integrable_idealNoise_difference_sq hn hr hA hB
  have hR := (integrable_finsetSum Finset.univ (fun i _ => hVi i)).const_mul
    ((2048 * r) ^ 2 / n)
  have hI := (integrable_const (μ := P) (36 * r ^ 2)).indicator hS
  have hb : ∀ ω, Z ω ≤ (2048 * r) ^ 2 / n * (∑ i, V i ω) +
      S.indicator (fun _ => 36 * r ^ 2) ω := by
    intro ω
    have hh := idealNoise_difference_sq hn hr (A ω) (B ω)
    by_cases hw : ω ∈ S
    · simpa only [Z, V, Set.indicator_of_mem hw, ite_eq_right hw] using hh
    · have hg : goodBlock r (A ω) ∧ goodBlock r (B ω) := not_not.mp hw
      simpa [Z, V, Set.indicator_of_notMem hw, hg] using hh
  have he := integral_mono hZi (hR.add hI) hb
  simp only [Pi.add_apply] at he
  rw [integral_add hR hI, integral_const_mul, integral_finsetSum _ (fun i _ => hVi i),
    integral_indicator_const _ hS, smul_eq_mul] at he
  have hsum : (∑ i, ∫ ω, V i ω ∂P) ≤ n * v := by
    calc
      _ ≤ ∑ _i : Fin n, v := Finset.sum_le_sum (fun i _ => hv i)
      _ = _ := by simp
  have hm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (2048 * r) ^ 2 / (n : ℝ))
  have hd := mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 36 * r ^ 2)
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hid : (2048 * r) ^ 2 / (n : ℝ) * (n * v) = (2048 * r) ^ 2 * v := by field_simp
  rw [hid] at hm
  dsimp [Z, S] at he hd
  nlinarith

lemma integral_idealNoise_difference_product {Ω : Type*} [MeasurableSpace Ω]
    {p : Measure Ω} [IsProbabilityMeasure p] {k : ℕ} (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) {X Y : Ω → E} (hX : Measurable X) (hY : Measurable Y)
    (hpX : p.real {ω | r < ‖X ω‖} ≤ 1 / 64)
    (hpY : p.real {ω | r < ‖Y ω‖} ≤ 1 / 64) {v : ℝ} (hv0 : 0 ≤ v)
    (hv : (∫ ω, (‖X ω - Y ω‖ / (r + ‖X ω‖ + ‖Y ω‖)) ^ 2 ∂p) ≤ v) :
    (∫ ξ, ‖idealNoise r (fun i => X (ξ i)) - idealNoise r (fun i => Y (ξ i))‖ ^ 2
      ∂(Measure.pi fun _ : Fin (4 * k) => p)) ≤
        (2 : ℝ) ^ 23 * r ^ 2 * (v + (1 / 4 : ℝ) ^ k) := by
  have hA : Measurable (fun ξ : Fin (4 * k) → Ω => fun i => X (ξ i)) :=
    Measurable.of_eval (fun i => hX.comp (measurable_pi_apply i))
  have hB : Measurable (fun ξ : Fin (4 * k) → Ω => fun i => Y (ξ i)) :=
    Measurable.of_eval (fun i => hY.comp (measurable_pi_apply i))
  have hvi (i : Fin (4 * k)) :
      (∫ ξ : Fin (4 * k) → Ω, (‖X (ξ i) - Y (ξ i)‖ /
        (r + ‖X (ξ i)‖ + ‖Y (ξ i)‖)) ^ 2 ∂(Measure.pi fun _ => p)) ≤ v := by
    rw [integral_comp_eval (μ := fun _ : Fin (4 * k) => p) (i := i)
      (f := fun ω => (‖X ω - Y ω‖ / (r + ‖X ω‖ + ‖Y ω‖)) ^ 2)
      (integrable_relative_ratio_sq (P := p) hr.le hX hY).aestronglyMeasurable]
    exact hv
  have he := integral_idealNoise_difference_sq (by omega : 0 < 4 * k) hr hA hB hvi
    (goodBlock_pair_failure_real hX hY r hpX hpY k)
  have hp : 0 ≤ (1 / 4 : ℝ) ^ k := by positivity
  nlinarith [mul_nonneg (sq_nonneg r) hv0, mul_nonneg (sq_nonneg r) hp]

end OracleTemplate.RadialFairLocation
