import LongTails.Proofs.RobustEnergyConcentration
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.StochasticGeneralizedConcentration

open MeasureTheory

namespace OracleTemplate.AdaptiveEntropicConcentration

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma unit_integrable {X : Ω → ℝ} (hX : Measurable X)
    (hbound : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) : Integrable X P := by
  apply Integrable.of_bound hX.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun ω => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hbound ω).1] using (hbound ω).2)

lemma unit_square_integrable {X : Ω → ℝ} (hX : Measurable X)
    (hbound : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) :
    Integrable (fun ω => (X ω) ^ 2) P := by
  apply unit_integrable (hX.pow_const 2)
  intro ω
  constructor
  · positivity
  · nlinarith [(hbound ω).1, (hbound ω).2]

lemma unit_square_mean {X : Ω → ℝ} (hX : Measurable X)
    (hbound : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) :
    (∫ ω, (X ω) ^ 2 ∂P) ≤ ∫ ω, X ω ∂P := by
  apply integral_mono (unit_square_integrable hX hbound) (unit_integrable hX hbound)
  intro ω
  nlinarith [(hbound ω).1, (hbound ω).2]

omit [IsProbabilityMeasure P] in
lemma exponential_shift {Z : Ω → ℝ} {c b : ℝ}
    (hi : Integrable (fun ω => Real.exp (Z ω)) P)
    (hb : (∫ ω, Real.exp (Z ω) ∂P) ≤ Real.exp b) (hcb : c + b ≤ 0) :
    Integrable (fun ω => Real.exp (c + Z ω)) P ∧
      (∫ ω, Real.exp (c + Z ω) ∂P) ≤ 1 := by
  have he : (fun ω => Real.exp (c + Z ω)) =
      fun ω => Real.exp c * Real.exp (Z ω) := by ext ω; rw [Real.exp_add]
  rw [he]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ Real.exp c * Real.exp b := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg c)
    _ = Real.exp (c + b) := (Real.exp_add c b).symm
    _ ≤ 1 := by simpa using Real.exp_le_exp.mpr hcb

lemma unit_forward_mgf {X : Ω → ℝ} (hX : Measurable X)
    (hbound : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) :
    Integrable (fun ω => Real.exp (X ω / 2 - ∫ z, X z ∂P)) P ∧
      (∫ ω, Real.exp (X ω / 2 - ∫ z, X z ∂P) ∂P) ≤ 1 := by
  let m := ∫ z, X z ∂P
  have hm : 0 ≤ m := integral_nonneg (fun ω => (hbound ω).1)
  have hmean : (∫ ω, X ω / 2 ∂P) ≤ m / 2 := by rw [integral_div]
  have hsecond : (∫ ω, (X ω / 2) ^ 2 ∂P) ≤ m / 4 := by
    simp_rw [div_pow]
    rw [integral_div]
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
      div_le_div_of_nonneg_right (unit_square_mean (P := P) hX hbound) (by norm_num : (0 : ℝ) ≤ 4)
  have hh := RobustGradient.bounded_increment_mgf (hX.div_const 2)
    (fun ω => by rw [abs_of_nonneg (div_nonneg (hbound ω).1 (by norm_num) : 0 ≤ X ω / 2)]; linarith [(hbound ω).2])
    hmean hsecond
  have hs := exponential_shift hh.1 hh.2 (c := -m) (by linarith : -m + (m / 2 + m / 4) ≤ 0)
  simpa only [m, sub_eq_add_neg, add_comm] using hs

lemma unit_inverse_mgf {X : Ω → ℝ} (hX : Measurable X)
    (hbound : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) :
    Integrable (fun ω => Real.exp ((∫ z, X z ∂P) / 4 - X ω / 2)) P ∧
      (∫ ω, Real.exp ((∫ z, X z ∂P) / 4 - X ω / 2) ∂P) ≤ 1 := by
  let m := ∫ z, X z ∂P
  have hmean : (∫ ω, -(X ω / 2) ∂P) ≤ -(m / 2) := by
    rw [integral_neg, integral_div]
  have hsecond : (∫ ω, (-(X ω / 2)) ^ 2 ∂P) ≤ m / 4 := by
    simp_rw [neg_sq, div_pow]
    rw [integral_div]
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using
      div_le_div_of_nonneg_right (unit_square_mean (P := P) hX hbound) (by norm_num : (0 : ℝ) ≤ 4)
  have hh := RobustGradient.bounded_increment_mgf (hX.div_const 2).neg
    (fun ω => by
      change |-(X ω / 2)| ≤ 1
      rw [abs_neg, abs_of_nonneg (div_nonneg (hbound ω).1 (by norm_num) : 0 ≤ X ω / 2)]
      linarith [(hbound ω).2]) hmean hsecond
  have hs := exponential_shift hh.1 hh.2 (c := m / 4) (by linarith : m / 4 + (-(m / 2) + m / 4) ≤ 0)
  simpa only [m, sub_eq_add_neg, Pi.neg_apply] using hs

lemma accumulated_unit_forward {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (X : (n : ℕ) → S → (Fin n → Ω) → ℝ)
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hX : ∀ n, Measurable (Function.uncurry (X n)))
    (hb : ∀ n s b, 0 ≤ X n s b ∧ X n s b ≤ 1) (N : ℕ) (s : S) :
    let inc := fun n s b => X n s b / 2 - ∫ z, X n s z ∂Measure.pi (fun _ : Fin n => p)
    Integrable (fun ξ => Real.exp (StochasticGeneralized.accumulated cost next inc N s ξ))
      (Measure.infinitePi fun _ : ℕ => p) ∧
      (∫ ξ, Real.exp (StochasticGeneralized.accumulated cost next inc N s ξ)
        ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ 1 := by
  intro inc
  apply StochasticGeneralized.accumulated_exp_control p hc hn
  · intro n
    have hm : Measurable (fun s => ∫ z, X n s z ∂Measure.pi (fun _ : Fin n => p)) :=
      (hX n).stronglyMeasurable.integral_prod_right.measurable
    exact ((hX n).div_const 2).sub (hm.comp measurable_fst)
  · intro s
    exact (unit_forward_mgf ((hX (cost s)).comp measurable_prodMk_left) (hb (cost s) s)).1
  · intro s
    exact (unit_forward_mgf ((hX (cost s)).comp measurable_prodMk_left) (hb (cost s) s)).2

lemma accumulated_unit_inverse {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (X : (n : ℕ) → S → (Fin n → Ω) → ℝ)
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hX : ∀ n, Measurable (Function.uncurry (X n)))
    (hb : ∀ n s b, 0 ≤ X n s b ∧ X n s b ≤ 1) (N : ℕ) (s : S) :
    let inc := fun n s b => (∫ z, X n s z ∂Measure.pi (fun _ : Fin n => p)) / 4 - X n s b / 2
    Integrable (fun ξ => Real.exp (StochasticGeneralized.accumulated cost next inc N s ξ))
      (Measure.infinitePi fun _ : ℕ => p) ∧
      (∫ ξ, Real.exp (StochasticGeneralized.accumulated cost next inc N s ξ)
        ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ 1 := by
  intro inc
  apply StochasticGeneralized.accumulated_exp_control p hc hn
  · intro n
    have hm : Measurable (fun s => ∫ z, X n s z ∂Measure.pi (fun _ : Fin n => p)) :=
      (hX n).stronglyMeasurable.integral_prod_right.measurable
    exact ((hm.comp measurable_fst).div_const 4).sub ((hX n).div_const 2)
  · intro s
    exact (unit_inverse_mgf ((hX (cost s)).comp measurable_prodMk_left) (hb (cost s) s)).1
  · intro s
    exact (unit_inverse_mgf ((hX (cost s)).comp measurable_prodMk_left) (hb (cost s) s)).2

lemma accumulated_inverse_tail {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (X : (n : ℕ) → S → (Fin n → Ω) → ℝ)
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hX : ∀ n, Measurable (Function.uncurry (X n)))
    (hb : ∀ n s b, 0 ≤ X n s b ∧ X n s b ≤ 1) (N : ℕ) (s : S) (H : ℝ) :
    let m := fun n s (_ : Fin n → Ω) => ∫ z, X n s z ∂Measure.pi (fun _ : Fin n => p)
    (Measure.infinitePi fun _ : ℕ => p)
      {ξ | 2 * StochasticGeneralized.accumulated cost next X N s ξ + 4 * H <
        StochasticGeneralized.accumulated cost next m N s ξ} ≤ ENNReal.ofReal (Real.exp (-H)) := by
  intro m
  let inc := fun n s b => (∫ z, X n s z ∂Measure.pi (fun _ : Fin n => p)) / 4 - X n s b / 2
  have hm := accumulated_unit_inverse p cost next X hc hn hX hb N s
  change Integrable (fun ξ => Real.exp (StochasticGeneralized.accumulated cost next inc N s ξ)) _ ∧
    (∫ ξ, Real.exp (StochasticGeneralized.accumulated cost next inc N s ξ)
      ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ 1 at hm
  have he (ξ : ℕ → Ω) : StochasticGeneralized.accumulated cost next inc N s ξ =
      (1 / 4 : ℝ) * StochasticGeneralized.accumulated cost next m N s ξ +
        (-1 / 2 : ℝ) * StochasticGeneralized.accumulated cost next X N s ξ := by
    have hi : inc = fun n s b => (1 / 4 : ℝ) * m n s b + (-1 / 2 : ℝ) * X n s b := by
      funext n s b
      dsimp [inc, m]
      ring
    rw [hi, StochasticGeneralized.accumulated_linear]
  have ht := StochasticGeneralized.exponential_tail (P := Measure.infinitePi (fun _ : ℕ => p))
    (Z := fun ξ => StochasticGeneralized.accumulated cost next inc N s ξ)
    (t := 1) (C := 0) (r := H) (by norm_num)
    (by simpa only [one_mul] using hm.1) (by simpa only [one_mul, Real.exp_zero] using hm.2)
  have hset : {ξ | 2 * StochasticGeneralized.accumulated cost next X N s ξ + 4 * H <
      StochasticGeneralized.accumulated cost next m N s ξ} =
      {ξ | H < StochasticGeneralized.accumulated cost next inc N s ξ} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, he]
    constructor <;> intro h <;> linarith
  rw [hset]
  simpa only [one_mul, zero_sub] using ht

lemma exponential_unit_tail_ge {Z : Ω → ℝ}
    (hi : Integrable (fun ω => Real.exp (Z ω)) P)
    (hm : (∫ ω, Real.exp (Z ω) ∂P) ≤ 1) (H : ℝ) :
    P {ω | H ≤ Z ω} ≤ ENNReal.ofReal (Real.exp (-H)) := by
  have ht := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := P) (X := Z) H
    (show (0 : ℝ) ≤ 1 by norm_num) (by simpa only [one_mul] using hi)
  have he : P.real {ω | H ≤ Z ω} ≤ Real.exp (-H) := by
    have hh := mul_le_mul_of_nonneg_left hm (Real.exp_nonneg (-H))
    simp only [ProbabilityTheory.mgf, one_mul, neg_one_mul] at ht
    exact ht.trans (by simpa only [mul_one] using hh)
  calc
    _ = ENNReal.ofReal (P.real {ω | H ≤ Z ω}) :=
      (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal he

lemma accumulated_forward_tail {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (X : (n : ℕ) → S → (Fin n → Ω) → ℝ)
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hX : ∀ n, Measurable (Function.uncurry (X n)))
    (hb : ∀ n s b, 0 ≤ X n s b ∧ X n s b ≤ 1) (N : ℕ) (s : S) (H : ℝ) :
    let m := fun n s (_ : Fin n → Ω) => ∫ z, X n s z ∂Measure.pi (fun _ : Fin n => p)
    (Measure.infinitePi fun _ : ℕ => p)
      {ξ | 2 * StochasticGeneralized.accumulated cost next m N s ξ + 2 * H ≤
        StochasticGeneralized.accumulated cost next X N s ξ} ≤ ENNReal.ofReal (Real.exp (-H)) := by
  intro m
  let inc := fun n s b => X n s b / 2 - ∫ z, X n s z ∂Measure.pi (fun _ : Fin n => p)
  have hm := accumulated_unit_forward p cost next X hc hn hX hb N s
  change Integrable (fun ξ => Real.exp (StochasticGeneralized.accumulated cost next inc N s ξ)) _ ∧
    (∫ ξ, Real.exp (StochasticGeneralized.accumulated cost next inc N s ξ)
      ∂Measure.infinitePi (fun _ : ℕ => p)) ≤ 1 at hm
  have he (ξ : ℕ → Ω) : StochasticGeneralized.accumulated cost next inc N s ξ =
      (-1 : ℝ) * StochasticGeneralized.accumulated cost next m N s ξ +
        (1 / 2 : ℝ) * StochasticGeneralized.accumulated cost next X N s ξ := by
    have hi : inc = fun n s b => (-1 : ℝ) * m n s b + (1 / 2 : ℝ) * X n s b := by
      funext n s b
      dsimp [inc, m]
      ring
    rw [hi, StochasticGeneralized.accumulated_linear]
  have ht := exponential_unit_tail_ge hm.1 hm.2 H
  have hset : {ξ | 2 * StochasticGeneralized.accumulated cost next m N s ξ + 2 * H ≤
      StochasticGeneralized.accumulated cost next X N s ξ} =
      {ξ | H ≤ StochasticGeneralized.accumulated cost next inc N s ξ} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, he]
    constructor <;> intro h <;> linarith
  rw [hset]
  simpa only [one_mul, zero_sub] using ht

omit [IsProbabilityMeasure P] in
lemma zero_moment_ae {X : Ω → ℝ} {p : ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (hi : Integrable (fun ω => X ω ^ p) P)
    (hm : (∫ ω, X ω ^ p ∂P) ≤ 0) : ∀ᵐ ω ∂P, X ω = 0 := by
  have he : (∫ ω, X ω ^ p ∂P) = 0 :=
    le_antisymm hm (integral_nonneg fun ω => Real.rpow_nonneg (hX ω) p)
  have ha := (integral_eq_zero_iff_of_nonneg
    (fun ω => Real.rpow_nonneg (hX ω) p) hi).mp he
  filter_upwards [ha] with ω hω
  exact ((Real.rpow_eq_zero_iff_of_nonneg (hX ω)).mp hω).1

lemma accumulated_rare_tail {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (p : Measure Ω) [IsProbabilityMeasure p] (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (X : (n : ℕ) → S → (Fin n → Ω) → ℝ)
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hX : ∀ n, Measurable (Function.uncurry (X n)))
    (hb : ∀ n s b, 0 ≤ X n s b ∧ X n s b ≤ 1) (N : ℕ) (s : S) (k : ℝ)
    (hm : ∀ ξ, StochasticGeneralized.accumulated cost next
      (fun n s (_ : Fin n → Ω) => ∫ z, X n s z ∂Measure.pi (fun _ : Fin n => p))
      N s ξ ≤ k / 8) :
    (Measure.infinitePi fun _ : ℕ => p)
      {ξ | k / 2 ≤ StochasticGeneralized.accumulated cost next X N s ξ} ≤
      ENNReal.ofReal (Real.exp (-k / 8)) := by
  have ht := accumulated_forward_tail p cost next X hc hn hX hb N s (k / 8)
  apply (measure_mono ?_).trans (by simpa only [neg_div] using ht)
  intro ξ hξ
  change k / 2 ≤ StochasticGeneralized.accumulated cost next X N s ξ at hξ
  change 2 * StochasticGeneralized.accumulated cost next
    (fun n s (_ : Fin n → Ω) => ∫ z, X n s z ∂Measure.pi (fun _ : Fin n => p))
    N s ξ + 2 * (k / 8) ≤ StochasticGeneralized.accumulated cost next X N s ξ
  linarith [hm ξ]

omit [IsProbabilityMeasure P] in
lemma noise_tail_eighth {X : Ω → ℝ} {p σ : ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (hp : 1 ≤ p) (hσ : 0 ≤ σ)
    (hi : Integrable (fun ω => X ω ^ p) P)
    (hm : (∫ ω, X ω ^ p ∂P) ≤ σ ^ p) :
    P.real {ω | 8 * σ < X ω} ≤ 1 / 8 := by
  by_cases hz : σ = 0
  · have ha := zero_moment_ae hX hi (by simpa [hz, show p ≠ 0 by linarith] using hm)
    have hn : ∀ᵐ ω ∂P, ¬ (8 * σ < X ω) := by
      filter_upwards [ha] with ω hω
      simp [hz, hω]
    have he : P {ω | 8 * σ < X ω} = 0 := by
      simpa only [not_not] using (ae_iff.mp hn)
    simp [measureReal_def, he]
  have hs : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hz)
  have hr : 0 < (8 * σ) ^ p := Real.rpow_pos_of_pos (by positivity) _
  have ht := (hi.div_const ((8 * σ) ^ p)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => div_nonneg (Real.rpow_nonneg (hX ω) _) hr.le))
    (s := {ω | 8 * σ < X ω}) (by
      intro ω hω
      apply (one_le_div hr).mpr
      exact Real.rpow_le_rpow (by positivity) (show 8 * σ < X ω from hω).le (by linarith))
  have hpow : (8 : ℝ) ≤ 8 ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8) hp
  have hb : σ ^ p / (8 * σ) ^ p ≤ 1 / 8 := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hσ]
    have hsp : 0 < σ ^ p := Real.rpow_pos_of_pos hs p
    apply (div_le_iff₀ (mul_pos (by positivity) hsp)).mpr
    nlinarith
  have he : P {ω | 8 * σ < X ω} ≤ ENNReal.ofReal (1 / 8) := by
    apply ht.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_div]
    exact (div_le_div_of_nonneg_right hm hr.le).trans hb
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 8)] using hh

end OracleTemplate.AdaptiveEntropicConcentration
