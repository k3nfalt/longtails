import LongTails.Algorithms.StochasticEnvelopeProgram
import LongTails.Proofs.StochasticEnvelopeSampling
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.StochasticEnvelopeDebiasing

lemma exponent_loss {q t : ℝ} (hq : 2 ≤ q) (ht : 0 < t) (ht1 : t ≤ 1) :
    let p' := q * (1 + t) / (q * (1 + t) - 1)
    1 < p' ∧ p' ≤ 2 ∧
      t / (4 * q) ≤ p' / q - (1 + t / 2) * (p' - 1) ∧
      p' / q - (1 + t / 2) * (p' - 1) ≤ 1 / 2 := by
  have hq0 : 0 < q := by linarith
  have hqt : 2 ≤ q * (1 + t) := by nlinarith
  have hd : 0 < q * (1 + t) - 1 := by linarith
  have he : (q * (1 + t) / (q * (1 + t) - 1)) / q -
      (1 + t / 2) * (q * (1 + t) / (q * (1 + t) - 1) - 1) =
      t / (2 * (q * (1 + t) - 1)) := by
    field_simp
    ring
  dsimp only
  refine ⟨(lt_div_iff₀ hd).mpr (by linarith),
    (div_le_iff₀ hd).mpr (by linarith), ?_, ?_⟩
  · rw [he]
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * q) (by positivity)).mpr
    have hh : 2 * (q * (1 + t) - 1) ≤ 4 * q := by nlinarith
    exact mul_le_mul_of_nonneg_left hh ht.le
  · rw [he]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (q * (1 + t) - 1))).mpr
    linarith

lemma transformed_exponent {p t : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (ht : 0 < t) (ht1 : t ≤ 1) :
    let q := p / (p - 1)
    let r := q * (1 + t) / (q * (1 + t) - 1)
    2 ≤ q ∧ 1 < r ∧ r ≤ p ∧ r ≤ 2 := by
  let q := p / (p - 1)
  let r := q * (1 + t) / (q * (1 + t) - 1)
  have hq : 2 ≤ q := (le_div_iff₀ (by linarith : 0 < p - 1)).mpr (by linarith)
  have hqr := exponent_loss hq ht ht1
  refine ⟨hq, hqr.1, ?_, hqr.2.1⟩
  have hden : 0 < q * (1 + t) - 1 := by nlinarith
  apply (div_le_iff₀ hden).mpr
  have hqp : q * (p - 1) = p := by exact div_mul_cancel₀ p (by linarith : p - 1 ≠ 0)
  have hqt : q * t * (p - 1) = p * t := by nlinarith
  nlinarith

lemma quadratic_geometric_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ 2 * r ^ n) ((1 + r) / (1 - r) ^ 3) := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have h2 := hasSum_sq_mul_geometric_of_norm_lt_one hr
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one hr).mul_left 2
  have h0 := hasSum_geometric_of_lt_one hr0 hr1
  convert (h2.add h1).add h0 using 1
  · ext n
    ring
  · field_simp
    ring

lemma quadratic_geometric_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * r ^ n) ≤ 2 / (1 - r) ^ 3 := by
  rw [(quadratic_geometric_sum hr0 hr1).tsum_eq]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

lemma geometric_quadratic_work {p : unitInterval} (hp : (1 / 2 : ℝ) < p)
    (C : ℝ) (hC : 0 ≤ C) (work : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ work n)
    (hw : ∀ n, work n ≤ C * 2 ^ n * ((n : ℝ) + 1) ^ 2) :
    Integrable work (geometricMeasure p) ∧
      (∫ n, work n ∂geometricMeasure p) ≤ 2 * C * p / (2 * p - 1) ^ 3 := by
  have hp0 : p ≠ 0 := by
    intro he
    have hz : (p : ℝ) = 0 := congrArg Subtype.val he
    linarith
  have hr0 : 0 ≤ 2 * (1 - (p : ℝ)) := by nlinarith [p.2.2]
  have hr1 : 2 * (1 - (p : ℝ)) < 1 := by linarith
  let r : ℝ := 2 * (1 - (p : ℝ))
  have he (n : ℕ) : ((1 - p : ℝ) ^ n * p) *
      (C * 2 ^ n * ((n : ℝ) + 1) ^ 2) =
      C * p * (((n : ℝ) + 1) ^ 2 * r ^ n) := by
    dsimp [r]
    rw [mul_pow]
    ring
  have hmajor : Summable (fun n : ℕ => ((1 - p : ℝ) ^ n * p) *
      (C * 2 ^ n * ((n : ℝ) + 1) ^ 2)) := by
    simp_rw [he]
    exact (quadratic_geometric_sum hr0 hr1).summable.mul_left _
  have hbound (n : ℕ) : ((1 - p : ℝ) ^ n * p) * work n ≤
      ((1 - p : ℝ) ^ n * p) * (C * 2 ^ n * ((n : ℝ) + 1) ^ 2) :=
    mul_le_mul_of_nonneg_left (hw n) (geometricMeasure_nonneg p n)
  have hs : Summable (fun n => ((1 - p : ℝ) ^ n * p) * work n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (geometricMeasure_nonneg p n) (hw0 n))
      hbound hmajor
  have hi : Integrable work (geometricMeasure p) := by
    apply (integrable_geometricMeasure_iff hp0).mpr
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hw0 _)] using hs
  refine ⟨hi, ?_⟩
  rw [integral_geometricMeasure' hp0 hi]
  calc
    _ ≤ ∑' n : ℕ, ((1 - p : ℝ) ^ n * p) *
        (C * 2 ^ n * ((n : ℝ) + 1) ^ 2) := hs.tsum_le_tsum hbound hmajor
    _ = C * p * ((1 + r) / (1 - r) ^ 3) := by
      simp_rw [he]
      rw [tsum_mul_left, (quadratic_geometric_sum hr0 hr1).tsum_eq]
    _ ≤ C * p * (2 / (1 - r) ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC p.2.1)
      exact div_le_div_of_nonneg_right (by dsimp [r]; linarith) (by positivity)
    _ = _ := by
      have hd : 1 - r = 2 * (p : ℝ) - 1 := by dsimp [r]; ring
      rw [hd]
      ring

lemma dyadic_gap_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 4 ≤ 1 - (2 : ℝ) ^ (-x) := by
  have hl : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have he := Real.add_one_le_exp (Real.log 2 * x)
  rw [← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at he
  have hlog := mul_le_mul_of_nonneg_right hl hx
  have hu : (2 : ℝ) ^ x ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hx1
  have hp : 0 < (2 : ℝ) ^ x := by positivity
  have hm := mul_le_mul_of_nonneg_left hu hx
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  apply (mul_le_mul_iff_left₀ hp).mp
  rw [sub_mul, inv_mul_cancel₀ hp.ne']
  nlinarith only [he, hlog, hm]

lemma debiasing_decay_ratio (a r β : ℝ) :
    ((2 : ℝ) ^ (-a)) ^ (1 - r) * 2 ^ (-β) = 2 ^ (-(β - a * (r - 1))) := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

lemma exponent_loss_ratio {q t : ℝ} (hq : 2 ≤ q) (ht : 0 < t) (ht1 : t ≤ 1) :
    let r := q * (1 + t) / (q * (1 + t) - 1)
    0 ≤ ((2 : ℝ) ^ (-(1 + t / 2))) ^ (1 - r) * 2 ^ (-(r / q)) ∧
      ((2 : ℝ) ^ (-(1 + t / 2))) ^ (1 - r) * 2 ^ (-(r / q)) ≤ 1 - t / (16 * q) := by
  dsimp only
  let r := q * (1 + t) / (q * (1 + t) - 1)
  obtain ⟨_, _, hlo, hhi⟩ := exponent_loss hq ht ht1
  have hq0 : 0 < q := by linarith
  have hg0 : 0 ≤ r / q - (1 + t / 2) * (r - 1) :=
    le_trans (by positivity) hlo
  have hg1 : r / q - (1 + t / 2) * (r - 1) ≤ 1 := by linarith
  have hh := dyadic_gap_lower hg0 hg1
  rw [debiasing_decay_ratio]
  refine ⟨by positivity, ?_⟩
  change (2 : ℝ) ^ (-(r / q - (1 + t / 2) * (r - 1))) ≤ _
  have he : t / (4 * q) / 4 = t / (16 * q) := by ring
  rw [← he]
  linarith only [hh, hlo]

lemma linear_level_ratio {q t : ℝ} (hq : 2 ≤ q) (ht : 0 < t) (ht1 : t ≤ 1) :
    let r := q * (1 + t) / (q * (1 + t) - 1)
    (1 - (1 / 2 + t / 16)) ^ (1 - r) * (2 : ℝ) ^ (-(r / q)) ≤ 1 - t / (16 * q) := by
  let r := q * (1 + t) / (q * (1 + t) - 1)
  have hr := (exponent_loss hq ht ht1).1
  have hgap := dyadic_gap_lower (by positivity : 0 ≤ t / 2) (by linarith : t / 2 ≤ 1)
  have he : (2 : ℝ) ^ (-(1 + t / 2)) = (1 / 2) * 2 ^ (-(t / 2)) := by
    rw [show -(1 + t / 2) = -1 + -(t / 2) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hb : (2 : ℝ) ^ (-(1 + t / 2)) ≤ 1 - (1 / 2 + t / 16) := by
    rw [he]
    linarith only [hgap]
  have hp := Real.rpow_le_rpow_of_nonpos
    (by positivity : 0 < (2 : ℝ) ^ (-(1 + t / 2))) hb (by linarith : 1 - r ≤ 0)
  exact (mul_le_mul_of_nonneg_right hp (by positivity)).trans (exponent_loss_ratio hq ht ht1).2

lemma linear_level_prefactor {r t : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) (ht : 0 ≤ t) :
    (1 / 2 + t / 16 : ℝ) ^ (1 - r) ≤ 2 := by
  have hh := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 2)
    (show (1 / 2 : ℝ) ≤ 1 / 2 + t / 16 by linarith) (by linarith : 1 - r ≤ 0)
  have he := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (show (-1 : ℝ) ≤ 1 - r by linarith)
  norm_num at he
  exact hh.trans he

lemma linear_level_work {p : unitInterval} {t : ℝ} (ht : 0 < t)
    (hp : (p : ℝ) = 1 / 2 + t / 16)
    (C : ℝ) (hC : 0 ≤ C) (work : ℕ → ℝ) (hw0 : ∀ n, 0 ≤ work n)
    (hw : ∀ n, work n ≤ C * 2 ^ n * ((n : ℝ) + 1) ^ 2) :
    Integrable work (geometricMeasure p) ∧
      (∫ n, work n ∂geometricMeasure p) ≤ 1024 * C / t ^ 3 := by
  have hp' : (1 / 2 : ℝ) < p := by rw [hp]; linarith
  obtain ⟨hi, hb⟩ := geometric_quadratic_work hp' C hC work hw0 hw
  refine ⟨hi, hb.trans ?_⟩
  have hden : 0 < (2 * (p : ℝ) - 1) ^ 3 := pow_pos (by linarith) _
  calc
    _ ≤ 2 * C / (2 * p - 1) ^ 3 := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_of_le_one_right (by positivity) p.2.2
    _ = _ := by
      rw [hp]
      have he : 2 * (1 / 2 + t / 16) - 1 = t / 8 := by ring
      rw [he]
      field_simp
      ring

lemma shifted_quadratic_work (n : ℕ) :
    (2 : ℝ) ^ (n + 1) * ((n : ℝ) + 2) ^ 2 ≤
      8 * 2 ^ n * ((n : ℝ) + 1) ^ 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hh : ((n : ℝ) + 2) ^ 2 ≤ 4 * ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * (2 : ℝ) ^ n)
  rw [pow_succ]
  nlinarith only [hm]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma weighted_increment_integrable {p : unitInterval} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (d : ℕ → E) (hd : Summable (fun n => ‖d n‖)) :
    Integrable (fun n => ((1 - p : ℝ) ^ n * p)⁻¹ • d n) (geometricMeasure p) := by
  apply (integrable_geometricMeasure_iff hp0).mpr
  convert hd using 1
  ext n
  have hw := geometricMeasure_pos hp0 hp1 n
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw)]
  rw [← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]

lemma weighted_increment_mean {p : unitInterval} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (d : ℕ → E) (hd : Summable (fun n => ‖d n‖)) :
    (∫ n, ((1 - p : ℝ) ^ n * p)⁻¹ • d n ∂geometricMeasure p) = ∑' n, d n := by
  rw [integral_geometricMeasure' hp0 (weighted_increment_integrable hp0 hp1 d hd)]
  congr 1
  ext n
  rw [smul_smul, mul_inv_cancel₀ (geometricMeasure_pos hp0 hp1 n).ne', one_smul]

lemma debiased_mean {p : unitInterval} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (base : E) (d : ℕ → E) (hd : Summable (fun n => ‖d n‖)) :
    Integrable (fun n => base + ((1 - p : ℝ) ^ n * p)⁻¹ • d n) (geometricMeasure p) ∧
    (∫ n, base + ((1 - p : ℝ) ^ n * p)⁻¹ • d n ∂geometricMeasure p) = base + ∑' n, d n := by
  have hi := weighted_increment_integrable hp0 hp1 d hd
  refine ⟨(integrable_const base).add hi, ?_⟩
  rw [integral_add (integrable_const base) hi, integral_const,
    weighted_increment_mean hp0 hp1 d hd]
  simp

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma geometric_nonnegative_integral {p : unitInterval} (hp0 : p ≠ 0)
    (F : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (F n)) (hn : ∀ n ω, 0 ≤ F n ω)
    (hi : ∀ n, Integrable (F n) P)
    (hs : Summable (fun n => ((1 - p : ℝ) ^ n * p) * (∫ ω, F n ω ∂P))) :
    Integrable (Function.uncurry F) ((geometricMeasure p).prod P) ∧
      (∫ z, F z.1 z.2 ∂((geometricMeasure p).prod P)) =
        ∑' n, ((1 - p : ℝ) ^ n * p) * (∫ ω, F n ω ∂P) := by
  have hm' : Measurable (Function.uncurry F) := measurable_from_prod_countable_right hm
  have he : ∀ n, 0 ≤ ∫ ω, F n ω ∂P := fun n => integral_nonneg (hn n)
  have houter : Integrable (fun n => ∫ ω, F n ω ∂P) (geometricMeasure p) := by
    apply (integrable_geometricMeasure_iff hp0).mpr
    simpa only [Real.norm_eq_abs, abs_of_nonneg (he _)] using hs
  have hprod : Integrable (Function.uncurry F) ((geometricMeasure p).prod P) := by
    apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hi, ?_⟩
    simpa only [Function.uncurry_def, Real.norm_eq_abs, abs_of_nonneg (hn _ _)] using houter
  refine ⟨hprod, ?_⟩
  change (∫ z, Function.uncurry F z ∂((geometricMeasure p).prod P)) = _
  rw [integral_prod _ hprod]
  change (∫ n, (∫ ω, F n ω ∂P) ∂geometricMeasure p) = _
  rw [integral_geometricMeasure' hp0 houter]
  rfl

omit [CompleteSpace E] in
lemma random_increment_integrable {p : unitInterval} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (d : ℕ → Ω → E) (hm : ∀ n, Measurable (d n)) (hi : ∀ n, Integrable (d n) P)
    (hs : Summable (fun n => ∫ ω, ‖d n ω‖ ∂P)) :
    Integrable (fun z : ℕ × Ω => ((1 - p : ℝ) ^ z.1 * p)⁻¹ • d z.1 z.2)
      ((geometricMeasure p).prod P) := by
  have hm' : Measurable (fun z : ℕ × Ω => ((1 - p : ℝ) ^ z.1 * p)⁻¹ • d z.1 z.2) :=
    measurable_from_prod_countable_right (fun n => by
      exact (measurable_const : Measurable (fun _ : Ω => (((1 - p : ℝ) ^ n * p)⁻¹))).smul (hm n))
  apply (integrable_prod_iff hm'.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun n => by
    exact Integrable.smul (((1 - p : ℝ) ^ n * p)⁻¹) (hi n)), ?_⟩
  have he (n : ℕ) : (∫ ω, ‖((1 - p : ℝ) ^ n * p)⁻¹ • d n ω‖ ∂P) =
      ((1 - p : ℝ) ^ n * p)⁻¹ * (∫ ω, ‖d n ω‖ ∂P) := by
    simp only [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (geometricMeasure_pos hp0 hp1 n)), integral_const_mul]
  simp_rw [he]
  apply (integrable_geometricMeasure_iff hp0).mpr
  convert hs using 1
  ext n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (inv_nonneg.mpr (geometricMeasure_nonneg p n)) (integral_nonneg (fun ω => norm_nonneg _))),
    ← mul_assoc, mul_inv_cancel₀ (geometricMeasure_pos hp0 hp1 n).ne', one_mul]

lemma random_increment_mean {p : unitInterval} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (d : ℕ → Ω → E) (hm : ∀ n, Measurable (d n)) (hi : ∀ n, Integrable (d n) P)
    (hs : Summable (fun n => ∫ ω, ‖d n ω‖ ∂P)) :
    (∫ z : ℕ × Ω, ((1 - p : ℝ) ^ z.1 * p)⁻¹ • d z.1 z.2
      ∂((geometricMeasure p).prod P)) = ∑' n, ∫ ω, d n ω ∂P := by
  rw [integral_prod _ (random_increment_integrable hp0 hp1 d hm hi hs)]
  simp_rw [integral_smul]
  apply weighted_increment_mean hp0 hp1
  exact Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_integral_le_integral_norm _) hs

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma random_increment_moment {p : unitInterval} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (d : ℕ → Ω → E) (hm : ∀ n, Measurable (d n)) (r : ℝ)
    (hi : ∀ n, Integrable (fun ω => ‖d n ω‖ ^ r) P)
    (hs : Summable (fun n => ((1 - p : ℝ) ^ n * p) *
      (((1 - p : ℝ) ^ n * p)⁻¹) ^ r * (∫ ω, ‖d n ω‖ ^ r ∂P))) :
    Integrable (fun z : ℕ × Ω => ‖((1 - p : ℝ) ^ z.1 * p)⁻¹ • d z.1 z.2‖ ^ r)
      ((geometricMeasure p).prod P) ∧
    (∫ z : ℕ × Ω, ‖((1 - p : ℝ) ^ z.1 * p)⁻¹ • d z.1 z.2‖ ^ r
      ∂((geometricMeasure p).prod P)) =
      ∑' n, ((1 - p : ℝ) ^ n * p) * (((1 - p : ℝ) ^ n * p)⁻¹) ^ r *
        (∫ ω, ‖d n ω‖ ^ r ∂P) := by
  let F : ℕ → Ω → ℝ := fun n ω => ‖((1 - p : ℝ) ^ n * p)⁻¹ • d n ω‖ ^ r
  have he (n : ℕ) (ω : Ω) : F n ω =
      (((1 - p : ℝ) ^ n * p)⁻¹) ^ r * ‖d n ω‖ ^ r := by
    dsimp [F]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (geometricMeasure_pos hp0 hp1 n)),
      Real.mul_rpow (inv_nonneg.mpr (geometricMeasure_nonneg p n)) (norm_nonneg _)]
  have hFm (n : ℕ) : Measurable (F n) := by
    simp_rw [funext (he n)]
    exact measurable_const.mul ((hm n).norm.pow_const r)
  have hFi (n : ℕ) : Integrable (F n) P := by
    simp_rw [funext (he n)]
    exact (hi n).const_mul _
  have hFe (n : ℕ) : (∫ ω, F n ω ∂P) =
      (((1 - p : ℝ) ^ n * p)⁻¹) ^ r * (∫ ω, ‖d n ω‖ ^ r ∂P) := by
    simp_rw [he, integral_const_mul]
  have hsum : Summable (fun n => ((1 - p : ℝ) ^ n * p) * (∫ ω, F n ω ∂P)) := by
    simp_rw [hFe, ← mul_assoc]
    exact hs
  have hh := geometric_nonnegative_integral hp0 F hFm
    (fun n ω => Real.rpow_nonneg (norm_nonneg _) _) hFi hsum
  refine ⟨hh.1, hh.2.trans ?_⟩
  simp_rw [hFe, ← mul_assoc]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma geometric_weight_power {p : unitInterval} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (r b : ℝ) (n : ℕ) :
    ((1 - p : ℝ) ^ n * p) * (((1 - p : ℝ) ^ n * p)⁻¹) ^ r * b ^ n =
      (p : ℝ) ^ (1 - r) * (((1 - p : ℝ) ^ (1 - r)) * b) ^ n := by
  have hw := geometricMeasure_pos hp0 hp1 n
  have hp' : 0 < (p : ℝ) := by simpa using geometricMeasure_pos hp0 hp1 0
  have hbase : 0 ≤ 1 - (p : ℝ) := by linarith [p.2.2]
  have he : ((1 - p : ℝ) ^ n * p) * (((1 - p : ℝ) ^ n * p)⁻¹) ^ r =
      ((1 - p : ℝ) ^ n * p) ^ (1 - r) := by
    rw [Real.inv_rpow hw.le, Real.rpow_sub hw, Real.rpow_one, div_eq_mul_inv]
  rw [he, Real.mul_rpow (pow_nonneg hbase n) hp'.le,
    ← Real.rpow_pow_comm hbase (1 - r) n, mul_pow]
  ring

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma random_increment_geometric_moment {p : unitInterval} (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (d : ℕ → Ω → E) (hm : ∀ n, Measurable (d n)) (r : ℝ)
    (hi : ∀ n, Integrable (fun ω => ‖d n ω‖ ^ r) P)
    {D b : ℝ} (hb : 0 ≤ b)
    (hdecay : ∀ n, (∫ ω, ‖d n ω‖ ^ r ∂P) ≤ D * b ^ n)
    (hgap : (1 - p : ℝ) ^ (1 - r) * b < 1) :
    Integrable (fun z : ℕ × Ω => ‖((1 - p : ℝ) ^ z.1 * p)⁻¹ • d z.1 z.2‖ ^ r)
      ((geometricMeasure p).prod P) ∧
    (∫ z : ℕ × Ω, ‖((1 - p : ℝ) ^ z.1 * p)⁻¹ • d z.1 z.2‖ ^ r
      ∂((geometricMeasure p).prod P)) ≤
      (p : ℝ) ^ (1 - r) * D / (1 - (1 - p : ℝ) ^ (1 - r) * b) := by
  let R := (1 - p : ℝ) ^ (1 - r) * b
  let W := fun n : ℕ => ((1 - p : ℝ) ^ n * p) * (((1 - p : ℝ) ^ n * p)⁻¹) ^ r
  have hR : 0 ≤ R := mul_nonneg (Real.rpow_nonneg (by linarith [p.2.2]) _) hb
  have hW (n : ℕ) : 0 ≤ W n := by
    exact mul_nonneg (geometricMeasure_nonneg p n)
      (Real.rpow_nonneg (inv_nonneg.mpr (geometricMeasure_nonneg p n)) _)
  have he (n : ℕ) : W n * (D * b ^ n) = (p : ℝ) ^ (1 - r) * D * R ^ n := by
    dsimp [W, R]
    have hh := geometric_weight_power hp0 hp1 r b n
    linear_combination D * hh
  have hmajor : Summable (fun n => W n * (D * b ^ n)) := by
    simp_rw [he]
    exact (hasSum_geometric_of_lt_one hR hgap).summable.mul_left _
  have hminor : Summable (fun n => W n * (∫ ω, ‖d n ω‖ ^ r ∂P)) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hW n)
      (integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg _) _)))
      (fun n => mul_le_mul_of_nonneg_left (hdecay n) (hW n)) hmajor
  have hh := random_increment_moment hp0 hp1 d hm r hi hminor
  refine ⟨hh.1, hh.2.trans_le ?_⟩
  change (∑' n, W n * (∫ ω, ‖d n ω‖ ^ r ∂P)) ≤ _
  calc
    _ ≤ ∑' n, W n * (D * b ^ n) := hminor.tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_left (hdecay n) (hW n)) hmajor
    _ = _ := by
      simp_rw [he]
      rw [tsum_mul_left, (hasSum_geometric_of_lt_one hR hgap).tsum_eq]
      rfl

omit [NormedSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure P] in
lemma increment_geometric_moment (X : ℕ → Ω → E) (z : E)
    (hm : ∀ n, Measurable (X n)) {r D b : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2)
    (hD : 0 ≤ D) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hi : ∀ n, Integrable (fun ω => ‖X n ω - z‖ ^ r) P)
    (he : ∀ n, (∫ ω, ‖X n ω - z‖ ^ r ∂P) ≤ D * b ^ n) (n : ℕ) :
    Integrable (fun ω => ‖X (n + 1) ω - X n ω‖ ^ r) P ∧
      (∫ ω, ‖X (n + 1) ω - X n ω‖ ^ r ∂P) ≤ 4 * D * b ^ n := by
  have hpoint (ω : Ω) : ‖X (n + 1) ω - X n ω‖ ^ r ≤
      2 * (‖X (n + 1) ω - z‖ ^ r + ‖X n ω - z‖ ^ r) := by
    have hh := HilbertSmallMoments.addition_power_bound (X (n + 1) ω - z) (-(X n ω - z)) hr hr2
    rw [show X (n + 1) ω - z + -(X n ω - z) = X (n + 1) ω - X n ω by abel,
      norm_neg] at hh
    exact hh
  have hi' : Integrable (fun ω => ‖X (n + 1) ω - X n ω‖ ^ r) P := by
    apply (((hi (n + 1)).add (hi n)).const_mul 2).mono'
      (((hm (n + 1)).sub (hm n)).norm.pow_const r).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hpoint ω
  refine ⟨hi', ?_⟩
  have hh := integral_mono hi' (((hi (n + 1)).add (hi n)).const_mul 2) hpoint
  change (∫ ω, ‖X (n + 1) ω - X n ω‖ ^ r ∂P) ≤
    (∫ ω, 2 * (‖X (n + 1) ω - z‖ ^ r + ‖X n ω - z‖ ^ r) ∂P) at hh
  rw [integral_const_mul, integral_add (hi (n + 1)) (hi n)] at hh
  have hpow : D * b ^ (n + 1) ≤ D * b ^ n := by
    rw [pow_succ]
    nlinarith [mul_nonneg hD (pow_nonneg hb n)]
  linarith [he (n + 1), he n]


omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma approximation_telescope (X : ℕ → Ω → E) (z : E)
    (hi : ∀ n, Integrable (X n) P) {D b : ℝ} (hD : 0 ≤ D) (hb : 0 ≤ b) (hb1 : b < 1)
    (he : ∀ n, (∫ ω, ‖X n ω - z‖ ∂P) ≤ D * b ^ n) :
    Summable (fun n => ∫ ω, ‖X (n + 1) ω - X n ω‖ ∂P) ∧
      HasSum (fun n => ∫ ω, X (n + 1) ω - X n ω ∂P) (z - ∫ ω, X 0 ω ∂P) := by
  have hni (n : ℕ) : Integrable (fun ω => ‖X n ω - z‖) P :=
    ((hi n).sub (integrable_const z)).norm
  have hpoint (n : ℕ) (ω : Ω) : ‖X (n + 1) ω - X n ω‖ ≤
      ‖X (n + 1) ω - z‖ + ‖X n ω - z‖ := by
    simpa only [norm_sub_rev (z) (X n ω)] using
      norm_sub_le_norm_sub_add_norm_sub (X (n + 1) ω) z (X n ω)
  have hd (n : ℕ) : (∫ ω, ‖X (n + 1) ω - X n ω‖ ∂P) ≤ 2 * D * b ^ n := by
    have hh := integral_mono ((hi (n + 1)).sub (hi n)).norm
      (((hi (n + 1)).sub (integrable_const z)).norm.add
        ((hi n).sub (integrable_const z)).norm) (hpoint n)
    change (∫ ω, ‖X (n + 1) ω - X n ω‖ ∂P) ≤
      (∫ ω, ‖X (n + 1) ω - z‖ + ‖X n ω - z‖ ∂P) at hh
    rw [integral_add (hni (n + 1)) (hni n)] at hh
    have hpow : D * b ^ (n + 1) ≤ D * b ^ n := by
      rw [pow_succ]
      nlinarith [mul_nonneg hD (pow_nonneg hb n)]
    linarith [he n, he (n + 1)]
  have hs : Summable (fun n => ∫ ω, ‖X (n + 1) ω - X n ω‖ ∂P) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun ω => norm_nonneg _)) hd
      ((hasSum_geometric_of_lt_one hb hb1).summable.mul_left (2 * D))
  refine ⟨hs, ?_⟩
  have hsn : Summable (fun n => ‖∫ ω, X (n + 1) ω - X n ω ∂P‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_integral_le_integral_norm _) hs
  apply (hasSum_iff_tendsto_nat_of_summable_norm hsn).mpr
  have hlim : Filter.Tendsto (fun n => ∫ ω, X n ω ∂P) Filter.atTop (nhds z) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _) ?_
      (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hb hb1).const_mul D)
    intro n
    have hh := norm_integral_le_integral_norm (μ := P) (fun ω => X n ω - z)
    rw [integral_sub (hi n) (integrable_const z), integral_const] at hh
    simpa using hh.trans (he n)
  have heq (n : ℕ) : (∫ ω, X (n + 1) ω - X n ω ∂P) =
      (∫ ω, X (n + 1) ω ∂P) - ∫ ω, X n ω ∂P := integral_sub (hi (n + 1)) (hi n)
  simp_rw [heq]
  convert hlim.sub_const (∫ ω, X 0 ω ∂P) using 1
  funext n
  exact Finset.sum_range_sub (fun j => ∫ ω, X j ω ∂P) n

lemma random_debiased_mean {v : unitInterval} (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (X : ℕ → Ω → E) (z : E) (hm : ∀ n, Measurable (X n))
    (hi : ∀ n, Integrable (X n) P) {D b : ℝ} (hD : 0 ≤ D) (hb : 0 ≤ b) (hb1 : b < 1)
    (he : ∀ n, (∫ ω, ‖X n ω - z‖ ∂P) ≤ D * b ^ n) :
    Integrable (fun w : ℕ × Ω => X 0 w.2 +
      ((1 - v : ℝ) ^ w.1 * v)⁻¹ • (X (w.1 + 1) w.2 - X w.1 w.2))
      ((geometricMeasure v).prod P) ∧
    (∫ w : ℕ × Ω, X 0 w.2 +
      ((1 - v : ℝ) ^ w.1 * v)⁻¹ • (X (w.1 + 1) w.2 - X w.1 w.2)
      ∂((geometricMeasure v).prod P)) = z := by
  have ht := approximation_telescope X z hi hD hb hb1 he
  let d := fun n ω => X (n + 1) ω - X n ω
  have hdm (n : ℕ) : Measurable (d n) := (hm (n + 1)).sub (hm n)
  have hdi (n : ℕ) : Integrable (d n) P := (hi (n + 1)).sub (hi n)
  have hbase : Integrable (fun w : ℕ × Ω => X 0 w.2) ((geometricMeasure v).prod P) :=
    (measurePreserving_snd (μ := geometricMeasure v) (ν := P)).integrable_comp_of_integrable (hi 0)
  have hinc := random_increment_integrable hv0 hv1 d hdm hdi ht.1
  refine ⟨hbase.add hinc, ?_⟩
  rw [integral_add hbase hinc, integral_fun_snd,
    random_increment_mean hv0 hv1 d hdm hdi ht.1, ht.2.tsum_eq]
  simp


omit [CompleteSpace E] in
lemma random_debiased_moment {v : unitInterval} (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (X : ℕ → Ω → E) (z : E) (hm : ∀ n, Measurable (X n))
    {r D b : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) (hD : 0 ≤ D) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hi : ∀ n, Integrable (fun ω => ‖X n ω - z‖ ^ r) P)
    (he : ∀ n, (∫ ω, ‖X n ω - z‖ ^ r ∂P) ≤ D * b ^ n)
    (hgap : (1 - v : ℝ) ^ (1 - r) * b < 1) :
    Integrable (fun w : ℕ × Ω => ‖X 0 w.2 +
      ((1 - v : ℝ) ^ w.1 * v)⁻¹ • (X (w.1 + 1) w.2 - X w.1 w.2) - z‖ ^ r)
      ((geometricMeasure v).prod P) ∧
    (∫ w : ℕ × Ω, ‖X 0 w.2 +
      ((1 - v : ℝ) ^ w.1 * v)⁻¹ • (X (w.1 + 1) w.2 - X w.1 w.2) - z‖ ^ r
      ∂((geometricMeasure v).prod P)) ≤
      2 * D + 8 * (v : ℝ) ^ (1 - r) * D / (1 - (1 - v : ℝ) ^ (1 - r) * b) := by
  let d := fun n ω => X (n + 1) ω - X n ω
  have hdm (n : ℕ) : Measurable (d n) := (hm (n + 1)).sub (hm n)
  have hd := increment_geometric_moment X z hm hr hr2 hD hb hb1 hi he
  obtain ⟨hIi, hIb⟩ := random_increment_geometric_moment hv0 hv1 d hdm r
    (fun n => (hd n).1) hb (fun n => (hd n).2) hgap
  let A := fun w : ℕ × Ω => X 0 w.2 - z
  let B := fun w : ℕ × Ω => ((1 - v : ℝ) ^ w.1 * v)⁻¹ • d w.1 w.2
  have hA : Measurable A := ((hm 0).comp measurable_snd).sub_const z
  have hB : Measurable B := measurable_from_prod_countable_right fun n =>
    (measurable_const : Measurable (fun _ : Ω => ((1 - v : ℝ) ^ n * v)⁻¹)).smul (hdm n)
  have hAi : Integrable (fun w => ‖A w‖ ^ r) ((geometricMeasure v).prod P) :=
    (measurePreserving_snd (μ := geometricMeasure v) (ν := P)).integrable_comp_of_integrable (hi 0)
  have hsum : Integrable (fun w => ‖A w + B w‖ ^ r) ((geometricMeasure v).prod P) := by
    apply ((hAi.add hIi).const_mul 2).mono' ((hA.add hB).norm.pow_const r).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact HilbertSmallMoments.addition_power_bound (A w) (B w) hr hr2
  have heq (w : ℕ × Ω) : X 0 w.2 +
      ((1 - v : ℝ) ^ w.1 * v)⁻¹ • (X (w.1 + 1) w.2 - X w.1 w.2) - z = A w + B w := by
    dsimp [A, B, d]
    abel
  simp_rw [heq]
  refine ⟨hsum, ?_⟩
  have hpoint (w : ℕ × Ω) := HilbertSmallMoments.addition_power_bound (A w) (B w) hr hr2
  have hh := integral_mono hsum ((hAi.add hIi).const_mul 2) hpoint
  change (∫ w, ‖A w + B w‖ ^ r ∂((geometricMeasure v).prod P)) ≤
    (∫ w, 2 * (‖A w‖ ^ r + ‖B w‖ ^ r) ∂((geometricMeasure v).prod P)) at hh
  rw [integral_const_mul, integral_add hAi hIi] at hh
  have hAb : (∫ w, ‖A w‖ ^ r ∂((geometricMeasure v).prod P)) ≤ D := by
    dsimp only [A]
    rw [integral_fun_snd (fun ω => ‖X 0 ω - z‖ ^ r)]
    simpa using he 0
  calc
    _ ≤ 2 * (D + (v : ℝ) ^ (1 - r) * (4 * D) /
      (1 - (1 - v : ℝ) ^ (1 - r) * b)) := hh.trans (by linarith)
    _ = _ := by ring


omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] [IsProbabilityMeasure P] in
lemma linear_debiased_bound {q t D : ℝ} (hq : 2 ≤ q) (ht : 0 < t) (ht1 : t ≤ 1)
    (hD : 0 ≤ D) :
    let r := q * (1 + t) / (q * (1 + t) - 1)
    let v := 1 / 2 + t / 16
    let b := (2 : ℝ) ^ (-(r / q))
    2 * D + 8 * v ^ (1 - r) * D / (1 - (1 - v) ^ (1 - r) * b) ≤ 512 * q * D / t := by
  dsimp only
  let r := q * (1 + t) / (q * (1 + t) - 1)
  let v := 1 / 2 + t / 16
  let b := (2 : ℝ) ^ (-(r / q))
  have hq0 : 0 < q := by linarith
  have hr := exponent_loss hq ht ht1
  have hfac : v ^ (1 - r) ≤ 2 := linear_level_prefactor hr.1.le hr.2.1 ht.le
  have hgap : (1 - v) ^ (1 - r) * b ≤ 1 - t / (16 * q) := linear_level_ratio hq ht ht1
  have hd : 0 < 1 - (1 - v) ^ (1 - r) * b := by
    have : 0 < t / (16 * q) := by positivity
    linarith
  have hbnd : 8 * v ^ (1 - r) * D / (1 - (1 - v) ^ (1 - r) * b) ≤ 256 * q * D / t := by
    calc
      _ ≤ 16 * D / (1 - (1 - v) ^ (1 - r) * b) := by
        apply div_le_div_of_nonneg_right _ hd.le
        nlinarith
      _ ≤ 16 * D / (t / (16 * q)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = _ := by field_simp; ring
  change 2 * D + 8 * v ^ (1 - r) * D / (1 - (1 - v) ^ (1 - r) * b) ≤ _
  have hrem : 2 * D ≤ 256 * q * D / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith [mul_nonneg hD (show 0 ≤ 256 * q - 2 by linarith)]
  calc
    _ ≤ 256 * q * D / t + 256 * q * D / t := add_le_add hrem hbnd
    _ = _ := by ring


omit [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma approximation_lower_moment {X : Ω → E} (hX : Measurable X) {p r S m : ℝ}
    (hp : 1 < p) (hr : 0 ≤ r) (hrp : r ≤ p) (hS : 0 ≤ S) (hm : 0 < m)
    (hi : Integrable (fun ω => ‖X ω‖ ^ p) P) (ell : ℕ)
    (he : (∫ ω, ‖X ω‖ ^ p ∂P) ≤ (2 : ℝ) ^ (18 : ℝ) * S ^ p *
      (m * (2 : ℝ) ^ ell) ^ (-(p - 1))) :
    let q := p / (p - 1)
    Integrable (fun ω => ‖X ω‖ ^ r) P ∧
      (∫ ω, ‖X ω‖ ^ r ∂P) ≤
        ((2 : ℝ) ^ (18 : ℝ) * S ^ r * m ^ (-(r / q))) *
          ((2 : ℝ) ^ (-(r / q))) ^ ell := by
  have hp0 : 0 < p := by linarith
  have hlow := StochasticEnvelopeSampling.lower_power_moment hX hp0 hr hrp hi
  refine ⟨hlow.1, hlow.2.trans ?_⟩
  have he' := Real.rpow_le_rpow
    (integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg _) _)) he (div_nonneg hr hp0.le)
  refine he'.trans ?_
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (Real.rpow_nonneg hS _),
    ← Real.rpow_mul hS, ← Real.rpow_mul (show 0 ≤ m * (2 : ℝ) ^ ell by positivity)]
  have hp_cancel : p * (r / p) = r := by field_simp
  have hexp : -(p - 1) * (r / p) = -(r / (p / (p - 1))) := by field_simp
  rw [hp_cancel, hexp, Real.mul_rpow hm.le (by positivity), ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
  have hC : ((2 : ℝ) ^ (18 : ℝ)) ^ (r / p) ≤ (2 : ℝ) ^ (18 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ (2 : ℝ) ^ (18 : ℝ))
      ((div_le_one hp0).mpr hrp)
  calc
    _ ≤ (2 : ℝ) ^ (18 : ℝ) * S ^ r *
        (m ^ (-(r / (p / (p - 1)))) * ((2 : ℝ) ^ (-(r / (p / (p - 1))))) ^ ell) := by gcongr
    _ = _ := by ring


omit [CompleteSpace E] in
lemma base_increment_moment {v : unitInterval} (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (base : Ω → E) (d : ℕ → Ω → E) (z : E) (hm : Measurable base)
    (hdm : ∀ n, Measurable (d n)) {r D₀ D₁ b : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2)
    (hb : 0 ≤ b) (hi : Integrable (fun ω => ‖base ω - z‖ ^ r) P)
    (hdi : ∀ n, Integrable (fun ω => ‖d n ω‖ ^ r) P)
    (he : (∫ ω, ‖base ω - z‖ ^ r ∂P) ≤ D₀)
    (hde : ∀ n, (∫ ω, ‖d n ω‖ ^ r ∂P) ≤ D₁ * b ^ n)
    (hgap : (1 - v : ℝ) ^ (1 - r) * b < 1) :
    Integrable (fun w : ℕ × Ω => ‖base w.2 + ((1 - v : ℝ) ^ w.1 * v)⁻¹ • d w.1 w.2 - z‖ ^ r)
      ((geometricMeasure v).prod P) ∧
    (∫ w : ℕ × Ω, ‖base w.2 + ((1 - v : ℝ) ^ w.1 * v)⁻¹ • d w.1 w.2 - z‖ ^ r
      ∂((geometricMeasure v).prod P)) ≤
      2 * D₀ + 2 * (v : ℝ) ^ (1 - r) * D₁ / (1 - (1 - v : ℝ) ^ (1 - r) * b) := by
  obtain ⟨hIi, hIb⟩ := random_increment_geometric_moment hv0 hv1 d hdm r hdi hb hde hgap
  let A := fun w : ℕ × Ω => base w.2 - z
  let B := fun w : ℕ × Ω => ((1 - v : ℝ) ^ w.1 * v)⁻¹ • d w.1 w.2
  have hA : Measurable A := (hm.comp measurable_snd).sub_const z
  have hB : Measurable B := measurable_from_prod_countable_right fun n =>
    (measurable_const : Measurable (fun _ : Ω => ((1 - v : ℝ) ^ n * v)⁻¹)).smul (hdm n)
  have hAi : Integrable (fun w => ‖A w‖ ^ r) ((geometricMeasure v).prod P) :=
    (measurePreserving_snd (μ := geometricMeasure v) (ν := P)).integrable_comp_of_integrable hi
  have hsum : Integrable (fun w => ‖A w + B w‖ ^ r) ((geometricMeasure v).prod P) := by
    apply ((hAi.add hIi).const_mul 2).mono' ((hA.add hB).norm.pow_const r).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact HilbertSmallMoments.addition_power_bound (A w) (B w) hr hr2
  have heq (w : ℕ × Ω) : base w.2 + ((1 - v : ℝ) ^ w.1 * v)⁻¹ • d w.1 w.2 - z = A w + B w := by
    dsimp [A, B]
    abel
  simp_rw [heq]
  refine ⟨hsum, ?_⟩
  have hpoint (w : ℕ × Ω) := HilbertSmallMoments.addition_power_bound (A w) (B w) hr hr2
  have hh := integral_mono hsum ((hAi.add hIi).const_mul 2) hpoint
  change (∫ w, ‖A w + B w‖ ^ r ∂((geometricMeasure v).prod P)) ≤
    (∫ w, 2 * (‖A w‖ ^ r + ‖B w‖ ^ r) ∂((geometricMeasure v).prod P)) at hh
  rw [integral_const_mul, integral_add hAi hIi] at hh
  have hAb : (∫ w, ‖A w‖ ^ r ∂((geometricMeasure v).prod P)) ≤ D₀ := by
    dsimp only [A]
    rw [integral_fun_snd (fun ω => ‖base ω - z‖ ^ r)]
    simpa using he
  calc
    _ ≤ 2 * (D₀ + (v : ℝ) ^ (1 - r) * D₁ /
      (1 - (1 - v : ℝ) ^ (1 - r) * b)) := hh.trans (by linarith)
    _ = _ := by ring


lemma base_increment_mean {v : unitInterval} (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (base : Ω → E) (d : ℕ → Ω → E) (z : E) (hdm : ∀ n, Measurable (d n))
    (hi : Integrable base P) (hdi : ∀ n, Integrable (d n) P)
    (hs : Summable (fun n => ∫ ω, ‖d n ω‖ ∂P))
    (ht : HasSum (fun n => ∫ ω, d n ω ∂P) (z - ∫ ω, base ω ∂P)) :
    Integrable (fun w : ℕ × Ω => base w.2 + ((1 - v : ℝ) ^ w.1 * v)⁻¹ • d w.1 w.2)
      ((geometricMeasure v).prod P) ∧
    (∫ w : ℕ × Ω, base w.2 + ((1 - v : ℝ) ^ w.1 * v)⁻¹ • d w.1 w.2
      ∂((geometricMeasure v).prod P)) = z := by
  have hbase : Integrable (fun w : ℕ × Ω => base w.2) ((geometricMeasure v).prod P) :=
    (measurePreserving_snd (μ := geometricMeasure v) (ν := P)).integrable_comp_of_integrable hi
  have hinc := random_increment_integrable hv0 hv1 d hdm hdi hs
  refine ⟨hbase.add hinc, ?_⟩
  rw [integral_add hbase hinc, integral_fun_snd,
    random_increment_mean hv0 hv1 d hdm hdi hs, ht.tsum_eq]
  simp


omit [CompleteSpace E] in
lemma three_copy_moment {v : unitInterval} (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (X : ℕ → Ω → E) (z : E) (hm : ∀ n, Measurable (X n))
    {r D b : ℝ} (hr : 1 ≤ r) (hr2 : r ≤ 2) (hD : 0 ≤ D) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hi : ∀ n, Integrable (fun ω => ‖X n ω - z‖ ^ r) P)
    (he : ∀ n, (∫ ω, ‖X n ω - z‖ ^ r ∂P) ≤ D * b ^ n)
    (hgap : (1 - v : ℝ) ^ (1 - r) * b < 1) :
    let Q := (geometricMeasure v).prod (P.prod (P.prod P))
    let Z := fun w : ℕ × (Ω × Ω × Ω) => X 0 w.2.1 +
      ((1 - v : ℝ) ^ w.1 * v)⁻¹ • (X (w.1 + 1) w.2.2.1 - X w.1 w.2.2.2)
    Integrable (fun w => ‖Z w - z‖ ^ r) Q ∧
      (∫ w, ‖Z w - z‖ ^ r ∂Q) ≤
        2 * D + 8 * (v : ℝ) ^ (1 - r) * D / (1 - (1 - v : ℝ) ^ (1 - r) * b) := by
  let R := P.prod (P.prod P)
  let base := fun w : Ω × Ω × Ω => X 0 w.1
  let d := fun n (w : Ω × Ω × Ω) => X (n + 1) w.2.1 - X n w.2.2
  have h0 : MeasurePreserving (fun w : Ω × Ω × Ω => w.1) R P := measurePreserving_fst
  have h1 : MeasurePreserving (fun w : Ω × Ω × Ω => w.2.1) R P :=
    (measurePreserving_fst (μ := P) (ν := P)).comp measurePreserving_snd
  have h2 : MeasurePreserving (fun w : Ω × Ω × Ω => w.2.2) R P :=
    (measurePreserving_snd (μ := P) (ν := P)).comp measurePreserving_snd
  have hbmeas : Measurable base := (hm 0).comp measurable_fst
  have hdmeas (n : ℕ) : Measurable (d n) :=
    ((hm (n + 1)).comp (measurable_fst.comp measurable_snd)).sub
      ((hm n).comp (measurable_snd.comp measurable_snd))
  have hi0 : Integrable (fun w => ‖base w - z‖ ^ r) R := h0.integrable_comp_of_integrable (hi 0)
  have he0 : (∫ w, ‖base w - z‖ ^ r ∂R) ≤ D := by
    have hh := (show HasLaw (fun w : Ω × Ω × Ω => w.1) P R from
      ⟨h0.measurable.aemeasurable, h0.map_eq⟩).integral_comp (hi 0).aestronglyMeasurable
    change (∫ w, ‖X 0 w.1 - z‖ ^ r ∂R) ≤ D
    simp only [Function.comp_apply] at hh
    rw [hh]
    simpa using he 0
  have hd (n : ℕ) : Integrable (fun w => ‖d n w‖ ^ r) R ∧
      (∫ w, ‖d n w‖ ^ r ∂R) ≤ (4 * D) * b ^ n := by
    have hh := StochasticEnvelopeSampling.difference_moment
      ((hm (n + 1)).comp (measurable_fst.comp measurable_snd))
      ((hm n).comp (measurable_snd.comp measurable_snd)) z hr hr2
      (h1.integrable_comp_of_integrable (hi (n + 1)))
      (h2.integrable_comp_of_integrable (hi n))
    refine ⟨hh.1, hh.2.trans ?_⟩
    have he1 := (show HasLaw (fun w : Ω × Ω × Ω => w.2.1) P R from
      ⟨h1.measurable.aemeasurable, h1.map_eq⟩).integral_comp (hi (n + 1)).aestronglyMeasurable
    have he2 := (show HasLaw (fun w : Ω × Ω × Ω => w.2.2) P R from
      ⟨h2.measurable.aemeasurable, h2.map_eq⟩).integral_comp (hi n).aestronglyMeasurable
    change 2 * ((∫ w, ‖X (n + 1) w.2.1 - z‖ ^ r ∂R) +
      (∫ w, ‖X n w.2.2 - z‖ ^ r ∂R)) ≤ _
    simp only [Function.comp_apply] at he1 he2
    rw [he1, he2]
    have hdec : D * b ^ (n + 1) ≤ D * b ^ n := by
      rw [pow_succ]
      nlinarith [mul_nonneg hD (pow_nonneg hb n)]
    linarith [he (n + 1), he n]
  have hh := base_increment_moment hv0 hv1 base d z hbmeas hdmeas hr hr2 hb hi0
    (fun n => (hd n).1) he0 (fun n => (hd n).2) hgap
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  ring


lemma three_copy_mean {v : unitInterval} (hv0 : v ≠ 0) (hv1 : v ≠ 1)
    (X : ℕ → Ω → E) (z : E) (hm : ∀ n, Measurable (X n))
    (hi : ∀ n, Integrable (X n) P) {D b : ℝ} (hD : 0 ≤ D) (hb : 0 ≤ b) (hb1 : b < 1)
    (he : ∀ n, (∫ ω, ‖X n ω - z‖ ∂P) ≤ D * b ^ n) :
    let Q := (geometricMeasure v).prod (P.prod (P.prod P))
    let Z := fun w : ℕ × (Ω × Ω × Ω) => X 0 w.2.1 +
      ((1 - v : ℝ) ^ w.1 * v)⁻¹ • (X (w.1 + 1) w.2.2.1 - X w.1 w.2.2.2)
    Integrable Z Q ∧ (∫ w, Z w ∂Q) = z := by
  let R := P.prod (P.prod P)
  let base := fun w : Ω × Ω × Ω => X 0 w.1
  let d := fun n (w : Ω × Ω × Ω) => X (n + 1) w.2.1 - X n w.2.2
  have h0 : MeasurePreserving (fun w : Ω × Ω × Ω => w.1) R P := measurePreserving_fst
  have h1 : MeasurePreserving (fun w : Ω × Ω × Ω => w.2.1) R P :=
    (measurePreserving_fst (μ := P) (ν := P)).comp measurePreserving_snd
  have h2 : MeasurePreserving (fun w : Ω × Ω × Ω => w.2.2) R P :=
    (measurePreserving_snd (μ := P) (ν := P)).comp measurePreserving_snd
  have hi0 : Integrable base R := h0.integrable_comp_of_integrable (hi 0)
  have hdi (n : ℕ) : Integrable (d n) R :=
    (h1.integrable_comp_of_integrable (hi (n + 1))).sub (h2.integrable_comp_of_integrable (hi n))
  have hdm (n : ℕ) : Measurable (d n) :=
    ((hm (n + 1)).comp (measurable_fst.comp measurable_snd)).sub
      ((hm n).comp (measurable_snd.comp measurable_snd))
  have hni (n : ℕ) : Integrable (fun ω => ‖X n ω - z‖) P := ((hi n).sub (integrable_const z)).norm
  have hd (n : ℕ) : (∫ w, ‖d n w‖ ∂R) ≤ 4 * D * b ^ n := by
    have hi1n : Integrable (fun w : Ω × Ω × Ω => ‖X (n + 1) w.2.1 - z‖) R :=
      h1.integrable_comp_of_integrable (hni (n + 1))
    have hi2n : Integrable (fun w : Ω × Ω × Ω => ‖X n w.2.2 - z‖) R :=
      h2.integrable_comp_of_integrable (hni n)
    have hh := StochasticEnvelopeSampling.difference_moment
      ((hm (n + 1)).comp (measurable_fst.comp measurable_snd))
      ((hm n).comp (measurable_snd.comp measurable_snd)) z (le_refl (1 : ℝ)) (by norm_num : (1 : ℝ) ≤ 2)
      (by simpa only [Real.rpow_one, Function.comp_apply] using hi1n)
      (by simpa only [Real.rpow_one, Function.comp_apply] using hi2n)
    have he1 := (show HasLaw (fun w : Ω × Ω × Ω => w.2.1) P R from
      ⟨h1.measurable.aemeasurable, h1.map_eq⟩).integral_comp (hni (n + 1)).aestronglyMeasurable
    have he2 := (show HasLaw (fun w : Ω × Ω × Ω => w.2.2) P R from
      ⟨h2.measurable.aemeasurable, h2.map_eq⟩).integral_comp (hni n).aestronglyMeasurable
    have hbound := hh.2
    simp only [Real.rpow_one, Function.comp_apply] at hbound
    simp only [Function.comp_apply] at he1 he2
    rw [he1, he2] at hbound
    have hdec : D * b ^ (n + 1) ≤ D * b ^ n := by
      rw [pow_succ]
      nlinarith [mul_nonneg hD (pow_nonneg hb n)]
    change (∫ w, ‖d n w‖ ∂R) ≤ _ at hbound
    linarith [he (n + 1), he n]
  have hs : Summable (fun n => ∫ w, ‖d n w‖ ∂R) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun w => norm_nonneg _)) hd
      ((hasSum_geometric_of_lt_one hb hb1).summable.mul_left (4 * D))
  have he0 : (∫ w, base w ∂R) = ∫ ω, X 0 ω ∂P :=
    (show HasLaw (fun w : Ω × Ω × Ω => w.1) P R from
      ⟨h0.measurable.aemeasurable, h0.map_eq⟩).integral_comp (hi 0).aestronglyMeasurable
  have hed (n : ℕ) : (∫ w, d n w ∂R) = ∫ ω, X (n + 1) ω - X n ω ∂P := by
    have he1 := (show HasLaw (fun w : Ω × Ω × Ω => w.2.1) P R from
      ⟨h1.measurable.aemeasurable, h1.map_eq⟩).integral_comp (hi (n + 1)).aestronglyMeasurable
    have he2 := (show HasLaw (fun w : Ω × Ω × Ω => w.2.2) P R from
      ⟨h2.measurable.aemeasurable, h2.map_eq⟩).integral_comp (hi n).aestronglyMeasurable
    change (∫ w, X (n + 1) w.2.1 - X n w.2.2 ∂R) = _
    have hi1 : Integrable (fun w : Ω × Ω × Ω => X (n + 1) w.2.1) R :=
      h1.integrable_comp_of_integrable (hi (n + 1))
    have hi2 : Integrable (fun w : Ω × Ω × Ω => X n w.2.2) R :=
      h2.integrable_comp_of_integrable (hi n)
    simp only [Function.comp_apply] at he1 he2
    rw [integral_sub hi1 hi2, he1, he2, integral_sub (hi (n + 1)) (hi n)]
  have ht : HasSum (fun n => ∫ w, d n w ∂R) (z - ∫ w, base w ∂R) := by
    simp_rw [hed, he0]
    exact (approximation_telescope X z hi hD hb hb1 he).2
  exact base_increment_mean hv0 hv1 base d z hdm hi0 hdi hs ht


open LongTails.Algorithms.StochasticEnvelopeProgram in
lemma dyadic_debiased_contract (X : ℕ → Ω → E) (z : E) (hm : ∀ n, Measurable (X n))
    {p t S m : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (ht : 0 < t) (ht1 : t ≤ 1)
    (hS : 0 ≤ S) (hm0 : 0 < m)
    (hi : ∀ n, Integrable (fun ω => ‖X n ω - z‖ ^ p) P)
    (he : ∀ n, (∫ ω, ‖X n ω - z‖ ^ p ∂P) ≤ (2 : ℝ) ^ (18 : ℝ) * S ^ p *
      (m * (2 : ℝ) ^ n) ^ (-(p - 1))) :
    let q := p / (p - 1)
    let r := q * (1 + t) / (q * (1 + t) - 1)
    let v := levelProbability t ht.le ht1
    let Q := (geometricMeasure v).prod (P.prod (P.prod P))
    let Z := fun w : ℕ × (Ω × Ω × Ω) => debiasedValue v w.1
      (X 0 w.2.1) (X (w.1 + 1) w.2.2.1) (X w.1 w.2.2.2)
    Measurable Z ∧ Integrable Z Q ∧ (∫ w, Z w ∂Q) = z ∧
      Integrable (fun w => ‖Z w - z‖ ^ r) Q ∧
      (∫ w, ‖Z w - z‖ ^ r ∂Q) ≤
        (2 : ℝ) ^ (27 : ℝ) * q / t * S ^ r * m ^ (-(r / q)) := by
  let q := p / (p - 1)
  let r := q * (1 + t) / (q * (1 + t) - 1)
  let v := levelProbability t ht.le ht1
  obtain ⟨hq, hr, hrp, hr2⟩ := transformed_exponent hp hp2 ht ht1
  have hq0 : 0 < q := by change 2 ≤ q at hq; linarith
  have hv0 : v ≠ 0 := by
    intro hh
    have hv := congrArg Subtype.val hh
    change 1 / 2 + t / 16 = 0 at hv
    linarith
  have hv1 : v ≠ 1 := by
    intro hh
    have hv := congrArg Subtype.val hh
    change 1 / 2 + t / 16 = 1 at hv
    linarith
  have hlow1 (n : ℕ) := approximation_lower_moment ((hm n).sub_const z) hp
    (by norm_num : (0 : ℝ) ≤ 1) hp.le hS hm0 (hi n) n (he n)
  have hiX (n : ℕ) : Integrable (X n) P := by
    have hn : Integrable (fun ω => ‖X n ω - z‖) P := by simpa only [Real.rpow_one] using (hlow1 n).1
    have hv := (integrable_norm_iff ((hm n).sub_const z).aestronglyMeasurable).mp hn
    have hh : Integrable (fun ω => (X n ω - z) + z) P := hv.add (integrable_const z)
    simpa only [sub_add_cancel] using hh
  have hb1 : (2 : ℝ) ^ (-(1 / q)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos (div_pos zero_lt_one hq0))
  have hmean := three_copy_mean hv0 hv1 X z hm hiX
    (show 0 ≤ (2 : ℝ) ^ (18 : ℝ) * S * m ^ (-(1 / q)) by positivity)
    (show 0 ≤ (2 : ℝ) ^ (-(1 / q)) by positivity) hb1
    (fun n => by simpa only [Real.rpow_one] using (hlow1 n).2)
  have hlowr (n : ℕ) := approximation_lower_moment ((hm n).sub_const z) hp (le_trans zero_le_one hr.le) hrp hS hm0 (hi n) n (he n)
  have hgap := linear_level_ratio hq ht ht1
  change (1 - (1 / 2 + t / 16)) ^ (1 - r) * (2 : ℝ) ^ (-(r / q)) ≤ 1 - t / (16 * q) at hgap
  have hgap' : (1 - (v : ℝ)) ^ (1 - r) * (2 : ℝ) ^ (-(r / q)) < 1 := by
    have : 0 < t / (16 * q) := by positivity
    change (1 - (1 / 2 + t / 16)) ^ (1 - r) * (2 : ℝ) ^ (-(r / q)) < 1
    linarith
  have hb : (2 : ℝ) ^ (-(r / q)) ≤ 1 :=
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (neg_neg_of_pos (div_pos (lt_trans zero_lt_one hr) hq0))).le
  have hmom := three_copy_moment hv0 hv1 X z hm hr.le hr2
    (show 0 ≤ (2 : ℝ) ^ (18 : ℝ) * S ^ r * m ^ (-(r / q)) by positivity)
    (show 0 ≤ (2 : ℝ) ^ (-(r / q)) by positivity) hb
    (fun n => (hlowr n).1) (fun n => (hlowr n).2) hgap'
  refine ⟨?_, hmean.1, hmean.2, hmom.1, hmom.2.trans ?_⟩
  · apply measurable_from_prod_countable_right
    intro n
    exact ((hm 0).comp measurable_fst).add
      ((measurable_const : Measurable (fun _ : Ω × Ω × Ω => ((1 - (v : ℝ)) ^ n * v)⁻¹)).smul
        (((hm (n + 1)).comp (measurable_fst.comp measurable_snd)).sub
          ((hm n).comp (measurable_snd.comp measurable_snd))))
  · have hh := linear_debiased_bound hq ht ht1
      (show 0 ≤ (2 : ℝ) ^ (18 : ℝ) * S ^ r * m ^ (-(r / q)) by positivity)
    refine hh.trans_eq ?_
    norm_num only [Real.rpow_ofNat, Nat.reducePow]
    ring


omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma envelope_reply_mean {X : Ω → E} (hi : Integrable X P) (z center : E) (μ : ℝ)
    (he : (∫ ω, X ω ∂P) = z) :
    Integrable (fun ω => μ • (center - X ω)) P ∧
      (∫ ω, μ • (center - X ω) ∂P) = μ • (center - z) := by
  refine ⟨((integrable_const center).sub hi).smul μ, ?_⟩
  rw [integral_smul, integral_sub (integrable_const center) hi, integral_const, he]
  simp

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [IsProbabilityMeasure P] in
lemma envelope_reply_moment {X : Ω → E} (z center : E)
    {μ r C s a : ℝ} (hμ : 0 < μ) (hr : 1 ≤ r) (hr2 : r ≤ 2)
    (hC : 0 ≤ C) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hi : Integrable (fun ω => ‖X ω - z‖ ^ r) P)
    (he : (∫ ω, ‖X ω - z‖ ^ r ∂P) ≤ C * (s / μ + a * ‖center - z‖) ^ r) :
    Integrable (fun ω => ‖μ • (center - X ω) - μ • (center - z)‖ ^ r) P ∧
      (∫ ω, ‖μ • (center - X ω) - μ • (center - z)‖ ^ r ∂P) ≤
        (2 * C) * (s ^ r + a ^ r * ‖μ • (center - z)‖ ^ r) := by
  have heq (ω : Ω) : ‖μ • (center - X ω) - μ • (center - z)‖ ^ r = μ ^ r * ‖X ω - z‖ ^ r := by
    rw [← smul_sub, show (center - X ω) - (center - z) = -(X ω - z) by abel,
      norm_smul, Real.norm_eq_abs, abs_of_pos hμ, norm_neg, Real.mul_rpow hμ.le (norm_nonneg _)]
  simp_rw [heq]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hμ.le r)
  have hscale : μ ^ r * (s / μ + a * ‖center - z‖) ^ r =
      (s + a * ‖μ • (center - z)‖) ^ r := by
    rw [← Real.mul_rpow hμ.le (by positivity), norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
    congr 1
    field_simp
  have hbound : (s + a * ‖μ • (center - z)‖) ^ r ≤
      2 * (s ^ r + a ^ r * ‖μ • (center - z)‖ ^ r) := by
    have hh := HilbertSmallMoments.addition_power_bound s (a * ‖μ • (center - z)‖) hr hr2
    simpa only [Real.norm_eq_abs, abs_of_nonneg hs, abs_of_nonneg (by positivity : 0 ≤ a * ‖μ • (center - z)‖),
      abs_of_nonneg (by positivity : 0 ≤ s + a * ‖μ • (center - z)‖),
      Real.mul_rpow ha (norm_nonneg _)] using hh
  calc
    _ ≤ C * (μ ^ r * (s / μ + a * ‖center - z‖) ^ r) := by nlinarith only [hh]
    _ = C * (s + a * ‖μ • (center - z)‖) ^ r := by rw [hscale]
    _ ≤ C * (2 * (s ^ r + a ^ r * ‖μ • (center - z)‖ ^ r)) := mul_le_mul_of_nonneg_left hbound hC
    _ = _ := by ring


end LongTails.Proofs.StochasticEnvelopeDebiasing
