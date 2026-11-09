import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory Set

namespace OracleTemplate.ChiSquareDro

section Tail

variable {Ξ : Type*} [MeasurableSpace Ξ] (p : Measure Ξ)

noncomputable def tail (ℓ : Ξ → ℝ) (η : ℝ) (ξ : Ξ) : ℝ := max (ℓ ξ - η) 0

noncomputable def first (ℓ : Ξ → ℝ) (η : ℝ) : ℝ := ∫ ξ, tail ℓ η ξ ∂p

noncomputable def sq (ℓ : Ξ → ℝ) (η : ℝ) : ℝ := ∫ ξ, tail ℓ η ξ ^ 2 ∂p

noncomputable def nrm (ℓ : Ξ → ℝ) (η : ℝ) : ℝ := Real.sqrt (sq p ℓ η)

omit [MeasurableSpace Ξ] in
lemma tail_nonneg (ℓ : Ξ → ℝ) (η : ℝ) (ξ : Ξ) : 0 ≤ tail ℓ η ξ := le_max_right _ _

omit [MeasurableSpace Ξ] in
lemma sub_le_tail (ℓ : Ξ → ℝ) (η : ℝ) (ξ : Ξ) : ℓ ξ - η ≤ tail ℓ η ξ := le_max_left _ _

omit [MeasurableSpace Ξ] in
lemma tail_le (ℓ : Ξ → ℝ) {B : ℝ} (η : ℝ) (hB : ∀ ξ, ℓ ξ ≤ B) (ξ : Ξ) :
    tail ℓ η ξ ≤ max (B - η) 0 :=
  max_le_max (by linarith [hB ξ]) le_rfl

omit [MeasurableSpace Ξ] in
lemma tail_sub_le (ℓ : Ξ → ℝ) (η η' : ℝ) (ξ : Ξ) :
    tail ℓ η ξ ≤ tail ℓ η' ξ + |η - η'| := by
  unfold tail
  rcases le_total (ℓ ξ - η) 0 with h | h
  · rw [max_eq_right h]; positivity
  · rw [max_eq_left h]
    have := le_max_left (ℓ ξ - η') 0
    have := le_abs_self (η' - η)
    rw [abs_sub_comm] at this
    linarith

lemma measurable_tail {ℓ : Ξ → ℝ} (hℓ : Measurable ℓ) (η : ℝ) : Measurable (tail ℓ η) :=
  (hℓ.sub_const η).max measurable_const

variable [IsProbabilityMeasure p]

lemma integral_quad {f : Ξ → ℝ} (hf : Integrable f p) (hf2 : Integrable (fun ξ => f ξ ^ 2) p)
    (a b : ℝ) :
    ∫ ξ, (f ξ ^ 2 + a * f ξ + b) ∂p = (∫ ξ, f ξ ^ 2 ∂p) + a * (∫ ξ, f ξ ∂p) + b := by
  rw [integral_add (f := fun ξ => f ξ ^ 2 + a * f ξ) (g := fun _ => b)
      (hf2.add (hf.const_mul a)) (integrable_const b),
    integral_add (f := fun ξ => f ξ ^ 2) (g := fun ξ => a * f ξ) hf2 (hf.const_mul a),
    integral_const_mul, integral_const, probReal_univ, one_smul]

lemma integral_sub_sq {f : Ξ → ℝ} (hf : Integrable f p) (hf2 : Integrable (fun ξ => f ξ ^ 2) p)
    (a : ℝ) :
    ∫ ξ, (f ξ - a) ^ 2 ∂p = (∫ ξ, f ξ ^ 2 ∂p) - 2 * a * (∫ ξ, f ξ ∂p) + a ^ 2 := by
  have e : (fun ξ => (f ξ - a) ^ 2) = fun ξ => f ξ ^ 2 + (-2 * a) * f ξ + a ^ 2 := by
    funext ξ; ring
  rw [e, integral_quad p hf hf2]
  ring

lemma integral_add_const' {f : Ξ → ℝ} (hf : Integrable f p) (b : ℝ) :
    ∫ ξ, (f ξ + b) ∂p = (∫ ξ, f ξ ∂p) + b := by
  rw [integral_add (f := f) (g := fun _ => b) hf (integrable_const b), integral_const,
    probReal_univ, one_smul]

lemma integrable_tail {ℓ : Ξ → ℝ} {B : ℝ} (hℓ : Measurable ℓ) (hB : ∀ ξ, ℓ ξ ≤ B) (η : ℝ) :
    Integrable (tail ℓ η) p := by
  refine Integrable.of_bound (measurable_tail hℓ η).aestronglyMeasurable (max (B - η) 0) ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (tail_nonneg ℓ η ξ)]
    exact tail_le ℓ η hB ξ

lemma integrable_tail_sq {ℓ : Ξ → ℝ} {B : ℝ} (hℓ : Measurable ℓ) (hB : ∀ ξ, ℓ ξ ≤ B) (η : ℝ) :
    Integrable (fun ξ => tail ℓ η ξ ^ 2) p := by
  refine Integrable.of_bound ((measurable_tail hℓ η).pow_const 2).aestronglyMeasurable
    (max (B - η) 0 ^ 2) ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (tail_nonneg ℓ η ξ) (tail_le ℓ η hB ξ) 2

omit [IsProbabilityMeasure p] in
lemma sq_nonneg' (ℓ : Ξ → ℝ) (η : ℝ) : 0 ≤ sq p ℓ η :=
  integral_nonneg fun _ => sq_nonneg _

omit [IsProbabilityMeasure p] in
lemma first_nonneg (ℓ : Ξ → ℝ) (η : ℝ) : 0 ≤ first p ℓ η :=
  integral_nonneg fun ξ => tail_nonneg ℓ η ξ

omit [IsProbabilityMeasure p] in
lemma nrm_sq (ℓ : Ξ → ℝ) (η : ℝ) : nrm p ℓ η ^ 2 = sq p ℓ η :=
  Real.sq_sqrt (sq_nonneg' p ℓ η)

omit [IsProbabilityMeasure p] in
lemma nrm_nonneg (ℓ : Ξ → ℝ) (η : ℝ) : 0 ≤ nrm p ℓ η := Real.sqrt_nonneg _

lemma first_sq_le {ℓ : Ξ → ℝ} {B : ℝ} (hℓ : Measurable ℓ) (hB : ∀ ξ, ℓ ξ ≤ B) (η : ℝ) :
    first p ℓ η ^ 2 ≤ sq p ℓ η := by
  have h0 : 0 ≤ ∫ ξ, (tail ℓ η ξ - first p ℓ η) ^ 2 ∂p := integral_nonneg fun ξ => sq_nonneg _
  rw [integral_sub_sq p (integrable_tail p hℓ hB η) (integrable_tail_sq p hℓ hB η)] at h0
  change 0 ≤ sq p ℓ η - 2 * first p ℓ η * first p ℓ η + first p ℓ η ^ 2 at h0
  nlinarith

lemma first_le_nrm {ℓ : Ξ → ℝ} {B : ℝ} (hℓ : Measurable ℓ) (hB : ∀ ξ, ℓ ξ ≤ B) (η : ℝ) :
    first p ℓ η ≤ nrm p ℓ η :=
  Real.le_sqrt_of_sq_le (first_sq_le p hℓ hB η)

lemma first_lipschitz {ℓ : Ξ → ℝ} {B : ℝ} (hℓ : Measurable ℓ) (hB : ∀ ξ, ℓ ξ ≤ B) (η η' : ℝ) :
    first p ℓ η ≤ first p ℓ η' + |η - η'| := by
  have h := integral_mono (integrable_tail p hℓ hB η)
    ((integrable_tail p hℓ hB η').add (integrable_const |η - η'|)) (tail_sub_le ℓ η η')
  change _ ≤ ∫ ξ, (tail ℓ η' ξ + |η - η'|) ∂p at h
  rw [integral_add_const' p (integrable_tail p hℓ hB η')] at h
  exact h

lemma nrm_lipschitz {ℓ : Ξ → ℝ} {B : ℝ} (hℓ : Measurable ℓ) (hB : ∀ ξ, ℓ ξ ≤ B) (η η' : ℝ) :
    nrm p ℓ η ≤ nrm p ℓ η' + |η - η'| := by
  set d := |η - η'|
  have hd : 0 ≤ d := abs_nonneg _
  have hi' := integrable_tail p hℓ hB η'
  have hi2' := integrable_tail_sq p hℓ hB η'
  have hpt : ∀ ξ, tail ℓ η ξ ^ 2 ≤ tail ℓ η' ξ ^ 2 + 2 * d * tail ℓ η' ξ + d ^ 2 := by
    intro ξ
    have h1 := tail_sub_le ℓ η η' ξ
    have h2 := tail_nonneg ℓ η ξ
    nlinarith
  have hint : Integrable (fun ξ => tail ℓ η' ξ ^ 2 + 2 * d * tail ℓ η' ξ + d ^ 2) p :=
    (hi2'.add (hi'.const_mul _)).add (integrable_const _)
  have hle := integral_mono (integrable_tail_sq p hℓ hB η) hint hpt
  rw [integral_quad p hi' hi2'] at hle
  change sq p ℓ η ≤ sq p ℓ η' + 2 * d * first p ℓ η' + d ^ 2 at hle
  have hf := first_le_nrm p hℓ hB η'
  have hsq : sq p ℓ η ≤ (nrm p ℓ η' + d) ^ 2 := by
    have := nrm_sq p ℓ η'
    nlinarith [nrm_nonneg p ℓ η']
  calc nrm p ℓ η = Real.sqrt (sq p ℓ η) := rfl
    _ ≤ Real.sqrt ((nrm p ℓ η' + d) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = nrm p ℓ η' + d := Real.sqrt_sq (add_nonneg (nrm_nonneg p ℓ η') hd)

lemma continuous_first {ℓ : Ξ → ℝ} {B : ℝ} (hℓ : Measurable ℓ) (hB : ∀ ξ, ℓ ξ ≤ B) :
    Continuous (first p ℓ) := by
  refine (LipschitzWith.of_le_add_mul 1 fun η η' => ?_).continuous
  have := first_lipschitz p hℓ hB η η'
  rw [Real.dist_eq]
  simpa using this

lemma continuous_nrm {ℓ : Ξ → ℝ} {B : ℝ} (hℓ : Measurable ℓ) (hB : ∀ ξ, ℓ ξ ≤ B) :
    Continuous (nrm p ℓ) := by
  refine (LipschitzWith.of_le_add_mul 1 fun η η' => ?_).continuous
  have := nrm_lipschitz p hℓ hB η η'
  rw [Real.dist_eq]
  simpa using this

end Tail

section Duality

variable {Ξ : Type*} [MeasurableSpace Ξ] (p : Measure Ξ) [IsProbabilityMeasure p]

def Feasible (ρ : ℝ) (w : Ξ → ℝ) : Prop :=
  Measurable w ∧ (∀ ξ, 0 ≤ w ξ) ∧ MemLp w 2 p ∧ (∫ ξ, w ξ ∂p) = 1 ∧
    (∫ ξ, (w ξ - 1) ^ 2 ∂p) / 2 ≤ ρ

lemma Feasible.integrable {ρ : ℝ} {w : Ξ → ℝ} (h : Feasible p ρ w) : Integrable w p :=
  h.2.2.1.integrable one_le_two

omit [IsProbabilityMeasure p] in
lemma Feasible.integrable_sq {ρ : ℝ} {w : Ξ → ℝ} (h : Feasible p ρ w) :
    Integrable (fun ξ => w ξ ^ 2) p :=
  h.2.2.1.integrable_sq

lemma Feasible.second {ρ : ℝ} {w : Ξ → ℝ} (h : Feasible p ρ w) :
    (∫ ξ, w ξ ^ 2 ∂p) ≤ 1 + 2 * ρ := by
  have hw := h.integrable
  have hw2 := h.integrable_sq
  have hexp : ∫ ξ, (w ξ - 1) ^ 2 ∂p = (∫ ξ, w ξ ^ 2 ∂p) - 1 := by
    rw [integral_sub_sq p hw hw2, h.2.2.2.1]
    ring
  have := h.2.2.2.2
  rw [hexp] at this
  linarith

lemma one_feasible {ρ : ℝ} (hρ : 0 ≤ ρ) : Feasible p ρ (fun _ => 1) := by
  refine ⟨measurable_const, fun _ => zero_le_one, memLp_const 1, ?_, ?_⟩
  · simp
  · simp; exact hρ

lemma mul_le_amgm {a b t : ℝ} (ht : 0 < t) : a * b ≤ (t * a ^ 2 + b ^ 2 / t) / 2 := by
  have h : 0 ≤ (t * a - b) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have : (t * a - b) ^ 2 / t = t * a ^ 2 - 2 * a * b + b ^ 2 / t := by
    field_simp; ring
  linarith

lemma integral_mul_tail_le {ℓ : Ξ → ℝ} {B ρ : ℝ} (hℓ : Measurable ℓ) (hB : ∀ ξ, ℓ ξ ≤ B)
    {w : Ξ → ℝ} (hw : Feasible p ρ w) (hρ : 0 ≤ ρ) (η : ℝ) :
    (∫ ξ, w ξ * tail ℓ η ξ ∂p) ≤ Real.sqrt (1 + 2 * ρ) * nrm p ℓ η := by
  set c := Real.sqrt (1 + 2 * ρ)
  have hc : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hcc : c ^ 2 = 1 + 2 * ρ := Real.sq_sqrt (by linarith)
  have hwi := hw.integrable
  have hw2 := hw.integrable_sq
  have ht2 := integrable_tail_sq p hℓ hB η
  have hwt : Integrable (fun ξ => w ξ * tail ℓ η ξ) p := by
    refine (hwi.norm.const_mul (max (B - η) 0)).mono'
      (hw.1.mul (measurable_tail hℓ η)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tail_nonneg ℓ η ξ), Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (tail_le ℓ η hB ξ) (abs_nonneg _)
  have hgen : ∀ t, 0 < t → (∫ ξ, w ξ * tail ℓ η ξ ∂p) ≤ (t * c ^ 2 + nrm p ℓ η ^ 2 / t) / 2 := by
    intro t ht
    have hint : Integrable (fun ξ => (t * w ξ ^ 2 + tail ℓ η ξ ^ 2 / t) / 2) p :=
      ((hw2.const_mul t).add (ht2.div_const t)).div_const 2
    have hle := integral_mono hwt hint fun ξ => mul_le_amgm (a := w ξ) (b := tail ℓ η ξ) ht
    rw [integral_div, integral_add (f := fun ξ => t * w ξ ^ 2)
      (g := fun ξ => tail ℓ η ξ ^ 2 / t) (hw2.const_mul t) (ht2.div_const t), integral_const_mul,
      integral_div] at hle
    rw [nrm_sq, hcc]
    have h2 := hw.second
    have : t * (∫ ξ, w ξ ^ 2 ∂p) ≤ t * (1 + 2 * ρ) := mul_le_mul_of_nonneg_left h2 ht.le
    change (∫ ξ, w ξ * tail ℓ η ξ ∂p) ≤ _ at hle
    unfold sq
    linarith
  rcases (nrm_nonneg p ℓ η).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := hgen (2 * δ / c ^ 2) (by positivity)
    rw [← h0] at this
    have hc2 : c ^ 2 ≠ 0 := by positivity
    calc _ ≤ _ := this
      _ = 0 + δ := by field_simp; ring
  · have := hgen (nrm p ℓ η / c) (div_pos hpos hc)
    calc _ ≤ _ := this
      _ = c * nrm p ℓ η := by field_simp; ring

lemma weak_duality {ℓ : Ξ → ℝ} {B ρ : ℝ} (hℓ : Measurable ℓ) (hB0 : ∀ ξ, 0 ≤ ℓ ξ)
    (hB : ∀ ξ, ℓ ξ ≤ B)
    {w : Ξ → ℝ} (hw : Feasible p ρ w) (hρ : 0 ≤ ρ) (η : ℝ) :
    (∫ ξ, w ξ * ℓ ξ ∂p) ≤ η + Real.sqrt (1 + 2 * ρ) * nrm p ℓ η := by
  have hwi := hw.integrable
  have hwt : Integrable (fun ξ => w ξ * tail ℓ η ξ) p := by
    refine (hwi.norm.const_mul (max (B - η) 0)).mono'
      (hw.1.mul (measurable_tail hℓ η)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tail_nonneg ℓ η ξ), Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (tail_le ℓ η hB ξ) (abs_nonneg _)
  have hpt : ∀ ξ, w ξ * ℓ ξ ≤ η * w ξ + w ξ * tail ℓ η ξ := by
    intro ξ
    have := mul_le_mul_of_nonneg_left (sub_le_tail ℓ η ξ) (hw.2.1 ξ)
    nlinarith
  have hwl : Integrable (fun ξ => w ξ * ℓ ξ) p := by
    refine (hwi.norm.const_mul B).mono' (hw.1.mul hℓ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hB0 ξ), Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB ξ) (abs_nonneg _)
  have hle := integral_mono hwl ((hwi.const_mul η).add hwt) hpt
  change _ ≤ ∫ ξ, (η * w ξ + w ξ * tail ℓ η ξ) ∂p at hle
  rw [integral_add (f := fun ξ => η * w ξ) (g := fun ξ => w ξ * tail ℓ η ξ) (hwi.const_mul η) hwt,
    integral_const_mul, hw.2.2.2.1, mul_one] at hle
  linarith [integral_mul_tail_le p hℓ hB hw hρ η]

omit [MeasurableSpace Ξ] [IsProbabilityMeasure p] in
lemma tail_at_top {ℓ : Ξ → ℝ} {B : ℝ} (hB : ∀ ξ, ℓ ξ ≤ B) (ξ : Ξ) : tail ℓ B ξ = 0 :=
  max_eq_right (by linarith [hB ξ])

omit [IsProbabilityMeasure p] in
lemma first_top {ℓ : Ξ → ℝ} {B : ℝ} (hB : ∀ ξ, ℓ ξ ≤ B) : first p ℓ B = 0 := by
  simp [first, tail_at_top hB]

omit [IsProbabilityMeasure p] in
lemma nrm_top {ℓ : Ξ → ℝ} {B : ℝ} (hB : ∀ ξ, ℓ ξ ≤ B) : nrm p ℓ B = 0 := by
  simp [nrm, sq, tail_at_top hB]

omit [MeasurableSpace Ξ] [IsProbabilityMeasure p] in
lemma tail_of_nonpos {ℓ : Ξ → ℝ} (hB0 : ∀ ξ, 0 ≤ ℓ ξ) {a : ℝ} (ha : a ≤ 0) (ξ : Ξ) :
    tail ℓ a ξ = ℓ ξ - a :=
  max_eq_left (by linarith [hB0 ξ])

lemma gap_left {ℓ : Ξ → ℝ} {B ρ : ℝ} (hℓ : Measurable ℓ) (hB0 : ∀ ξ, 0 ≤ ℓ ξ)
    (hB : ∀ ξ, ℓ ξ ≤ B) (hB0' : 0 ≤ B) (hρ : 0 < ρ) :
    nrm p ℓ (-B / Real.sqrt ρ) ≤ Real.sqrt (1 + 2 * ρ) * first p ℓ (-B / Real.sqrt ρ) := by
  set a := -B / Real.sqrt ρ
  have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have ha : a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hsρ.le
  have ha2 : a ^ 2 = B ^ 2 / ρ := by
    simp only [a, div_pow, neg_sq, Real.sq_sqrt hρ.le]
  have hli : Integrable ℓ p := Integrable.of_bound hℓ.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hB0 ξ)]; exact hB ξ)
  have hl2 : Integrable (fun ξ => ℓ ξ ^ 2) p := Integrable.of_bound
    (hℓ.pow_const 2).aestronglyMeasurable (B ^ 2)
    (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hB0 ξ) (hB ξ) 2)
  set m := ∫ ξ, ℓ ξ ∂p
  have hm0 : 0 ≤ m := integral_nonneg hB0
  have hmB : m ≤ B := by
    have := integral_mono hli (integrable_const B) hB
    simpa using this
  have hfirst : first p ℓ a = m - a := by
    simp only [first, tail_of_nonpos hB0 ha]
    rw [integral_sub hli (integrable_const _), integral_const, probReal_univ, one_smul]
  have hsq : sq p ℓ a ≤ B * m - 2 * a * m + a ^ 2 := by
    simp only [sq, tail_of_nonpos hB0 ha]
    rw [integral_sub_sq p hli hl2]
    have : ∫ ξ, ℓ ξ ^ 2 ∂p ≤ ∫ ξ, B * ℓ ξ ∂p :=
      integral_mono hl2 (hli.const_mul B) fun ξ => by nlinarith [hB0 ξ, hB ξ]
    rw [integral_const_mul] at this
    change _ ≤ B * m - 2 * a * m + a ^ 2
    linarith
  have hc2 : Real.sqrt (1 + 2 * ρ) ^ 2 = 1 + 2 * ρ := Real.sq_sqrt (by linarith)
  have hkey : sq p ℓ a ≤ (Real.sqrt (1 + 2 * ρ) * first p ℓ a) ^ 2 := by
    rw [mul_pow, hc2, hfirst]
    have hma : a ^ 2 ≤ (m - a) ^ 2 := by nlinarith
    have : 2 * ρ * a ^ 2 = 2 * B ^ 2 := by rw [ha2]; field_simp
    nlinarith
  calc nrm p ℓ a = Real.sqrt (sq p ℓ a) := rfl
    _ ≤ Real.sqrt ((Real.sqrt (1 + 2 * ρ) * first p ℓ a) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = _ := Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (first_nonneg p ℓ a))

lemma strong_duality {ℓ : Ξ → ℝ} {B ρ : ℝ} (hℓ : Measurable ℓ) (hB0 : ∀ ξ, 0 ≤ ℓ ξ)
    (hB : ∀ ξ, ℓ ξ ≤ B) (hBpos : 0 < B) (hρ : 0 < ρ) :
    ∃ η ∈ Icc (-B / Real.sqrt ρ) B, ∀ δ, 0 < δ → ∃ w, Feasible p ρ w ∧
      η + Real.sqrt (1 + 2 * ρ) * nrm p ℓ η - δ ≤ ∫ ξ, w ξ * ℓ ξ ∂p := by
  set c := Real.sqrt (1 + 2 * ρ)
  set a := -B / Real.sqrt ρ
  have hc : 0 < c := Real.sqrt_pos.mpr (by linarith)
  have hcc : c ^ 2 = 1 + 2 * ρ := Real.sq_sqrt (by linarith)
  have hsρ : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have ha : a < 0 := div_neg_of_neg_of_pos (by linarith) hsρ
  have haB : a ≤ B := by linarith
  set h : ℝ → ℝ := fun η => c * first p ℓ η - nrm p ℓ η
  have hcont : Continuous h :=
    (continuous_const.mul (continuous_first p hℓ hB)).sub (continuous_nrm p hℓ hB)
  have ha0 : 0 ≤ h a := by
    have := gap_left p hℓ hB0 hB hBpos.le hρ
    simp only [h]; linarith
  have hB0h : h B = 0 := by simp [h, first_top p hB, nrm_top p hB]
  set S := {η ∈ Icc a B | h η = 0}
  have hSne : S.Nonempty := ⟨B, ⟨haB, le_rfl⟩, hB0h⟩
  have hSclosed : IsClosed S := isClosed_Icc.inter (isClosed_eq hcont continuous_const)
  have hSbdd : BddBelow S := ⟨a, fun η hη => hη.1.1⟩
  set η₀ := sInf S
  have hη₀S : η₀ ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hη₀min : ∀ η ∈ S, η₀ ≤ η := fun η hη => csInf_le hSbdd hη
  have hpos : ∀ η ∈ Ico a η₀, 0 < h η := by
    intro η hη
    by_contra hneg
    have hneg := not_lt.mp hneg
    have hIcc : ContinuousOn h (Icc a η) := hcont.continuousOn
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hη.1 hIcc ⟨hneg, ha0⟩
    have hrS : r ∈ S := ⟨⟨hr.1, le_trans hr.2 (le_trans hη.2.le hη₀S.1.2)⟩, hr0⟩
    linarith [hη₀min r hrS, hr.2, hη.2]
  refine ⟨η₀, hη₀S.1, ?_⟩
  intro δ hδ
  have hroot : c * first p ℓ η₀ = nrm p ℓ η₀ := by
    have := hη₀S.2; simp only [h] at this; linarith
  rcases (nrm_nonneg p ℓ η₀).eq_or_lt with hz | hnz
  · have hz' : nrm p ℓ η₀ = 0 := hz.symm
    have hηa : a < η₀ := by
      rcases hη₀S.1.1.eq_or_lt with heq | hlt
      · exfalso
        have h1 : -a ≤ first p ℓ a := by
          have hint := integrable_tail p hℓ hB a
          have := integral_mono (integrable_const (-a)) hint fun ξ => by
            rw [tail_of_nonpos hB0 ha.le]; linarith [hB0 ξ]
          simpa [first] using this
        have h2 := first_le_nrm p hℓ hB a
        rw [heq] at h1 h2
        linarith
      · exact hlt
    set η := max a (η₀ - δ / 2)
    have hηI : η ∈ Ico a η₀ := ⟨le_max_left _ _, max_lt hηa (by linarith)⟩
    have hgap := hpos η hηI
    set A := {ξ | η < ℓ ξ}
    have hAm : MeasurableSet A := measurableSet_lt measurable_const hℓ
    set π := p.real A
    have hπ0 : 0 ≤ π := measureReal_nonneg
    have htailA : ∀ ξ, tail ℓ η ξ = A.indicator (fun ξ => tail ℓ η ξ) ξ := by
      intro ξ
      by_cases hξ : ξ ∈ A
      · rw [Set.indicator_of_mem hξ]
      · rw [Set.indicator_of_notMem hξ]
        have hξ' : ¬ (η < ℓ ξ) := hξ
        exact max_eq_right (by linarith [not_lt.mp hξ'])
    have hamgm : ∀ t, 0 < t → first p ℓ η ≤ (t * π + sq p ℓ η / t) / 2 := by
      intro t ht
      have hpt : ∀ ξ, tail ℓ η ξ ≤
          (t * A.indicator (fun _ => (1 : ℝ)) ξ + tail ℓ η ξ ^ 2 / t) / 2 := by
        intro ξ
        by_cases hξ : ξ ∈ A
        · rw [Set.indicator_of_mem hξ]
          have := mul_le_amgm (a := (1 : ℝ)) (b := tail ℓ η ξ) ht
          simpa using this
        · rw [Set.indicator_of_notMem hξ, htailA ξ, Set.indicator_of_notMem hξ]
          simp
      have hi1 : Integrable (fun ξ => A.indicator (fun _ => (1 : ℝ)) ξ) p :=
        (integrable_const (1 : ℝ)).indicator hAm
      have hint : Integrable (fun ξ => (t * A.indicator (fun _ => (1 : ℝ)) ξ +
          tail ℓ η ξ ^ 2 / t) / 2) p :=
        ((hi1.const_mul t).add ((integrable_tail_sq p hℓ hB η).div_const t)).div_const 2
      have := integral_mono (integrable_tail p hℓ hB η) hint hpt
      rw [integral_div, integral_add (f := fun ξ => t * A.indicator (fun _ => (1 : ℝ)) ξ)
        (g := fun ξ => tail ℓ η ξ ^ 2 / t) (hi1.const_mul t)
        ((integrable_tail_sq p hℓ hB η).div_const t),
        integral_const_mul, integral_div, integral_indicator_const _ hAm] at this
      simpa [first, sq, π, smul_eq_mul] using this
    have hf0 : 0 < first p ℓ η := by
      have := nrm_nonneg p ℓ η
      by_contra hle
      have hle := not_lt.mp hle
      have : c * first p ℓ η ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le hle
      simp only [h] at hgap; linarith
    have hπpos : 0 < π := by
      rcases hπ0.eq_or_lt with h0 | h0
      · exfalso
        have := hamgm 1 one_pos
        have h2 : first p ℓ η ≤ sq p ℓ η / 2 := by rw [← h0] at this; linarith
        have h3 : ∀ t, 0 < t → first p ℓ η ≤ sq p ℓ η / t / 2 := by
          intro t ht; have := hamgm t ht; rw [← h0] at this; linarith
        have hs0 := sq_nonneg' p ℓ η
        have hden : 0 < 4 * sq p ℓ η / first p ℓ η + 1 :=
          add_pos_of_nonneg_of_pos (div_nonneg (by linarith) hf0.le) one_pos
        have h4 := h3 (4 * sq p ℓ η / first p ℓ η + 1) hden
        have : sq p ℓ η / (4 * sq p ℓ η / first p ℓ η + 1) / 2 < first p ℓ η := by
          rw [div_div, div_lt_iff₀ (by linarith)]
          nlinarith [div_mul_cancel₀ (4 * sq p ℓ η) hf0.ne']
        linarith
      · exact h0
    have hfs : first p ℓ η ^ 2 ≤ π * sq p ℓ η := by
      have := hamgm (first p ℓ η / π) (div_pos hf0 hπpos)
      have hs0 := sq_nonneg' p ℓ η
      field_simp at this
      nlinarith
    have hcs : sq p ℓ η < c ^ 2 * first p ℓ η ^ 2 := by
      have h1 : nrm p ℓ η < c * first p ℓ η := by simp only [h] at hgap; linarith
      have h2 := nrm_nonneg p ℓ η
      rw [← nrm_sq]
      nlinarith
    have hπc : 1 ≤ c ^ 2 * π := by
      have hs0 := sq_nonneg' p ℓ η
      by_contra hlt
      have hlt := not_le.mp hlt
      have : c ^ 2 * first p ℓ η ^ 2 ≤ c ^ 2 * (π * sq p ℓ η) :=
        mul_le_mul_of_nonneg_left hfs (by positivity)
      nlinarith
    set w : Ξ → ℝ := A.indicator (fun _ => 1 / π)
    have hwm : Measurable w := measurable_const.indicator hAm
    have hw0 : ∀ ξ, 0 ≤ w ξ := fun ξ => Set.indicator_nonneg (fun _ _ => by positivity) ξ
    have hwb : ∀ ξ, ‖w ξ‖ ≤ 1 / π := by
      intro ξ
      by_cases hξ : ξ ∈ A
      · simp [w, Set.indicator_of_mem hξ, abs_of_pos hπpos]
      · simp [w, Set.indicator_of_notMem hξ]; positivity
    have hwL : MemLp w 2 p := MemLp.of_bound hwm.aestronglyMeasurable (1 / π)
      (Filter.Eventually.of_forall hwb)
    have hw1 : (∫ ξ, w ξ ∂p) = 1 := by
      rw [integral_indicator_const _ hAm, smul_eq_mul]
      change π * (1 / π) = 1
      field_simp
    have hwsq : (fun ξ => w ξ ^ 2) = A.indicator (fun _ => 1 / π ^ 2) := by
      funext ξ
      by_cases hξ : ξ ∈ A
      · simp [w, Set.indicator_of_mem hξ]
      · simp [w, Set.indicator_of_notMem hξ]
    have hw2 : (∫ ξ, w ξ ^ 2 ∂p) = 1 / π := by
      rw [hwsq, integral_indicator_const _ hAm, smul_eq_mul]
      change π * (1 / π ^ 2) = 1 / π
      field_simp
    have hwi : Integrable w p := hwL.integrable one_le_two
    have hwi2 : Integrable (fun ξ => w ξ ^ 2) p := hwL.integrable_sq
    have hdev : (∫ ξ, (w ξ - 1) ^ 2 ∂p) / 2 ≤ ρ := by
      rw [integral_sub_sq p hwi hwi2, hw1, hw2]
      have : 1 / π ≤ c ^ 2 := by rw [div_le_iff₀ hπpos]; linarith
      rw [hcc] at this
      linarith
    refine ⟨w, ⟨hwm, hw0, hwL, hw1, hdev⟩, ?_⟩
    have hwl : Integrable (fun ξ => w ξ * ℓ ξ) p := by
      refine (hwi.norm.const_mul B).mono' (hwm.mul hℓ).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hB0 ξ), Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hB ξ) (abs_nonneg _)
    have hpt : ∀ ξ, η * w ξ ≤ w ξ * ℓ ξ := by
      intro ξ
      by_cases hξ : ξ ∈ A
      · have : η < ℓ ξ := hξ
        have := hw0 ξ
        nlinarith
      · simp [w, Set.indicator_of_notMem hξ]
    have := integral_mono (hwi.const_mul η) hwl hpt
    rw [integral_const_mul, hw1, mul_one] at this
    rw [hz', mul_zero, add_zero]
    have : η₀ - δ / 2 ≤ η := le_max_right _ _
    linarith
  · set N := nrm p ℓ η₀
    set w : Ξ → ℝ := fun ξ => c * tail ℓ η₀ ξ / N
    have hwm : Measurable w := ((measurable_tail hℓ η₀).const_mul c).div_const N
    have hw0 : ∀ ξ, 0 ≤ w ξ := fun ξ => div_nonneg (mul_nonneg hc.le (tail_nonneg ℓ η₀ ξ)) hnz.le
    have hwb : ∀ ξ, ‖w ξ‖ ≤ c * max (B - η₀) 0 / N := by
      intro ξ
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 ξ)]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (tail_le ℓ η₀ hB ξ) hc.le) hnz.le
    have hwL : MemLp w 2 p := MemLp.of_bound hwm.aestronglyMeasurable _
      (Filter.Eventually.of_forall hwb)
    have hti := integrable_tail p hℓ hB η₀
    have hti2 := integrable_tail_sq p hℓ hB η₀
    have hw1 : (∫ ξ, w ξ ∂p) = 1 := by
      simp only [w]
      rw [integral_div, integral_const_mul]
      change c * first p ℓ η₀ / N = 1
      rw [hroot]; exact div_self hnz.ne'
    have hwsq : (fun ξ => w ξ ^ 2) = fun ξ => c ^ 2 / N ^ 2 * tail ℓ η₀ ξ ^ 2 := by
      funext ξ; simp only [w]; ring
    have hw2 : (∫ ξ, w ξ ^ 2 ∂p) = c ^ 2 := by
      rw [hwsq, integral_const_mul]
      change c ^ 2 / N ^ 2 * sq p ℓ η₀ = c ^ 2
      rw [show sq p ℓ η₀ = N ^ 2 from (nrm_sq p ℓ η₀).symm]
      field_simp
    have hwi : Integrable w p := hwL.integrable one_le_two
    have hwi2 : Integrable (fun ξ => w ξ ^ 2) p := hwL.integrable_sq
    have hdev : (∫ ξ, (w ξ - 1) ^ 2 ∂p) / 2 ≤ ρ := by
      rw [integral_sub_sq p hwi hwi2, hw1, hw2, hcc]
      linarith
    refine ⟨w, ⟨hwm, hw0, hwL, hw1, hdev⟩, ?_⟩
    have hpt : ∀ ξ, w ξ * ℓ ξ = η₀ * w ξ + c / N * tail ℓ η₀ ξ ^ 2 := by
      intro ξ
      simp only [w]
      rcases le_total 0 (ℓ ξ - η₀) with hle | hle
      · have : tail ℓ η₀ ξ = ℓ ξ - η₀ := max_eq_left hle
        rw [this]; field_simp; ring
      · have : tail ℓ η₀ ξ = 0 := max_eq_right hle
        rw [this]; simp
    have hval : (∫ ξ, w ξ * ℓ ξ ∂p) = η₀ + c * N := by
      simp_rw [hpt]
      rw [integral_add (f := fun ξ => η₀ * w ξ) (g := fun ξ => c / N * tail ℓ η₀ ξ ^ 2)
        (hwi.const_mul _) (hti2.const_mul _), integral_const_mul, hw1, integral_const_mul]
      change η₀ * 1 + c / N * sq p ℓ η₀ = η₀ + c * N
      rw [show sq p ℓ η₀ = N ^ 2 from (nrm_sq p ℓ η₀).symm]
      field_simp
    rw [hval]
    linarith

end Duality

end OracleTemplate.ChiSquareDro
