import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import LongTails.Algorithms.ClippedSpsa

open MeasureTheory

namespace LongTails.Proofs.ClippedScalarDescent

open OracleTemplate.ClippedSpsa

section Clip

variable {c : ℝ}

lemma clip_abs_le (hc : 0 ≤ c) (y : ℝ) : |clipScalar c y| ≤ c := by
  unfold clipScalar
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma clip_lipschitz (y z : ℝ) : |clipScalar c y - clipScalar c z| ≤ |y - z| := by
  unfold clipScalar
  calc |max (-c) (min c y) - max (-c) (min c z)| ≤ |min c y - min c z| := by
        rw [max_comm (-c), max_comm (-c)]; exact abs_max_sub_max_le_abs _ _ _
    _ ≤ |y - z| := by
        have := abs_min_sub_min_le_max c y c z
        simpa using this

lemma clip_self_mul (hc : 0 ≤ c) (y : ℝ) : clipScalar c y * y = min |y| c * |y| := by
  unfold clipScalar
  rcases le_total c y with h | h
  · have hy : 0 ≤ y := hc.trans h
    rw [min_eq_left h, max_eq_right (by linarith), abs_of_nonneg hy, min_eq_right h]
  · rcases le_total (-c) y with h' | h'
    · rw [min_eq_right h, max_eq_right h']
      have : |y| ≤ c := abs_le.mpr ⟨h', h⟩
      rw [min_eq_left this, abs_mul_abs_self]
    · have hy : y ≤ 0 := by linarith
      rw [min_eq_right h, max_eq_left h', abs_of_nonpos hy, min_eq_right (by linarith)]
      ring

lemma clip_sq_le_min (hc : 0 ≤ c) (y : ℝ) : clipScalar c y ^ 2 ≤ min (c ^ 2) (y ^ 2) := by
  have h1 := clip_abs_le hc y
  have h2 : |clipScalar c y| ≤ |y| := by
    have := clip_lipschitz (c := c) y 0
    have h0 : clipScalar c 0 = 0 := by
      unfold clipScalar; rw [min_eq_right hc, max_eq_right (by linarith)]
    rwa [h0, sub_zero, sub_zero] at this
  refine le_min ?_ ?_
  · rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  · rw [← sq_abs, ← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2

lemma excess_le (hc : 0 ≤ c) (a v : ℝ) :
    |(a + v) - clipScalar c (a + v)| ≤
      (if c / 2 < |a| then |a| else 0) + (if c / 2 < |v| then |v| else 0) := by
  set y := a + v with hy
  have key : |y - clipScalar c y| ≤ max (|y| - c) 0 := by
    unfold clipScalar
    rcases le_total c y with h | h
    · rw [min_eq_left h, max_eq_right (by linarith),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ y - c), abs_of_nonneg (by linarith : (0 : ℝ) ≤ y)]
      exact le_max_left _ _
    · rcases le_total (-c) y with h' | h'
      · rw [min_eq_right h, max_eq_right h', sub_self, abs_zero]; exact le_max_right _ _
      · rw [min_eq_right h, max_eq_left h', abs_of_nonpos (by linarith : y - -c ≤ 0),
          abs_of_nonpos (by linarith : y ≤ 0)]
        exact le_max_of_le_left (by linarith)
  have hA : 0 ≤ (if c / 2 < |a| then |a| else 0) := by split_ifs <;> simp
  have hV : 0 ≤ (if c / 2 < |v| then |v| else 0) := by split_ifs <;> simp
  refine key.trans (max_le ?_ (add_nonneg hA hV))
  have hav : |y| ≤ |a| + |v| := abs_add_le a v
  split_ifs with ha hv hv
  · linarith
  · push Not at hv; linarith
  · push Not at ha; linarith
  · push Not at ha hv; linarith

end Clip

lemma measurable_abs_comp {α : Type*} [MeasurableSpace α] {g : α → ℝ} (h : Measurable g) :
    Measurable (fun z => |g z|) :=
  continuous_abs.measurable.comp h

lemma iadd {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (fun x => f x + g x) μ := hf.add hg

lemma isub {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) : Integrable (fun x => f x - g x) μ := hf.sub hg

section Expectation

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} [IsProbabilityMeasure μ]

lemma holder_indicator {X : Z → ℝ} {p : ℝ} (hp : 1 < p) (hX : Measurable X) (hX0 : ∀ z, 0 ≤ X z)
    (hXp : Integrable (fun z => X z ^ p) μ) {s : Set Z} (hs : MeasurableSet s) :
    ∫ z, s.indicator X z ∂μ ≤ (∫ z, X z ^ p ∂μ) ^ (1 / p) * (μ.real s) ^ ((p - 1) / p) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have hp0 : 0 < p := by linarith
  have hLp : MemLp X (ENNReal.ofReal p) μ := by
    apply (integrable_norm_rpow_iff hX.aestronglyMeasurable (by simp [hp0]) (by simp)).mp
    simp only [ENNReal.toReal_ofReal hp0.le, Real.norm_eq_abs]
    refine hXp.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [abs_of_nonneg (hX0 z)]
  have hI : MemLp (s.indicator (fun _ : Z => (1 : ℝ))) (ENNReal.ofReal p.conjExponent) μ :=
    (memLp_const 1).indicator hs
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (Filter.Eventually.of_forall hX0)
    (Filter.Eventually.of_forall (fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) z)) hLp hI
  have heq : (fun z => X z * s.indicator (fun _ : Z => (1 : ℝ)) z) = s.indicator X := by
    funext z; by_cases hz : z ∈ s <;> simp [hz]
  have heqpow : (fun z => (s.indicator (fun _ : Z => (1 : ℝ)) z) ^ p.conjExponent) =
      s.indicator (fun _ : Z => (1 : ℝ)) := by
    funext z; by_cases hz : z ∈ s <;> simp [hz, Real.zero_rpow hpq.symm.pos.ne']
  rw [heq, heqpow] at hh
  have h1 : ∫ z, s.indicator (fun _ : Z => (1 : ℝ)) z ∂μ = μ.real s := by
    rw [integral_indicator hs]; simp
  have hq : 1 / p.conjExponent = (p - 1) / p := by
    rw [Real.conjExponent]; field_simp
  rw [h1, hq] at hh
  exact hh

lemma markov_rpow {V : Z → ℝ} {p m : ℝ} (hp : 0 < p) (hm : 0 < m)
    (hVi : Integrable (fun z => |V z| ^ p) μ) :
    μ.real {z | m < |V z|} ≤ (∫ z, |V z| ^ p ∂μ) / m ^ p := by
  have hmp : 0 < m ^ p := Real.rpow_pos_of_pos hm p
  rw [le_div_iff₀ hmp, mul_comm]
  have hmk := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun z => Real.rpow_nonneg (abs_nonneg (V z)) p)) hVi (m ^ p)
  refine le_trans ?_ hmk
  refine mul_le_mul_of_nonneg_left ?_ hmp.le
  apply measureReal_mono
  · intro z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    exact Real.rpow_le_rpow hm.le hz.le hp.le
  · exact measure_ne_top _ _

end Expectation

section Descent

variable {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} [IsProbabilityMeasure μ]

structure MomentHyp (μ : Measure Z) (A V : Z → ℝ) (α ρ S p : ℝ) : Prop where
  measA : Measurable A
  measV : Measurable V
  bound : ∃ M, ∀ z, |A z| ≤ M
  second : ∫ z, A z ^ 2 ∂μ = α ^ 2
  fourth : ∫ z, A z ^ 4 ∂μ ≤ 3 * α ^ 4
  cross_int : Integrable (fun z => V z * A z) μ
  cross : -(ρ * α) ≤ ∫ z, V z * A z ∂μ
  vp_int : Integrable (fun z => |V z| ^ p) μ
  vp : ∫ z, |V z| ^ p ∂μ ≤ S ^ p
  vap_int : Integrable (fun z => |V z * A z| ^ p) μ
  vap : ∫ z, |V z * A z| ^ p ∂μ ≤ (Real.sqrt 3 * S * α) ^ p

variable {A V : Z → ℝ} {α ρ S p c : ℝ}

lemma int_of_bdd {g : Z → ℝ} (hg : Measurable g)
    (hb : ∃ M, ∀ z, |g z| ≤ M) : Integrable g μ := by
  obtain ⟨M, hM⟩ := hb
  exact Integrable.of_bound hg.aestronglyMeasurable M (Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hM z)

lemma MomentHyp.abs_cross_le (H : MomentHyp μ A V α ρ S p) (hp : 1 < p) (hα : 0 ≤ α)
    (hS : 0 ≤ S) : ∫ z, |V z * A z| ∂μ ≤ Real.sqrt 3 * S * α := by
  have h : ∫ z, |V z * A z| ∂μ ≤ (∫ z, |V z * A z| ^ p ∂μ) ^ (1 / p) := by
    have hm : Measurable (fun z => |V z * A z|) := (measurable_abs_comp (H.measV.mul H.measA))
    have hpi : Integrable (fun z => |V z * A z| ^ p) μ := H.vap_int
    have hh := holder_indicator (μ := μ) hp hm (fun z => abs_nonneg _) hpi MeasurableSet.univ
    simpa using hh
  refine h.trans ?_
  have hb : 0 ≤ Real.sqrt 3 * S * α := by positivity
  have hp0 : 0 < p := by linarith
  calc (∫ z, |V z * A z| ^ p ∂μ) ^ (1 / p) ≤ ((Real.sqrt 3 * S * α) ^ p) ^ (1 / p) :=
        Real.rpow_le_rpow (integral_nonneg fun z => by positivity) H.vap (by positivity)
    _ = Real.sqrt 3 * S * α := by
        rw [← Real.rpow_mul hb, mul_one_div_cancel hp0.ne', Real.rpow_one]

lemma MomentHyp.tail_cross_le (H : MomentHyp μ A V α ρ S p) (hp1 : 1 < p) (hα : 0 ≤ α)
    (hS : 0 < S) (hc : 0 < c) :
    ∫ z, (if c / 2 < |V z| then |V z * A z| else 0) ∂μ ≤
      Real.sqrt 3 * S * α * (2 * S / c) ^ (p - 1) := by
  have hp0 : 0 < p := by linarith
  set s := {z | c / 2 < |V z|} with hsdef
  have hs : MeasurableSet s := measurableSet_lt measurable_const (measurable_abs_comp H.measV)
  have heq : (fun z => if c / 2 < |V z| then |V z * A z| else 0) =
      s.indicator (fun z => |V z * A z|) := by
    funext z; by_cases hz : c / 2 < |V z| <;> simp [s, hz]
  rw [heq]
  have hho := holder_indicator (μ := μ) hp1 (measurable_abs_comp (H.measV.mul H.measA)) (fun z => abs_nonneg _)
    H.vap_int hs
  have hmk := markov_rpow (μ := μ) (V := V) hp0 (by linarith : 0 < c / 2) H.vp_int
  have hroot : (∫ z, |V z * A z| ^ p ∂μ) ^ (1 / p) ≤ Real.sqrt 3 * S * α := by
    have hb : 0 ≤ Real.sqrt 3 * S * α := by positivity
    calc (∫ z, |V z * A z| ^ p ∂μ) ^ (1 / p) ≤ ((Real.sqrt 3 * S * α) ^ p) ^ (1 / p) :=
          Real.rpow_le_rpow (integral_nonneg fun z => by positivity) H.vap (by positivity)
      _ = Real.sqrt 3 * S * α := by
          rw [← Real.rpow_mul hb, mul_one_div_cancel hp0.ne', Real.rpow_one]
  have hprob : μ.real s ≤ (2 * S / c) ^ p := by
    refine hmk.trans ?_
    rw [div_le_iff₀ (Real.rpow_pos_of_pos (by linarith) p)]
    calc (∫ z, |V z| ^ p ∂μ) ≤ S ^ p := H.vp
      _ = (2 * S / c) ^ p * (c / 2) ^ p := by
          rw [← Real.mul_rpow (by positivity) (by positivity)]
          congr 1; field_simp
  have hprob' : (μ.real s) ^ ((p - 1) / p) ≤ (2 * S / c) ^ (p - 1) := by
    calc (μ.real s) ^ ((p - 1) / p) ≤ ((2 * S / c) ^ p) ^ ((p - 1) / p) :=
          Real.rpow_le_rpow measureReal_nonneg hprob (div_nonneg (by linarith) hp0.le)
      _ = (2 * S / c) ^ (p - 1) := by
          rw [← Real.rpow_mul (by positivity)]; congr 1; field_simp
  calc ∫ z, s.indicator (fun z => |V z * A z|) z ∂μ
      ≤ (∫ z, |V z * A z| ^ p ∂μ) ^ (1 / p) * (μ.real s) ^ ((p - 1) / p) := hho
    _ ≤ Real.sqrt 3 * S * α * (2 * S / c) ^ (p - 1) :=
        mul_le_mul hroot hprob' (Real.rpow_nonneg measureReal_nonneg _) (by positivity)

lemma min_mul_ge {α c : ℝ} (hα : 0 < α) (hc : 0 < c) {x : ℝ} (hx : 0 ≤ x) :
    min 1 (c / (2 * α)) * (x ^ 2 - x ^ 4 / (4 * α ^ 2)) ≤ min x c * x := by
  set t := min 1 (c / (2 * α)) with ht
  have ht0 : 0 ≤ t := le_min zero_le_one (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have h1 : t * min x (2 * α) ≤ min x c := by
    rcases le_total (2 * α) c with hca | hca
    · have : t = 1 := by
        rw [ht, min_eq_left]; rw [le_div_iff₀ (by positivity)]; linarith
      rw [this, one_mul]
      exact min_le_min le_rfl hca
    · have htv : t = c / (2 * α) := by
        rw [ht, min_eq_right]; rw [div_le_one (by positivity)]; exact hca
      rcases le_total x c with hxc | hxc
      · rw [min_eq_left hxc]
        calc t * min x (2 * α) ≤ 1 * x := mul_le_mul ht1 (min_le_left _ _)
              (le_min hx (by positivity)) zero_le_one
          _ = x := one_mul x
      · rw [min_eq_right hxc]
        calc t * min x (2 * α) ≤ t * (2 * α) := mul_le_mul_of_nonneg_left (min_le_right _ _) ht0
          _ = c := by rw [htv]; field_simp
  have h2 : x ^ 2 - x ^ 4 / (4 * α ^ 2) ≤ min x (2 * α) * x := by
    rcases le_total x (2 * α) with hxa | hxa
    · rw [min_eq_left hxa]
      have : 0 ≤ x ^ 4 / (4 * α ^ 2) := by positivity
      nlinarith
    · rw [min_eq_right hxa]
      have hq : x ^ 2 ≤ x ^ 4 / (4 * α ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        have : 4 * α ^ 2 ≤ x ^ 2 := by nlinarith
        nlinarith [sq_nonneg x]
      nlinarith [mul_nonneg hx hα.le]
  calc t * (x ^ 2 - x ^ 4 / (4 * α ^ 2)) ≤ t * (min x (2 * α) * x) :=
        mul_le_mul_of_nonneg_left h2 ht0
    _ = (t * min x (2 * α)) * x := by ring
    _ ≤ min x c * x := mul_le_mul_of_nonneg_right h1 hx

lemma clip_inner_small_pt {c : ℝ} (hc : 0 < c) (a v : ℝ) :
    a ^ 2 + v * a - a ^ 4 * (4 / c ^ 2) - (if c / 2 < |v| then |v * a| else 0) ≤
      clipScalar c (a + v) * a := by
  have he := excess_le hc.le a v
  have h1 : (if c / 2 < |a| then |a| else 0) * |a| ≤ a ^ 4 * (4 / c ^ 2) := by
    split_ifs with h
    · have hc2 : (c / 2) ^ 2 ≤ |a| ^ 2 := pow_le_pow_left₀ (by positivity) h.le 2
      rw [← sq, sq_abs]
      rw [sq_abs] at hc2
      have : a ^ 2 * (c / 2) ^ 2 ≤ a ^ 2 * a ^ 2 := mul_le_mul_of_nonneg_left hc2 (sq_nonneg a)
      have e : a ^ 4 * (4 / c ^ 2) = a ^ 2 * a ^ 2 / (c / 2) ^ 2 := by field_simp; ring
      rw [e, le_div_iff₀ (by positivity)]
      linarith
    · simp only [zero_mul]; positivity
  have h2 : (if c / 2 < |v| then |v| else 0) * |a| = (if c / 2 < |v| then |v * a| else 0) := by
    split_ifs <;> simp [abs_mul]
  have hprod : |((a + v) - clipScalar c (a + v)) * a| ≤
      (if c / 2 < |a| then |a| else 0) * |a| + (if c / 2 < |v| then |v| else 0) * |a| := by
    rw [abs_mul, ← add_mul]
    exact mul_le_mul_of_nonneg_right he (abs_nonneg a)
  have hlow := le_abs_self (((a + v) - clipScalar c (a + v)) * a)
  have hexp : clipScalar c (a + v) * a = (a ^ 2 + v * a) - ((a + v) - clipScalar c (a + v)) * a := by
    ring
  rw [hexp]
  rw [h2] at hprod
  linarith

theorem MomentHyp.clipped_inner_lower (H : MomentHyp μ A V α ρ S p) (hp1 : 1 < p)
    (hα : 0 ≤ α) (hρ : 0 ≤ ρ) (hS : 0 < S) (hc : 256 * S ≤ c) :
    min (α ^ 2 / 2) (c * α / 128) - α * (ρ + Real.sqrt 3 * S * (2 * S / c) ^ (p - 1)) ≤
      ∫ z, clipScalar c (A z + V z) * A z ∂μ := by
  have hc0 : 0 < c := by linarith
  obtain ⟨M, hM⟩ := H.bound
  have hψm : Measurable (fun z => clipScalar c (A z + V z) * A z) := by
    unfold clipScalar
    exact ((measurable_const.max (measurable_const.min (H.measA.add H.measV)))).mul H.measA
  have hψi : Integrable (fun z => clipScalar c (A z + V z) * A z) μ :=
    int_of_bdd hψm ⟨c * M, fun z => by
      rw [abs_mul]
      exact mul_le_mul (clip_abs_le hc0.le _) (hM z) (abs_nonneg _) hc0.le⟩
  have hA2i : Integrable (fun z => A z ^ 2) μ :=
    int_of_bdd (H.measA.pow_const 2) ⟨M ^ 2, fun z => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM z) 2⟩
  have hA4i : Integrable (fun z => A z ^ 4) μ :=
    int_of_bdd (H.measA.pow_const 4) ⟨M ^ 4, fun z => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM z) 4⟩
  have hVAa : Integrable (fun z => |V z * A z|) μ := H.cross_int.abs
  have hB0 : 0 ≤ Real.sqrt 3 * S * (2 * S / c) ^ (p - 1) := by positivity
  have hsq3 : Real.sqrt 3 ≤ 7 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  by_cases hsmall : α ≤ c / 16
  · have hg2m : Measurable (fun z => if c / 2 < |V z| then |V z * A z| else 0) :=
      Measurable.ite (measurableSet_lt measurable_const (measurable_abs_comp H.measV))
        (measurable_abs_comp (H.measV.mul H.measA)) measurable_const
    have hg2i : Integrable (fun z => if c / 2 < |V z| then |V z * A z| else 0) μ :=
      Integrable.mono' hVAa hg2m.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
        split_ifs
        · simp
        · simp only [norm_zero]; exact abs_nonneg _)
    have hlowi : Integrable (fun z => A z ^ 2 + V z * A z - A z ^ 4 * (4 / c ^ 2) -
        (if c / 2 < |V z| then |V z * A z| else 0)) μ :=
      ((hA2i.add H.cross_int).sub (hA4i.mul_const _)).sub hg2i
    have hmono := integral_mono hlowi hψi (fun z => clip_inner_small_pt hc0 (A z) (V z))
    rw [integral_sub (isub (iadd hA2i H.cross_int) (hA4i.mul_const _)) hg2i,
      integral_sub (iadd hA2i H.cross_int) (hA4i.mul_const _), integral_add hA2i H.cross_int,
      integral_mul_const, H.second] at hmono
    have htail := H.tail_cross_le hp1 hα hS hc0
    have h4 : (∫ z, A z ^ 4 ∂μ) * (4 / c ^ 2) ≤ 3 * α ^ 4 * (4 / c ^ 2) :=
      mul_le_mul_of_nonneg_right H.fourth (by positivity)
    have hα2 : α ^ 2 ≤ c ^ 2 / 256 := by
      have := pow_le_pow_left₀ hα hsmall 2; rw [div_pow] at this; linarith
    have h4' : 3 * α ^ 4 * (4 / c ^ 2) ≤ α ^ 2 * (12 / 256) := by
      have e : 3 * α ^ 4 * (4 / c ^ 2) = 12 * α ^ 2 * (α ^ 2 / c ^ 2) := by field_simp; ring
      rw [e]
      have : α ^ 2 / c ^ 2 ≤ 1 / 256 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      nlinarith [sq_nonneg α]
    have hcross := H.cross
    have hmin : min (α ^ 2 / 2) (c * α / 128) ≤ α ^ 2 / 2 := min_le_left _ _
    nlinarith [sq_nonneg α]
  · push Not at hsmall
    have hαpos : 0 < α := by linarith [hc0]
    have hpt : ∀ z, min 1 (c / (2 * α)) * (A z ^ 2 - A z ^ 4 / (4 * α ^ 2)) - |V z * A z| ≤
        clipScalar c (A z + V z) * A z := by
      intro z
      have hlip := clip_lipschitz (c := c) (A z + V z) (A z)
      rw [add_sub_cancel_left] at hlip
      have hself := clip_self_mul hc0.le (A z)
      have hmg := min_mul_ge hαpos hc0 (abs_nonneg (A z))
      have h4 : |A z| ^ 4 = A z ^ 4 := by
        rw [← abs_pow]; exact abs_of_nonneg (by positivity)
      rw [sq_abs, h4] at hmg
      have hd : clipScalar c (A z) * A z - |V z * A z| ≤ clipScalar c (A z + V z) * A z := by
        have : |(clipScalar c (A z + V z) - clipScalar c (A z)) * A z| ≤ |V z * A z| := by
          rw [abs_mul, abs_mul]; exact mul_le_mul_of_nonneg_right hlip (abs_nonneg _)
        have := neg_abs_le ((clipScalar c (A z + V z) - clipScalar c (A z)) * A z)
        nlinarith
      rw [hself] at hd
      linarith
    have hlowi : Integrable (fun z => min 1 (c / (2 * α)) * (A z ^ 2 - A z ^ 4 / (4 * α ^ 2)) -
        |V z * A z|) μ := ((hA2i.sub (hA4i.div_const _)).const_mul _).sub hVAa
    have hmono := integral_mono hlowi hψi hpt
    rw [integral_sub ((isub hA2i (hA4i.div_const _)).const_mul _) hVAa, integral_const_mul,
      integral_sub hA2i (hA4i.div_const _), integral_div, H.second] at hmono
    have habs := H.abs_cross_le hp1 hα hS.le
    set t := min 1 (c / (2 * α)) with ht
    have ht0 : 0 ≤ t := le_min zero_le_one (by positivity)
    have h4 : (∫ z, A z ^ 4 ∂μ) / (4 * α ^ 2) ≤ 3 * α ^ 2 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [H.fourth]
    have hmain : c * α / 64 ≤ t * (α ^ 2 / 4) := by
      rcases le_total 1 (c / (2 * α)) with h | h
      · rw [ht, min_eq_left h]; nlinarith
      · rw [ht, min_eq_right h]
        have e : c / (2 * α) * (α ^ 2 / 4) = c * α / 8 := by field_simp; ring
        rw [e]; nlinarith
    have hlow1 : t * (α ^ 2 / 4) ≤ t * (α ^ 2 - (∫ z, A z ^ 4 ∂μ) / (4 * α ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) ht0
    have hS3 : Real.sqrt 3 * S * α ≤ c * α / 128 := by
      have : Real.sqrt 3 * S ≤ c / 128 := by nlinarith [Real.sqrt_nonneg 3]
      nlinarith
    have hmin : min (α ^ 2 / 2) (c * α / 128) ≤ c * α / 128 := min_le_right _ _
    have hαB : 0 ≤ α * (ρ + Real.sqrt 3 * S * (2 * S / c) ^ (p - 1)) := by positivity
    linarith

theorem MomentHyp.clipped_sq_upper (H : MomentHyp μ A V α ρ S p) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (hc : 0 < c) :
    Integrable (fun z => clipScalar c (A z + V z) ^ 2) μ ∧
    ∫ z, clipScalar c (A z + V z) ^ 2 ∂μ ≤ c ^ 2 ∧
      ∫ z, clipScalar c (A z + V z) ^ 2 ∂μ ≤ 2 * α ^ 2 + 2 * (c ^ (2 - p) * S ^ p) := by
  obtain ⟨M, hM⟩ := H.bound
  have hψm : Measurable (fun z => clipScalar c (A z + V z) ^ 2) := by
    unfold clipScalar
    exact ((measurable_const.max (measurable_const.min (H.measA.add H.measV)))).pow_const 2
  have hψi : Integrable (fun z => clipScalar c (A z + V z) ^ 2) μ :=
    int_of_bdd hψm ⟨c ^ 2, fun z => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (clip_abs_le hc.le _) 2⟩
  have hA2i : Integrable (fun z => A z ^ 2) μ :=
    int_of_bdd (H.measA.pow_const 2) ⟨M ^ 2, fun z => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM z) 2⟩
  refine ⟨hψi, ?_, ?_⟩
  · have := integral_mono hψi (integrable_const (c ^ 2)) (fun z => (clip_sq_le_min hc.le _).trans
      (min_le_left _ _))
    simpa using this
  · have hpt : ∀ z, clipScalar c (A z + V z) ^ 2 ≤ 2 * A z ^ 2 + 2 * (c ^ (2 - p) * |V z| ^ p) := by
      intro z
      have h1 := clip_sq_le_min hc.le (A z + V z)
      have hmv : min (c ^ 2) (V z ^ 2) ≤ c ^ (2 - p) * |V z| ^ p := by
        rcases le_total |V z| c with hv | hv
        · refine (min_le_right _ _).trans ?_
          rw [← sq_abs]
          have e : |V z| ^ 2 = |V z| ^ (2 - p) * |V z| ^ p := by
            rw [← Real.rpow_natCast, ← Real.rpow_add' (abs_nonneg _) (by norm_num)]; norm_num
          rw [e]
          exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (abs_nonneg _) hv (by linarith))
            (by positivity)
        · refine (min_le_left _ _).trans ?_
          have e : c ^ 2 = c ^ (2 - p) * c ^ p := by
            rw [← Real.rpow_natCast, ← Real.rpow_add' hc.le (by norm_num)]; norm_num
          rw [e]
          exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hc.le hv (by linarith))
            (by positivity)
      have hsplit : min (c ^ 2) ((A z + V z) ^ 2) ≤ 2 * A z ^ 2 + 2 * min (c ^ 2) (V z ^ 2) := by
        rcases le_total (c ^ 2) (V z ^ 2) with h | h
        · rw [min_eq_left h]
          refine (min_le_left _ _).trans ?_
          nlinarith [sq_nonneg (A z), sq_nonneg c]
        · rw [min_eq_right h]
          refine (min_le_right _ _).trans ?_
          nlinarith [sq_nonneg (A z - V z)]
      linarith
    have hboundi : Integrable (fun z => 2 * A z ^ 2 + 2 * (c ^ (2 - p) * |V z| ^ p)) μ :=
      (hA2i.const_mul 2).add ((H.vp_int.const_mul _).const_mul 2)
    have hm := integral_mono hψi hboundi hpt
    rw [integral_add (hA2i.const_mul 2) ((H.vp_int.const_mul _).const_mul 2), integral_const_mul,
      integral_const_mul, integral_const_mul, H.second] at hm
    have : c ^ (2 - p) * ∫ z, |V z| ^ p ∂μ ≤ c ^ (2 - p) * S ^ p :=
      mul_le_mul_of_nonneg_left H.vp (by positivity)
    linarith

end Descent

end LongTails.Proofs.ClippedScalarDescent
