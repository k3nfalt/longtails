import LongTails.Proofs.GdConvex
import LongTails.Proofs.LinearDecaySgdStep
import LongTails.Setups.SampledCompositeSmoothConvex
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.SampledComposite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma nonneg_of_forall_small {B C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ B + t * C) : 0 ≤ B := by
  by_contra hB'
  have hB : B < 0 := lt_of_not_ge hB'
  set t : ℝ := min 1 (-B / (2 * (|C| + 1))) with ht
  have hpos : 0 < -B / (2 * (|C| + 1)) := by
    apply div_pos (by linarith) (by positivity)
  have ht0 : 0 < t := lt_min one_pos hpos
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ -B / (2 * (|C| + 1)) := min_le_right _ _
  have hC : t * C ≤ t * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) ht0.le
  have h3 : t * |C| ≤ -B / 2 := by
    have h4 : t * (|C| + 1) ≤ -B / 2 := by
      calc t * (|C| + 1) ≤ -B / (2 * (|C| + 1)) * (|C| + 1) :=
            mul_le_mul_of_nonneg_right ht2 (by positivity)
        _ = -B / 2 := by field_simp
    nlinarith [abs_nonneg C]
  have := h t ht0 ht1
  linarith

noncomputable def proxObj (ψ : E → ℝ) (a : ℝ) (z g u : E) : ℝ :=
  ‖u - z‖ ^ 2 / (2 * a) + ⟪g, u - z⟫ + ψ u

lemma prox_three_point {ψ : E → ℝ} {Q : Set E} (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ) {a : ℝ}
    (ha : 0 < a) {z g v : E} (hv : v ∈ Q) (hmin : IsMinOn (proxObj ψ a z g) Q v) {u : E} (hu : u ∈ Q) :
    ψ v + ⟪g, v - u⟫ ≤ ψ u + (‖u - z‖ ^ 2 - ‖u - v‖ ^ 2 - ‖v - z‖ ^ 2) / (2 * a) := by
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ (⟪v - z, u - v⟫ / a + ⟪g, u - v⟫ + ψ u - ψ v) + t * (‖u - v‖ ^ 2 / (2 * a)) := by
    intro t ht0 ht1
    have hw : (1 - t) • v + t • u ∈ Q := hQ hv hu (by linarith) ht0.le (by ring)
    have hm := hmin hw
    change proxObj ψ a z g v ≤ proxObj ψ a z g ((1 - t) • v + t • u) at hm
    have hψw : ψ ((1 - t) • v + t • u) ≤ (1 - t) * ψ v + t * ψ u := by
      have := hψ.2 hv hu (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
      simpa using this
    have hwz : (1 - t) • v + t • u - z = (v - z) + t • (u - v) := by module
    have hnorm : ‖(v - z) + t • (u - v)‖ ^ 2 =
        ‖v - z‖ ^ 2 + 2 * t * ⟪v - z, u - v⟫ + t ^ 2 * ‖u - v‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, abs_of_pos ht0]
      ring
    have hinner : ⟪g, (v - z) + t • (u - v)⟫ = ⟪g, v - z⟫ + t * ⟪g, u - v⟫ := by
      rw [inner_add_right, real_inner_smul_right]
    simp only [proxObj, hwz, hnorm, hinner] at hm
    have h2 : 0 ≤ t * ((⟪v - z, u - v⟫ / a + ⟪g, u - v⟫ + ψ u - ψ v) +
        t * (‖u - v‖ ^ 2 / (2 * a))) := by
      have e : t * ((⟪v - z, u - v⟫ / a + ⟪g, u - v⟫ + ψ u - ψ v) +
          t * (‖u - v‖ ^ 2 / (2 * a))) =
          (‖v - z‖ ^ 2 + 2 * t * ⟪v - z, u - v⟫ + t ^ 2 * ‖u - v‖ ^ 2) / (2 * a) +
            (⟪g, v - z⟫ + t * ⟪g, u - v⟫) + ((1 - t) * ψ v + t * ψ u) -
            (‖v - z‖ ^ 2 / (2 * a) + ⟪g, v - z⟫ + ψ v) := by
        field_simp
        ring
      rw [e]
      linarith
    exact (mul_nonneg_iff_of_pos_left ht0).mp h2
  have h0 := nonneg_of_forall_small key
  have hid : ⟪v - z, u - v⟫ = (‖u - z‖ ^ 2 - ‖u - v‖ ^ 2 - ‖v - z‖ ^ 2) / 2 := by
    have : u - z = (u - v) + (v - z) := by abel
    rw [this, norm_add_sq_real, real_inner_comm]
    ring
  rw [hid] at h0
  have hg : ⟪g, v - u⟫ = -⟪g, u - v⟫ := by rw [← inner_neg_right, neg_sub]
  rw [hg]
  have e2 : (‖u - z‖ ^ 2 - ‖u - v‖ ^ 2 - ‖v - z‖ ^ 2) / 2 / a =
      (‖u - z‖ ^ 2 - ‖u - v‖ ^ 2 - ‖v - z‖ ^ 2) / (2 * a) := by
    field_simp
  linarith

lemma prox_nonexpansive {ψ : E → ℝ} {Q : Set E} (hQ : Convex ℝ Q) (hψ : ConvexOn ℝ Q ψ) {a : ℝ}
    (ha : 0 < a) {z g v z' g' v' : E} (hv : v ∈ Q) (hmin : IsMinOn (proxObj ψ a z g) Q v)
    (hv' : v' ∈ Q) (hmin' : IsMinOn (proxObj ψ a z' g') Q v') :
    ‖v - v'‖ ≤ ‖(z - a • g) - (z' - a • g')‖ := by
  have h1 := prox_three_point hQ hψ ha hv hmin hv'
  have h2 := prox_three_point hQ hψ ha hv' hmin' hv
  have hsum : a * ⟪g - g', v - v'⟫ ≤ ⟪z - z', v - v'⟫ - ‖v - v'‖ ^ 2 := by
    have e1 : ‖v' - z‖ ^ 2 - ‖v - z‖ ^ 2 + (‖v - z'‖ ^ 2 - ‖v' - z'‖ ^ 2) =
        2 * ⟪z' - z, v' - v⟫ := by
      rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, inner_sub_left,
        inner_sub_right, inner_sub_right, real_inner_comm z v', real_inner_comm z v,
        real_inner_comm z' v', real_inner_comm z' v]
      ring
    have hgg : ⟪g, v - v'⟫ + ⟪g', v' - v⟫ = ⟪g - g', v - v'⟫ := by
      rw [inner_sub_left]
      have : ⟪g', v' - v⟫ = -⟪g', v - v'⟫ := by rw [← inner_neg_right, neg_sub]
      rw [this]; ring
    have hzz : ⟪z' - z, v' - v⟫ = ⟪z - z', v - v'⟫ := by
      rw [← neg_sub z z', ← neg_sub v v', inner_neg_left, inner_neg_right, neg_neg]
    have hvv : ‖v' - v‖ = ‖v - v'‖ := norm_sub_rev _ _
    have hsum' : ⟪g, v - v'⟫ + ⟪g', v' - v⟫ ≤
        (‖v' - z‖ ^ 2 - ‖v - z‖ ^ 2 + (‖v - z'‖ ^ 2 - ‖v' - z'‖ ^ 2) - 2 * ‖v - v'‖ ^ 2) /
          (2 * a) := by
      rw [hvv] at h1
      have hadd := add_le_add h1 h2
      have e : ψ v' + (‖v' - z‖ ^ 2 - ‖v - v'‖ ^ 2 - ‖v - z‖ ^ 2) / (2 * a) +
          (ψ v + (‖v - z'‖ ^ 2 - ‖v - v'‖ ^ 2 - ‖v' - z'‖ ^ 2) / (2 * a)) =
          ψ v + ψ v' + (‖v' - z‖ ^ 2 - ‖v - z‖ ^ 2 + (‖v - z'‖ ^ 2 - ‖v' - z'‖ ^ 2) -
            2 * ‖v - v'‖ ^ 2) / (2 * a) := by
        field_simp
        ring
      linarith
    have key : a * (⟪g, v - v'⟫ + ⟪g', v' - v⟫) ≤
        (‖v' - z‖ ^ 2 - ‖v - z‖ ^ 2 + (‖v - z'‖ ^ 2 - ‖v' - z'‖ ^ 2)) / 2 - ‖v - v'‖ ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left hsum' ha.le
      have e : a * ((‖v' - z‖ ^ 2 - ‖v - z‖ ^ 2 + (‖v - z'‖ ^ 2 - ‖v' - z'‖ ^ 2) -
          2 * ‖v - v'‖ ^ 2) / (2 * a)) =
          (‖v' - z‖ ^ 2 - ‖v - z‖ ^ 2 + (‖v - z'‖ ^ 2 - ‖v' - z'‖ ^ 2)) / 2 - ‖v - v'‖ ^ 2 := by
        field_simp
      linarith
    rw [hgg, e1, hzz] at key
    linarith
  have hcs : ⟪(z - a • g) - (z' - a • g'), v - v'⟫ ≤ ‖(z - a • g) - (z' - a • g')‖ * ‖v - v'‖ :=
    real_inner_le_norm _ _
  have hexp : ⟪(z - a • g) - (z' - a • g'), v - v'⟫ = ⟪z - z', v - v'⟫ - a * ⟪g - g', v - v'⟫ := by
    have : (z - a • g) - (z' - a • g') = (z - z') - a • (g - g') := by module
    rw [this, inner_sub_left, real_inner_smul_left]
  have hsq : ‖v - v'‖ ^ 2 ≤ ‖(z - a • g) - (z' - a • g')‖ * ‖v - v'‖ := by linarith
  by_cases hz : ‖v - v'‖ = 0
  · rw [hz]; exact norm_nonneg _
  · have hpos : 0 < ‖v - v'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {Ξ : Type*} [MeasurableSpace Ξ]

structure Hyp (p : Measure Ξ) (F : Ξ → E → ℝ) (G : Ξ → E → E) (ψ : E → ℝ) (Q : Set E)
    (prox : ℝ → E → E → E) (L σ : ℝ) (xstar : E) : Prop where
  pos : 0 < L
  meas : Measurable (Function.uncurry G)
  convex : ∀ ξ, ConvexOn ℝ univ (F ξ)
  grad : ∀ ξ x, HasGradientAt (F ξ) (G ξ x) x
  lip : ∀ ξ x y, ‖G ξ x - G ξ y‖ ≤ L * ‖x - y‖
  int : ∀ x, Integrable (fun ξ => F ξ x) p
  convQ : Convex ℝ Q
  closedQ : IsClosed Q
  convψ : ConvexOn ℝ Q ψ
  lscψ : LowerSemicontinuous ψ
  proxQ : ∀ a, 0 < a → ∀ z g, prox a z g ∈ Q ∧ IsMinOn (proxObj ψ a z g) Q (prox a z g)
  starQ : xstar ∈ Q
  min : IsMinOn (fun x => (∫ ξ, F ξ x ∂p) + ψ x) Q xstar
  grad_int : Integrable (fun ξ => G ξ xstar) p
  var_int : Integrable (fun ξ => ‖G ξ xstar - ∫ ζ, G ζ xstar ∂p‖ ^ 2) p
  var : ∫ ξ, ‖G ξ xstar - ∫ ζ, G ζ xstar ∂p‖ ^ 2 ∂p ≤ σ ^ 2

noncomputable def obj (p : Measure Ξ) (F : Ξ → E → ℝ) (x : E) : ℝ := ∫ ξ, F ξ x ∂p

noncomputable def mean (p : Measure Ξ) (G : Ξ → E → E) (x : E) : E := ∫ ξ, G ξ x ∂p

noncomputable def total (p : Measure Ξ) (F : Ξ → E → ℝ) (ψ : E → ℝ) (x : E) : ℝ := obj p F x + ψ x

namespace Hyp

variable {p : Measure Ξ} [IsProbabilityMeasure p] {F : Ξ → E → ℝ} {G : Ξ → E → E} {ψ : E → ℝ}
  {Q : Set E} {prox : ℝ → E → E → E} {L σ : ℝ} {xstar : E}

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma grad_meas (h : Hyp p F G ψ Q prox L σ xstar) (x : E) : Measurable (fun ξ => G ξ x) :=
  h.meas.comp (measurable_id.prodMk measurable_const)

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma grad_sq_le (h : Hyp p F G ψ Q prox L σ xstar) (ξ : Ξ) (x : E) :
    ‖G ξ x‖ ^ 2 ≤ 2 * ‖G ξ xstar‖ ^ 2 + 2 * L ^ 2 * ‖x - xstar‖ ^ 2 := by
  have h1 : ‖G ξ x‖ ≤ ‖G ξ xstar‖ + L * ‖x - xstar‖ := by
    calc ‖G ξ x‖ = ‖G ξ xstar + (G ξ x - G ξ xstar)‖ := by congr 1; abel
      _ ≤ ‖G ξ xstar‖ + ‖G ξ x - G ξ xstar‖ := norm_add_le _ _
      _ ≤ _ := by linarith [h.lip ξ x xstar]
  have h2 : 0 ≤ L * ‖x - xstar‖ := mul_nonneg h.pos.le (norm_nonneg _)
  nlinarith [sq_nonneg (‖G ξ xstar‖ - L * ‖x - xstar‖), norm_nonneg (G ξ x)]

omit [SecondCountableTopology E] in
lemma sq_int_star (h : Hyp p F G ψ Q prox L σ xstar) :
    Integrable (fun ξ => ‖G ξ xstar‖ ^ 2) p := by
  refine Integrable.mono' ((h.var_int.const_mul 2).add
    (integrable_const (2 * ‖mean p G xstar‖ ^ 2)))
    ((h.grad_meas xstar).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 : ‖G ξ xstar‖ ≤ ‖G ξ xstar - mean p G xstar‖ + ‖mean p G xstar‖ := by
    calc ‖G ξ xstar‖ = ‖(G ξ xstar - mean p G xstar) + mean p G xstar‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  change ‖G ξ xstar‖ ^ 2 ≤ 2 * ‖G ξ xstar - mean p G xstar‖ ^ 2 + 2 * ‖mean p G xstar‖ ^ 2
  nlinarith [sq_nonneg (‖G ξ xstar - mean p G xstar‖ - ‖mean p G xstar‖), norm_nonneg (G ξ xstar)]

omit [SecondCountableTopology E] in
lemma int_grad_sq (h : Hyp p F G ψ Q prox L σ xstar) (x : E) :
    Integrable (fun ξ => ‖G ξ x‖ ^ 2) p := by
  refine Integrable.mono' ((h.sq_int_star.const_mul 2).add
    (integrable_const (2 * L ^ 2 * ‖x - xstar‖ ^ 2)))
    ((h.grad_meas x).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact h.grad_sq_le ξ x

lemma int_grad (h : Hyp p F G ψ Q prox L σ xstar) (x : E) : Integrable (fun ξ => G ξ x) p := by
  have hb : Integrable (fun ξ => 1 + ‖G ξ x‖ ^ 2) p := (integrable_const (1 : ℝ)).add (h.int_grad_sq x)
  refine Integrable.mono' hb (h.grad_meas x).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => ?_))
  nlinarith [sq_nonneg (‖G ξ x‖ - 1), norm_nonneg (G ξ x)]

lemma inner_integral (h : Hyp p F G ψ Q prox L σ xstar) (a v : E) :
    Integrable (fun ξ => ⟪v, G ξ a⟫) p ∧ ∫ ξ, ⟪v, G ξ a⟫ ∂p = ⟪v, mean p G a⟫ :=
  ⟨(h.int_grad a).const_inner v, integral_inner (h.int_grad a) v⟩

lemma obj_upper (h : Hyp p F G ψ Q prox L σ xstar) (a b : E) :
    obj p F b ≤ obj p F a + ⟪mean p G a, b - a⟫ + L / 2 * ‖b - a‖ ^ 2 := by
  obtain ⟨hii, hie⟩ := h.inner_integral a (b - a)
  have hi1 : Integrable (fun ξ => F ξ a + ⟪b - a, G ξ a⟫) p := (h.int a).add hii
  have hi : Integrable (fun ξ => F ξ a + ⟪b - a, G ξ a⟫ + L / 2 * ‖b - a‖ ^ 2) p :=
    hi1.add (integrable_const _)
  have hle := integral_mono (h.int b) hi (fun ξ => by
    have := Gradient.smooth_upper_bound (h.grad ξ) (h.lip ξ) a b
    rw [real_inner_comm] at this
    exact this)
  have e1 : ∫ ξ, (F ξ a + ⟪b - a, G ξ a⟫ + L / 2 * ‖b - a‖ ^ 2) ∂p =
      obj p F a + ⟪b - a, mean p G a⟫ + L / 2 * ‖b - a‖ ^ 2 := by
    rw [integral_add hi1 (integrable_const _), integral_add (h.int a) hii, hie]
    simp [obj]
  rw [e1, real_inner_comm] at hle
  exact hle

lemma obj_lower (h : Hyp p F G ψ Q prox L σ xstar) (a b : E) :
    obj p F a + ⟪mean p G a, b - a⟫ ≤ obj p F b := by
  obtain ⟨hii, hie⟩ := h.inner_integral a (b - a)
  have hi1 : Integrable (fun ξ => F ξ a + ⟪b - a, G ξ a⟫) p := (h.int a).add hii
  have hle := integral_mono hi1 (h.int b) (fun ξ => by
    have := Gradient.convex_support (h.convex ξ) (h.grad ξ) a b
    rw [real_inner_comm] at this
    show F ξ a + ⟪b - a, G ξ a⟫ ≤ F ξ b
    linarith)
  have e1 : ∫ ξ, (F ξ a + ⟪b - a, G ξ a⟫) ∂p = obj p F a + ⟪b - a, mean p G a⟫ := by
    rw [integral_add (h.int a) hii, hie]
    rfl
  rw [e1, real_inner_comm] at hle
  exact hle

lemma obj_continuous (h : Hyp p F G ψ Q prox L σ xstar) : Continuous (obj p F) := by
  rw [continuous_iff_continuousAt]
  intro a
  have hL := h.pos
  have hb : ∀ b, |obj p F b - obj p F a| ≤ ‖mean p G a‖ * ‖b - a‖ + L / 2 * ‖b - a‖ ^ 2 := by
    intro b
    have hu := h.obj_upper a b
    have hl := h.obj_lower a b
    have hc := abs_real_inner_le_norm (mean p G a) (b - a)
    rw [abs_le]
    constructor
    · have := neg_abs_le ⟪mean p G a, b - a⟫
      nlinarith [sq_nonneg ‖b - a‖]
    · have := le_abs_self ⟪mean p G a, b - a⟫
      linarith
  have ht : Filter.Tendsto (fun b => ‖mean p G a‖ * ‖b - a‖ + L / 2 * ‖b - a‖ ^ 2)
      (nhds a) (nhds 0) := by
    have h1 : Filter.Tendsto (fun b => ‖b - a‖) (nhds a) (nhds 0) := tendsto_norm_sub_self a
    have := (h1.const_mul ‖mean p G a‖).add ((h1.pow 2).const_mul (L / 2))
    simpa using this
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun b => norm_nonneg _) (fun b => by
    rw [Real.norm_eq_abs]; exact hb b) ht

lemma total_measurable (h : Hyp p F G ψ Q prox L σ xstar) : Measurable (total p F ψ) :=
  h.obj_continuous.measurable.add h.lscψ.measurable

lemma vi (h : Hyp p F G ψ Q prox L σ xstar) {y : E} (hy : y ∈ Q) :
    0 ≤ ψ y - ψ xstar + ⟪mean p G xstar, y - xstar⟫ := by
  have hL := h.pos
  apply nonneg_of_forall_small (C := L / 2 * ‖y - xstar‖ ^ 2)
  intro t ht0 ht1
  have hw : (1 - t) • xstar + t • y ∈ Q := h.convQ h.starQ hy (by linarith) ht0.le (by ring)
  have hm := h.min hw
  change obj p F xstar + ψ xstar ≤ obj p F ((1 - t) • xstar + t • y) + ψ ((1 - t) • xstar + t • y)
    at hm
  have hψw : ψ ((1 - t) • xstar + t • y) ≤ (1 - t) * ψ xstar + t * ψ y := by
    have := h.convψ.2 h.starQ hy (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    simpa using this
  have hup := h.obj_upper xstar ((1 - t) • xstar + t • y)
  have hdiff : (1 - t) • xstar + t • y - xstar = t • (y - xstar) := by module
  rw [hdiff, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hup
  have h2 : 0 ≤ t * ((ψ y - ψ xstar + ⟪mean p G xstar, y - xstar⟫) +
      t * (L / 2 * ‖y - xstar‖ ^ 2)) := by nlinarith
  exact (mul_nonneg_iff_of_pos_left ht0).mp h2

lemma gap_transfer (h : Hyp p F G ψ Q prox L σ xstar) {x : E} (hx : x ∈ Q) :
    obj p F x - obj p F xstar - ⟪mean p G xstar, x - xstar⟫ ≤
      total p F ψ x - total p F ψ xstar := by
  have := h.vi hx
  simp only [total]
  linarith

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma total_ge (h : Hyp p F G ψ Q prox L σ xstar) {x : E} (hx : x ∈ Q) :
    total p F ψ xstar ≤ total p F ψ x := h.min hx

lemma dev_le_star (h : Hyp p F G ψ Q prox L σ xstar) (x : E) :
    ∫ ξ, ‖G ξ x - mean p G x‖ ^ 2 ∂p ≤ ∫ ξ, ‖G ξ x - mean p G xstar‖ ^ 2 ∂p := by
  have hgi := h.int_grad x
  have hgs := h.int_grad_sq x
  set m := mean p G x
  set c := mean p G xstar
  have hexp : ∀ ξ, ‖G ξ x - c‖ ^ 2 = ‖G ξ x - m‖ ^ 2 + 2 * ⟪m - c, G ξ x - m⟫ + ‖m - c‖ ^ 2 := by
    intro ξ
    have : G ξ x - c = (G ξ x - m) + (m - c) := by abel
    rw [this, norm_add_sq_real, real_inner_comm]
  have hi1 : Integrable (fun ξ => ‖G ξ x - m‖ ^ 2) p := by
    have hb : Integrable (fun ξ => 2 * ‖G ξ x‖ ^ 2 + 2 * ‖m‖ ^ 2) p :=
      (hgs.const_mul 2).add (integrable_const _)
    refine Integrable.mono' hb (((h.grad_meas x).sub measurable_const).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := norm_sub_le (G ξ x) m
    nlinarith [sq_nonneg (‖G ξ x‖ - ‖m‖), norm_nonneg (G ξ x), norm_nonneg m, norm_nonneg (G ξ x - m)]
  have hint : Integrable (fun ξ => G ξ x - m) p := hgi.sub (integrable_const _)
  have hi2 : Integrable (fun ξ => 2 * ⟪m - c, G ξ x - m⟫) p := (hint.const_inner (m - c)).const_mul 2
  have hzero : ∫ ξ, 2 * ⟪m - c, G ξ x - m⟫ ∂p = 0 := by
    rw [integral_const_mul, integral_inner hint, integral_sub hgi (integrable_const _), integral_const,
      probReal_univ, one_smul]
    simp [m, mean]
  have hi12 : Integrable (fun ξ => ‖G ξ x - m‖ ^ 2 + 2 * ⟪m - c, G ξ x - m⟫) p := hi1.add hi2
  have hi3 : Integrable (fun ξ => ‖G ξ x - c‖ ^ 2) p := by
    simp_rw [hexp]; exact hi12.add (integrable_const _)
  calc ∫ ξ, ‖G ξ x - m‖ ^ 2 ∂p ≤ ∫ ξ, ‖G ξ x - m‖ ^ 2 ∂p + ‖m - c‖ ^ 2 := by
        linarith [sq_nonneg ‖m - c‖]
    _ = ∫ ξ, ‖G ξ x - c‖ ^ 2 ∂p := by
        simp_rw [hexp]
        rw [integral_add hi12 (integrable_const _), integral_add hi1 hi2, hzero,
          integral_const, probReal_univ, one_smul]
        ring

lemma dev_integral (h : Hyp p F G ψ Q prox L σ xstar) {x : E} (hx : x ∈ Q) :
    ∫ ξ, ‖G ξ x - mean p G x‖ ^ 2 ∂p ≤
      4 * L * (total p F ψ x - total p F ψ xstar) + 2 * σ ^ 2 := by
  have hL := h.pos
  set c := mean p G xstar
  have hpt : ∀ ξ, ‖G ξ x - c‖ ^ 2 ≤
      4 * L * (F ξ x - F ξ xstar - ⟪x - xstar, G ξ xstar⟫) + 2 * ‖G ξ xstar - c‖ ^ 2 := by
    intro ξ
    have hc := SampledConvex.cocoercive h.pos (h.convex ξ) (h.grad ξ) (h.lip ξ) x xstar
    rw [real_inner_comm] at hc
    have h1 : ‖G ξ x - c‖ ^ 2 ≤ 2 * ‖G ξ x - G ξ xstar‖ ^ 2 + 2 * ‖G ξ xstar - c‖ ^ 2 := by
      have := norm_add_le (G ξ x - G ξ xstar) (G ξ xstar - c)
      rw [show G ξ x - G ξ xstar + (G ξ xstar - c) = G ξ x - c by abel] at this
      nlinarith [sq_nonneg (‖G ξ x - G ξ xstar‖ - ‖G ξ xstar - c‖), norm_nonneg (G ξ x - c),
        norm_nonneg (G ξ x - G ξ xstar), norm_nonneg (G ξ xstar - c)]
    linarith
  obtain ⟨hii, hie⟩ := h.inner_integral xstar (x - xstar)
  have hi0 : Integrable (fun ξ => F ξ x - F ξ xstar) p := (h.int x).sub (h.int xstar)
  have hi1 : Integrable (fun ξ => F ξ x - F ξ xstar - ⟪x - xstar, G ξ xstar⟫) p := hi0.sub hii
  have hi1' : Integrable (fun ξ => 4 * L * (F ξ x - F ξ xstar - ⟪x - xstar, G ξ xstar⟫)) p :=
    hi1.const_mul _
  have hi2 : Integrable (fun ξ => 2 * ‖G ξ xstar - c‖ ^ 2) p := h.var_int.const_mul _
  have hi3 : Integrable (fun ξ => 4 * L * (F ξ x - F ξ xstar - ⟪x - xstar, G ξ xstar⟫) +
      2 * ‖G ξ xstar - c‖ ^ 2) p := hi1'.add hi2
  have hic : Integrable (fun ξ => ‖G ξ x - c‖ ^ 2) p := by
    have hb : Integrable (fun ξ => 2 * ‖G ξ x‖ ^ 2 + 2 * ‖c‖ ^ 2) p :=
      ((h.int_grad_sq x).const_mul 2).add (integrable_const _)
    refine Integrable.mono' hb (((h.grad_meas x).sub measurable_const).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := norm_sub_le (G ξ x) c
    nlinarith [sq_nonneg (‖G ξ x‖ - ‖c‖), norm_nonneg (G ξ x), norm_nonneg c, norm_nonneg (G ξ x - c)]
  have hle := integral_mono hic hi3 hpt
  have e1 : ∫ ξ, (4 * L * (F ξ x - F ξ xstar - ⟪x - xstar, G ξ xstar⟫) + 2 * ‖G ξ xstar - c‖ ^ 2) ∂p =
      4 * L * (obj p F x - obj p F xstar - ⟪x - xstar, mean p G xstar⟫) +
        2 * ∫ ξ, ‖G ξ xstar - c‖ ^ 2 ∂p := by
    rw [integral_add hi1' hi2, integral_const_mul, integral_const_mul, integral_sub hi0 hii,
      integral_sub (h.int x) (h.int xstar), hie]
    rfl
  rw [e1] at hle
  have hvar := h.var
  have hgt := h.gap_transfer hx
  rw [real_inner_comm] at hgt
  have hdev := h.dev_le_star x
  change ∫ ξ, ‖G ξ xstar - c‖ ^ 2 ∂p ≤ σ ^ 2 at hvar
  nlinarith

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma prox_mem (h : Hyp p F G ψ Q prox L σ xstar) {a : ℝ} (ha : 0 < a) (z g : E) :
    prox a z g ∈ Q := (h.proxQ a ha z g).1

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma prox_lipschitz (h : Hyp p F G ψ Q prox L σ xstar) {a : ℝ} (ha : 0 < a) (z g z' g' : E) :
    ‖prox a z g - prox a z' g'‖ ≤ ‖(z - a • g) - (z' - a • g')‖ :=
  prox_nonexpansive h.convQ h.convψ ha (h.proxQ a ha z g).1 (h.proxQ a ha z g).2
    (h.proxQ a ha z' g').1 (h.proxQ a ha z' g').2

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma prox_continuous (h : Hyp p F G ψ Q prox L σ xstar) {a : ℝ} (ha : 0 < a) :
    Continuous (fun zg : E × E => prox a zg.1 zg.2) := by
  have hlip : LipschitzWith (⟨1 + a, by positivity⟩ : NNReal) (fun zg : E × E => prox a zg.1 zg.2) := by
    apply LipschitzWith.of_dist_le_mul
    rintro ⟨z, g⟩ ⟨z', g'⟩
    rw [dist_eq_norm]
    calc ‖prox a z g - prox a z' g'‖ ≤ ‖(z - a • g) - (z' - a • g')‖ := h.prox_lipschitz ha z g z' g'
      _ = ‖(z - z') - a • (g - g')‖ := by congr 1; module
      _ ≤ ‖z - z'‖ + a * ‖g - g'‖ := by
          calc ‖(z - z') - a • (g - g')‖ ≤ ‖z - z'‖ + ‖a • (g - g')‖ := norm_sub_le _ _
            _ = ‖z - z'‖ + a * ‖g - g'‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ (1 + a) * dist (z, g) (z', g') := by
          have h1 : ‖z - z'‖ ≤ dist (z, g) (z', g') := by
            rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]; exact le_max_left _ _
          have h2 : ‖g - g'‖ ≤ dist (z, g) (z', g') := by
            rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]; exact le_max_right _ _
          nlinarith [dist_nonneg (x := (z, g)) (y := (z', g'))]
  exact hlip.continuous

omit [IsProbabilityMeasure p] in
lemma prox_measurable (h : Hyp p F G ψ Q prox L σ xstar) {a : ℝ} (ha : 0 < a) :
    Measurable (fun zg : E × E => prox a zg.1 zg.2) :=
  (h.prox_continuous ha).measurable

lemma one_step_pointwise (h : Hyp p F G ψ Q prox L σ xstar) {x y : E} (hy : y ∈ Q)
    {η : ℝ} (hη : 0 < η) (hLη : L * η ≤ 1 / 2) (ξ : Ξ) :
    total p F ψ (prox η x (G ξ x)) ≤ total p F ψ y +
      (‖x - y‖ ^ 2 - ‖prox η x (G ξ x) - y‖ ^ 2) / (2 * η) + ⟪mean p G x - G ξ x, x - y⟫ +
        η / (2 * (1 - L * η)) * ‖mean p G x - G ξ x‖ ^ 2 := by
  have hL := h.pos
  set m := mean p G x
  have hθ : 0 < 1 - L * η := by linarith
  set v := prox η x (G ξ x)
  have hvQ : v ∈ Q := h.prox_mem hη x (G ξ x)
  have htp := prox_three_point h.convQ h.convψ hη hvQ (h.proxQ η hη x (G ξ x)).2 hy
  have hup := h.obj_upper x v
  have hlo := h.obj_lower x y
  have hf : obj p F v ≤ obj p F y + ⟪m, v - y⟫ + L / 2 * ‖v - x‖ ^ 2 := by
    have e : ⟪m, v - x⟫ = ⟪m, v - y⟫ - ⟪m, x - y⟫ := by
      rw [← inner_sub_right]; congr 1; abel
    have e2 : ⟪m, y - x⟫ = -⟪m, x - y⟫ := by rw [← inner_neg_right, neg_sub]
    rw [e] at hup; rw [e2] at hlo
    linarith
  have hyoung : ⟪m - G ξ x, v - x⟫ ≤
      η / (2 * (1 - L * η)) * ‖m - G ξ x‖ ^ 2 + (1 - L * η) / (2 * η) * ‖v - x‖ ^ 2 := by
    have hcs := real_inner_le_norm (m - G ξ x) (v - x)
    have hθη : 0 < η / (1 - L * η) := by positivity
    have hamgm : ‖m - G ξ x‖ * ‖v - x‖ ≤
        η / (2 * (1 - L * η)) * ‖m - G ξ x‖ ^ 2 + (1 - L * η) / (2 * η) * ‖v - x‖ ^ 2 := by
      have key : 0 ≤ (Real.sqrt (η / (1 - L * η)) * ‖m - G ξ x‖ -
          Real.sqrt ((1 - L * η) / η) * ‖v - x‖) ^ 2 := sq_nonneg _
      have hs1 : Real.sqrt (η / (1 - L * η)) ^ 2 = η / (1 - L * η) := Real.sq_sqrt hθη.le
      have hs2 : Real.sqrt ((1 - L * η) / η) ^ 2 = (1 - L * η) / η :=
        Real.sq_sqrt (by positivity)
      have hs12 : Real.sqrt (η / (1 - L * η)) * Real.sqrt ((1 - L * η) / η) = 1 := by
        have hne1 : 1 - L * η ≠ 0 := hθ.ne'
        have hne2 : η ≠ 0 := hη.ne'
        have hprod : η / (1 - L * η) * ((1 - L * η) / η) = 1 := by
          rw [div_mul_div_comm, mul_comm (1 - L * η) η, div_self (mul_ne_zero hne2 hne1)]
        calc Real.sqrt (η / (1 - L * η)) * Real.sqrt ((1 - L * η) / η)
            = Real.sqrt (η / (1 - L * η) * ((1 - L * η) / η)) :=
              (Real.sqrt_mul hθη.le _).symm
          _ = Real.sqrt 1 := by rw [hprod]
          _ = 1 := Real.sqrt_one
      have e : (Real.sqrt (η / (1 - L * η)) * ‖m - G ξ x‖ -
          Real.sqrt ((1 - L * η) / η) * ‖v - x‖) ^ 2 =
          η / (1 - L * η) * ‖m - G ξ x‖ ^ 2 + (1 - L * η) / η * ‖v - x‖ ^ 2 -
            2 * ‖m - G ξ x‖ * ‖v - x‖ := by
        have hcross : (Real.sqrt (η / (1 - L * η)) * ‖m - G ξ x‖) *
            (Real.sqrt ((1 - L * η) / η) * ‖v - x‖) = ‖m - G ξ x‖ * ‖v - x‖ := by
          calc (Real.sqrt (η / (1 - L * η)) * ‖m - G ξ x‖) *
              (Real.sqrt ((1 - L * η) / η) * ‖v - x‖) =
              (Real.sqrt (η / (1 - L * η)) * Real.sqrt ((1 - L * η) / η)) *
                (‖m - G ξ x‖ * ‖v - x‖) := by ring
            _ = ‖m - G ξ x‖ * ‖v - x‖ := by simp only [hs12, one_mul]
        rw [sub_sq, mul_pow, mul_pow, hs1, hs2]
        linear_combination (-2 : ℝ) * hcross
      rw [e] at key
      have e3 : η / (2 * (1 - L * η)) * ‖m - G ξ x‖ ^ 2 + (1 - L * η) / (2 * η) * ‖v - x‖ ^ 2 =
          (η / (1 - L * η) * ‖m - G ξ x‖ ^ 2 + (1 - L * η) / η * ‖v - x‖ ^ 2) / 2 := by
        field_simp
      rw [e3]; linarith
    linarith
  have hsplit : ⟪m - G ξ x, v - y⟫ = ⟪m - G ξ x, x - y⟫ + ⟪m - G ξ x, v - x⟫ := by
    rw [← inner_add_right]; congr 1; abel
  have hcoef : (1 - L * η) / (2 * η) = 1 / (2 * η) - L / 2 := by field_simp
  have hgv : ⟪G ξ x, v - y⟫ = ⟪m, v - y⟫ - ⟪m - G ξ x, v - y⟫ := by
    rw [inner_sub_left]; ring
  have hnorm : ‖v - x‖ ^ 2 / (2 * η) = (1 / (2 * η)) * ‖v - x‖ ^ 2 := by ring
  have hsum : total p F ψ v ≤ total p F ψ y + ⟪m - G ξ x, v - y⟫ +
      (‖y - x‖ ^ 2 - ‖y - v‖ ^ 2) / (2 * η) - (1 / (2 * η) - L / 2) * ‖v - x‖ ^ 2 := by
    simp only [total]
    have htp' : ψ v + ⟪G ξ x, v - y⟫ ≤ ψ y + (‖y - x‖ ^ 2 - ‖y - v‖ ^ 2 - ‖v - x‖ ^ 2) / (2 * η) :=
      htp
    rw [hgv] at htp'
    have e4 : (‖y - x‖ ^ 2 - ‖y - v‖ ^ 2 - ‖v - x‖ ^ 2) / (2 * η) =
        (‖y - x‖ ^ 2 - ‖y - v‖ ^ 2) / (2 * η) - (1 / (2 * η)) * ‖v - x‖ ^ 2 := by ring
    rw [e4] at htp'
    linarith
  rw [hsplit, ← hcoef] at hsum
  rw [norm_sub_rev y x, norm_sub_rev y v] at hsum
  linarith

lemma one_sample (h : Hyp p F G ψ Q prox L σ xstar) {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) {η : ℝ}
    (hη : 0 < η) (hLη : L * η ≤ 1 / 2) :
    Integrable (fun ξ => total p F ψ (prox η x (G ξ x))) p ∧
    Integrable (fun ξ => ‖prox η x (G ξ x) - y‖ ^ 2) p ∧
    ∫ ξ, total p F ψ (prox η x (G ξ x)) ∂p - total p F ψ y ≤
      (‖x - y‖ ^ 2 - ∫ ξ, ‖prox η x (G ξ x) - y‖ ^ 2 ∂p) / (2 * η) +
        2 * L * η * (1 + 2 * L * η) * (total p F ψ x - total p F ψ xstar) +
        η * (1 + 2 * L * η) * σ ^ 2 := by
  have hL := h.pos
  set m := mean p G x
  have hgi := h.int_grad x
  have hgs := h.int_grad_sq x
  have hdev := h.dev_integral hx
  have hθ : 0 < 1 - L * η := by linarith
  have hos : ∀ ξ, total p F ψ (prox η x (G ξ x)) ≤ total p F ψ y +
      (‖x - y‖ ^ 2 - ‖prox η x (G ξ x) - y‖ ^ 2) / (2 * η) + ⟪m - G ξ x, x - y⟫ +
        η / (2 * (1 - L * η)) * ‖m - G ξ x‖ ^ 2 :=
    fun ξ => h.one_step_pointwise hy hη hLη ξ
  have hvmeas : Measurable (fun ξ => prox η x (G ξ x)) :=
    (h.prox_measurable hη).comp (measurable_const.prodMk (h.grad_meas x))
  have hdevpt : ∀ ξ, ‖prox η x (G ξ x) - y‖ ≤ η * ‖G ξ x - m‖ + ‖prox η x m - y‖ := by
    intro ξ
    have h1 := h.prox_lipschitz hη x (G ξ x) x m
    rw [show (x - η • G ξ x) - (x - η • m) = -(η • (G ξ x - m)) by module, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos hη] at h1
    calc ‖prox η x (G ξ x) - y‖ = ‖(prox η x (G ξ x) - prox η x m) + (prox η x m - y)‖ := by
          congr 1; abel
      _ ≤ ‖prox η x (G ξ x) - prox η x m‖ + ‖prox η x m - y‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hdevi : Integrable (fun ξ => ‖G ξ x - m‖ ^ 2) p := by
    have hb : Integrable (fun ξ => 2 * ‖G ξ x‖ ^ 2 + 2 * ‖m‖ ^ 2) p :=
      (hgs.const_mul 2).add (integrable_const _)
    refine Integrable.mono' hb (((h.grad_meas x).sub measurable_const).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := norm_sub_le (G ξ x) m
    nlinarith [sq_nonneg (‖G ξ x‖ - ‖m‖), norm_nonneg (G ξ x), norm_nonneg m, norm_nonneg (G ξ x - m)]
  have hidist : Integrable (fun ξ => ‖prox η x (G ξ x) - y‖ ^ 2) p := by
    have hb : Integrable (fun ξ => 2 * η ^ 2 * ‖G ξ x - m‖ ^ 2 + 2 * ‖prox η x m - y‖ ^ 2) p :=
      (hdevi.const_mul _).add (integrable_const _)
    refine Integrable.mono' hb ((hvmeas.sub measurable_const).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := hdevpt ξ
    nlinarith [sq_nonneg (η * ‖G ξ x - m‖ - ‖prox η x m - y‖), norm_nonneg (prox η x (G ξ x) - y),
      mul_nonneg hη.le (norm_nonneg (G ξ x - m)), norm_nonneg (prox η x m - y)]
  have hinner_i : Integrable (fun ξ => ⟪m - G ξ x, x - y⟫) p :=
    ((integrable_const m).sub hgi).inner_const (x - y)
  have hinner_z : ∫ ξ, ⟪m - G ξ x, x - y⟫ ∂p = 0 := by
    have hfun : (fun ξ => ⟪m - G ξ x, x - y⟫) = fun ξ => ⟪x - y, m - G ξ x⟫ := by
      funext ξ; exact real_inner_comm _ _
    have hsub : Integrable (fun ξ => m - G ξ x) p := (integrable_const m).sub hgi
    rw [hfun, integral_inner hsub, integral_sub (integrable_const _) hgi,
      integral_const, probReal_univ, one_smul]
    simp [m, mean]
  have hrhs_i : Integrable (fun ξ => total p F ψ y +
      (‖x - y‖ ^ 2 - ‖prox η x (G ξ x) - y‖ ^ 2) / (2 * η) + ⟪m - G ξ x, x - y⟫ +
        η / (2 * (1 - L * η)) * ‖m - G ξ x‖ ^ 2) p := by
    have h1 : Integrable (fun ξ => (‖x - y‖ ^ 2 - ‖prox η x (G ξ x) - y‖ ^ 2) / (2 * η)) p :=
      ((integrable_const _).sub hidist).div_const _
    have h2 : Integrable (fun ξ => η / (2 * (1 - L * η)) * ‖m - G ξ x‖ ^ 2) p := by
      simp_rw [norm_sub_rev m]; exact hdevi.const_mul _
    exact (((integrable_const _).add h1).add hinner_i).add h2
  have hitot : Integrable (fun ξ => total p F ψ (prox η x (G ξ x))) p := by
    have hlow : ∀ ξ, total p F ψ xstar ≤ total p F ψ (prox η x (G ξ x)) :=
      fun ξ => h.total_ge (h.prox_mem hη x (G ξ x))
    have hb : Integrable (fun ξ => |total p F ψ y +
        (‖x - y‖ ^ 2 - ‖prox η x (G ξ x) - y‖ ^ 2) / (2 * η) + ⟪m - G ξ x, x - y⟫ +
          η / (2 * (1 - L * η)) * ‖m - G ξ x‖ ^ 2| + |total p F ψ xstar|) p :=
      hrhs_i.abs.add (integrable_const _)
    refine Integrable.mono' hb (h.total_measurable.comp hvmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_le]
    have a1 := hos ξ
    have a2 := hlow ξ
    constructor
    · have := neg_abs_le (total p F ψ xstar)
      have := abs_nonneg (total p F ψ y +
        (‖x - y‖ ^ 2 - ‖prox η x (G ξ x) - y‖ ^ 2) / (2 * η) + ⟪m - G ξ x, x - y⟫ +
          η / (2 * (1 - L * η)) * ‖m - G ξ x‖ ^ 2)
      linarith
    · have := le_abs_self (total p F ψ y +
        (‖x - y‖ ^ 2 - ‖prox η x (G ξ x) - y‖ ^ 2) / (2 * η) + ⟪m - G ξ x, x - y⟫ +
          η / (2 * (1 - L * η)) * ‖m - G ξ x‖ ^ 2)
      have := abs_nonneg (total p F ψ xstar)
      linarith
  refine ⟨hitot, hidist, ?_⟩
  have hint := integral_mono hitot hrhs_i hos
  have h1 : Integrable (fun ξ => (‖x - y‖ ^ 2 - ‖prox η x (G ξ x) - y‖ ^ 2) / (2 * η)) p :=
    ((integrable_const _).sub hidist).div_const _
  have hdevi' : Integrable (fun ξ => ‖m - G ξ x‖ ^ 2) p := by
    simp_rw [norm_sub_rev m]; exact hdevi
  have h2 : Integrable (fun ξ => η / (2 * (1 - L * η)) * ‖m - G ξ x‖ ^ 2) p := hdevi'.const_mul _
  have hA : Integrable (fun ξ => total p F ψ y +
      (‖x - y‖ ^ 2 - ‖prox η x (G ξ x) - y‖ ^ 2) / (2 * η)) p := (integrable_const _).add h1
  have hB : Integrable (fun ξ => total p F ψ y +
      (‖x - y‖ ^ 2 - ‖prox η x (G ξ x) - y‖ ^ 2) / (2 * η) + ⟪m - G ξ x, x - y⟫) p :=
    hA.add hinner_i
  rw [integral_add hB h2, integral_add hA hinner_i, integral_add (integrable_const _) h1,
    integral_const, probReal_univ, one_smul, hinner_z, integral_const_mul, integral_div,
    integral_sub (integrable_const _) hidist, integral_const, probReal_univ, one_smul] at hint
  have hdev' : ∫ ξ, ‖m - G ξ x‖ ^ 2 ∂p ≤ 4 * L * (total p F ψ x - total p F ψ xstar) + 2 * σ ^ 2 := by
    simp_rw [norm_sub_rev m]; exact hdev
  have hcoef : η / (2 * (1 - L * η)) ≤ η / 2 * (1 + 2 * L * η) := by
    rw [div_le_iff₀ (by positivity)]
    have hu : 0 ≤ L * η := by positivity
    have key : η / 2 * (1 + 2 * L * η) * (2 * (1 - L * η)) - η =
        η * (L * η) * (1 - 2 * (L * η)) := by ring
    have hnn : 0 ≤ η * (L * η) * (1 - 2 * (L * η)) :=
      mul_nonneg (mul_nonneg hη.le hu) (by linarith)
    linarith
  have hdev0 : 0 ≤ ∫ ξ, ‖m - G ξ x‖ ^ 2 ∂p := integral_nonneg (fun ξ => sq_nonneg _)
  have hgap0 : 0 ≤ 4 * L * (total p F ψ x - total p F ψ xstar) + 2 * σ ^ 2 := le_trans hdev0 hdev'
  have hm1 := mul_le_mul hcoef hdev' hdev0 (by positivity)
  have hfinal : ∫ ξ, total p F ψ (prox η x (G ξ x)) ∂p ≤ total p F ψ y +
      (‖x - y‖ ^ 2 - ∫ ξ, ‖prox η x (G ξ x) - y‖ ^ 2 ∂p) / (2 * η) +
        η / 2 * (1 + 2 * L * η) * (4 * L * (total p F ψ x - total p F ψ xstar) + 2 * σ ^ 2) := by
    linarith [hint, hm1]
  have e : η / 2 * (1 + 2 * L * η) * (4 * L * (total p F ψ x - total p F ψ xstar) + 2 * σ ^ 2) =
      2 * L * η * (1 + 2 * L * η) * (total p F ψ x - total p F ψ xstar) +
        η * (1 + 2 * L * η) * σ ^ 2 := by ring
  linarith [hfinal, e]
end Hyp

end OracleTemplate.SampledComposite
