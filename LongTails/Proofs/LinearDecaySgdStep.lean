import LongTails.Proofs.GdConvex
import LongTails.Setups.SampledSmoothConvex
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.SampledConvex

open LongTails.Setups.SampledSmoothConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma cocoercive {φ : E → ℝ} {g : E → E} {L : ℝ} (hL : 0 < L) (hc : ConvexOn ℝ univ φ)
    (hg : ∀ x, HasGradientAt φ (g x) x) (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖) (a b : E) :
    ‖g a - g b‖ ^ 2 ≤ 2 * L * (φ a - φ b - ⟪g b, a - b⟫) := by
  let ψ : E → ℝ := fun z => φ z - ⟪g b, z⟫
  have hψg : ∀ z, HasGradientAt ψ (g z - g b) z := by
    intro z
    rw [hasGradientAt_iff_hasFDerivAt]
    have h2 := HasFDerivAt.inner ℝ (hasFDerivAt_const (g b) z) (hasFDerivAt_id z)
    convert (hg z).hasFDerivAt.sub h2 using 1
    · funext v
      simp [ψ]
    · ext v
      simp [fderivInnerCLM_apply]
  have hhl : ∀ x y, ‖(g x - g b) - (g y - g b)‖ ≤ L * ‖x - y‖ := by
    intro x y
    simpa using hlip x y
  have hd := Gradient.descent hL hψg hhl a
  have hmin := Gradient.convex_support hc hg b (a - (1 / L) • (g a - g b))
  simp only [ψ] at hd
  rw [inner_sub_right] at hmin
  have he : ⟪g b, a - b⟫ = ⟪g b, a⟫ - ⟪g b, b⟫ := inner_sub_right _ _ _
  rw [he]
  have hq : ‖g a - g b‖ ^ 2 / (2 * L) ≤ φ a - φ b - (⟪g b, a⟫ - ⟪g b, b⟫) := by linarith
  have := (div_le_iff₀ (by positivity : 0 < 2 * L)).mp hq
  linarith

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]

structure Hyp (p : Measure Ξ) (F : Ξ → E → ℝ) (G : Ξ → E → E) (L σ : ℝ) (xstar : E) : Prop where
  pos : 0 < L
  meas : Measurable (Function.uncurry G)
  convex : ∀ ξ, ConvexOn ℝ univ (F ξ)
  grad : ∀ ξ x, HasGradientAt (F ξ) (G ξ x) x
  lip : ∀ ξ x y, ‖G ξ x - G ξ y‖ ≤ L * ‖x - y‖
  int : ∀ x, Integrable (fun ξ => F ξ x) p
  min : IsMinOn (fun x => ∫ ξ, F ξ x ∂p) univ xstar
  sq_int : Integrable (fun ξ => ‖G ξ xstar‖ ^ 2) p
  sq : ∫ ξ, ‖G ξ xstar‖ ^ 2 ∂p ≤ σ ^ 2

noncomputable def obj (p : Measure Ξ) (F : Ξ → E → ℝ) (x : E) : ℝ := ∫ ξ, F ξ x ∂p

noncomputable def mean (p : Measure Ξ) (G : Ξ → E → E) (x : E) : E := ∫ ξ, G ξ x ∂p

namespace Hyp

variable {p : Measure Ξ} [IsProbabilityMeasure p] {F : Ξ → E → ℝ} {G : Ξ → E → E} {L σ : ℝ}
  {xstar : E}

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma grad_meas (h : Hyp p F G L σ xstar) (x : E) : Measurable (fun ξ => G ξ x) :=
  h.meas.comp (measurable_id.prodMk measurable_const)

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma grad_sq_le (h : Hyp p F G L σ xstar) (ξ : Ξ) (x : E) :
    ‖G ξ x‖ ^ 2 ≤ 2 * ‖G ξ xstar‖ ^ 2 + 2 * L ^ 2 * ‖x - xstar‖ ^ 2 := by
  have h1 : ‖G ξ x‖ ≤ ‖G ξ xstar‖ + L * ‖x - xstar‖ := by
    calc ‖G ξ x‖ = ‖G ξ xstar + (G ξ x - G ξ xstar)‖ := by congr 1; abel
      _ ≤ ‖G ξ xstar‖ + ‖G ξ x - G ξ xstar‖ := norm_add_le _ _
      _ ≤ _ := by linarith [h.lip ξ x xstar]
  have h2 : 0 ≤ L * ‖x - xstar‖ := mul_nonneg h.pos.le (norm_nonneg _)
  nlinarith [sq_nonneg (‖G ξ xstar‖ - L * ‖x - xstar‖), norm_nonneg (G ξ x)]

omit [SecondCountableTopology E] in
lemma int_grad_sq (h : Hyp p F G L σ xstar) (x : E) :
    Integrable (fun ξ => ‖G ξ x‖ ^ 2) p := by
  refine Integrable.mono' ((h.sq_int.const_mul 2).add (integrable_const (2 * L ^ 2 * ‖x - xstar‖ ^ 2)))
    ((h.grad_meas x).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact h.grad_sq_le ξ x

lemma int_grad (h : Hyp p F G L σ xstar) (x : E) : Integrable (fun ξ => G ξ x) p := by
  have hb : Integrable (fun ξ => 1 + ‖G ξ x‖ ^ 2) p := (integrable_const (1 : ℝ)).add (h.int_grad_sq x)
  refine Integrable.mono' hb (h.grad_meas x).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => ?_))
  nlinarith [sq_nonneg (‖G ξ x‖ - 1), norm_nonneg (G ξ x)]

lemma inner_integral (h : Hyp p F G L σ xstar) (a v : E) :
    Integrable (fun ξ => ⟪v, G ξ a⟫) p ∧ ∫ ξ, ⟪v, G ξ a⟫ ∂p = ⟪v, mean p G a⟫ :=
  ⟨(h.int_grad a).const_inner v, integral_inner (h.int_grad a) v⟩

lemma obj_upper (h : Hyp p F G L σ xstar) (a b : E) :
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

lemma obj_lower (h : Hyp p F G L σ xstar) (a b : E) :
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

lemma mean_star (h : Hyp p F G L σ xstar) : mean p G xstar = 0 := by
  have hu := h.obj_upper xstar (xstar - (1 / L) • mean p G xstar)
  have hm := h.min (mem_univ (xstar - (1 / L) • mean p G xstar))
  change obj p F xstar ≤ obj p F (xstar - (1 / L) • mean p G xstar) at hm
  have hL := h.pos
  rw [show xstar - (1 / L) • mean p G xstar - xstar = -((1 / L) • mean p G xstar) by abel,
    inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / L), real_inner_self_eq_norm_sq] at hu
  have hsq : ‖mean p G xstar‖ ^ 2 ≤ 0 := by
    have : (1 / L) * ‖mean p G xstar‖ ^ 2 - L / 2 * ((1 / L) * ‖mean p G xstar‖) ^ 2 ≤ 0 := by
      linarith
    have heq : (1 / L) * ‖mean p G xstar‖ ^ 2 - L / 2 * ((1 / L) * ‖mean p G xstar‖) ^ 2 =
        (1 / (2 * L)) * ‖mean p G xstar‖ ^ 2 := by field_simp; ring
    rw [heq] at this
    have hpos : 0 < 1 / (2 * L) := by positivity
    nlinarith
  have : ‖mean p G xstar‖ = 0 := by nlinarith [norm_nonneg (mean p G xstar)]
  exact norm_eq_zero.mp this

lemma grad_sq_integral (h : Hyp p F G L σ xstar) (x : E) :
    ∫ ξ, ‖G ξ x‖ ^ 2 ∂p ≤ 4 * L * (obj p F x - obj p F xstar) + 2 * σ ^ 2 := by
  have hpt : ∀ ξ, ‖G ξ x‖ ^ 2 ≤
      4 * L * (F ξ x - F ξ xstar - ⟪G ξ xstar, x - xstar⟫) + 2 * ‖G ξ xstar‖ ^ 2 := by
    intro ξ
    have hc := cocoercive h.pos (h.convex ξ) (h.grad ξ) (h.lip ξ) x xstar
    have h1 : ‖G ξ x‖ ^ 2 ≤ 2 * ‖G ξ x - G ξ xstar‖ ^ 2 + 2 * ‖G ξ xstar‖ ^ 2 := by
      have := norm_add_le (G ξ x - G ξ xstar) (G ξ xstar)
      simp only [sub_add_cancel] at this
      nlinarith [sq_nonneg (‖G ξ x - G ξ xstar‖ - ‖G ξ xstar‖), norm_nonneg (G ξ x),
        norm_nonneg (G ξ x - G ξ xstar), norm_nonneg (G ξ xstar)]
    linarith
  obtain ⟨hii, hie⟩ := h.inner_integral xstar (x - xstar)
  have hpt' : ∀ ξ, ‖G ξ x‖ ^ 2 ≤
      4 * L * (F ξ x - F ξ xstar - ⟪x - xstar, G ξ xstar⟫) + 2 * ‖G ξ xstar‖ ^ 2 := by
    intro ξ; rw [real_inner_comm]; exact hpt ξ
  have hi0 : Integrable (fun ξ => F ξ x - F ξ xstar) p := (h.int x).sub (h.int xstar)
  have hi1 : Integrable (fun ξ => F ξ x - F ξ xstar - ⟪x - xstar, G ξ xstar⟫) p := hi0.sub hii
  have hi1' : Integrable (fun ξ => 4 * L * (F ξ x - F ξ xstar - ⟪x - xstar, G ξ xstar⟫)) p :=
    hi1.const_mul _
  have hi2 : Integrable (fun ξ => 2 * ‖G ξ xstar‖ ^ 2) p := h.sq_int.const_mul _
  have hi3 : Integrable (fun ξ => 4 * L * (F ξ x - F ξ xstar - ⟪x - xstar, G ξ xstar⟫) +
      2 * ‖G ξ xstar‖ ^ 2) p := hi1'.add hi2
  have hle := integral_mono (h.int_grad_sq x) hi3 hpt'
  have e1 : ∫ ξ, (4 * L * (F ξ x - F ξ xstar - ⟪x - xstar, G ξ xstar⟫) + 2 * ‖G ξ xstar‖ ^ 2) ∂p =
      4 * L * (obj p F x - obj p F xstar - ⟪x - xstar, mean p G xstar⟫) +
        2 * ∫ ξ, ‖G ξ xstar‖ ^ 2 ∂p := by
    rw [integral_add hi1' hi2, integral_const_mul, integral_const_mul, integral_sub hi0 hii,
      integral_sub (h.int x) (h.int xstar), hie]
    rfl
  rw [e1, h.mean_star, inner_zero_right, sub_zero] at hle
  have := h.sq
  linarith

lemma obj_continuous (h : Hyp p F G L σ xstar) : Continuous (obj p F) := by
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

lemma one_sample (h : Hyp p F G L σ xstar) (x y : E) {η : ℝ} (hη : 0 < η) :
    Integrable (fun ξ => obj p F (x - η • G ξ x)) p ∧
    Integrable (fun ξ => ‖x - η • G ξ x - y‖ ^ 2) p ∧
    ∫ ξ, obj p F (x - η • G ξ x) ∂p - obj p F y ≤
      (‖x - y‖ ^ 2 - ∫ ξ, ‖x - η • G ξ x - y‖ ^ 2 ∂p) / (2 * η) +
        2 * L * η * (1 + L * η) * (obj p F x - obj p F xstar) + η * (1 + L * η) * σ ^ 2 := by
  have hL := h.pos
  set m := mean p G x
  have hgi := h.int_grad x
  have hgs := h.int_grad_sq x
  have hcont := h.obj_continuous
  have hmeas : Measurable (fun ξ => x - η • G ξ x) := measurable_const.sub ((h.grad_meas x).const_smul η)
  have hup : ∀ ξ, obj p F (x - η • G ξ x) ≤ obj p F x - η * ⟪m, G ξ x⟫ + L / 2 * η ^ 2 * ‖G ξ x‖ ^ 2 := by
    intro ξ
    have := h.obj_upper x (x - η • G ξ x)
    rw [show x - η • G ξ x - x = -(η • G ξ x) by abel, inner_neg_right, real_inner_smul_right,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη] at this
    nlinarith
  have hlo : ∀ ξ, obj p F x - η * ⟪m, G ξ x⟫ ≤ obj p F (x - η • G ξ x) := by
    intro ξ
    have := h.obj_lower x (x - η • G ξ x)
    rw [show x - η • G ξ x - x = -(η • G ξ x) by abel, inner_neg_right, real_inner_smul_right] at this
    linarith
  have hi1 : Integrable (fun ξ => obj p F x - η * ⟪m, G ξ x⟫) p :=
    (integrable_const _).sub ((hgi.const_inner m).const_mul η)
  have hi2 : Integrable (fun ξ => obj p F x - η * ⟪m, G ξ x⟫ + L / 2 * η ^ 2 * ‖G ξ x‖ ^ 2) p :=
    hi1.add (hgs.const_mul _)
  have hiobj : Integrable (fun ξ => obj p F (x - η • G ξ x)) p := by
    have hb : Integrable (fun ξ => |obj p F x - η * ⟪m, G ξ x⟫ + L / 2 * η ^ 2 * ‖G ξ x‖ ^ 2| +
        |obj p F x - η * ⟪m, G ξ x⟫|) p := hi2.abs.add hi1.abs
    refine Integrable.mono' hb (hcont.measurable.comp hmeas).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_le]
    have a1 := hup ξ
    have a2 := hlo ξ
    constructor
    · have := neg_abs_le (obj p F x - η * ⟪m, G ξ x⟫)
      have := abs_nonneg (obj p F x - η * ⟪m, G ξ x⟫ + L / 2 * η ^ 2 * ‖G ξ x‖ ^ 2)
      linarith
    · have := le_abs_self (obj p F x - η * ⟪m, G ξ x⟫ + L / 2 * η ^ 2 * ‖G ξ x‖ ^ 2)
      have := abs_nonneg (obj p F x - η * ⟪m, G ξ x⟫)
      linarith
  have hexp : ∀ ξ, ‖x - η • G ξ x - y‖ ^ 2 =
      ‖x - y‖ ^ 2 - 2 * η * ⟪x - y, G ξ x⟫ + η ^ 2 * ‖G ξ x‖ ^ 2 := by
    intro ξ
    rw [show x - η • G ξ x - y = (x - y) - η • G ξ x by abel, norm_sub_sq_real, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right]
    ring
  have hid : Integrable (fun ξ => ‖x - y‖ ^ 2 - 2 * η * ⟪x - y, G ξ x⟫ + η ^ 2 * ‖G ξ x‖ ^ 2) p :=
    ((integrable_const _).sub ((hgi.const_inner (x - y)).const_mul _)).add (hgs.const_mul _)
  have hidist : Integrable (fun ξ => ‖x - η • G ξ x - y‖ ^ 2) p := by
    simp_rw [hexp]; exact hid
  refine ⟨hiobj, hidist, ?_⟩
  have hgsq := h.grad_sq_integral x
  have hcvx := h.obj_lower x y
  have hint_obj : ∫ ξ, obj p F (x - η • G ξ x) ∂p ≤
      obj p F x - η * ⟪m, m⟫ + L / 2 * η ^ 2 * ∫ ξ, ‖G ξ x‖ ^ 2 ∂p := by
    have := integral_mono hiobj hi2 hup
    have hj1 : Integrable (fun ξ => η * ⟪m, G ξ x⟫) p := (hgi.const_inner m).const_mul _
    have hj3 : Integrable (fun ξ => L / 2 * η ^ 2 * ‖G ξ x‖ ^ 2) p := hgs.const_mul _
    rwa [integral_add hi1 hj3, integral_sub (integrable_const _) hj1, integral_const_mul,
      integral_const_mul, integral_inner hgi, integral_const, probReal_univ, one_smul] at this
  have hint_dist : ∫ ξ, ‖x - η • G ξ x - y‖ ^ 2 ∂p =
      ‖x - y‖ ^ 2 - 2 * η * ⟪x - y, m⟫ + η ^ 2 * ∫ ξ, ‖G ξ x‖ ^ 2 ∂p := by
    simp_rw [hexp]
    have hj1 : Integrable (fun ξ => 2 * η * ⟪x - y, G ξ x⟫) p := (hgi.const_inner (x - y)).const_mul _
    have hj2 : Integrable (fun ξ => ‖x - y‖ ^ 2 - 2 * η * ⟪x - y, G ξ x⟫) p :=
      (integrable_const _).sub hj1
    have hj3 : Integrable (fun ξ => η ^ 2 * ‖G ξ x‖ ^ 2) p := hgs.const_mul _
    rw [integral_add hj2 hj3, integral_sub (integrable_const _) hj1, integral_const_mul,
      integral_const_mul, integral_inner hgi, integral_const, probReal_univ, one_smul]
    rfl
  rw [hint_dist]
  have hmm : ⟪m, m⟫ = ‖m‖ ^ 2 := real_inner_self_eq_norm_sq m
  have hxy : ⟪m, y - x⟫ = -⟪x - y, m⟫ := by
    rw [real_inner_comm, ← inner_neg_left, neg_sub]
  rw [hmm] at hint_obj
  rw [hxy] at hcvx
  have hgap : 0 ≤ obj p F x - obj p F xstar := sub_nonneg.mpr (h.min (mem_univ x))
  have hLη : 0 ≤ L * η := by positivity
  have hdiv : (‖x - y‖ ^ 2 - (‖x - y‖ ^ 2 - 2 * η * ⟪x - y, m⟫ + η ^ 2 * ∫ ξ, ‖G ξ x‖ ^ 2 ∂p)) /
      (2 * η) = ⟪x - y, m⟫ - η / 2 * ∫ ξ, ‖G ξ x‖ ^ 2 ∂p := by
    field_simp
    ring
  rw [hdiv]
  have hsq0 : 0 ≤ ∫ ξ, ‖G ξ x‖ ^ 2 ∂p := integral_nonneg (fun ξ => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hgsq (by positivity : (0 : ℝ) ≤ η / 2 * (1 + L * η))
  nlinarith [sq_nonneg ‖m‖, mul_nonneg hη.le (sq_nonneg ‖m‖)]

end Hyp

end OracleTemplate.SampledConvex
