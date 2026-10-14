import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.MarkovProduct

def Complexified (E : Type*) := WithLp 2 (E × E)

namespace Complexified

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable instance : NormedAddCommGroup (Complexified E) :=
  inferInstanceAs (NormedAddCommGroup (WithLp 2 (E × E)))

noncomputable instance : NormedSpace ℝ (Complexified E) :=
  inferInstanceAs (NormedSpace ℝ (WithLp 2 (E × E)))

instance [CompleteSpace E] : CompleteSpace (Complexified E) :=
  inferInstanceAs (CompleteSpace (WithLp 2 (E × E)))

def realPart (x : Complexified E) : E := x.ofLp.1

def imagPart (x : Complexified E) : E := x.ofLp.2

def pair (x y : E) : Complexified E := WithLp.toLp 2 (x, y)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[ext] lemma ext {x y : Complexified E} (hr : realPart x = realPart y)
    (hi : imagPart x = imagPart y) : x = y := by
  exact (WithLp.equiv 2 (E × E)).injective (Prod.ext hr hi)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] lemma real_pair (x y : E) : realPart (pair x y) = x := rfl
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] lemma imag_pair (x y : E) : imagPart (pair x y) = y := rfl
omit [InnerProductSpace ℝ E] in
@[simp] lemma real_add (x y : Complexified E) : realPart (x + y) = realPart x + realPart y := rfl
omit [InnerProductSpace ℝ E] in
@[simp] lemma imag_add (x y : Complexified E) : imagPart (x + y) = imagPart x + imagPart y := rfl
omit [InnerProductSpace ℝ E] in
@[simp] lemma real_zero : realPart (0 : Complexified E) = 0 := rfl
omit [InnerProductSpace ℝ E] in
@[simp] lemma imag_zero : imagPart (0 : Complexified E) = 0 := rfl

omit [InnerProductSpace ℝ E] in
@[simp] lemma real_sub (x y : Complexified E) : realPart (x - y) = realPart x - realPart y := rfl
omit [InnerProductSpace ℝ E] in
@[simp] lemma imag_sub (x y : Complexified E) : imagPart (x - y) = imagPart x - imagPart y := rfl

noncomputable instance : SMul ℂ (Complexified E) where
  smul z x := pair (z.re • realPart x - z.im • imagPart x)
    (z.im • realPart x + z.re • imagPart x)

@[simp] lemma real_smul (z : ℂ) (x : Complexified E) :
    realPart (z • x) = z.re • realPart x - z.im • imagPart x := rfl
@[simp] lemma imag_smul (z : ℂ) (x : Complexified E) :
    imagPart (z • x) = z.im • realPart x + z.re • imagPart x := rfl

noncomputable instance : Module ℂ (Complexified E) where
  one_smul x := by ext <;> simp
  mul_smul a b x := by
    ext <;> simp [Complex.mul_re, Complex.mul_im, add_smul, sub_smul, smul_add,
      smul_sub, mul_smul] <;> module
  smul_zero a := by ext <;> simp
  smul_add a x y := by ext <;> simp [smul_add] <;> abel
  add_smul a b x := by ext <;> simp [add_smul] <;> abel
  zero_smul x := by ext <;> simp

omit [InnerProductSpace ℝ E] in
lemma norm_sq (x : Complexified E) :
    ‖x‖ ^ 2 = ‖realPart x‖ ^ 2 + ‖imagPart x‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 x

lemma norm_smul_sq (z : ℂ) (x : Complexified E) :
    ‖z • x‖ ^ 2 = ‖z‖ ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_sq, real_smul, imag_smul, norm_sub_sq_real, norm_add_sq_real, norm_sq x]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_left,
    inner_smul_right, starRingEnd_apply, star_trivial, Complex.sq_norm, Complex.normSq_apply]
  ring

noncomputable instance : NormedSpace ℂ (Complexified E) where
  norm_smul_le z x := by
    have he := norm_smul_sq z x
    have hn : 0 ≤ ‖z‖ * ‖x‖ := mul_nonneg (norm_nonneg z) (norm_nonneg x)
    nlinarith [norm_nonneg (z • x)]

noncomputable instance : InnerProductSpace ℂ (Complexified E) where
  inner x y := ⟨⟪realPart x, realPart y⟫ + ⟪imagPart x, imagPart y⟫,
    ⟪realPart x, imagPart y⟫ - ⟪imagPart x, realPart y⟫⟩
  norm_sq_eq_re_inner x := by
    change ‖x‖ ^ 2 = ⟪realPart x, realPart x⟫ + ⟪imagPart x, imagPart x⟫
    simpa only [real_inner_self_eq_norm_sq] using norm_sq x
  conj_inner_symm x y := by
    apply Complex.ext <;> simp [real_inner_comm]
  add_left x y z := by
    apply Complex.ext <;> simp [inner_add_left] <;> ring
  smul_left x y z := by
    apply Complex.ext <;>
      simp [inner_sub_left, inner_add_left, inner_smul_left, real_inner_comm] <;> ring

@[simp] lemma inner_re (x y : Complexified E) :
    (inner ℂ x y).re = ⟪realPart x, realPart y⟫ + ⟪imagPart x, imagPart y⟫ := rfl

@[simp] lemma inner_im (x y : Complexified E) :
    (inner ℂ x y).im = ⟪realPart x, imagPart y⟫ - ⟪imagPart x, realPart y⟫ := rfl

noncomputable def liftLinear (H : E →L[ℝ] E) : Complexified E →ₗ[ℂ] Complexified E where
  toFun x := pair (H (realPart x)) (H (imagPart x))
  map_add' x y := by ext <;> simp [map_add]
  map_smul' z x := by ext <;> simp [map_add, map_sub, map_smul]

lemma norm_liftLinear_le (H : E →L[ℝ] E) (x : Complexified E) :
    ‖liftLinear H x‖ ≤ ‖H‖ * ‖x‖ := by
  have hr := H.le_opNorm (realPart x)
  have hi := H.le_opNorm (imagPart x)
  have hr2 : ‖H (realPart x)‖ ^ 2 ≤ ‖H‖ ^ 2 * ‖realPart x‖ ^ 2 := by
    rw [← mul_pow]
    gcongr
  have hi2 : ‖H (imagPart x)‖ ^ 2 ≤ ‖H‖ ^ 2 * ‖imagPart x‖ ^ 2 := by
    rw [← mul_pow]
    gcongr
  have he : ‖liftLinear H x‖ ^ 2 ≤ (‖H‖ * ‖x‖) ^ 2 := by
    rw [mul_pow, norm_sq x, norm_sq]
    change ‖H (realPart x)‖ ^ 2 + ‖H (imagPart x)‖ ^ 2 ≤ _
    nlinarith
  nlinarith [norm_nonneg (liftLinear H x), mul_nonneg (norm_nonneg H) (norm_nonneg x)]

noncomputable def lift (H : E →L[ℝ] E) : Complexified E →L[ℂ] Complexified E :=
  (liftLinear H).mkContinuous ‖H‖ (norm_liftLinear_le H)

@[simp] lemma lift_apply (H : E →L[ℝ] E) (x : Complexified E) :
    lift H x = pair (H (realPart x)) (H (imagPart x)) := rfl

lemma norm_lift_le (H : E →L[ℝ] E) : ‖lift H‖ ≤ ‖H‖ :=
  (liftLinear H).mkContinuous_norm_le (norm_nonneg H) (norm_liftLinear_le H)

lemma lift_positive (H : E →L[ℝ] E) (hp : ∀ x, 0 ≤ ⟪x, H x⟫) (x : Complexified E) :
    0 ≤ (inner ℂ x (lift H x)).re := by
  simp only [inner_re, lift_apply, real_pair, imag_pair]
  exact add_nonneg (hp _) (hp _)

lemma lift_upper (H : E →L[ℝ] E) {L : ℝ}
    (hb : ∀ x, ⟪x, H x⟫ ≤ L * ‖x‖ ^ 2) (x : Complexified E) :
    (inner ℂ x (lift H x)).re ≤ L * ‖x‖ ^ 2 := by
  simp only [inner_re, lift_apply, real_pair, imag_pair, norm_sq]
  nlinarith [hb (realPart x), hb (imagPart x)]

lemma lift_adjoint [CompleteSpace E] (H : E →L[ℝ] E) (hs : H.adjoint = H) :
    (lift H).adjoint = lift H := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  have he (a b : E) : ⟪H a, b⟫ = ⟪a, H b⟫ := by
    simpa only [hs] using (H.adjoint_inner_right a b).symm
  apply Complex.ext <;> simp [he]

omit [InnerProductSpace ℝ E] in
lemma norm_pair_zero (x : E) : ‖pair x 0‖ = ‖x‖ := by
  have he := norm_sq (pair x 0)
  simp only [real_pair, imag_pair, norm_zero, zero_pow (by omega : 2 ≠ 0), add_zero] at he
  nlinarith [norm_nonneg (pair x 0), norm_nonneg x]

lemma inner_pair_zero (x y : E) : inner ℂ (pair x 0) (pair y 0) = (⟪x, y⟫ : ℂ) := by
  apply Complex.ext <;> simp

lemma lift_pair_zero (H : E →L[ℝ] E) (x : E) :
    lift H (pair x 0) = pair (H x) 0 := by simp

lemma lift_gradient_step (H : E →L[ℝ] E) (η : ℝ) :
    lift (ContinuousLinearMap.id ℝ E - η • H) =
      ContinuousLinearMap.id ℂ (Complexified E) - (η : ℂ) • lift H := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext <;> simp only [lift_apply, real_pair, imag_pair,
    ContinuousLinearMap.id_apply, sub_apply, smul_apply,
    real_sub, imag_sub, real_smul, imag_smul, Complex.ofReal_re, Complex.ofReal_im,
    zero_smul, sub_zero, zero_add]

end Complexified
end OracleTemplate.MarkovProduct
