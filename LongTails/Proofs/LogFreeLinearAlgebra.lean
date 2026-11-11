import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace LongTails.Proofs.LogFreeLinearAlgebra

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def Symm (B : E →L[ℝ] E) : Prop := ∀ u v, ⟪B u, v⟫ = ⟪B v, u⟫

lemma psd_cauchy_schwarz {B : E →L[ℝ] E} (hB : Symm B) (hpos : ∀ v, 0 ≤ ⟪B v, v⟫)
    (u w : E) : ⟪B u, w⟫ ^ 2 ≤ ⟪B u, u⟫ * ⟪B w, w⟫ := by
  have hq : ∀ t : ℝ, 0 ≤ ⟪B w, w⟫ * (t * t) + (2 * ⟪B u, w⟫) * t + ⟪B u, u⟫ := by
    intro t
    have h := hpos (u + t • w)
    have hs := hB w u
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real] at h
    have he : ⟪B w, w⟫ * (t * t) + (2 * ⟪B u, w⟫) * t + ⟪B u, u⟫ =
        ⟪B u, u⟫ + t * ⟪B w, u⟫ + t * (⟪B u, w⟫ + t * ⟪B w, w⟫) := by rw [hs]; ring
    linarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith [hd]

lemma relative_bilinear {B M : E →L[ℝ] E} (hB : Symm B) (hM : Symm M) {ζ : ℝ} (hζ0 : 0 ≤ ζ)
    (hrel : ∀ v, |⟪M v, v⟫| ≤ ζ * ⟪B v, v⟫) (u w : E) :
    |⟪M u, w⟫| ≤ 2 * ζ * Real.sqrt (⟪B u, u⟫ * ⟪B w, w⟫) := by
  have hζ : ∀ v, 0 ≤ ζ * ⟪B v, v⟫ := fun v => (abs_nonneg _).trans (hrel v)
  let P : E →L[ℝ] E := ζ • B + M
  let N : E →L[ℝ] E := ζ • B - M
  have hPs : Symm P := by
    intro a b
    simp [P, inner_add_left,
      inner_smul_left, hB a b, hM a b]
  have hNs : Symm N := by
    intro a b
    simp [N, inner_sub_left,
      inner_smul_left, hB a b, hM a b]
  have hPv : ∀ v, ⟪P v, v⟫ = ζ * ⟪B v, v⟫ + ⟪M v, v⟫ := by
    intro v
    simp [P, inner_add_left,
      inner_smul_left]
  have hNv : ∀ v, ⟪N v, v⟫ = ζ * ⟪B v, v⟫ - ⟪M v, v⟫ := by
    intro v
    simp [N, inner_sub_left,
      inner_smul_left]
  have hPp : ∀ v, 0 ≤ ⟪P v, v⟫ := by
    intro v; rw [hPv]; have := hrel v; have := neg_abs_le (⟪M v, v⟫); linarith
  have hNp : ∀ v, 0 ≤ ⟪N v, v⟫ := by
    intro v; rw [hNv]; have := hrel v; have := le_abs_self (⟪M v, v⟫); linarith
  have hcP := psd_cauchy_schwarz hPs hPp u w
  have hcN := psd_cauchy_schwarz hNs hNp u w
  have hsplit : ⟪M u, w⟫ = (⟪P u, w⟫ - ⟪N u, w⟫) / 2 := by
    simp [P, N, inner_add_left, inner_sub_left, inner_smul_left]
    try ring
  set a := ⟪B u, u⟫
  set c := ⟪B w, w⟫
  have hPu : ⟪P u, u⟫ ≤ 2 * (ζ * a) := by rw [hPv]; have := hrel u; have := le_abs_self (⟪M u, u⟫); linarith
  have hPw : ⟪P w, w⟫ ≤ 2 * (ζ * c) := by rw [hPv]; have := hrel w; have := le_abs_self (⟪M w, w⟫); linarith
  have hNu : ⟪N u, u⟫ ≤ 2 * (ζ * a) := by rw [hNv]; have := hrel u; have := neg_abs_le (⟪M u, u⟫); linarith
  have hNw : ⟪N w, w⟫ ≤ 2 * (ζ * c) := by rw [hNv]; have := hrel w; have := neg_abs_le (⟪M w, w⟫); linarith
  have hza := hζ u
  have hzc := hζ w
  have hprod : ⟪P u, u⟫ * ⟪P w, w⟫ ≤ 4 * ((ζ * a) * (ζ * c)) := by
    have := mul_le_mul hPu hPw (hPp w) (by linarith)
    linarith
  have hprodN : ⟪N u, u⟫ * ⟪N w, w⟫ ≤ 4 * ((ζ * a) * (ζ * c)) := by
    have := mul_le_mul hNu hNw (hNp w) (by linarith)
    linarith
  have hroot : Real.sqrt (4 * ((ζ * a) * (ζ * c))) = 2 * ζ * Real.sqrt (a * c) := by
    have : 4 * ((ζ * a) * (ζ * c)) = (2 * ζ) ^ 2 * (a * c) := by ring
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hP' : |⟪P u, w⟫| ≤ Real.sqrt (4 * ((ζ * a) * (ζ * c))) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (hcP.trans hprod)
  have hN' : |⟪N u, w⟫| ≤ Real.sqrt (4 * ((ζ * a) * (ζ * c))) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (hcN.trans hprodN)
  rw [hsplit, ← hroot]
  rw [abs_div, abs_two]
  have := abs_sub (⟪P u, w⟫) (⟪N u, w⟫)
  have hs : 0 ≤ Real.sqrt (4 * ((ζ * a) * (ζ * c))) := Real.sqrt_nonneg _
  rw [div_le_iff₀ (by norm_num)]
  linarith

lemma image_norm_sq {B : E →L[ℝ] E} (hB : Symm B) (hpos : ∀ v, 0 ≤ ⟪B v, v⟫) (d : E) :
    ‖B d‖ ^ 2 ≤ ‖B‖ * ⟪B d, d⟫ := by
  have hcs := psd_cauchy_schwarz hB hpos d (B d)
  have hself : ⟪B d, B d⟫ = ‖B d‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hup : ⟪B (B d), B d⟫ ≤ ‖B‖ * ‖B d‖ ^ 2 := by
    calc ⟪B (B d), B d⟫ ≤ ‖B (B d)‖ * ‖B d‖ := real_inner_le_norm _ _
      _ ≤ (‖B‖ * ‖B d‖) * ‖B d‖ := by gcongr; exact B.le_opNorm _
      _ = ‖B‖ * ‖B d‖ ^ 2 := by ring
  rw [hself] at hcs
  have hd0 : 0 ≤ ⟪B d, d⟫ := hpos d
  by_cases hz : ‖B d‖ = 0
  · rw [hz]; nlinarith [mul_nonneg (norm_nonneg B) hd0]
  have hpos' : 0 < ‖B d‖ ^ 2 := by positivity
  have h2 : (‖B d‖ ^ 2) ^ 2 ≤ ⟪B d, d⟫ * (‖B‖ * ‖B d‖ ^ 2) :=
    hcs.trans (mul_le_mul_of_nonneg_left hup hd0)
  nlinarith

lemma solve_exists [FiniteDimensional ℝ E] {B : E →L[ℝ] E} {μ : ℝ} (hμ : 0 < μ)
    (hcoer : ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪B v, v⟫) (g : E) : ∃ d, B d = g := by
  have hinj : Function.Injective (B : E →ₗ[ℝ] E) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h := hcoer v
    have hv' : B v = 0 := hv
    rw [hv', inner_zero_left] at h
    have : ‖v‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp this
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  exact hsurj g

end LongTails.Proofs.LogFreeLinearAlgebra
