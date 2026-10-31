import LongTails.Proofs.GdConvex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.MultiplicativeAccelerationEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma coupling {f : E → ℝ} {x z u y g v d : E} {A a η L : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hB : 0 < A + a)
    (hy : (A + a) • y = A • x + a • z)
    (hx : f y + ⟪g, x - y⟫ ≤ f x)
    (hu : f y + ⟪g, u - y⟫ ≤ f u)
    (hd : f (y - η • d) ≤ f y - η * ⟪g, d⟫ + L * η ^ 2 / 2 * ‖d‖ ^ 2) :
    (A + a) * (f (y - η • d) - f u) + ‖z - a • v - u‖ ^ 2 / 2 ≤
      A * (f x - f u) + ‖z - u‖ ^ 2 / 2 - a * ⟪v - g, z - u⟫ -
        (A + a) * η * ⟪g, d⟫ + (A + a) * L * η ^ 2 / 2 * ‖d‖ ^ 2 + a ^ 2 / 2 * ‖v‖ ^ 2 := by
  have hid : A • (x - y) + a • (u - y) = a • (u - z) := by
    have h : A • (x - y) + a • (u - y) =
        a • (u - z) + (A • x + a • z - (A + a) • y) := by module
    rw [h, hy, sub_self, add_zero]
  have hi := congrArg (fun w => ⟪g, w⟫) hid
  simp only [inner_add_right, inner_smul_right] at hi
  have hn : ⟪g, u - z⟫ = -⟪g, z - u⟫ := by rw [← neg_sub, inner_neg_right]
  rw [hn] at hi
  have hx' := mul_le_mul_of_nonneg_left hx hA
  have hu' := mul_le_mul_of_nonneg_left hu ha
  have hd' := mul_le_mul_of_nonneg_left hd hB.le
  have hz : z - a • v - u = (z - u) - a • v := by module
  rw [hz, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  rw [real_inner_comm v (z - u), inner_sub_left]
  nlinarith

lemma coupling_error {f : E → ℝ} {x z u y g v d : E} {A a L : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a) (hB : 0 < A + a) (hL : 0 < L)
    (hy : (A + a) • y = A • x + a • z)
    (hx : f y + ⟪g, x - y⟫ ≤ f x)
    (hu : f y + ⟪g, u - y⟫ ≤ f u)
    (hd : f (y - (1/L) • d) ≤ f y - (1/L) * ⟪g, d⟫ + L * (1/L)^2 / 2 * ‖d‖^2) :
    (A + a) * (f (y - (1/L) • d) - f u) + ‖z - a • v - u‖^2 / 2 ≤
      A * (f x-f u) + ‖z-u‖^2/2 - a*⟪v-g,z-u⟫ -
        (A+a)/(2*L)*‖g‖^2 + (A+a)/(2*L)*‖d-g‖^2 + a^2/2*‖v‖^2 := by
  apply (coupling hA ha hB hy hx hu hd).trans_eq
  rw [norm_sub_sq_real d g, real_inner_comm d g]
  field_simp [hL.ne']
  ring

lemma relative_bias_absorption {B η a V α r s : ℝ}
    (hB : 0 < B) (hη : 0 < η) (hV : 0 < V)
    (ha : a ^ 2 * V ≤ B * η / 4) :
    a * α * r * s ≤ B * η / 4 * s ^ 2 + α ^ 2 / (4 * V) * r ^ 2 := by
  have hs := sq_nonneg (B * η * s - 2 * a * α * r)
  have hp := mul_le_mul_of_nonneg_right ha (sq_nonneg (α * r))
  have hsV := mul_nonneg hV.le hs
  apply (mul_le_mul_iff_right₀ (show 0 < 4 * V * (B * η) by positivity)).mp
  field_simp
  have hsum : 0 ≤ B * η * (V * B * η * s ^ 2 + α ^ 2 * r ^ 2 - 4 * V * a * α * r * s) := by
    nlinarith only [hsV, hp]
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left (mul_pos hB hη)).mp hsum)

lemma energy_growth {B η a V α r s U U' : ℝ}
    (hB : 0 < B) (hη : 0 < η) (hV : 0 < V)
    (ha : a ^ 2 * V ≤ B * η / 4) (hr : r ^ 2 ≤ 2 * U)
    (hstep : U' ≤ U + a * α * r * s - B * η / 2 * s ^ 2) :
    U' ≤ (1 + α ^ 2 / (2 * V)) * U := by
  have hb := relative_bias_absorption hB hη hV ha (α := α) (r := r) (s := s)
  have hc := mul_le_mul_of_nonneg_left hr (show 0 ≤ α ^ 2 / (4 * V) by positivity)
  have hs : 0 ≤ B * η / 4 * s ^ 2 := by positivity
  have he : α ^ 2 / (4 * V) * (2 * U) = α ^ 2 / (2 * V) * U := by ring
  rw [he] at hc
  nlinarith only [hstep, hb, hc, hs]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
lemma expected_energy_growth {d v : Ω → E} {F : Ω → ℝ} {g z : E} {U B L a V α : ℝ}
    (hB : 0 < B) (hL : 0 < L) (ha : 0 ≤ a) (hV : 0 < V)
    (hstep : a^2*V ≤ B/(16*L)) (hz : ‖z‖^2 ≤ 2*U)
    (hvi : Integrable v P)
    (hdi : Integrable (fun ω => ‖d ω-g‖^2) P)
    (hv2i : Integrable (fun ω => ‖v ω‖^2) P) (hFi : Integrable F P)
    (hdm : (∫ ω, ‖d ω-g‖^2 ∂P) ≤ ‖g‖^2/64)
    (hvm : (∫ ω, ‖v ω‖^2 ∂P) ≤ V*‖g‖^2)
    (hbias : ‖(∫ ω, v ω ∂P)-g‖ ≤ α*‖g‖)
    (hpoint : ∀ ω, F ω ≤ U-a*⟪v ω-g,z⟫-B/(2*L)*‖g‖^2+
      B/(2*L)*‖d ω-g‖^2+a^2/2*‖v ω‖^2) :
    (∫ ω, F ω ∂P) ≤ (1+α^2/(2*V))*U := by
  have hvinner : Integrable (fun ω => ⟪v ω-g,z⟫) P :=
    (hvi.sub (integrable_const g)).inner_const z
  have h0 : Integrable (fun ω => U-a*⟪v ω-g,z⟫) P :=
    (integrable_const U).sub (hvinner.const_mul a)
  have h1 : Integrable (fun ω => U-a*⟪v ω-g,z⟫-B/(2*L)*‖g‖^2) P :=
    h0.sub (integrable_const _)
  have h2 : Integrable (fun ω => U-a*⟪v ω-g,z⟫-B/(2*L)*‖g‖^2+
      B/(2*L)*‖d ω-g‖^2) P := h1.add (hdi.const_mul _)
  have hright : Integrable (fun ω => U-a*⟪v ω-g,z⟫-B/(2*L)*‖g‖^2+
      B/(2*L)*‖d ω-g‖^2+a^2/2*‖v ω‖^2) P := h2.add (hv2i.const_mul _)
  have h := integral_mono hFi hright hpoint
  rw [integral_add h2 (hv2i.const_mul _),
    integral_add h1 (hdi.const_mul _),
    integral_sub h0 (integrable_const _),
    integral_sub (integrable_const U) (hvinner.const_mul a)] at h
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul] at h
  have hvsub : Integrable (fun ω => v ω-g) P := hvi.sub (integrable_const g)
  have heinner : (∫ ω, ⟪v ω-g,z⟫ ∂P) = ⟪(∫ ω, v ω ∂P)-g,z⟫ := by
    calc
      _ = ∫ ω, ⟪z,v ω-g⟫ ∂P := integral_congr_ae
        (Filter.Eventually.of_forall (fun ω => real_inner_comm _ _))
      _ = _ := by
        rw [integral_inner hvsub z, integral_sub hvi (integrable_const g)]
        simp only [integral_const, probReal_univ, one_smul, real_inner_comm]
  rw [heinner] at h
  have hb : -a*⟪(∫ ω, v ω ∂P)-g,z⟫ ≤ a*α*‖z‖*‖g‖ := by
    have hi := (neg_le_abs ⟪(∫ ω, v ω ∂P)-g,z⟫).trans
      (abs_real_inner_le_norm _ _)
    have hn := hi.trans (mul_le_mul_of_nonneg_right hbias (norm_nonneg _))
    have ht := mul_le_mul_of_nonneg_left hn ha
    nlinarith only [ht]
  have hderr := mul_le_mul_of_nonneg_left hdm (show 0 ≤ B/(2*L) by positivity)
  have hverr := mul_le_mul_of_nonneg_left hvm (show 0 ≤ a^2/2 by positivity)
  have hvar := mul_le_mul_of_nonneg_right hstep (sq_nonneg ‖g‖)
  have hloss : (∫ ω, F ω ∂P) ≤ U+a*α*‖z‖*‖g‖-B*(1/(4*L))/2*‖g‖^2 := by
    have hn : 0 ≤ B/L*‖g‖^2 := by positivity
    simp only [div_eq_mul_inv, mul_inv_rev] at h hderr hverr hvar hn ⊢
    norm_num at h hderr hverr hvar hn ⊢
    nlinarith only [h, hb, hderr, hverr, hvar, hn]
  apply energy_growth hB (by positivity : 0 < 1/(4*L)) hV _ hz hloss
  convert hstep using 1; ring

end LongTails.Proofs.MultiplicativeAccelerationEnergy
