import LongTails.Algorithms.AdjointAnchoredProximal
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous

open scoped RealInnerProductSpace
open Filter Topology

namespace OracleTemplate.CohypomonotoneAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Hyp (F : E → E) (J : E → E →L[ℝ] E) (L L₂ ρ : ℝ) : Prop where
  deriv : ∀ x, HasFDerivAt F (J x) x
  jlip : ∀ x y, ‖J x - J y‖ ≤ L₂ * ‖x - y‖
  lip : ∀ x y, ‖F x - F y‖ ≤ L * ‖x - y‖
  cohypo : ∀ x y, -ρ * ‖F x - F y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫

variable {F : E → E} {J : E → E →L[ℝ] E} {L L₂ ρ : ℝ}

lemma Hyp.jnorm (h : Hyp F J L L₂ ρ) (hL : 0 ≤ L) (x : E) : ‖J x‖ ≤ L :=
  (h.deriv x).le_of_lip' hL (Eventually.of_forall fun y => h.lip y x)

lemma Hyp.jcohypo (h : Hyp F J L L₂ ρ) (x v : E) : -ρ * ‖J x v‖ ^ 2 ≤ ⟪J x v, v⟫ := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h2 : HasDerivAt (fun t : ℝ => F (x + t • v)) (J x v) 0 := by
    have hd : HasFDerivAt F (J x) ((fun t : ℝ => x + t • v) 0) := by
      simpa using h.deriv x
    exact hd.comp_hasDerivAt (0 : ℝ) h1
  have ht := h2.tendsto_slope_zero_right
  have hl : Tendsto (fun t : ℝ => -ρ * ‖t⁻¹ • (F (x + (0 + t) • v) - F (x + (0 : ℝ) • v))‖ ^ 2)
      (𝓝[>] 0) (𝓝 (-ρ * ‖J x v‖ ^ 2)) :=
    (((Filter.Tendsto.norm ht).pow 2).const_mul (-ρ))
  have hr : Tendsto (fun t : ℝ => ⟪t⁻¹ • (F (x + (0 + t) • v) - F (x + (0 : ℝ) • v)), v⟫)
      (𝓝[>] 0) (𝓝 ⟪J x v, v⟫) :=
    Filter.Tendsto.inner ht tendsto_const_nhds
  refine le_of_tendsto_of_tendsto hl hr ?_
  filter_upwards [self_mem_nhdsWithin] with t (htpos : 0 < t)
  simp only [zero_add, zero_smul, add_zero]
  have hc := h.cohypo (x + t • v) x
  have e : x + t • v - x = t • v := by abel
  rw [e, inner_smul_right] at hc
  rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, abs_of_pos htpos, real_inner_smul_left]
  have ht2 : 0 < t ^ 2 := by positivity
  have key : -ρ * ‖F (x + t • v) - F x‖ ^ 2 / t ^ 2 ≤
      t * ⟪F (x + t • v) - F x, v⟫ / t ^ 2 := div_le_div_of_nonneg_right hc ht2.le
  have e1 : -ρ * ((t⁻¹) ^ 2 * ‖F (x + t • v) - F x‖ ^ 2) =
      -ρ * ‖F (x + t • v) - F x‖ ^ 2 / t ^ 2 := by field_simp
  have e2 : t⁻¹ * ⟪F (x + t • v) - F x, v⟫ = t * ⟪F (x + t • v) - F x, v⟫ / t ^ 2 := by
    field_simp
  rw [e1, e2]
  exact key

lemma Hyp.dlower (h : Hyp F J L L₂ ρ) {γ : ℝ} (hγ : 2 * ρ ≤ γ) (hγ0 : 0 ≤ γ) (x v : E) :
    ‖v‖ ≤ ‖v + γ • J x v‖ := by
  have hc := h.jcohypo x v
  have hc' : -ρ * ‖J x v‖ ^ 2 ≤ ⟪v, J x v⟫ := by rwa [real_inner_comm] at hc
  have hsq : ‖v‖ ^ 2 ≤ ‖v + γ • J x v‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0, real_inner_smul_right]
    have hJ := sq_nonneg ‖J x v‖
    nlinarith [mul_le_mul_of_nonneg_left hc' hγ0, mul_nonneg hγ0 (mul_nonneg (sub_nonneg.mpr hγ) hJ)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

section Adjoint

variable {x r b : E} {γ : ℝ}

lemma adj_inner (hb : ∀ h, ⟪b, h⟫ = ⟪r, J x h⟫) (h : E) :
    ⟪r + γ • b, h⟫ = ⟪r, h + γ • J x h⟫ := by
  rw [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hb]

lemma adj_upper (hJ : ‖J x‖ ≤ L) (hγ0 : 0 ≤ γ) (hb : ∀ h, ⟪b, h⟫ = ⟪r, J x h⟫) :
    ‖r + γ • b‖ ≤ (1 + γ * L) * ‖r‖ := by
  set a := r + γ • b with ha
  have hDa : ‖a + γ • J x a‖ ≤ (1 + γ * L) * ‖a‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]
    have := (J x).le_of_opNorm_le hJ a
    nlinarith [norm_nonneg a]
  have hsq : ‖a‖ ^ 2 ≤ ‖r‖ * ((1 + γ * L) * ‖a‖) := by
    rw [← real_inner_self_eq_norm_sq, adj_inner hb]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hDa (norm_nonneg r))
  have hL : 0 ≤ L := (norm_nonneg _).trans hJ
  rcases (norm_nonneg a).eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg (by positivity) (norm_nonneg r)
  · nlinarith

lemma adj_Dnorm (hJ : ‖J x‖ ≤ L) (hγ0 : 0 ≤ γ) (a : E) :
    ‖a + γ • J x a‖ ≤ (1 + γ * L) * ‖a‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]
  have := (J x).le_of_opNorm_le hJ a
  nlinarith [norm_nonneg a]

lemma adj_Dinner (hb : ∀ h, ⟪b, h⟫ = ⟪r, J x h⟫) :
    ⟪(r + γ • b) + γ • J x (r + γ • b), r⟫ = ‖r + γ • b‖ ^ 2 := by
  rw [real_inner_comm, ← adj_inner hb, real_inner_self_eq_norm_sq]

lemma adj_lower [FiniteDimensional ℝ E] (h : Hyp F J L L₂ ρ) (hγ : 2 * ρ ≤ γ) (hγ0 : 0 ≤ γ)
    (hb : ∀ h, ⟪b, h⟫ = ⟪r, J x h⟫) : ‖r‖ ≤ ‖r + γ • b‖ := by
  let D : E →ₗ[ℝ] E := LinearMap.id + γ • ((J x : E →L[ℝ] E) : E →ₗ[ℝ] E)
  have hDv : ∀ v, D v = v + γ • J x v := fun v => rfl
  have hinj : Function.Injective D := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have := h.dlower hγ hγ0 x v
    rw [← hDv, hv, norm_zero] at this
    exact norm_le_zero_iff.mp this
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.mp hinj) r
  have hwr : ‖w‖ ≤ ‖r‖ := by
    have := h.dlower hγ hγ0 x w
    rwa [← hDv, hw] at this
  have hsq : ‖r‖ ^ 2 ≤ ‖r + γ • b‖ * ‖r‖ := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => rw [show ⟪r, r⟫ = ⟪r, D w⟫ by rw [hw]]
    rw [hDv, ← adj_inner hb]
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hwr (norm_nonneg _))
  rcases (norm_nonneg r).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

end Adjoint

lemma Hyp.taylor (h : Hyp F J L L₂ ρ) (hL₂ : 0 ≤ L₂) (v d : E) :
    ‖F (v + d) - F v - J v d‖ ≤ L₂ * ‖d‖ ^ 2 := by
  have hconv : Convex ℝ (Metric.closedBall v ‖d‖) := convex_closedBall v ‖d‖
  have hderiv : ∀ z ∈ Metric.closedBall v ‖d‖,
      HasFDerivWithinAt (fun z => F z - J v z) (J z - J v) (Metric.closedBall v ‖d‖) z :=
    fun z _ => ((h.deriv z).sub (J v).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ Metric.closedBall v ‖d‖, ‖J z - J v‖ ≤ L₂ * ‖d‖ := by
    intro z hz
    have hz' : ‖z - v‖ ≤ ‖d‖ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
    exact (h.jlip z v).trans (mul_le_mul_of_nonneg_left hz' hL₂)
  have hv : v ∈ Metric.closedBall v ‖d‖ := Metric.mem_closedBall_self (norm_nonneg d)
  have hvd : v + d ∈ Metric.closedBall v ‖d‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have key := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound hv hvd
  have e : F (v + d) - J v (v + d) - (F v - J v v) = F (v + d) - F v - J v d := by
    rw [map_add]; abel
  rw [e, add_sub_cancel_left] at key
  calc ‖F (v + d) - F v - J v d‖ ≤ L₂ * ‖d‖ * ‖d‖ := key
    _ = L₂ * ‖d‖ ^ 2 := by ring

lemma contraction_core (r a Da : E) {α Λ : ℝ} (hα0 : 0 ≤ α) (hΛ : 1 ≤ Λ)
    (hαΛ : α * Λ ^ 2 ≤ 1) (hDin : ⟪Da, r⟫ = ‖a‖ ^ 2) (hDa : ‖Da‖ ≤ Λ * ‖a‖)
    (hlow : ‖r‖ ≤ ‖a‖) : ‖r - α • Da‖ ≤ (1 - α / 2) * ‖r‖ := by
  have hα1 : α ≤ 1 := by
    have h1 : (1 : ℝ) ≤ Λ ^ 2 := one_le_pow₀ hΛ
    nlinarith [mul_le_mul_of_nonneg_left h1 hα0]
  have hsq : ‖r - α • Da‖ ^ 2 ≤ (1 - α) * ‖r‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm, hDin, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hα0, mul_pow]
    have h1 : ‖Da‖ ^ 2 ≤ Λ ^ 2 * ‖a‖ ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg _) hDa
      nlinarith
    have h2 : ‖r‖ ^ 2 ≤ ‖a‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg r) hlow 2
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg α), sq_nonneg α,
      mul_le_mul_of_nonneg_left hαΛ (mul_nonneg hα0 (sq_nonneg ‖a‖))]
  have hnn : 0 ≤ 1 - α / 2 := by linarith
  have hsq2 : (1 - α) * ‖r‖ ^ 2 ≤ ((1 - α / 2) * ‖r‖) ^ 2 := by
    nlinarith [sq_nonneg (α * ‖r‖), sq_nonneg ‖r‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hnn (norm_nonneg r))
    two_ne_zero).mp (hsq.trans hsq2)

lemma step_decrease [FiniteDimensional ℝ E] (h : Hyp F J L L₂ ρ) (hL : 0 ≤ L) (hL₂ : 0 ≤ L₂)
    {γ α : ℝ} (hγ : 2 * ρ ≤ γ) (hγ0 : 0 ≤ γ) (hα0 : 0 ≤ α)
    (hα1 : α * (1 + γ * L) ^ 2 ≤ 1)
    (t v b : E) (hb : ∀ h, ⟪b, h⟫ = ⟪v + γ • F v - t, J v h⟫)
    (hE : γ * L₂ * α ^ 2 * (1 + γ * L) ^ 2 * ‖v + γ • F v - t‖ ^ 2 ≤
      α / 4 * ‖v + γ • F v - t‖) :
    ‖(v - α • (v + γ • F v - t + γ • b)) + γ • F (v - α • (v + γ • F v - t + γ • b)) - t‖ ≤
      (1 - α / 4) * ‖v + γ • F v - t‖ := by
  set r := v + γ • F v - t with hr
  set a := r + γ • b with ha
  set w := v - α • a with hw
  have hJ := h.jnorm hL v
  have hlow := adj_lower h hγ hγ0 hb
  have hup := adj_upper hJ hγ0 hb
  have hDa := adj_Dnorm hJ hγ0 a
  have hDin := adj_Dinner (γ := γ) hb
  rw [← ha] at hlow hup hDin
  set E1 := F w - F v - J v (w - v) with hE1
  have hrw : w + γ • F w - t = (r - α • (a + γ • J v a)) + γ • E1 := by
    rw [hE1, hr, hw, show v - α • a - v = -(α • a) by abel, map_neg, map_smul]
    module
  have hα1' : α ≤ 1 := by
    have : 1 ≤ (1 + γ * L) ^ 2 := by nlinarith [mul_nonneg hγ0 hL]
    nlinarith
  have hmain : ‖r - α • (a + γ • J v a)‖ ≤ (1 - α / 2) * ‖r‖ :=
    contraction_core r a (a + γ • J v a) hα0 (by nlinarith [mul_nonneg hγ0 hL]) hα1 hDin hDa hlow
  have hE1n : ‖γ • E1‖ ≤ α / 4 * ‖r‖ := by
    have ht := h.taylor hL₂ v (w - v)
    rw [show v + (w - v) = w by abel] at ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ0]
    have hwv : ‖w - v‖ = α * ‖a‖ := by
      rw [hw, show v - α • a - v = -(α • a) by abel, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hα0]
    rw [hwv] at ht
    have hup2 : (α * ‖a‖) ^ 2 ≤ α ^ 2 * (1 + γ * L) ^ 2 * ‖r‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hup hα0
      nlinarith [norm_nonneg a, mul_nonneg hα0 (norm_nonneg a)]
    calc γ * ‖E1‖ ≤ γ * (L₂ * (α * ‖a‖) ^ 2) := mul_le_mul_of_nonneg_left ht hγ0
      _ ≤ γ * (L₂ * (α ^ 2 * (1 + γ * L) ^ 2 * ‖r‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hup2 hL₂) hγ0
      _ = γ * L₂ * α ^ 2 * (1 + γ * L) ^ 2 * ‖r‖ ^ 2 := by ring
      _ ≤ α / 4 * ‖r‖ := hE
  rw [hrw]
  calc ‖(r - α • (a + γ • J v a)) + γ • E1‖ ≤ ‖r - α • (a + γ • J v a)‖ + ‖γ • E1‖ :=
        norm_add_le _ _
    _ ≤ (1 - α / 2) * ‖r‖ + α / 4 * ‖r‖ := add_le_add hmain hE1n
    _ = (1 - α / 4) * ‖r‖ := by ring

end OracleTemplate.CohypomonotoneAdjoint
