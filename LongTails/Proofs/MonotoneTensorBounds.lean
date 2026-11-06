import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import LongTails.Proofs.FrozenJacobianSplitting

open scoped RealInnerProductSpace

namespace LongTails.Proofs.MonotoneTensorBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure Regular (F : E → E) (L : ℝ) : Prop where
  smooth : ContDiff ℝ 2 F
  lip : ∀ x y, ‖fderiv ℝ (fderiv ℝ F) x - fderiv ℝ (fderiv ℝ F) y‖ ≤ L * ‖x - y‖
  mono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫
  nonneg : 0 ≤ L

variable {F : E → E} {L : ℝ}

lemma Regular.hasFDerivAt (h : Regular F L) (x : E) : HasFDerivAt F (fderiv ℝ F x) x :=
  ((h.smooth.differentiable (by norm_num)) x).hasFDerivAt

lemma Regular.hasFDerivAt_fderiv (h : Regular F L) (x : E) :
    HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) x) x := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ F) := h.smooth.fderiv_right (m := 1) (by norm_num)
  exact ((h1.differentiable (by norm_num)) x).hasFDerivAt

lemma Regular.symm (h : Regular F L) (x v w : E) :
    fderiv ℝ (fderiv ℝ F) x v w = fderiv ℝ (fderiv ℝ F) x w v :=
  (h.smooth.contDiffAt.isSymmSndFDerivAt (by simp)) v w

lemma Regular.psd (h : Regular F L) (x u : E) : 0 ≤ ⟪fderiv ℝ F x u, u⟫ :=
  LongTails.Proofs.FrozenJacobianSplitting.jacobian_monotone h.mono (h.hasFDerivAt x) u

lemma Regular.jac_taylor (h : Regular F L) (x y : E) :
    ‖fderiv ℝ F y - fderiv ℝ F x - fderiv ℝ (fderiv ℝ F) x (y - x)‖ ≤ L * ‖y - x‖ ^ 2 := by
  set B := fderiv ℝ (fderiv ℝ F)
  set r := ‖y - x‖
  have hs : Convex ℝ (Metric.closedBall x r) := convex_closedBall x r
  have hf : ∀ z ∈ Metric.closedBall x r,
      HasFDerivWithinAt (fun z => fderiv ℝ F z - B x (z - x)) (B z - B x)
        (Metric.closedBall x r) z := by
    intro z _
    have h1 := h.hasFDerivAt_fderiv z
    have h2 : HasFDerivAt (fun z => B x (z - x)) (B x) z := by
      have h3 := ((B x).hasFDerivAt).comp z ((hasFDerivAt_id z).sub_const x)
      simp only [ContinuousLinearMap.comp_id] at h3
      exact h3
    exact (h1.sub h2).hasFDerivWithinAt
  have hb : ∀ z ∈ Metric.closedBall x r, ‖B z - B x‖ ≤ L * r := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact (h.lip z x).trans (mul_le_mul_of_nonneg_left hz h.nonneg)
  have := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hf hb
    (Metric.mem_closedBall_self (norm_nonneg _))
    (by rw [Metric.mem_closedBall, dist_eq_norm])
  simp only [sub_self, map_zero, sub_zero] at this
  calc ‖fderiv ℝ F y - fderiv ℝ F x - B x (y - x)‖
      = ‖fderiv ℝ F y - B x (y - x) - fderiv ℝ F x‖ := by congr 1; abel
    _ ≤ L * r * ‖y - x‖ := this
    _ = L * ‖y - x‖ ^ 2 := by ring

lemma Regular.taylor (h : Regular F L) (x y : E) :
    ‖F y - F x - fderiv ℝ F x (y - x) - (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ F) x (y - x) (y - x)‖ ≤
      L * ‖y - x‖ ^ 3 := by
  set B := fderiv ℝ (fderiv ℝ F)
  set J := fderiv ℝ F
  set v := y - x
  set φ : ℝ → E := fun t => F (x + t • v) - t • J x v - (t ^ 2 / 2) • B x v v
  set φ' : ℝ → E := fun t => J (x + t • v) v - J x v - t • B x v v
  have hderiv : ∀ t, HasDerivAt φ (φ' t) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h1 : HasDerivAt (fun t => F (x + t • v)) (J (x + t • v) v) t :=
      (h.hasFDerivAt (x + t • v)).comp_hasDerivAt t hl
    have h2 : HasDerivAt (fun t : ℝ => t • J x v) (J x v) t := by
      simpa using (hasDerivAt_id t).smul_const (J x v)
    have h3 : HasDerivAt (fun t : ℝ => (t ^ 2 / 2) • B x v v) (t • B x v v) t := by
      have := ((hasDerivAt_pow 2 t).div_const 2).smul_const (B x v v)
      convert this using 1
      congr 1; norm_num
    exact (h1.sub h2).sub h3
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖φ' t‖ ≤ L * ‖v‖ ^ 3 := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2.le
    have hjt := h.jac_taylor x (x + t • v)
    have hsub : x + t • v - x = t • v := by abel
    rw [hsub] at hjt
    have heq : φ' t = (J (x + t • v) - J x - B x (t • v)) v := by
      simp only [φ', sub_apply, map_smul, smul_apply]
    rw [heq]
    have hn : ‖t • v‖ ≤ ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      exact mul_le_of_le_one_left (norm_nonneg _) ht1
    calc ‖(J (x + t • v) - J x - B x (t • v)) v‖
        ≤ ‖J (x + t • v) - J x - B x (t • v)‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * ‖t • v‖ ^ 2 * ‖v‖ := by gcongr
      _ ≤ L * ‖v‖ ^ 2 * ‖v‖ := by have := h.nonneg; gcongr
      _ = L * ‖v‖ ^ 3 := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t _ => (hderiv t).hasDerivWithinAt) hbound 1 (by simp)
  have e1 : φ 1 = F y - J x v - (1 / 2 : ℝ) • B x v v := by
    simp only [φ, one_smul, v]; norm_num
  have e0 : φ 0 = F x := by simp [φ]
  rw [e1, e0] at hmvt
  calc ‖F y - F x - J x v - (1 / 2 : ℝ) • B x v v‖
      = ‖F y - J x v - (1 / 2 : ℝ) • B x v v - F x‖ := by congr 1; abel
    _ ≤ L * ‖v‖ ^ 3 * (1 - 0) := hmvt
    _ = L * ‖v‖ ^ 3 := by ring

lemma Regular.tau_bound (h : Regular F L) (x hv u : E) {τ : ℝ} (hτ : 0 < τ) :
    |⟪fderiv ℝ (fderiv ℝ F) x hv u, u⟫| ≤
      ⟪fderiv ℝ F x u, u⟫ / τ + L * τ * ‖hv‖ ^ 2 * ‖u‖ ^ 2 := by
  set B := fderiv ℝ (fderiv ℝ F)
  set J := fderiv ℝ F
  have side : ∀ v : E, ‖v‖ = ‖hv‖ →
      -(τ * ⟪B x v u, u⟫) ≤ ⟪J x u, u⟫ + L * τ ^ 2 * ‖hv‖ ^ 2 * ‖u‖ ^ 2 := by
    intro v hv'
    have ht := h.jac_taylor x (x + τ • v)
    have hpsd := h.psd (x + τ • v) u
    have hsub : x + τ • v - x = τ • v := by abel
    rw [hsub] at ht
    set Er := J (x + τ • v) - J x - B x (τ • v)
    have hEr : |⟪Er u, u⟫| ≤ L * τ ^ 2 * ‖hv‖ ^ 2 * ‖u‖ ^ 2 := by
      have h1 : |⟪Er u, u⟫| ≤ ‖Er u‖ * ‖u‖ := abs_real_inner_le_norm _ _
      have h2 : ‖Er u‖ ≤ ‖Er‖ * ‖u‖ := Er.le_opNorm u
      have h3 : ‖Er‖ ≤ L * (τ ^ 2 * ‖hv‖ ^ 2) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ, hv'] at ht
        nlinarith [ht]
      calc |⟪Er u, u⟫| ≤ ‖Er‖ * ‖u‖ * ‖u‖ := by nlinarith [norm_nonneg u]
        _ ≤ L * (τ ^ 2 * ‖hv‖ ^ 2) * ‖u‖ * ‖u‖ := by gcongr
        _ = L * τ ^ 2 * ‖hv‖ ^ 2 * ‖u‖ ^ 2 := by ring
    have hdecomp : ⟪J (x + τ • v) u, u⟫ = ⟪J x u, u⟫ + τ * ⟪B x v u, u⟫ + ⟪Er u, u⟫ := by
      have : J (x + τ • v) = J x + τ • B x v + Er := by
        simp only [Er, map_smul]; abel
      rw [this]
      simp only [add_apply, smul_apply,
        inner_add_left, real_inner_smul_left]
    have := le_abs_self ⟪Er u, u⟫
    linarith
  have h1 := side hv rfl
  have h2 := side (-hv) (norm_neg hv)
  simp only [map_neg, neg_apply, inner_neg_left, mul_neg, neg_neg] at h2
  rw [abs_le]
  constructor
  · have : -(⟪J x u, u⟫ / τ + L * τ * ‖hv‖ ^ 2 * ‖u‖ ^ 2) * τ ≤ ⟪B x hv u, u⟫ * τ := by
      rw [neg_mul, add_mul, div_mul_cancel₀ _ hτ.ne']; nlinarith
    exact le_of_mul_le_mul_right this hτ
  · have : ⟪B x hv u, u⟫ * τ ≤ (⟪J x u, u⟫ / τ + L * τ * ‖hv‖ ^ 2 * ‖u‖ ^ 2) * τ := by
      rw [add_mul, div_mul_cancel₀ _ hτ.ne']; nlinarith
    exact le_of_mul_le_mul_right this hτ

lemma inf_amgm {t a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : ∀ X > 0, t ≤ X * a + b / X) :
    t ≤ 2 * Real.sqrt (a * b) := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · subst ha0
    simp only [zero_mul, Real.sqrt_zero, mul_zero]
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := h ((b + 1) / δ) (by positivity)
    simp only [mul_zero, zero_add] at this
    have hle : b / ((b + 1) / δ) ≤ δ := by
      rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · subst hb0
    simp only [mul_zero, Real.sqrt_zero, mul_zero]
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := h (δ / (a + 1)) (by positivity)
    simp only [zero_div, add_zero] at this
    have hle : δ / (a + 1) * a ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hX : 0 < Real.sqrt (b / a) := Real.sqrt_pos.mpr (div_pos hb0 ha0)
  have := h (Real.sqrt (b / a)) hX
  have h1 : Real.sqrt (b / a) * a = Real.sqrt (a * b) := by
    calc Real.sqrt (b / a) * a = Real.sqrt (b / a) * Real.sqrt (a ^ 2) := by
          rw [Real.sqrt_sq ha]
      _ = Real.sqrt (b / a * a ^ 2) := (Real.sqrt_mul (div_nonneg hb ha) _).symm
      _ = Real.sqrt (a * b) := by congr 1; field_simp
  have h2 : b / Real.sqrt (b / a) = Real.sqrt (a * b) := by
    calc b / Real.sqrt (b / a) = Real.sqrt (b ^ 2) / Real.sqrt (b / a) := by
          rw [Real.sqrt_sq hb]
      _ = Real.sqrt (b ^ 2 / (b / a)) := (Real.sqrt_div' _ (div_nonneg hb ha)).symm
      _ = Real.sqrt (a * b) := by congr 1; field_simp
  linarith

lemma inf_amgm₂ {t a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : ∀ X > 0, ∀ Y > 0, t ≤ X * a + b / X + (Y * c + d / Y)) :
    t ≤ 2 * Real.sqrt (a * b) + 2 * Real.sqrt (c * d) := by
  have hY : ∀ Y > 0, t - (Y * c + d / Y) ≤ 2 * Real.sqrt (a * b) := fun Y hY =>
    inf_amgm ha hb fun X hX => by linarith [h X hX Y hY]
  have := inf_amgm (t := t - 2 * Real.sqrt (a * b)) hc hd fun Y hY' => by linarith [hY Y hY']
  linarith

noncomputable def sn (F : E → E) (x u : E) : ℝ := Real.sqrt ⟪fderiv ℝ F x u, u⟫

lemma Regular.sn_sq (h : Regular F L) (x u : E) : sn F x u ^ 2 = ⟪fderiv ℝ F x u, u⟫ :=
  Real.sq_sqrt (h.psd x u)

lemma sn_nonneg (x u : E) : 0 ≤ sn F x u := Real.sqrt_nonneg _

lemma sn_le (x u : E) :
    sn F x u ≤ Real.sqrt ‖fderiv ℝ F x‖ * ‖u‖ := by
  unfold sn
  rw [← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul (norm_nonneg _)]
  apply Real.sqrt_le_sqrt
  calc ⟪fderiv ℝ F x u, u⟫ ≤ ‖fderiv ℝ F x u‖ * ‖u‖ := real_inner_le_norm _ _
    _ ≤ ‖fderiv ℝ F x‖ * ‖u‖ * ‖u‖ := by gcongr; exact (fderiv ℝ F x).le_opNorm u
    _ = ‖fderiv ℝ F x‖ * ‖u‖ ^ 2 := by ring

lemma parallelogram_form (A : E →L[ℝ] E) (y z : E) :
    ⟪A (y + z), y + z⟫ + ⟪A (y - z), y - z⟫ = 2 * ⟪A y, y⟫ + 2 * ⟪A z, z⟫ := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  ring

lemma polar_form (A : E →L[ℝ] E) (y z : E) :
    ⟪A (y + z), y + z⟫ - ⟪A (y - z), y - z⟫ = 2 * (⟪A y, z⟫ + ⟪A z, y⟫) := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  ring

lemma Regular.pair_bound (h : Regular F L) (x hv u v : E) :
    |⟪fderiv ℝ (fderiv ℝ F) x hv u, v⟫ + ⟪fderiv ℝ (fderiv ℝ F) x hv v, u⟫| ≤
      2 * Real.sqrt L * ‖hv‖ * (sn F x u * ‖v‖ + ‖u‖ * sn F x v) := by
  set B := fderiv ℝ (fderiv ℝ F) x hv
  set J := fderiv ℝ F x
  set β := L * ‖hv‖ ^ 2 with hβ
  have hβ0 : 0 ≤ β := mul_nonneg h.nonneg (sq_nonneg _)
  have hscaled : ∀ t > 0, ∀ τ > 0, |⟪B u, v⟫ + ⟪B v, u⟫| ≤
      t ^ 2 / τ * ⟪J u, u⟫ + β * ‖v‖ ^ 2 / (t ^ 2 / τ) +
        (t ^ 2 * τ * (β * ‖u‖ ^ 2) + ⟪J v, v⟫ / (t ^ 2 * τ)) := by
    intro t ht τ hτ
    set y := t • u
    set z := t⁻¹ • v
    have hq : ∀ w : E, |⟪B w, w⟫| ≤ ⟪J w, w⟫ / τ + L * τ * ‖hv‖ ^ 2 * ‖w‖ ^ 2 :=
      fun w => h.tau_bound x hv w hτ
    have hpol := polar_form B y z
    have hyz : ⟪B y, z⟫ + ⟪B z, y⟫ = ⟪B u, v⟫ + ⟪B v, u⟫ := by
      simp only [y, z, map_smul, real_inner_smul_left, real_inner_smul_right]
      field_simp
    have hpar := parallelogram_form J y z
    have hn : ‖y + z‖ ^ 2 + ‖y - z‖ ^ 2 = 2 * ‖y‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
      have := norm_add_sq_real y z
      have := norm_sub_sq_real y z
      linarith
    have h1 := hq (y + z)
    have h2 := hq (y - z)
    have habs : |2 * (⟪B u, v⟫ + ⟪B v, u⟫)| ≤
        (⟪J (y + z), y + z⟫ + ⟪J (y - z), y - z⟫) / τ +
          L * τ * ‖hv‖ ^ 2 * (‖y + z‖ ^ 2 + ‖y - z‖ ^ 2) := by
      rw [← hyz, ← hpol]
      calc |⟪B (y + z), y + z⟫ - ⟪B (y - z), y - z⟫|
          ≤ |⟪B (y + z), y + z⟫| + |⟪B (y - z), y - z⟫| := abs_sub _ _
        _ ≤ _ := by rw [add_div]; nlinarith [h1, h2]
    rw [hpar, hn] at habs
    have hy : ⟪J y, y⟫ = t ^ 2 * ⟪J u, u⟫ := by
      simp only [y, map_smul, real_inner_smul_left, real_inner_smul_right]; ring
    have hz : ⟪J z, z⟫ = ⟪J v, v⟫ / t ^ 2 := by
      simp only [z, map_smul, real_inner_smul_left, real_inner_smul_right]; field_simp
    have hny : ‖y‖ ^ 2 = t ^ 2 * ‖u‖ ^ 2 := by
      simp only [y, norm_smul, Real.norm_eq_abs, abs_of_pos ht]; ring
    have hnz : ‖z‖ ^ 2 = ‖v‖ ^ 2 / t ^ 2 := by
      simp only [z, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht]; field_simp
    rw [hy, hz, hny, hnz, abs_mul, abs_two] at habs
    have hgoal : t ^ 2 / τ * ⟪J u, u⟫ + β * ‖v‖ ^ 2 / (t ^ 2 / τ) +
        (t ^ 2 * τ * (β * ‖u‖ ^ 2) + ⟪J v, v⟫ / (t ^ 2 * τ)) =
        ((2 * (t ^ 2 * ⟪J u, u⟫) + 2 * (⟪J v, v⟫ / t ^ 2)) / τ +
          L * τ * ‖hv‖ ^ 2 * (2 * (t ^ 2 * ‖u‖ ^ 2) + 2 * (‖v‖ ^ 2 / t ^ 2))) / 2 := by
      rw [hβ]; field_simp; ring
    rw [hgoal]
    linarith
  have hXY : ∀ X > 0, ∀ Y > 0, |⟪B u, v⟫ + ⟪B v, u⟫| ≤
      X * ⟪J u, u⟫ + β * ‖v‖ ^ 2 / X + (Y * (β * ‖u‖ ^ 2) + ⟪J v, v⟫ / Y) := by
    intro X hX Y hY
    set t := Real.sqrt (Real.sqrt (X * Y))
    set τ := Real.sqrt (Y / X)
    have hτ : 0 < τ := Real.sqrt_pos.mpr (div_pos hY hX)
    have ht : 0 < t := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (mul_pos hX hY))
    have ht2 : t ^ 2 = Real.sqrt (X * Y) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have e1 : t ^ 2 / τ = X := by
      rw [ht2, ← Real.sqrt_div' _ (div_nonneg hY.le hX.le),
        show X * Y / (Y / X) = X ^ 2 by field_simp, Real.sqrt_sq hX.le]
    have e2 : t ^ 2 * τ = Y := by
      rw [ht2, ← Real.sqrt_mul (mul_pos hX hY).le]
      rw [show X * Y * (Y / X) = Y * Y by field_simp, Real.sqrt_mul_self hY.le]
    have := hscaled t ht τ hτ
    rwa [e1, e2] at this
  have hfin := inf_amgm₂ (h.psd x u) (by positivity) (by positivity) (h.psd x v) hXY
  have e3 : Real.sqrt (⟪J u, u⟫ * (β * ‖v‖ ^ 2)) = Real.sqrt L * ‖hv‖ * (sn F x u * ‖v‖) := by
    rw [hβ, show ⟪J u, u⟫ * (L * ‖hv‖ ^ 2 * ‖v‖ ^ 2) = L * (‖hv‖ * ‖v‖) ^ 2 * ⟪J u, u⟫ by ring]
    rw [Real.sqrt_mul (mul_nonneg h.nonneg (sq_nonneg _)), Real.sqrt_mul h.nonneg,
      Real.sqrt_sq (by positivity)]
    unfold sn; ring
  have e4 : Real.sqrt (β * ‖u‖ ^ 2 * ⟪J v, v⟫) = Real.sqrt L * ‖hv‖ * (‖u‖ * sn F x v) := by
    rw [hβ, show L * ‖hv‖ ^ 2 * ‖u‖ ^ 2 * ⟪J v, v⟫ = L * (‖hv‖ * ‖u‖) ^ 2 * ⟪J v, v⟫ by ring]
    rw [Real.sqrt_mul (mul_nonneg h.nonneg (sq_nonneg _)), Real.sqrt_mul h.nonneg,
      Real.sqrt_sq (by positivity)]
    unfold sn; ring
  rw [e3, e4] at hfin
  linarith

lemma koszul (B : E →L[ℝ] E →L[ℝ] E) (hB : ∀ v w, B v w = B w v) (u h k : E) :
    2 * ⟪u, B h k⟫ = (⟪B h u, k⟫ + ⟪B h k, u⟫) + (⟪B k u, h⟫ + ⟪B k h, u⟫) -
      (⟪B u h, k⟫ + ⟪B u k, h⟫) := by
  rw [hB h u, hB k u, hB k h, real_inner_comm u]
  ring

lemma Regular.tensor_bound (h : Regular F L) (x u hv k : E) :
    |⟪u, fderiv ℝ (fderiv ℝ F) x hv k⟫| ≤ 2 * Real.sqrt L *
      (sn F x u * ‖hv‖ * ‖k‖ + ‖u‖ * sn F x hv * ‖k‖ + ‖u‖ * ‖hv‖ * sn F x k) := by
  have hk := koszul (fderiv ℝ (fderiv ℝ F) x) (h.symm x) u hv k
  have p1 := h.pair_bound x hv u k
  have p2 := h.pair_bound x k u hv
  have p3 := h.pair_bound x u hv k
  have hs := Real.sqrt_nonneg L
  have : |2 * ⟪u, fderiv ℝ (fderiv ℝ F) x hv k⟫| ≤
      2 * Real.sqrt L * ‖hv‖ * (sn F x u * ‖k‖ + ‖u‖ * sn F x k) +
      2 * Real.sqrt L * ‖k‖ * (sn F x u * ‖hv‖ + ‖u‖ * sn F x hv) +
      2 * Real.sqrt L * ‖u‖ * (sn F x hv * ‖k‖ + ‖hv‖ * sn F x k) := by
    rw [hk]
    refine (abs_sub _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (add_le_add p1 p2)) p3
  rw [abs_mul, abs_two] at this
  nlinarith [this]

end LongTails.Proofs.MonotoneTensorBounds
