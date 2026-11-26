import LongTails.Proofs.EscapeChainSmooth
import LongTails.Proofs.EscapeChainGeometry
import LongTails.Proofs.RelativeHessianCutoffBounds

namespace LongTails.Proofs.EscapeChainCertificate

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus EscapeChainFunction
open EscapeChainCoordinates EscapeChainCount EscapeChainBounds EscapeChainJets EscapeChainSmooth
open EscapeChainGeometry RelativeHessianArctan ThirdOrderJetDifference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

variable {K : ℕ} {u v : ℕ → E}

noncomputable def radius (K : ℕ) : ℝ := 2 ^ 130 * Real.sqrt (K + 1)

lemma radius_pos (K : ℕ) : 0 < radius K := by
  unfold radius; have : 0 < Real.sqrt (K + 1) := Real.sqrt_pos.2 (by positivity); positivity

lemma sqrt_succ_ge (K : ℕ) : 1 ≤ Real.sqrt (K + 1) := by
  exact Real.one_le_sqrt.2 (by linarith [Nat.cast_nonneg (α := ℝ) K])

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma link_nonpos (u v : ℕ → E) (l : ℕ) (x : E) : link u v l x ≤ 0 := by
  unfold link
  have h1 := (lam_bounds ⟪v l, x⟫).1
  have h2 := (prevPsi_bounds u l x).1
  have h3 := (profile_bounds ⟪u l, x⟫).1
  have : 0 ≤ RidgeJets.value lam (v l) x * (prevPsi u l x * RidgeJets.value profile (u l) x) := by
    simp only [RidgeJets.value]; positivity
  nlinarith [strength_pos]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma saddle_nonpos (u v : ℕ → E) (l : ℕ) (x : E) : saddle u v l x ≤ 0 := by
  unfold saddle
  have h1 := (prevGam_bounds u l x).1
  have h2 := sad_nonpos ⟪v l, x⟫
  have h3 := (loc_bounds (quarter u v l x)).1
  simp only [RidgeJets.value]
  have : sad ⟪v l, x⟫ * window u v l x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h2 h3
  exact mul_nonpos_of_nonneg_of_nonpos h1 this

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma hidden_nonpos (K : ℕ) (u v : ℕ → E) (x : E) : hidden K u v x ≤ 0 :=
  Finset.sum_nonpos fun l _ => add_nonpos (link_nonpos u v l x) (saddle_nonpos u v l x)

lemma objective_D (K : ℕ) (R : ℝ) (u v : ℕ → E) (x e : E) :
    D (objective K R u v) x e = RelativeHessianCutoffSpatial.value R x * D (hidden K u v) x e +
      hidden K u v x * D (RelativeHessianCutoffSpatial.value R) x e + ⟪x, e⟫ := by
  have h : objective K R u v = fun y => RelativeHessianCutoffSpatial.value R y * hidden K u v y +
      (1 / 2 : ℝ) * FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E) y := rfl
  have hp := (RelativeHessianCutoffSpatial.smooth R).mul (hidden_smooth K u v)
  have hq := RelativeHessianGuard.quadratic_smooth (E := E) 2
  rw [h, D_add hp (contDiff_const.mul hq), D_mul (RelativeHessianCutoffSpatial.smooth R)
    (hidden_smooth K u v), D_const_mul hq, D_normsq]
  ring

lemma radial (fr : Frame K u v) {g : ℝ} (hg : g ≤ 1) (x : E) (hx : radius K < ‖x‖) :
    g < |D (objective K (radius K) u v) x ((‖x‖⁻¹) • x)| := by
  have hR := radius_pos K
  have hxp : 0 < ‖x‖ := hR.trans hx
  have hD := objective_D K (radius K) u v x x
  obtain ⟨c0, c1⟩ := RelativeHessianCutoff.bounds (RelativeHessianCutoffSpatial.argument (radius K) x)
  have hcut : RelativeHessianCutoffSpatial.value (radius K) x =
      RelativeHessianCutoff.profile (RelativeHessianCutoffSpatial.argument (radius K) x) := rfl
  have hDc : D (RelativeHessianCutoffSpatial.value (radius K)) x x ≤ 0 := by
    unfold D
    rw [RelativeHessianCutoffSpatial.gradient_eq, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    have : RelativeHessianCutoff.first (RelativeHessianCutoffSpatial.argument (radius K) x) ≤ 0 := by
      unfold RelativeHessianCutoff.first
      have := RelativeHessianGate.gateSlope_nonneg
        ((RelativeHessianCutoffSpatial.argument (radius K) x + 2) / 30)
      linarith
    have : 0 ≤ 2 / radius K ^ 2 * ‖x‖ ^ 2 := by positivity
    nlinarith
  have hh := hidden_nonpos K u v x
  have hG := hidden_gradient_bound fr x
  have hDh : |D (hidden K u v) x x| ≤ 2 ^ 123 * Real.sqrt (K + 1) * ‖x‖ := by
    unfold D
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hG (norm_nonneg x))
  have hterm : -(2 ^ 123 * Real.sqrt (K + 1) * ‖x‖) ≤
      RelativeHessianCutoffSpatial.value (radius K) x * D (hidden K u v) x x := by
    rw [hcut]
    have := neg_abs_le (D (hidden K u v) x x)
    nlinarith [abs_nonneg (D (hidden K u v) x x)]
  have hsec : 0 ≤ hidden K u v x * D (RelativeHessianCutoffSpatial.value (radius K)) x x :=
    mul_nonneg_of_nonpos_of_nonpos hh hDc
  have hlow : ‖x‖ ^ 2 - 2 ^ 123 * Real.sqrt (K + 1) * ‖x‖ ≤ D (objective K (radius K) u v) x x := by
    rw [hD, real_inner_self_eq_norm_sq]; linarith
  have hlin : D (objective K (radius K) u v) x ((‖x‖⁻¹) • x) =
      ‖x‖⁻¹ * D (objective K (radius K) u v) x x := by
    unfold D; rw [inner_smul_right]
  rw [hlin, abs_mul, abs_inv, abs_norm]
  have hs1 := sqrt_succ_ge K
  have hbig : 2 ^ 123 * Real.sqrt (K + 1) + 1 < ‖x‖ := by
    have : 2 ^ 123 * Real.sqrt (K + 1) + 1 ≤ radius K := by unfold radius; nlinarith
    linarith
  have hpos : 0 < D (objective K (radius K) u v) x x := by nlinarith
  rw [abs_of_pos hpos, lt_inv_mul_iff₀ hxp]
  nlinarith

theorem certificate (fr : Frame K u v) {g : ℝ} (hg0 : 0 < g) (hg : g ≤ 1 / 2 ^ 30) (x : E)
    {k : ℕ} (hk : k < K) (hclean : ∀ l, k ≤ l → l < K → dead u v l x) :
    (∃ e : E, ‖e‖ = 1 ∧ g < |D (objective K (radius K) u v) x e|) ∨
      (∃ e : E, ‖e‖ = 1 ∧ Q (objective K (radius K) u v) x e < -(1 / 10)) := by
  by_cases hx : ‖x‖ ≤ radius K
  · by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    exact no_calm fr (radius_pos K) hg0 hg hx hk hclean ⟨h1, h2⟩
  · push Not at hx
    left
    have hxp : 0 < ‖x‖ := (radius_pos K).trans hx
    refine ⟨(‖x‖⁻¹) • x, ?_, radial fr (hg.trans (by norm_num)) x hx⟩
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hxp.ne']

end LongTails.Proofs.EscapeChainCertificate
