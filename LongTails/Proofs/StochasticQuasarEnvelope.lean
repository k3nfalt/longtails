import LongTails.Proofs.StochasticQuasarProx
import LongTails.Proofs.PowerMirrorGeometry
import LongTails.Proofs.PLMinimaxProx

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticQuasar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open LongTails.Setups.WeaklyConvexHeavyTailed (proxObj)

noncomputable def constrainedProx (Q : Set E) (f : E → ℝ) (L : ℝ) (c : E) : E := by
  classical
  exact if h : ∃ u ∈ Q, IsMinOn (proxObj f L c) Q u then h.choose else c

noncomputable def constrainedEnvelope (Q : Set E) (f : E → ℝ) (L : ℝ) (c : E) : ℝ :=
  proxObj f L c (constrainedProx Q f L c)

lemma regularized_hasGradientAt {f : E → ℝ} {g x : E}
    (hf : HasGradientAt f g x) (L : ℝ) (c : E) :
    HasGradientAt (fun y => f y + L * ‖y - c‖ ^ 2) (g + (2 * L) • (x - c)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf.hasFDerivAt.add
    ((((hasFDerivAt_id (𝕜 := ℝ) x).sub_const c).norm_sq).const_mul L) using 1
  · rfl
  · ext w
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
    ring

lemma regularized_minimizer_exists {Q : Set E} {f : E → ℝ} {g : E → E}
    (hQ : IsCompact Q) (hne : Q.Nonempty) (hg : ∀ x ∈ Q, HasGradientAt f (g x) x)
    (L : ℝ) (c : E) :
    ∃ u ∈ Q, IsMinOn (fun y => f y + L * ‖y - c‖ ^ 2) Q u := by
  apply hQ.exists_isMinOn hne
  intro x hx
  exact (regularized_hasGradientAt (hg x hx) L c).continuousAt.continuousWithinAt

lemma regularized_minimizer_normal {Q : Set E} {f : E → ℝ} {g u v c : E} {L : ℝ}
    (hQ : Convex ℝ Q) (hu : u ∈ Q) (hv : v ∈ Q) (hg : HasGradientAt f g u)
    (hm : IsMinOn (fun y => f y + L * ‖y - c‖ ^ 2) Q u) :
    0 ≤ ⟪g + (2 * L) • (u - c), v - u⟫ := by
  exact LongTails.Proofs.PowerMirrorGeometry.minimizer_derivative_nonneg hQ hu hv
    (fun w hw => hm hw)
    (regularized_hasGradientAt hg L c).hasFDerivAt

lemma regularized_minimizer_growth {Q : Set E} {f : E → ℝ} {g : E → E} {L : ℝ}
    (hQ : Convex ℝ Q) (hg : ∀ z ∈ Q, HasGradientAt f (g z) z)
    (hlip : ∀ z ∈ Q, ∀ w ∈ Q, ‖g z - g w‖ ≤ L * ‖z - w‖)
    {u v c : E} (hu : u ∈ Q) (hv : v ∈ Q)
    (hm : IsMinOn (fun y => f y + L * ‖y - c‖ ^ 2) Q u) :
    f u + L * ‖u - c‖ ^ 2 + L / 2 * ‖v - u‖ ^ 2 ≤ f v + L * ‖v - c‖ ^ 2 := by
  have hs := regularized_lower_support hQ hg hlip hu hv c
  have hn := regularized_minimizer_normal hQ hu hv (hg u hu) hm
  linarith

lemma regularized_minimizers_pair {Q : Set E} {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hQ : Convex ℝ Q) (hg : ∀ z ∈ Q, HasGradientAt f (g z) z)
    (hlip : ∀ z ∈ Q, ∀ w ∈ Q, ‖g z - g w‖ ≤ L * ‖z - w‖)
    {x y u v : E} (hu : u ∈ Q) (hv : v ∈ Q)
    (hmu : IsMinOn (fun w => f w + L * ‖w - x‖ ^ 2) Q u)
    (hmv : IsMinOn (fun w => f w + L * ‖w - y‖ ^ 2) Q v) :
    ‖u - v‖ ^ 2 ≤ 2 * ⟪x - y, u - v⟫ := by
  have h₁ := regularized_minimizer_growth hQ hg hlip hu hv hmu
  have h₂ := regularized_minimizer_growth hQ hg hlip hv hu hmv
  have he : ‖v - x‖ ^ 2 - ‖u - x‖ ^ 2 + ‖u - y‖ ^ 2 - ‖v - y‖ ^ 2 =
      2 * ⟪x - y, u - v⟫ := by
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
    rw [real_inner_comm x u, real_inner_comm x v, real_inner_comm y u, real_inner_comm y v]
    ring
  rw [norm_sub_rev v u] at h₁
  have hh : L * ‖u - v‖ ^ 2 ≤ L * (2 * ⟪x - y, u - v⟫) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hL).mp hh

lemma constrainedProx_spec {Q : Set E} {f : E → ℝ} {g : E → E}
    (hQ : IsCompact Q) (hne : Q.Nonempty) (hg : ∀ x ∈ Q, HasGradientAt f (g x) x)
    (L : ℝ) (c : E) :
    constrainedProx Q f L c ∈ Q ∧ IsMinOn (proxObj f L c) Q (constrainedProx Q f L c) := by
  have he : ∃ u ∈ Q, IsMinOn (proxObj f L c) Q u :=
    regularized_minimizer_exists hQ hne hg L c
  rw [constrainedProx, dite_eq_left he]
  exact he.choose_spec

lemma constrainedProx_pair {Q : Set E} {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hQ : IsCompact Q) (hne : Q.Nonempty) (hcv : Convex ℝ Q)
    (hg : ∀ z ∈ Q, HasGradientAt f (g z) z)
    (hlip : ∀ z ∈ Q, ∀ w ∈ Q, ‖g z - g w‖ ≤ L * ‖z - w‖) (x y : E) :
    ‖constrainedProx Q f L x - constrainedProx Q f L y‖ ^ 2 ≤
      2 * ⟪x - y, constrainedProx Q f L x - constrainedProx Q f L y⟫ := by
  have hx := constrainedProx_spec hQ hne hg L x
  have hy := constrainedProx_spec hQ hne hg L y
  exact regularized_minimizers_pair hL hcv hg hlip hx.1 hy.1 hx.2 hy.2

lemma constrainedProx_lipschitz {Q : Set E} {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hQ : IsCompact Q) (hne : Q.Nonempty) (hcv : Convex ℝ Q)
    (hg : ∀ z ∈ Q, HasGradientAt f (g z) z)
    (hlip : ∀ z ∈ Q, ∀ w ∈ Q, ‖g z - g w‖ ≤ L * ‖z - w‖) (x y : E) :
    ‖constrainedProx Q f L x - constrainedProx Q f L y‖ ≤ 2 * ‖x - y‖ := by
  have hp := constrainedProx_pair hL hQ hne hcv hg hlip x y
  have hi := real_inner_le_norm (x - y) (constrainedProx Q f L x - constrainedProx Q f L y)
  nlinarith [norm_nonneg (constrainedProx Q f L x - constrainedProx Q f L y), norm_nonneg (x - y)]

lemma constrainedEnvelope_remainder {Q : Set E} {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hQ : IsCompact Q) (hne : Q.Nonempty) (hcv : Convex ℝ Q)
    (hg : ∀ z ∈ Q, HasGradientAt f (g z) z)
    (hlip : ∀ z ∈ Q, ∀ w ∈ Q, ‖g z - g w‖ ≤ L * ‖z - w‖) (z h : E) :
    |constrainedEnvelope Q f L (z + h) - constrainedEnvelope Q f L z -
      ⟪(2 * L) • (z - constrainedProx Q f L z), h⟫| ≤ 3 * L * ‖h‖ ^ 2 := by
  have hz := constrainedProx_spec hQ hne hg L z
  have hy := constrainedProx_spec hQ hne hg L (z + h)
  have hu := hy.2 hz.1
  have hl := hz.2 hy.1
  change proxObj f L (z + h) (constrainedProx Q f L (z + h)) ≤
    proxObj f L (z + h) (constrainedProx Q f L z) at hu
  change proxObj f L z (constrainedProx Q f L z) ≤
    proxObj f L z (constrainedProx Q f L (z + h)) at hl
  have he := PLMinimax.proxObj_center_shift f L z h (constrainedProx Q f L z)
  have he' := PLMinimax.proxObj_center_shift f L z h (constrainedProx Q f L (z + h))
  have hd := constrainedProx_lipschitz hL hQ hne hcv hg hlip z (z + h)
  simp only [sub_add_cancel_left, norm_neg] at hd
  have hi := abs_real_inner_le_norm (constrainedProx Q f L z - constrainedProx Q f L (z + h)) h
  have hdiff : ⟪z - constrainedProx Q f L (z + h), h⟫ =
      ⟪z - constrainedProx Q f L z, h⟫ +
      ⟪constrainedProx Q f L z - constrainedProx Q f L (z + h), h⟫ := by
    simp only [inner_sub_left]
    ring
  have hb : -2 * ‖h‖ ^ 2 ≤ ⟪constrainedProx Q f L z - constrainedProx Q f L (z + h), h⟫ := by
    have hh := (abs_le.mp hi).1
    nlinarith [mul_le_mul_of_nonneg_right hd (norm_nonneg h)]
  rw [hdiff] at he'
  unfold constrainedEnvelope
  rw [real_inner_smul_left, abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * L by positivity),
    mul_nonneg hL.le (sq_nonneg ‖h‖)]

lemma constrainedEnvelope_hasGradient {Q : Set E} {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hQ : IsCompact Q) (hne : Q.Nonempty) (hcv : Convex ℝ Q)
    (hg : ∀ z ∈ Q, HasGradientAt f (g z) z)
    (hlip : ∀ z ∈ Q, ∀ w ∈ Q, ‖g z - g w‖ ≤ L * ‖z - w‖) (z : E) :
    HasGradientAt (constrainedEnvelope Q f L) ((2 * L) • (z - constrainedProx Q f L z)) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  apply PLMinimax.hasFDerivAt_of_quadratic_remainder (C := 3 * L)
  intro h
  simpa [Real.norm_eq_abs, real_inner_smul_left, inner_sub_left] using
    constrainedEnvelope_remainder hL hQ hne hcv hg hlip z h

lemma constrainedEnvelope_gradient_lipschitz {Q : Set E} {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 < L) (hQ : IsCompact Q) (hne : Q.Nonempty) (hcv : Convex ℝ Q)
    (hg : ∀ z ∈ Q, HasGradientAt f (g z) z)
    (hlip : ∀ z ∈ Q, ∀ w ∈ Q, ‖g z - g w‖ ≤ L * ‖z - w‖) (x y : E) :
    ‖(2 * L) • (x - constrainedProx Q f L x) -
      (2 * L) • (y - constrainedProx Q f L y)‖ ≤ 2 * L * ‖x - y‖ :=
  envelope_gradient_lipschitz hL.le (constrainedProx_pair hL hQ hne hcv hg hlip x y)

lemma constrainedEnvelope_bounds {Q : Set E} {f : E → ℝ} {g : E → E} {L : ℝ}
    (hL : 0 ≤ L) (hQ : IsCompact Q) (hg : ∀ z ∈ Q, HasGradientAt f (g z) z)
    {u : E} (hu : u ∈ Q) (hm : IsMinOn f Q u) (x : E) :
    f u ≤ constrainedEnvelope Q f L x ∧
      constrainedEnvelope Q f L x ≤ f u + L * ‖x - u‖ ^ 2 := by
  have hp := constrainedProx_spec hQ ⟨u, hu⟩ hg L x
  have hlo := hm hp.1
  change f u ≤ f (constrainedProx Q f L x) at hlo
  have hup := hp.2 hu
  change f (constrainedProx Q f L x) + L * ‖constrainedProx Q f L x - x‖ ^ 2 ≤
    f u + L * ‖u - x‖ ^ 2 at hup
  unfold constrainedEnvelope proxObj
  rw [norm_sub_rev u x] at hup
  exact ⟨by nlinarith [mul_nonneg hL (sq_nonneg ‖constrainedProx Q f L x - x‖)], hup⟩

lemma constrainedEnvelope_quasar {Q : Set E} {f : E → ℝ} {g : E → E} {L γ : ℝ}
    (hL : 0 ≤ L) (hγ : γ ≤ 1) (hQ : IsCompact Q) (hcv : Convex ℝ Q)
    (hg : ∀ z ∈ Q, HasGradientAt f (g z) z) {u : E} (hu : u ∈ Q)
    (hq : ∀ z ∈ Q, γ * (f z - f u) ≤ ⟪g z, z - u⟫) (x : E) :
    γ * (constrainedEnvelope Q f L x - f u) ≤
      ⟪(2 * L) • (x - constrainedProx Q f L x), x - u⟫ := by
  let y := constrainedProx Q f L x
  have hp := constrainedProx_spec hQ ⟨u, hu⟩ hg L x
  have hn := regularized_minimizer_normal hcv hp.1 hu (hg y hp.1) hp.2
  have he : (2 * L) • (x - y) - g y = -(g y + (2 * L) • (y - x)) := by module
  have hn' : 0 ≤ ⟪(2 * L) • (x - y) - g y, y - u⟫ := by
    rw [he, inner_neg_left, ← inner_neg_right, neg_sub]
    exact hn
  have ht := envelope_quasar_transfer (hq y hp.1) hn'
  have hc : 0 ≤ (2 - γ) * L * ‖x - y‖ ^ 2 := by
    exact mul_nonneg (mul_nonneg (by linarith) hL) (sq_nonneg _)
  change γ * (f y + L * ‖y - x‖ ^ 2 - f u) ≤ _
  rw [norm_sub_rev y x]
  linarith

end OracleTemplate.StochasticQuasar
