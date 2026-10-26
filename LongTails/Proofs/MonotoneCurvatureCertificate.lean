import LongTails.Proofs.MonotoneCurvatureGeometry
import LongTails.Proofs.QuarticStageCertificate
import LongTails.Proofs.ReusedCurvatureCorrection
import LongTails.Proofs.MonotoneCurvatureTuning

namespace LongTails.Proofs.MonotoneCurvatureCertificate

open LongTails.Algorithms.GuardedMetricAcceleration
open LongTails.Algorithms.QuarticMetricStage
open LongTails.Proofs.QuarticStageInvariant
open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma terminal_dual_gradient (p : Parameters E) (f : E → ℝ) {A τ : ℝ} {k : ℕ} {st : State E}
    (hi : Invariant p f A τ k st) (ha : 0 ≤ p.a) (ha₁ : p.a ≤ 1)
    (hμ : 0 < p.μ) (hL : 0 < p.L) (hμL : p.μ ≤ p.L) (hα : 0 < p.α)
    (hA : 0 ≤ A) (hτ : 0 ≤ τ) (hA₂ : A ^ 2 = 2 * p.q / p.μ)
    (hτ₂ : p.α * τ ^ 2 = p.q) (w : Point E)
    (hfull : p.S w.x = gradientStep p.L (p.S st.accepted.x) (transformedGradient p.S (gradient p st.accepted)))
    (hd : value p w ≤ value p st.accepted - ‖transformedGradient p.S (gradient p st.accepted)‖ ^ 2 / (2 * p.L))
    (hno : ¬successful p w) (hs : ∀ plane ∈ st.history, supports p w plane.point) :
    ‖transformedGradient p.S (gradient p st.accepted)‖ ^ 2 ≤ 10 * p.L * p.q * (1 - p.a) ^ k := by
  have hg := QuarticStageCertificate.certificate_geometry p st.accepted w
    hL hμ hμL hα hA hτ hA₂ hτ₂ hi.accepted_value hi.accepted_radius hfull hd hno
  have he := QuarticStageCertificate.certificate_estimate p f hi ha ha₁ hμ hL w hs hd
  have hn : p.center.value - p.q < w.value := lt_of_not_ge (not_or.mp hno).1
  have hw : w.value ≤ value p w := by
    unfold value regularizedValue
    exact le_add_of_nonneg_right (by positivity)
  have hr := pow_le_pow_left₀ (norm_nonneg _) hg.2.1 2
  have hmr := mul_le_mul_of_nonneg_left hr hμ.le
  have hq : p.μ * A ^ 2 = 2 * p.q := by
    have hh := (eq_div_iff hμ.ne').mp hA₂
    nlinarith only [hh]
  have hb : p.center.value - value p w + p.μ * ‖p.S (w.x - p.center.x)‖ ^ 2 / 2 ≤ 5 * p.q := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ 2 * p.L * (1 - p.a) ^ k by positivity)
  nlinarith only [he, hm]

lemma unregularized_dual_gradient (p : Parameters E) {b R G : ℝ}
    (hb : 0 < b) (hα : 0 ≤ p.α)
    (hS : ∀ v, b ^ 2 * ‖v‖ ^ 2 ≤ ‖p.S v‖ ^ 2) (x : Point E)
    (hr : ‖x.x - p.center.x‖ ≤ R) (hg : ‖transformedGradient p.S (gradient p x)‖ ≤ G) :
    ‖transformedGradient p.S x.gradient‖ ≤ G + 2 * p.α * R / b := by
  have he : transformedGradient p.S x.gradient = transformedGradient p.S (gradient p x) -
      transformedGradient p.S ((2 * p.α) • (x.x - p.center.x)) := by
    simp [transformedGradient, LongTails.Algorithms.QuarticMetricStage.gradient, regularizedGradient]
  have hd := MonotoneCurvatureGeometry.dual_norm p.S hb hS ((2 * p.α) • (x.x - p.center.x))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * p.α)] at hd
  have hr' : 2 * p.α * ‖x.x - p.center.x‖ / b ≤ 2 * p.α * R / b := by gcongr
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hg (hd.trans hr'))

lemma corrected_residual {g : E → E} {A : E → E →L[ℝ] E} {H κ b G : ℝ}
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (S : E ≃L[ℝ] E) (B : E →L[ℝ] E) (x : Point E)
    (hx : x.gradient = g x.x) (hB : B.toLinearMap.IsSymmetric)
    (hfactor : ∀ v, ‖S v‖ ^ 2 = ⟪v, B v⟫)
    (hb : 0 < b) (hS : ∀ v, b ^ 2 * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2)
    (hG : ‖transformedGradient S x.gradient‖ ≤ G)
    (hH : 0 ≤ H) (hκ : 0 ≤ κ) (herror : ‖B - A x.x‖ ≤ κ) :
    ‖g (LongTails.Algorithms.MonotoneCurvatureStage.correctedPoint S x)‖ ≤
      κ * (G / b) + H * (G / b) ^ 2 / 2 := by
  let s := S.symm (transformedGradient S x.gradient)
  have hs : B s = g x.x := (MonotoneCurvatureGeometry.correction_equation S B hB hfactor _).trans hx
  have hn : ‖s‖ ≤ G / b := (MonotoneCurvatureGeometry.inverse_radius S hb hS _).trans
    (div_le_div_of_nonneg_right hG hb.le)
  have hbnd := ReusedCurvatureCorrection.corrected_gradient hg hLip B x.x s hs herror
  have hn₂ := pow_le_pow_left₀ (norm_nonneg s) hn 2
  have h₁ := mul_le_mul_of_nonneg_left hn hκ
  have h₂ := mul_le_mul_of_nonneg_left hn₂ hH
  change ‖g (x.x - s)‖ ≤ _
  linarith

lemma tuned_terminal (S : E ≃L[ℝ] E) (c : Point E) {H γ t : ℝ}
    (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t) (f : E → ℝ) (st : State E) (w : Point E)
    (hi : Invariant (LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t) f
      (MonotoneCurvatureTuning.metricRadius H γ t) (MonotoneCurvatureTuning.distanceScale H γ)
      (LongTails.Algorithms.MonotoneCurvatureStage.horizon t) st)
    (hpoint : w.x = trialPoint (LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t) st.accepted)
    (hno : ¬successful (LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t) w)
    (hmodel : let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t;
      value p w ≤ value p st.accepted + ⟪gradient p st.accepted, w.x - st.accepted.x⟫ +
        p.L / 2 * ‖S (w.x - st.accepted.x)‖ ^ 2) :
    let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
    value p w ≤ c.value ∧
    ‖S (w.x - c.x)‖ ≤ 2 * MonotoneCurvatureTuning.metricRadius H γ t ∧
    ‖w.x - c.x‖ ≤ MonotoneCurvatureTuning.distanceScale H γ ∧
    ((∀ plane ∈ st.history, supports p w plane.point) →
      ‖transformedGradient S (gradient p st.accepted)‖ ^ 2 ≤ p.q / t ^ 2) := by
  let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
  have ht0 : 0 < t := by linarith
  have hscale := MonotoneCurvatureTuning.scales S c hH hγ ht
  have hL : 0 < p.L := by norm_num [p, LongTails.Algorithms.MonotoneCurvatureStage.parameters]
  have hA := (MonotoneCurvatureTuning.metricRadius_pos hH hγ ht0).le
  have hτ := (MonotoneCurvatureTuning.distanceScale_pos hH hγ).le
  have hA₂ := MonotoneCurvatureTuning.radius_identity S c (H := H) hγ.le ht0.ne'
  have hq := MonotoneCurvatureTuning.progress_clipping S c hH hγ ht
  have hh := QuarticStageCertificate.certificate_full p st.accepted w hL hscale.2.2.2.2.1
    hγ.le hq hi.accepted_value hpoint hmodel hno
  have hg := QuarticStageCertificate.certificate_geometry p st.accepted w hL hscale.2.2.1
    hscale.2.2.2.1 hγ hA hτ hA₂ rfl hi.accepted_value hi.accepted_radius hh.1 hh.2 hno
  refine ⟨hg.1, hg.2.1, hg.2.2, ?_⟩
  intro hs
  have hb := terminal_dual_gradient p f hi hscale.1 hscale.2.1 hscale.2.2.1 hL
    hscale.2.2.2.1 hγ hA hτ hA₂ rfl w hh.1 hh.2 hno hs
  have hd := MonotoneCurvatureTuning.horizon_decay S c (H := H) (γ := γ) ht
  have hm := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 80 * p.q by have h := hscale.2.2.2.2.2; positivity)
  have he : 80 * p.q * (1 / (80 * t ^ 2)) = p.q / t ^ 2 := by ring
  rw [he] at hm
  have hLval : p.L = 8 := rfl
  rw [hLval] at hb
  change 80 * p.q * (1 - p.a) ^ LongTails.Algorithms.MonotoneCurvatureStage.horizon t ≤ p.q / t ^ 2 at hm
  apply hb.trans
  convert hm using 1
  ring

lemma tuned_correction_distance (S : E ≃L[ℝ] E) (c x : Point E) {H γ t : ℝ}
    (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t)
    (hmetric : ∀ v, (t ^ 2 * γ) * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2)
    (hr : ‖x.x - c.x‖ ≤ MonotoneCurvatureTuning.distanceScale H γ)
    (hg : let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t;
      ‖transformedGradient S (gradient p x)‖ ^ 2 ≤ p.q / t ^ 2) :
    t ^ 2 * ‖S.symm (transformedGradient S x.gradient)‖ ≤
      3 * MonotoneCurvatureTuning.distanceScale H γ := by
  let p := LongTails.Algorithms.MonotoneCurvatureStage.parameters S c H γ t
  let τ := MonotoneCurvatureTuning.distanceScale H γ
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < Real.sqrt γ := Real.sqrt_pos.mpr hγ
  have hτ : 0 < τ := MonotoneCurvatureTuning.distanceScale_pos hH hγ
  have hs : (t * Real.sqrt γ) ^ 2 = t ^ 2 * γ := by rw [mul_pow, Real.sq_sqrt hγ.le]
  have hi : ∀ v, (t * Real.sqrt γ) ^ 2 * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2 :=
    fun v => by rw [hs]; exact hmetric v
  have he : (Real.sqrt γ * τ / t) ^ 2 = p.q / t ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hγ.le]
    rfl
  have hg' : ‖transformedGradient S (gradient p x)‖ ≤ Real.sqrt γ * τ / t := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [he]
    exact hg
  have hu := unregularized_dual_gradient p (show 0 < t * Real.sqrt γ by positivity)
    hγ.le hi x hr hg'
  have he' : Real.sqrt γ * τ / t + 2 * γ * τ / (t * Real.sqrt γ) =
      3 * Real.sqrt γ * τ / t := by
    have hsq := Real.sq_sqrt hγ.le
    field_simp
    nlinarith only [hsq]
  change ‖transformedGradient S x.gradient‖ ≤ Real.sqrt γ * τ / t + 2 * γ * τ / (t * Real.sqrt γ) at hu
  rw [he'] at hu
  have hn := MonotoneCurvatureGeometry.inverse_radius S (show 0 < t * Real.sqrt γ by positivity)
    hi (transformedGradient S x.gradient)
  have hb := hn.trans (div_le_div_of_nonneg_right hu (by positivity))
  have he'' : (3 * Real.sqrt γ * τ / t) / (t * Real.sqrt γ) = 3 * τ / t ^ 2 := by field_simp
  rw [he''] at hb
  have hh := (le_div_iff₀ (sq_pos_of_pos ht0)).mp hb
  nlinarith only [hh]

lemma correction_guarantee {f : E → ℝ} {g : E → E} {A : E → E →L[ℝ] E}
    {H γ t ε : ℝ} (hH : 0 < H) (hγ : 0 < γ) (ht : 1 ≤ t) (hε : γ ^ 2 = H * ε)
    (hf : ∀ y, HasFDerivAt f (innerSL ℝ (g y)) y)
    (hg : ∀ y, HasFDerivAt g (A y) y)
    (hLip : ∀ y z, ‖A y - A z‖ ≤ H * ‖y - z‖)
    (S : E ≃L[ℝ] E) (B : E →L[ℝ] E) (x : Point E)
    (hx : x.gradient = g x.x) (hB : B.toLinearMap.IsSymmetric)
    (hfactor : ∀ v, ‖S v‖ ^ 2 = ⟪v, B v⟫)
    (hmetric : ∀ v, (t ^ 2 * γ) * ‖v‖ ^ 2 ≤ ‖S v‖ ^ 2)
    (hupper : ∀ v, ⟪v, A x.x v⟫ ≤ ⟪v, B v⟫ - (t ^ 2 * γ) * ‖v‖ ^ 2)
    (herror : ‖B - A x.x‖ ≤ 6 * (t ^ 2 * γ))
    (hstep : t ^ 2 * ‖S.symm (transformedGradient S x.gradient)‖ ≤
      3 * MonotoneCurvatureTuning.distanceScale H γ) :
    let y := LongTails.Algorithms.MonotoneCurvatureStage.correctedPoint S x
    ‖g y‖ ≤ ε ∧ f y ≤ f x.x ∧ ‖y - x.x‖ ≤ 3 * MonotoneCurvatureTuning.distanceScale H γ := by
  let τ := MonotoneCurvatureTuning.distanceScale H γ
  let s := S.symm (transformedGradient S x.gradient)
  have hτ : 0 < τ := MonotoneCurvatureTuning.distanceScale_pos hH hγ
  have hτH : H * τ = γ / 2 ^ 30 := by
    dsimp [τ, MonotoneCurvatureTuning.distanceScale]
    field_simp
  have hτγ : γ * τ = ε / 2 ^ 30 := by
    dsimp [τ, MonotoneCurvatureTuning.distanceScale]
    field_simp
    nlinarith only [hε]
  have hε0 : 0 ≤ ε := by nlinarith [sq_nonneg γ]
  have hb := ReusedCurvatureCorrection.correction_scale_bound (ε := ε) hH.le hγ.le hτ.le ht
    (norm_nonneg s) hstep (by rw [hτH]; linarith) (by rw [hτγ]; linarith)
  have hs : B s = g x.x := (MonotoneCurvatureGeometry.correction_equation S B hB hfactor _).trans hx
  have hg' := ReusedCurvatureCorrection.corrected_gradient hg hLip B x.x s hs herror
  have hB' : (t ^ 2 * γ) * ‖s‖ ^ 2 ≤ ⟪s, B s⟫ := by rw [← hfactor]; exact hmetric s
  have hd := ReusedCurvatureCorrection.correction_descent hf hg hLip B x.x s hs hB' (hupper s)
    (by positivity : 0 ≤ t ^ 2 * γ) hb.2
  have hn : ‖s‖ ≤ 3 * τ := by
    have ht₂ : 1 ≤ t ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right ht₂ (norm_nonneg s)
    nlinarith
  change ‖g (x.x - s)‖ ≤ ε ∧ f (x.x - s) ≤ f x.x ∧ ‖x.x - s - x.x‖ ≤ 3 * τ
  refine ⟨hg'.trans hb.1, hd.trans ?_, ?_⟩
  · exact sub_le_self _ (by positivity)
  · simpa only [sub_sub_cancel_left, norm_neg] using hn

end LongTails.Proofs.MonotoneCurvatureCertificate
