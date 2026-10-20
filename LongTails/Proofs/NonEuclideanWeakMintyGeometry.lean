import LongTails.Setups.NonEuclideanWeakMinty
import LongTails.Proofs.PowerMirrorGeometry

namespace LongTails.Proofs.NonEuclideanWeakMintyGeometry

open LongTails.Setups.NonEuclideanWeakMinty

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma predictor_alignment {F : E → E →L[ℝ] ℝ} {L ρ : ℝ} {x u v : E}
    (hL : 0 < L) (hρ : 0 ≤ ρ) (hρL : ρ ≤ 1 / (20 * L))
    (hlip : ∀ a b, ‖F a - F b‖ ≤ L * ‖a - b‖)
    (hminty : ∀ z, -ρ * ‖F z‖ ^ 2 ≤ F z (z - u))
    (hv : ‖v‖ ≤ ‖F x‖) (hpair : F x v = ‖F x‖ ^ 2) :
    let y := x - (1 / (2 * L)) • v
    ‖F y‖ ≤ 3 / 2 * ‖F x‖ ∧
      11 / (80 * L) * ‖F x‖ ^ 2 ≤ F y (x - u) := by
  let η : ℝ := 1 / (2 * L)
  let y := x - η • v
  have hη : 0 < η := by dsimp [η]; positivity
  have hd : ‖F y - F x‖ ≤ ‖F x‖ / 2 := by
    have hh := hlip y x
    have hy : y - x = -(η • v) := by dsimp [y]; module
    rw [hy, norm_neg, norm_smul, Real.norm_of_nonneg hη.le] at hh
    have he : L * η = 1 / 2 := by dsimp [η]; field_simp
    rw [← mul_assoc, he] at hh
    linarith
  have hy : ‖F y‖ ≤ 3 / 2 * ‖F x‖ := by
    have ht' : ‖F y‖ ≤ ‖F y - F x‖ + ‖F x‖ := by
      simpa using norm_add_le (F y - F x) (F x)
    linarith
  have hdir : ‖F x‖ ^ 2 / 2 ≤ F y v := by
    have hp := (le_abs_self ((F x - F y) v)).trans ((F x - F y).le_opNorm v)
    simp only [sub_apply, norm_sub_rev (F x) (F y)] at hp
    rw [hpair] at hp
    have hb := mul_le_mul hd hv (norm_nonneg _) (by positivity : 0 ≤ ‖F x‖ / 2)
    nlinarith
  have hysq : ‖F y‖ ^ 2 ≤ 9 / 4 * ‖F x‖ ^ 2 := by
    nlinarith [sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3 / 2 * ‖F x‖) |>.mpr hy]
  have hm := hminty y
  have hs : x - u = η • v + (y - u) := by dsimp [y]; module
  have hp : η * (‖F x‖ ^ 2 / 2) - ρ * (9 / 4 * ‖F x‖ ^ 2) ≤
      F y (x - u) := by
    rw [hs, map_add, map_smul, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hdir hη.le,
      mul_le_mul_of_nonneg_left hysq hρ]
  have hr := mul_le_mul_of_nonneg_right hρL
    (show 0 ≤ 9 / 4 * ‖F x‖ ^ 2 by positivity)
  have he : η * (‖F x‖ ^ 2 / 2) -
      1 / (20 * L) * (9 / 4 * ‖F x‖ ^ 2) =
      11 / (80 * L) * ‖F x‖ ^ 2 := by
    dsimp [η]
    ring
  exact ⟨hy, by change _ ≤ F y (x - u); linarith⟩

lemma exists_mirror_step [FiniteDimensional ℝ E] {h : E → ℝ} {μ γ : ℝ}
    (hμ : 0 < μ) (hd : ∀ w, DifferentiableAt ℝ h w)
    (hc : ∀ a b, μ / 2 * ‖b - a‖ ^ 2 ≤
      h b - h a - fderiv ℝ h a (b - a)) (x : E) (g : E →L[ℝ] ℝ) :
    ∃ z, ∀ w, γ * g z + h z - h x - fderiv ℝ h x (z - x) ≤
      γ * g w + h w - h x - fderiv ℝ h x (w - x) := by
  let f := fun w => γ * g w + h w - h x - fderiv ℝ h x (w - x)
  let R := 2 * |γ| * ‖g‖ / μ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcont : Continuous f := by
    exact (((g.continuous.const_mul γ).add (continuous_iff_continuousAt.mpr
      (fun w => (hd w).continuousAt))).sub continuous_const).sub
        ((fderiv ℝ h x).continuous.comp (continuous_id.sub continuous_const))
  obtain ⟨z, hz, hmin⟩ := (isCompact_closedBall x R).exists_isMinOn
    (show (Metric.closedBall x R).Nonempty from ⟨x, by simp [hR]⟩)
    hcont.continuousOn
  refine ⟨z, fun w => ?_⟩
  by_cases hw : w ∈ Metric.closedBall x R
  · exact hmin hw
  · have hdist : R < ‖w - x‖ := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have hpair : -(|γ| * ‖g‖ * ‖w - x‖) ≤ γ * g (w - x) := by
      have hn := neg_abs_le (γ * g (w - x))
      have hb := mul_le_mul_of_nonneg_left (g.le_opNorm (w - x)) (abs_nonneg γ)
      rw [abs_mul] at hn
      rw [Real.norm_eq_abs] at hb
      nlinarith
    have hscale : 2 * |γ| * ‖g‖ ≤ μ * ‖w - x‖ := by
      have hh : 2 * |γ| * ‖g‖ / μ ≤ ‖w - x‖ := by dsimp [R] at hdist; linarith
      simpa only [mul_comm] using (div_le_iff₀ hμ).mp hh
    have hprod := mul_le_mul_of_nonneg_right hscale (norm_nonneg (w - x))
    have hcurv := hc x w
    have hfx : f x ≤ f w := by
      dsimp [f]
      simp only [sub_self, map_zero, sub_zero, map_sub] at hpair hcurv ⊢
      nlinarith
    exact (hmin (by simp [hR] : x ∈ Metric.closedBall x R)).trans hfx

lemma mirror_step_bound {h : E → ℝ} {μ γ : ℝ} {x z u : E}
    {g : E →L[ℝ] ℝ} (hμ : 0 < μ) (hγ : 0 ≤ γ)
    (hd : ∀ w, DifferentiableAt ℝ h w)
    (hc : ∀ a b, μ / 2 * ‖b - a‖ ^ 2 ≤
      h b - h a - fderiv ℝ h a (b - a))
    (hm : ∀ w, γ * g z + h z - h x - fderiv ℝ h x (z - x) ≤
      γ * g w + h w - h x - fderiv ℝ h x (w - x)) :
    h u - h z - fderiv ℝ h z (u - z) ≤
      h u - h x - fderiv ℝ h x (u - x) - γ * g (x - u) +
        γ ^ 2 * ‖g‖ ^ 2 / (2 * μ) := by
  have hf : HasFDerivAt
      (fun w => γ * g w + h w - h x - fderiv ℝ h x (w - x))
      (γ • g + fderiv ℝ h z - fderiv ℝ h x) z := by
    convert (((g.hasFDerivAt.const_mul γ).add (hd z).hasFDerivAt).sub_const (h x)).sub
      ((fderiv ℝ h x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x)) using 1
    · funext w
      simp [Pi.sub_apply, Function.comp_def, map_sub]
    · simp
  have ho := PowerMirrorGeometry.minimizer_derivative_nonneg
    (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ z)
    (Set.mem_univ u) (fun w _ => hm w) hf
  change 0 ≤ γ * g (u - z) + fderiv ℝ h z (u - z) -
    fderiv ℝ h x (u - z) at ho
  have hcurv := hc x z
  have hpair : g (x - z) ≤ ‖g‖ * ‖z - x‖ := by
    simpa only [norm_sub_rev x z] using
      (le_abs_self (g (x - z))).trans (g.le_opNorm (x - z))
  have hp := mul_le_mul_of_nonneg_left hpair hγ
  have hy := PowerMirrorEnergy.quadratic_cross_bound
    (a := ‖z - x‖) (b := γ * ‖g‖) (s := μ / 2) (by positivity)
  have he : (γ * ‖g‖) ^ 2 / (4 * (μ / 2)) = γ ^ 2 * ‖g‖ ^ 2 / (2 * μ) := by ring
  rw [he] at hy
  simp only [map_sub] at ho hcurv hp ⊢
  nlinarith

lemma descent_algebra {L μ a b c D D' : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbn : b ≤ 3 / 2 * a) (hc : 11 / (80 * L) * a ^ 2 ≤ c)
    (hm : D' ≤ D - (μ / (10 * L)) * c +
      (μ / (10 * L)) ^ 2 * b ^ 2 / (2 * μ)) :
    D' ≤ D - μ / (400 * L ^ 2) * a ^ 2 := by
  have hbs : b ^ 2 ≤ 9 / 4 * a ^ 2 := by
    nlinarith [sq_le_sq₀ hb (by positivity : 0 ≤ 3 / 2 * a) |>.mpr hbn]
  have hcp := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ μ / (10 * L) by positivity)
  have hbp := mul_le_mul_of_nonneg_left hbs
    (show 0 ≤ (μ / (10 * L)) ^ 2 / (2 * μ) by positivity)
  have he : -(μ / (10 * L)) * (11 / (80 * L) * a ^ 2) +
      (μ / (10 * L)) ^ 2 / (2 * μ) * (9 / 4 * a ^ 2) =
      -(μ / (400 * L ^ 2) * a ^ 2) := by
    field_simp
    ring
  have hm' : D' ≤ D - (μ / (10 * L)) * c +
      (μ / (10 * L)) ^ 2 / (2 * μ) * b ^ 2 := by
    convert hm using 1
    ring
  linarith only [hm', hcp, hbp, he]

lemma running_best_energy {D D' c a b b' : ℝ} (n : ℕ)
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hba : b' ≤ a) (hbb : n = 0 ∨ b' ≤ b)
    (hd : D' ≤ D - c * a ^ 2) :
    D' + ((n : ℝ) + 1) * c * b' ^ 2 ≤ D + (n : ℝ) * c * b ^ 2 := by
  have hnew := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hb' ha).mpr hba) hc
  rcases hbb with rfl | hbb
  · norm_num at *
    nlinarith only [hd, hnew]
  · have hold := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hb' hb).mpr hbb)
      (show 0 ≤ (n : ℝ) * c by positivity)
    nlinarith only [hd, hnew, hold]

end LongTails.Proofs.NonEuclideanWeakMintyGeometry
