import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow

open scoped RealInnerProductSpace Topology
open Filter

noncomputable section

namespace LongTails.Proofs.CappedCubicModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma nonneg_of_sphere_comparison (C : E →L[ℝ] E) {s : E} (hs : s ≠ 0)
    (hcomp : ∀ z : E, ‖z‖ = ‖s‖ → 0 ≤ ⟪z - s, C (z - s)⟫) :
    ∀ h : E, 0 ≤ ⟪h, C h⟫ := by
  have hnonorth (h : E) (hh : ⟪h, s⟫ ≠ 0) : 0 ≤ ⟪h, C h⟫ := by
    have hh0 : h ≠ 0 := by intro hz; simp [hz] at hh
    let a : ℝ := -2 * ⟪h, s⟫ / ‖h‖ ^ 2
    let z : E := -(Submodule.reflection (ℝ ∙ h) s)
    have hz : ‖z‖ = ‖s‖ := by simp [z]
    have hzs : z - s = a • h := by
      simp only [z, Submodule.reflection_singleton_apply]
      dsimp [a]
      module
    have ha : a ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hh)
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hh0))
    have hc := hcomp z hz
    rw [hzs] at hc
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right] at hc
    have hp : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    nlinarith
  intro h
  by_cases hh : ⟪h, s⟫ ≠ 0
  · exact hnonorth h hh
  · have hh : ⟪h, s⟫ = 0 := not_ne_iff.mp hh
    have hss : 0 < ⟪s, s⟫ := real_inner_self_pos.mpr hs
    have hc : Continuous (fun t : ℝ => ⟪h + t • s, C (h + t • s)⟫) := by
      fun_prop
    have ht : Tendsto (fun t : ℝ => ⟪h + t • s, C (h + t • s)⟫)
        (𝓝[Set.Ioi 0] 0) (𝓝 ⟪h, C h⟫) := by
      simpa using (hc.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply hnonorth
    simp only [inner_add_left, real_inner_smul_left, hh, zero_add]
    exact ne_of_gt (mul_pos ht hss)

lemma ball_normal_multiplier {s n : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hs : ‖s‖ ≤ ρ)
    (hn : ∀ z : E, ‖z‖ ≤ ρ → 0 ≤ ⟪n, z - s⟫) :
    ∃ μ : ℝ, 0 ≤ μ ∧ n + μ • s = 0 ∧ μ * (‖s‖ - ρ) = 0 := by
  by_cases hn0 : n = 0
  · exact ⟨0, le_rfl, by simp [hn0], by simp⟩
  have hnp : 0 < ‖n‖ := norm_pos_iff.mpr hn0
  let z := -(ρ / ‖n‖) • n
  have hz : ‖z‖ = ρ := by
    simp [z, norm_smul, ne_of_gt hnp, hρ.le]
  have hzinner : ⟪n, z⟫ = -ρ * ‖n‖ := by
    simp only [z, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hns := hn z hz.le
  rw [inner_sub_right, hzinner] at hns
  have hlo := (abs_le.mp (abs_real_inner_le_norm n s)).1
  have hsr : ‖s‖ = ρ := by nlinarith
  have hins : ⟪n, s⟫ = -ρ * ‖n‖ := by nlinarith
  refine ⟨‖n‖ / ρ, (div_pos hnp hρ).le, ?_, by simp [hsr]⟩
  apply norm_eq_zero.mp
  have hsq := norm_add_sq_real n ((‖n‖ / ρ) • s)
  rw [real_inner_smul_right, hins, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hnp hρ), hsr] at hsq
  have heq : ‖n‖ / ρ * ρ = ‖n‖ := div_mul_cancel₀ _ (ne_of_gt hρ)
  nlinarith [norm_nonneg (n + (‖n‖ / ρ) • s)]

lemma multiplier_of_min_ball {f : E → ℝ} {s n : E} {ρ : ℝ}
    (hρ : 0 < ρ) (hs : ‖s‖ ≤ ρ)
    (hf : HasFDerivAt f (innerSL ℝ n) s)
    (hmin : IsMinOn f (Metric.closedBall 0 ρ) s) :
    ∃ μ : ℝ, 0 ≤ μ ∧ n + μ • s = 0 ∧ μ * (‖s‖ - ρ) = 0 := by
  apply ball_normal_multiplier hρ hs
  intro z hz
  have hsm : s ∈ Metric.closedBall (0 : E) ρ := by simpa using hs
  have hzm : z ∈ Metric.closedBall (0 : E) ρ := by simpa using hz
  exact hmin.isLocalMinOn.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset
      ((convex_closedBall (0 : E) ρ).segment_subset hsm hzm))

def model (B : E →L[ℝ] E) (g : E) (δ σ : ℝ) (s : E) : ℝ :=
  ⟪g, s⟫ + (1 / 2 : ℝ) * ⟪s, B s⟫ + δ * ‖s‖ ^ 2 + σ / 3 * ‖s‖ ^ 3

lemma model_hasFDerivAt (B : E →L[ℝ] E) (g : E) (δ σ : ℝ) (s : E)
    (hB : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    HasFDerivAt (model B g δ σ)
      (innerSL ℝ (g + B s + (2 * δ + σ * ‖s‖) • s)) s := by
  have hcube : HasFDerivAt (fun x : E => ‖x‖ ^ 3)
      ((3 * ‖s‖) • innerSL ℝ s) s := by
    convert hasFDerivAt_norm_rpow s (by norm_num : (1 : ℝ) < 3) using 1 <;> norm_num
  have hquad := ((hasFDerivAt_id s).inner ℝ B.hasFDerivAt).const_mul (1 / 2 : ℝ)
  have hnorm := (hasStrictFDerivAt_norm_sq s).hasFDerivAt.const_mul δ
  have hcubic := hcube.const_mul (σ / 3)
  convert (((innerSL ℝ g).hasFDerivAt.add hquad).add hnorm).add hcubic using 1
  · rfl
  · ext y
    simp
    rw [hB s y, real_inner_comm y (B s)]
    ring

lemma model_exists_min [FiniteDimensional ℝ E] (B : E →L[ℝ] E) (g : E)
    (δ σ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s ∈ Metric.closedBall (0 : E) ρ,
      IsMinOn (model B g δ σ) (Metric.closedBall 0 ρ) s := by
  have hc : Continuous (model B g δ σ) := by unfold model; fun_prop
  obtain ⟨s, hs, hm⟩ := (isCompact_closedBall (0 : E) ρ).exists_isMinOn
    (Metric.nonempty_closedBall.mpr hρ.le) hc.continuousOn
  exact ⟨s, hs, hm⟩

lemma model_psd_of_stationarity (B : E →L[ℝ] E) (g s : E)
    (δ σ μ ρ : ℝ) (hs : s ≠ 0) (hsρ : ‖s‖ ≤ ρ)
    (hB : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫)
    (hmin : IsMinOn (model B g δ σ) (Metric.closedBall 0 ρ) s)
    (hstat : g + B s + (2 * δ + σ * ‖s‖ + μ) • s = 0) :
    ∀ h : E, 0 ≤ ⟪h, B h + (2 * δ + σ * ‖s‖ + μ) • h⟫ := by
  let ell := 2 * δ + σ * ‖s‖ + μ
  let C : E →L[ℝ] E := B + ell • ContinuousLinearMap.id ℝ E
  change ∀ h : E, 0 ≤ ⟪h, C h⟫
  apply nonneg_of_sphere_comparison C hs
  intro z hz
  have hzm : z ∈ Metric.closedBall (0 : E) ρ := by simpa [hz] using hsρ
  have hm : model B g δ σ s ≤ model B g δ σ z := hmin hzm
  simp only [model, hz] at hm
  have hgs := congrArg (fun v : E => ⟪v, z - s⟫) hstat
  simp only [inner_add_left, real_inner_smul_left, inner_sub_right,
    inner_zero_left] at hgs
  have hn : ⟪z, z⟫ = ⟪s, s⟫ := by
    simp only [real_inner_self_eq_norm_sq, hz]
  have hsym : ⟪z, B s⟫ = ⟪s, B z⟫ := by rw [hB, real_inner_comm]
  have hsBs : ⟪B s, s⟫ = ⟪s, B s⟫ := real_inner_comm _ _
  have hsBz : ⟪B s, z⟫ = ⟪s, B z⟫ := (hB s z).symm
  have hsz : ⟪z, s⟫ = ⟪s, z⟫ := real_inner_comm _ _
  simp only [C, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_sub, inner_add_right, real_inner_smul_right,
    inner_sub_left, inner_sub_right]
  rw [hsym, hsz, hn]
  rw [hsBs, hsBz] at hgs
  dsimp [ell]
  nlinarith

lemma model_certificate [FiniteDimensional ℝ E] (B : E →L[ℝ] E) (g : E)
    (δ σ : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hg : g ≠ 0)
    (hB : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    ∃ s : E, ∃ μ : ℝ, ‖s‖ ≤ ρ ∧ 0 ≤ μ ∧
      g + B s + (2 * δ + σ * ‖s‖ + μ) • s = 0 ∧
      μ * (‖s‖ - ρ) = 0 ∧
      (∀ h : E, 0 ≤ ⟪h, B h + (2 * δ + σ * ‖s‖ + μ) • h⟫) := by
  obtain ⟨s, hs, hm⟩ := model_exists_min B g δ σ hρ
  have hsρ : ‖s‖ ≤ ρ := by simpa using hs
  obtain ⟨μ, hμ, heq, hcap⟩ := multiplier_of_min_ball hρ hsρ
    (model_hasFDerivAt B g δ σ s hB) hm
  have hstat : g + B s + (2 * δ + σ * ‖s‖ + μ) • s = 0 := by
    convert heq using 1
    module
  have hs0 : s ≠ 0 := by
    intro hz
    apply hg
    simpa [hz] using hstat
  exact ⟨s, μ, hsρ, hμ, hstat, hcap,
    model_psd_of_stationarity B g s δ σ μ ρ hs0 hsρ hB hm hstat⟩

end LongTails.Proofs.CappedCubicModel
