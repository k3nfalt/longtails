import LongTails.Proofs.RhoSmoothHardParameters
import LongTails.Proofs.RhoSmoothHardSmoothed
import LongTails.Proofs.RhoSmoothHardLocalization
import LongTails.Proofs.GeneralizedSmoothCoordinateEmbedding
import LongTails.Proofs.GeneralizedSmoothChainPrefix
import LongTails.Proofs.GeneralizedSmoothHardChainRadius
import LongTails.Proofs.SmoothConvexFiniteLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace LongTails.Proofs.RhoSmoothHardInstance

open FiniteSumNondualLowerComponents GeneralizedSmoothCoordinateEmbedding GeneralizedSmoothChainPrefix
open RhoSmoothLocal RhoSmoothHardChain RhoSmoothHardSmoothed RhoSmoothHardParameters
open AdaptivePolynomialLocalization
open LongTails.Setups.RhoSmoothConvexFull

lemma composed_curvature {d m : ℕ} (π : Fin m ↪ Fin d)
    (g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hg : Differentiable ℝ g) (L₀ L₁ ρ : ℝ)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ (L₀ + L₁ * ‖g x‖ ^ ρ) / 64) (x : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (fun y => (coordinateMap π).adjoint (g (coordinateMap π y))) x‖ ≤
      (L₀ + L₁ * ‖(coordinateMap π).adjoint (g (coordinateMap π x))‖ ^ ρ) / 64 := by
  let A := coordinateMap π
  have hd := A.adjoint.hasFDerivAt.comp x ((hg (A x)).hasFDerivAt.comp x A.hasFDerivAt)
  change HasFDerivAt (fun y => (coordinateMap π).adjoint (g (coordinateMap π y))) _ x at hd
  rw [hd.fderiv, adjoint_norm]
  have hA := projection_opNorm π
  have hAt : ‖A.adjoint‖ ≤ 1 := by simpa [A] using hA
  have h₁ := ContinuousLinearMap.opNorm_comp_le A.adjoint ((fderiv ℝ g (A x)).comp A)
  have h₂ := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ g (A x)) A
  have h₃ : ‖(fderiv ℝ g (A x)).comp A‖ ≤ ‖fderiv ℝ g (A x)‖ := by
    exact h₂.trans (by simpa using mul_le_mul_of_nonneg_left hA (norm_nonneg (fderiv ℝ g (A x))))
  exact (h₁.trans ((mul_le_mul_of_nonneg_right hAt (norm_nonneg _)).trans (by simpa using h₃))).trans
    (hH (A x))

section

variable (p : Params) (hp : spec.valid p) (m : ℕ) (hmM : m ≤ links p)

include hp hmM

noncomputable def kernel : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)) where
  rIn := kernelRadius p m / 2
  rOut := kernelRadius p m
  rIn_pos := div_pos (kernelRadius_pos p hp m) (by norm_num)
  rIn_lt_rOut := by have hh := kernelRadius_pos p hp m; linarith

omit hmM in
lemma kernel_rOut : (kernel p hp m).rOut = kernelRadius p m := rfl

omit hmM in
lemma chain_hyps : 0 < cap p ∧ 0 < scale p ∧ 1 < p.ρ ∧ p.ρ ≤ 2 ∧ 0 < p.L0 / 512 ∧
    0 < p.L1 / 512 ∧ cap p * (p.ρ - 1) = 2 * scale p / (p.L0 / 512) ∧
    scale p ^ p.ρ * (p.L1 / 512) = p.L0 / 512 ∧ 0 < last p :=
  ⟨cap_pos p hp, scale_pos p hp, ρ_gt p hp, ρ_le p hp,
    by have := L0_pos p hp; positivity, by have := L1_pos p hp; positivity,
    cap_relation p hp, scale_rpow_internal p hp, last_pos p hp⟩

lemma center_norm_bound : ‖center (kernel p hp m) (6 * cap p)‖ ≤ p.R / 2 := by
  have hc := cap_pos p hp
  have hk := kernel_margin p m
  have hr := kernelRadius_pos p hp m
  have hh := GeneralizedSmoothHardChainRadius.norm_bound_of_coordinate_bound
    (center (kernel p hp m) (6 * cap p)) (6 * cap p + cap p / 2) (by positivity)
    (fun i => by
      change |-(6 * cap p) - kernelRadius p m| ≤ 6 * cap p + cap p / 2
      rw [abs_le]
      constructor <;> linarith)
  exact hh.trans (center_bound p hp m hmM)

omit hmM in
lemma smooth_curvature_bound (y : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ (smoothField (kernel p hp m) (cap p) (scale p) p.ρ (last p) (6 * cap p)) y‖ ≤
      (p.L0 + p.L1 *
        ‖smoothField (kernel p hp m) (cap p) (scale p) p.ρ (last p) (6 * cap p) y‖ ^ p.ρ) / 64 := by
  obtain ⟨hA, hG, hρ, hρ2, hL₀, hL₁, hAG, hGL, hg⟩ := chain_hyps p hp
  have h := smooth_curvature (kernel p hp m) (cap p) (scale p) p.ρ (p.L0 / 512) (p.L1 / 512)
    (last p) (6 * cap p) hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg y
  exact h.trans (internal_curvature p hp m _ (norm_nonneg _))

variable (π : Fin m ↪ Fin p.d)

noncomputable def seed :
    AdaptiveGeneralizedSmoothLocalization.Seed (E := EuclideanSpace ℝ (Fin p.d)) := by
  obtain ⟨hA, hG, hρ, hρ2, hL₀, hL₁, hAG, hGL, hg⟩ := chain_hyps p hp
  let φ := kernel p hp m
  let f := smoothObjective φ (cap p) (scale p) p.ρ (last p) (6 * cap p)
  let g := smoothField φ (cap p) (scale p) p.ρ (last p) (6 * cap p)
  have hgr : ∀ x, HasGradientAt f (g x) x :=
    smooth_hasGradientAt φ (cap p) (scale p) p.ρ (p.L0 / 512) (p.L1 / 512) (last p) (6 * cap p) hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg
  have hgd : Differentiable ℝ g :=
    (smoothField_contDiff φ (cap p) (scale p) p.ρ (p.L0 / 512) (p.L1 / 512) (last p) (6 * cap p) hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg 1).differentiable
      (by norm_num)
  have hc := smooth_convex φ (cap p) (scale p) p.ρ (p.L0 / 512) (p.L1 / 512) (last p) (6 * cap p) hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg
  have hP := peak_pos (m := m) hg
  have hH : ∀ x, ‖fderiv ℝ g x‖ ≤
      3 * (p.L0 + p.L1 * peak m (last p) ^ p.ρ) / 3 + 1 / 3 * ‖g x‖ := by
    intro x
    have h1 := smooth_curvature_bound p hp m x
    have h2 := smoothField_norm_bound φ (cap p) (scale p) p.ρ (p.L0 / 512) (p.L1 / 512) (last p) (6 * cap p) hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg x
    have h3 : ‖g x‖ ^ p.ρ ≤ peak m (last p) ^ p.ρ :=
      Real.rpow_le_rpow (norm_nonneg _) h2 (by linarith)
    have hL1 := L1_pos p hp
    have hL0 := L0_pos p hp
    have h4 := mul_le_mul_of_nonneg_left h3 hL1.le
    have h5 : 0 ≤ 1 / 3 * ‖g x‖ := by positivity
    have h6 : 0 ≤ p.L1 * ‖g x‖ ^ p.ρ := mul_nonneg hL1.le (Real.rpow_nonneg (norm_nonneg _) _)
    change ‖fderiv ℝ g x‖ ≤ (p.L0 + p.L1 * ‖g x‖ ^ p.ρ) / 64 at h1
    nlinarith
  refine {
    f := fun x => f (coordinateMap π x)
    g := fun x => (coordinateMap π).adjoint (g (coordinateMap π x))
    z := (coordinateMap π).adjoint (center φ (6 * cap p))
    G := peak m (last p)
    r := p.R / 2
    L₀ := 3 * (p.L0 + p.L1 * peak m (last p) ^ p.ρ)
    L₁ := 1
    G_nonneg := hP.le
    r_pos := by have := R_pos p hp; positivity
    L₀_pos := by
      have := L0_pos p hp
      have := L1_pos p hp
      have := Real.rpow_nonneg hP.le p.ρ
      positivity
    L₁_pos := one_pos
    convex := ?_
    gradient := composed_gradient π f g hgr
    differentiable := ?_
    curvature := ?_
    bounded := ?_
    nonnegative := fun x => smooth_nonnegative φ _ _ _ _ _ hG hg (coordinateMap π x)
    zero := ?_
    radius := ?_ }
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hh' := hc.2 (mem_univ (coordinateMap π x)) (mem_univ (coordinateMap π y)) ha hb hab
    simpa only [map_add, map_smul] using hh'
  · exact (coordinateMap π).adjoint.differentiable.comp (hgd.comp (coordinateMap π).differentiable)
  · intro x
    exact GeneralizedSmoothCoordinateEmbedding.composed_curvature π g hgd _ _ hH x
  · intro x
    rw [adjoint_norm]
    exact smoothField_norm_bound φ (cap p) (scale p) p.ρ (p.L0 / 512) (p.L1 / 512) (last p) (6 * cap p) hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg _
  · rw [projection_adjoint]
    exact smooth_center_zero φ _ _ _ _ _ hA hG hρ hg
  · rw [adjoint_norm]
    exact center_norm_bound p hp m hmM

noncomputable def objective : EuclideanSpace ℝ (Fin p.d) → ℝ :=
  value (seed p hp m hmM π).f (degree p) (coefficient p m) (width p)
    (coefficient p m * width p ^ 2)

noncomputable def field : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d) :=
  AdaptivePolynomialLocalization.field (seed p hp m hmM π).f (seed p hp m hmM π).g
    (degree p) (coefficient p m) (width p) (coefficient p m * width p ^ 2)

omit hmM in
lemma half_width : 2 * (p.R / 2) ≤ width p := by
  have := width_radius p hp
  have := R_pos p hp
  linarith

lemma field_curvature (x : EuclideanSpace ℝ (Fin p.d)) :
    ‖fderiv ℝ (field p hp m hmM π) x‖ ≤
      p.L0 + p.L1 * ‖field p hp m hmM π x‖ ^ p.ρ := by
  have hcurv : ∀ y, ‖fderiv ℝ (seed p hp m hmM π).g y‖ ≤
      (p.L0 + p.L1 * ‖(seed p hp m hmM π).g y‖ ^ p.ρ) / 64 := by
    intro y
    obtain ⟨hA, hG, hρ, hρ2, hL₀, hL₁, hAG, hGL, hg⟩ := chain_hyps p hp
    exact composed_curvature π _
      ((smoothField_contDiff (kernel p hp m) (cap p) (scale p) p.ρ (p.L0 / 512) (p.L1 / 512) (last p) (6 * cap p) hA hG hρ hρ2 hL₀ hL₁ hAG hGL hg
        1).differentiable (by norm_num)) _ _ _ (smooth_curvature_bound p hp m) y
  exact RhoSmoothHardLocalization.gradient_curvature (seed p hp m hmM π) (degree p)
    (degree_valid p) (coefficient p m) (width p) (coefficient_pos p hp m) (width_pos p hp)
    (half_width p hp) p.L0 p.L1 p.ρ (scale p) (L0_pos p hp) (L1_pos p hp) (ρ_gt p hp).le
    (ρ_le p hp) (scale_pos p hp) (scale_rpow p hp) hcurv (width_valid p hp)
    (coefficient_tuning p hp m) (leak p hp m hmM) x

lemma objective_nonnegative (x : EuclideanSpace ℝ (Fin p.d)) :
    0 ≤ objective p hp m hmM π x :=
  ((seed p hp m hmM π).nonnegative x).trans
    (value_above _ (degree p) (degree_valid p) _ _ _
      (by have := coefficient_pos p hp m; have := width_pos p hp; positivity) x)

lemma objective_above (x : EuclideanSpace ℝ (Fin p.d)) :
    (seed p hp m hmM π).f x ≤ objective p hp m hmM π x :=
  value_above _ (degree p) (degree_valid p) _ _ _
    (by have := coefficient_pos p hp m; have := width_pos p hp; positivity) x

lemma field_exterior (x : EuclideanSpace ℝ (Fin p.d)) (hx : 4 * width p ≤ ‖x‖) :
    field p hp m hmM π x = coefficient p m • x := by
  apply AdaptiveGeneralizedSmoothLocalization.field_exterior (seed p hp m hmM π) (degree p)
    (coefficient p m) (width p) (coefficient_pos p hp m) (width_pos p hp) (half_width p hp) _ x hx
  change peak m (last p) ≤ coefficient p m * width p
  rw [coefficient_tuning p hp m]
  have : 0 ≤ p.L0 * width p / 1000 := by
    have := L0_pos p hp
    have := width_pos p hp
    positivity
  linarith

lemma seed_r_le_width : (seed p hp m hmM π).r ≤ width p := by
  change p.R / 2 ≤ width p
  have := width_radius p hp
  have := R_pos p hp
  linarith

lemma objective_zero : objective p hp m hmM π (seed p hp m hmM π).z = 0 := by
  have hh := AdaptiveGeneralizedSmoothLocalization.value_interior (seed p hp m hmM π) (degree p)
    (coefficient p m) (width p) (coefficient_pos p hp m) (width_pos p hp)
    (seed p hp m hmM π).z
    ((seed p hp m hmM π).radius.trans (seed_r_le_width p hp m hmM π))
  exact hh.trans (seed p hp m hmM π).zero

lemma admissible : spec.admissible p
    (fun x : EuclideanSpace ℝ (Fin p.d) => objective p hp m hmM π (x - p.x0))
    (SmoothConvexFiniteLowerBound.oracle p.x0 (field p hp m hmM π)) := by
  let s := seed p hp m hmM π
  have ha := coefficient_pos p hp m
  have hB := width_pos p hp
  have hn := degree_valid p
  have hW : 0 < coefficient p m * width p ^ 2 := by positivity
  have hg := value_hasGradientAt s.f s.g (degree p) hn (coefficient p m) (width p) _ hW
  have hd := AdaptiveGeneralizedSmoothLocalization.field_differentiable s (degree p) hn
    (coefficient p m) (width p) (coefficient p m * width p ^ 2)
  refine ⟨SmoothConvexFiniteLowerBound.convex_translate p.x0 _
    (value_convex s.f s.g (degree p) hn _ _ _ ha.le hW s.convex s.gradient),
    ?_, ?_, ?_, p.x0 + s.z, ?_, ?_⟩
  · intro k ω x
    exact SmoothConvexFiniteLowerBound.gradient_translate p.x0 _ _ (fun y => hg y (s.gradient y)) x
  · intro k ω
    exact hd.comp (differentiable_id.sub_const p.x0)
  · intro k ω x
    change EuclideanSpace ℝ (Fin p.d) at x
    change ‖fderiv ℝ (fun y => field p hp m hmM π (y - p.x0)) x‖ ≤ _
    have ht := (hd (x - p.x0)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p.x0)
    change HasFDerivAt (fun y => field p hp m hmM π (y - p.x0)) _ x at ht
    rw [ht.fderiv, ContinuousLinearMap.comp_id]
    exact field_curvature p hp m hmM π (x - p.x0)
  · intro x _
    change EuclideanSpace ℝ (Fin p.d) at x
    change objective p hp m hmM π (p.x0 + s.z - p.x0) ≤ objective p hp m hmM π (x - p.x0)
    rw [add_sub_cancel_left]
    exact AdaptiveGeneralizedSmoothLocalization.value_minimizer s (degree p) hn
      (coefficient p m) (width p) ha hB (seed_r_le_width p hp m hmM π) (mem_univ (x - p.x0))
  · change ‖p.x0 - (p.x0 + s.z)‖ ≤ p.R
    simp only [sub_add_cancel_left, norm_neg]
    have hr : ‖s.z‖ ≤ p.R / 2 := s.radius
    have := R_pos p hp
    linarith

end

end LongTails.Proofs.RhoSmoothHardInstance
