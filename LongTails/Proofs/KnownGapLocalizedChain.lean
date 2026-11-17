import LongTails.Proofs.GeneralizedSmoothCoordinateEmbedding
import LongTails.Proofs.KnownGapParameters
import LongTails.Proofs.KnownGapSmoothedChain
import LongTails.Proofs.AdaptiveGeneralizedSmoothLocalization
import LongTails.Proofs.SmoothConvexFiniteLowerBound

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace LongTails.Proofs.KnownGapLocalizedChain

open FiniteSumNondualLowerComponents GeneralizedSmoothCoordinateEmbedding
open KnownGapChainWeights KnownGapSmoothedChain KnownGapParameters
open LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension

noncomputable def kernelRadius (p : Params) (m : ℕ) : ℝ :=
  min (threshold (p.L1 / 4) (ratio p m)) (p.R / (16 * Real.sqrt m))

section

variable (p : Params) (hp : spec.valid p) (m : ℕ) (hm : 0 < m) (hmM : m ≤ links p)

include hp hm hmM

omit hmM in
lemma kernelRadius_pos : 0 < kernelRadius p m := by
  unfold kernelRadius
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  exact lt_min (threshold_pos (p.L1 / 4) (ratio p m) (by have := L1_pos p hp; positivity)
    (ratio_pos p hp m hm)) (div_pos (R_pos p hp) (mul_pos (by norm_num) (Real.sqrt_pos.mpr hm0)))

noncomputable def kernel : ContDiffBump (0 : EuclideanSpace ℝ (Fin m)) where
  rIn := kernelRadius p m / 2
  rOut := kernelRadius p m
  rIn_pos := div_pos (kernelRadius_pos p hp m hm) (by norm_num)
  rIn_lt_rOut := by have hh := kernelRadius_pos p hp m hm; linarith

omit hmM in
lemma kernel_rOut : (kernel p hp m hm).rOut = kernelRadius p m := rfl

omit hmM in
lemma kernel_le_threshold : (kernel p hp m hm).rOut ≤ threshold (p.L1 / 4) (ratio p m) := by
  rw [kernel_rOut]
  exact min_le_left _ _

omit hm hmM in
lemma threshold_le : threshold (p.L1 / 4) (ratio p m) ≤ 1 / (4 * p.L1) := by
  rw [threshold_eq p m]
  have := L1_pos p hp
  apply div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)

omit hmM in
lemma kernel_curvature : p.L1 / 4 * (kernel p hp m hm).rOut ≤ 1 / 16 := by
  have h1 := kernel_le_threshold p hp m hm
  have h2 := threshold_le p hp m
  have hL1 := L1_pos p hp
  have : p.L1 / 4 * (1 / (4 * p.L1)) = 1 / 16 := by field_simp; ring
  calc p.L1 / 4 * (kernel p hp m hm).rOut ≤ p.L1 / 4 * (1 / (4 * p.L1)) := by
        gcongr; exact h1.trans h2
    _ = 1 / 16 := this

omit hmM in
lemma kernel_sqrt : Real.sqrt m * (kernel p hp m hm).rOut ≤ p.R / 16 := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hh := mul_le_mul_of_nonneg_left (min_le_right (threshold (p.L1 / 4) (ratio p m))
    (p.R / (16 * Real.sqrt m))) hs.le
  have he : Real.sqrt m * (p.R / (16 * Real.sqrt m)) = p.R / 16 := by field_simp
  rw [kernel_rOut]
  unfold kernelRadius
  simpa only [he] using hh

lemma center_norm_bound :
    ‖center (kernel p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m)‖ ≤ p.R / 2 := by
  let σ := GeneralizedSmoothHardTransfer.shift (p.L0 / 4) (p.L1 / 4)
    (peak m (p.L1 / 4) p.ε (ratio p m)) (weight m (p.L1 / 4) p.ε (ratio p m))
  let z := center (kernel p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m)
  have hh : ‖z + σ‖ ≤ Real.sqrt m * (kernel p hp m hm).rOut := by
    apply GeneralizedSmoothHardChainRadius.norm_bound_of_coordinate_bound _ _
      (kernel p hp m hm).rOut_pos.le
    intro i
    change |-GeneralizedSmoothHardTransfer.shiftCoordinate (p.L0 / 4) (p.L1 / 4)
      (peak m (p.L1 / 4) p.ε (ratio p m)) (weight m (p.L1 / 4) p.ε (ratio p m)) i -
      (kernel p hp m hm).rOut +
      GeneralizedSmoothHardTransfer.shiftCoordinate (p.L0 / 4) (p.L1 / 4)
        (peak m (p.L1 / 4) p.ε (ratio p m)) (weight m (p.L1 / 4) p.ε (ratio p m)) i| ≤
      (kernel p hp m hm).rOut
    have he : -GeneralizedSmoothHardTransfer.shiftCoordinate (p.L0 / 4) (p.L1 / 4)
      (peak m (p.L1 / 4) p.ε (ratio p m)) (weight m (p.L1 / 4) p.ε (ratio p m)) i -
      (kernel p hp m hm).rOut +
      GeneralizedSmoothHardTransfer.shiftCoordinate (p.L0 / 4) (p.L1 / 4)
        (peak m (p.L1 / 4) p.ε (ratio p m)) (weight m (p.L1 / 4) p.ε (ratio p m)) i =
      -(kernel p hp m hm).rOut := by ring
    rw [he, abs_neg, abs_of_pos (kernel p hp m hm).rOut_pos]
  have ht := norm_sub_le (z + σ) σ
  rw [add_sub_cancel_right] at ht
  have hσ := shift_norm_le p hp m hm hmM
  have hk := kernel_sqrt p hp m hm
  have hR := R_pos p hp
  change ‖z‖ ≤ p.R / 2
  change ‖σ‖ ≤ p.R / 4 at hσ
  linarith

variable (π : Fin m ↪ Fin p.d)

noncomputable def seed :
    AdaptiveGeneralizedSmoothLocalization.Seed (E := EuclideanSpace ℝ (Fin p.d)) := by
  have h0 : 0 < p.L0 / 4 := by have := L0_pos p hp; positivity
  have h1 : 0 < p.L1 / 4 := by have := L1_pos p hp; positivity
  have hε := ε_pos p hp
  have hh := ratio_pos p hp m hm
  let φ := kernel p hp m hm
  let f := smoothObjective φ (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m)
  let g := smoothField φ (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m)
  have hg : ∀ x, HasGradientAt f (g x) x := smooth_hasGradientAt hm φ _ _ _ _ h0 h1 hε hh
  have hgd : Differentiable ℝ g :=
    (smoothField_contDiff hm φ _ _ _ _ h0 h1 hε hh 1).differentiable (by norm_num)
  have hc := smooth_convex hm φ _ _ _ _ h0 h1 hε hh
  have hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 / 3 + p.L1 / 3 * ‖g x‖ := by
    intro x
    have hh' := smooth_curvature hm φ _ _ _ _ h0 h1 hε hh (kernel_curvature p hp m hm) x
    convert hh' using 1
    ring
  refine {
    f := fun x => f (coordinateMap π x)
    g := fun x => (coordinateMap π).adjoint (g (coordinateMap π x))
    z := (coordinateMap π).adjoint (center φ (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m))
    G := peak m (p.L1 / 4) p.ε (ratio p m)
    r := p.R / 2
    L₀ := p.L0
    L₁ := p.L1
    G_nonneg := (peak_pos m _ _ _ h1 hε).le
    r_pos := by have := R_pos p hp; positivity
    L₀_pos := L0_pos p hp
    L₁_pos := L1_pos p hp
    convex := ?_
    gradient := composed_gradient π f g hg
    differentiable := ?_
    curvature := composed_curvature π g hgd _ _ hH
    bounded := ?_
    nonnegative := fun x => smooth_nonnegative hm φ _ _ _ _ h0 h1 hε hh (coordinateMap π x)
    zero := ?_
    radius := ?_ }
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hh' := hc.2 (mem_univ (coordinateMap π x)) (mem_univ (coordinateMap π y)) ha hb hab
    simpa only [map_add, map_smul] using hh'
  · exact (coordinateMap π).adjoint.differentiable.comp (hgd.comp (coordinateMap π).differentiable)
  · intro x
    rw [adjoint_norm]
    exact smoothField_norm_bound hm φ _ _ _ _ h0 h1 hε hh _
  · rw [projection_adjoint]
    exact smooth_center_zero hm φ _ _ _ _ h0 h1 hε hh
  · rw [adjoint_norm]
    exact center_norm_bound p hp m hm hmM

noncomputable def coefficient : ℝ :=
  peak m (p.L1 / 4) p.ε (ratio p m) / width p + p.L0 / 1000

omit hm hmM in
lemma coefficient_pos : 0 < coefficient p m := by
  have hG := peak_pos m (p.L1 / 4) p.ε (ratio p m) (by have := L1_pos p hp; positivity) (ε_pos p hp)
  have hB := width_pos p hp
  have h0 := L0_pos p hp
  unfold coefficient
  positivity

omit hm hmM in
lemma coefficient_tuning :
    coefficient p m * width p = peak m (p.L1 / 4) p.ε (ratio p m) + p.L0 * width p / 1000 := by
  have hB := (width_pos p hp).ne'
  unfold coefficient
  field_simp

noncomputable def objective : EuclideanSpace ℝ (Fin p.d) → ℝ :=
  AdaptivePolynomialLocalization.value (seed p hp m hm hmM π).f (degree p)
    (coefficient p m) (width p) (coefficient p m * width p ^ 2)

noncomputable def field : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d) :=
  AdaptivePolynomialLocalization.field (seed p hp m hm hmM π).f (seed p hp m hm hmM π).g (degree p)
    (coefficient p m) (width p) (coefficient p m * width p ^ 2)

omit hm hmM in
lemma half_width : 2 * (p.R / 2) ≤ width p := by linarith [width_radius p hp]

lemma field_curvature (x : EuclideanSpace ℝ (Fin p.d)) :
    ‖fderiv ℝ (field p hp m hm hmM π) x‖ ≤ p.L0 + p.L1 * ‖field p hp m hm hmM π x‖ := by
  exact AdaptiveGeneralizedSmoothLocalization.gradient_curvature (seed p hp m hm hmM π)
    (degree p) (degree_valid p hp) (coefficient p m) (width p) (coefficient_pos p hp m)
    (width_pos p hp) (half_width p hp) (width_valid p hp)
    (coefficient_tuning p hp m) (peak_small p hp m hm) x

lemma objective_nonnegative (x : EuclideanSpace ℝ (Fin p.d)) :
    0 ≤ objective p hp m hm hmM π x := by
  exact ((seed p hp m hm hmM π).nonnegative x).trans
    (AdaptivePolynomialLocalization.value_above _ (degree p) (degree_valid p hp) _ _ _
      (by have := coefficient_pos p hp m; positivity) x)

lemma objective_above (x : EuclideanSpace ℝ (Fin p.d)) :
    (seed p hp m hm hmM π).f x ≤ objective p hp m hm hmM π x :=
  AdaptivePolynomialLocalization.value_above _ (degree p) (degree_valid p hp) _ _ _
    (by have := coefficient_pos p hp m; positivity) x

lemma field_exterior (x : EuclideanSpace ℝ (Fin p.d)) (hx : 4 * width p ≤ ‖x‖) :
    field p hp m hm hmM π x = coefficient p m • x := by
  apply AdaptiveGeneralizedSmoothLocalization.field_exterior (seed p hp m hm hmM π) (degree p)
    (coefficient p m) (width p) (coefficient_pos p hp m) (width_pos p hp)
    (half_width p hp) _ x hx
  change peak m (p.L1 / 4) p.ε (ratio p m) ≤ coefficient p m * width p
  rw [coefficient_tuning p hp m]
  have hh : 0 ≤ p.L0 * width p / 1000 := by have := L0_pos p hp; have := width_pos p hp; positivity
  linarith

lemma seed_r_le_width : (seed p hp m hm hmM π).r ≤ width p := by
  change p.R / 2 ≤ width p
  have := width_radius p hp
  have := R_pos p hp
  linarith

lemma objective_zero : objective p hp m hm hmM π (seed p hp m hm hmM π).z = 0 := by
  have hh := AdaptiveGeneralizedSmoothLocalization.value_interior (seed p hp m hm hmM π) (degree p)
    (coefficient p m) (width p) (coefficient_pos p hp m) (width_pos p hp)
    (seed p hp m hm hmM π).z ((seed p hp m hm hmM π).radius.trans (seed_r_le_width p hp m hm hmM π))
  exact hh.trans (seed p hp m hm hmM π).zero

lemma objective_initial : objective p hp m hm hmM π 0 ≤ p.Δ := by
  have h0 : 0 < p.L0 / 4 := by have := L0_pos p hp; positivity
  have h1 : 0 < p.L1 / 4 := by have := L1_pos p hp; positivity
  have hε := ε_pos p hp
  have hh := ratio_pos p hp m hm
  have hL1 := L1_pos p hp
  have hint := AdaptiveGeneralizedSmoothLocalization.value_interior (seed p hp m hm hmM π) (degree p)
    (coefficient p m) (width p) (coefficient_pos p hp m) (width_pos p hp) 0
    (by rw [norm_zero]; exact (width_pos p hp).le)
  change objective p hp m hm hmM π 0 = (seed p hp m hm hmM π).f 0 at hint
  rw [hint]
  change smoothObjective (kernel p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m)
    (coordinateMap π 0) ≤ p.Δ
  rw [map_zero]
  have hq := q_pos p hp
  have hup := smooth_upper hm (kernel p hp m hm) (p.L0 / 4) (p.L1 / 4) p.ε (ratio p m) h0 h1 hε hh
    0 ((q p + 1) / (4 * p.L1)) (by positivity) (by
      intro i
      have hs := shiftCoordinate_le p hp m hm hmM i
      have hr := (kernel_le_threshold p hp m hm).trans (threshold_le p hp m)
      change (0 : EuclideanSpace ℝ (Fin m)) i + (kernel p hp m hm).rOut + _ ≤ _
      simp only [PiLp.zero_apply, zero_add]
      have : 1 / (4 * p.L1) + q p / (4 * p.L1) = (q p + 1) / (4 * p.L1) := by ring
      linarith)
  exact hup.trans (gap_bound p hp m hm)

lemma admissible : LongTails.Setups.GeneralizedSmoothAndConvex.spec.admissible p.toGeneralized
    (fun x : EuclideanSpace ℝ (Fin p.d) => objective p hp m hm hmM π (x - p.x0))
    (SmoothConvexFiniteLowerBound.oracle p.x0 (field p hp m hm hmM π)) := by
  let s := seed p hp m hm hmM π
  have ha := coefficient_pos p hp m
  have hB := width_pos p hp
  have hn := degree_valid p hp
  have hW : 0 < coefficient p m * width p ^ 2 := by positivity
  have hg := AdaptivePolynomialLocalization.value_hasGradientAt s.f s.g (degree p) hn
    (coefficient p m) (width p) _ hW
  have hd := AdaptiveGeneralizedSmoothLocalization.field_differentiable s (degree p) hn
    (coefficient p m) (width p) (coefficient p m * width p ^ 2)
  refine ⟨SmoothConvexFiniteLowerBound.convex_translate p.x0 _
    (AdaptivePolynomialLocalization.value_convex s.f s.g (degree p) hn _ _ _ ha.le hW s.convex s.gradient),
    ?_, ?_, ?_, p.x0 + s.z, ?_, ?_, ?_⟩
  · intro k ω x
    exact SmoothConvexFiniteLowerBound.gradient_translate p.x0 _ _ (fun y => hg y (s.gradient y)) x
  · intro k ω
    exact hd.comp (differentiable_id.sub_const p.x0)
  · intro k ω x
    change ‖fderiv ℝ (fun y => field p hp m hm hmM π (y - p.x0)) x‖ ≤ _
    have ht := (hd (x - p.x0)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p.x0)
    change HasFDerivAt (fun y => field p hp m hm hmM π (y - p.x0)) _ x at ht
    rw [ht.fderiv, ContinuousLinearMap.comp_id]
    exact field_curvature p hp m hm hmM π (x - p.x0)
  · intro x _
    change objective p hp m hm hmM π (p.x0 + s.z - p.x0) ≤ _
    rw [add_sub_cancel_left]
    exact AdaptiveGeneralizedSmoothLocalization.value_minimizer s (degree p) hn
      (coefficient p m) (width p) ha hB (seed_r_le_width p hp m hm hmM π) (mem_univ (x - p.x0))
  · change ‖p.x0 - (p.x0 + s.z)‖ ≤ p.R
    simp only [sub_add_cancel_left, norm_neg]
    have hr : ‖s.z‖ ≤ p.R / 2 := s.radius
    have := R_pos p hp
    linarith
  · change objective p hp m hm hmM π (p.x0 - p.x0) - objective p hp m hm hmM π (p.x0 + s.z - p.x0) ≤ p.Δ
    rw [sub_self, add_sub_cancel_left, objective_zero p hp m hm hmM π, sub_zero]
    exact objective_initial p hp m hm hmM π

end

end LongTails.Proofs.KnownGapLocalizedChain
