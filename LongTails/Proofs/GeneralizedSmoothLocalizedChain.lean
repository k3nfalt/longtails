import LongTails.Proofs.GeneralizedSmoothCoordinateEmbedding
import LongTails.Proofs.GeneralizedSmoothHardChainRadius
import LongTails.Proofs.GeneralizedSmoothLocalization
import LongTails.Proofs.SmoothConvexFiniteLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace LongTails.Proofs.GeneralizedSmoothLocalizedChain

open FiniteSumNondualLowerComponents GeneralizedSmoothCoordinateEmbedding
open GeneralizedSmoothHardChain GeneralizedSmoothSmoothedChain GeneralizedSmoothHardChainRadius

noncomputable def seed (p : LongTails.Setups.GeneralizedSmoothConvexTransient.Params)
    (hp : LongTails.Setups.GeneralizedSmoothConvexTransient.spec.valid p) (m : ℕ) (hm : 0 < m)
    (hmB : m ≤ ⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊ + 1)
    (π : Fin m ↪ Fin p.d) : GeneralizedSmoothLocalization.Seed (E := EuclideanSpace ℝ (Fin p.d)) := by
  have h0 : 0 < p.L0 / 4 := by have := hp.1; positivity
  have h1 : 0 < p.L1 / 4 := by have := hp.2.1; positivity
  have hR := hp.2.2.1
  have hε := hp.2.2.2.1
  let φ := kernel hm (p.L1 / 4) p.R h1 hR
  let f := smoothObjective φ (p.L0 / 4) (p.L1 / 4) p.ε
  let g := smoothField φ (p.L0 / 4) (p.L1 / 4) p.ε
  have hg : ∀ x, HasGradientAt f (g x) x := smooth_hasGradientAt hm φ _ _ _ h0 h1 hε
  have hgd : Differentiable ℝ g := (smoothField_contDiff hm φ _ _ _ h0 h1 hε 1).differentiable (by norm_num)
  have hc := smooth_convex hm φ _ _ _ h0 h1 hε
  have hH : ∀ x, ‖fderiv ℝ g x‖ ≤ p.L0 / 3 + p.L1 / 3 * ‖g x‖ := by
    intro x
    have hh := smooth_curvature hm φ _ _ _ h0 h1 hε
      (kernel_curvature_radius hm (p.L1 / 4) p.R h1) x
    convert hh using 1
    ring
  refine {
    f := fun x => f (coordinateMap π x)
    g := fun x => (coordinateMap π).adjoint (g (coordinateMap π x))
    z := (coordinateMap π).adjoint (center φ (p.L0 / 4) (p.L1 / 4) p.ε)
    G := peak m (p.L1 / 4) p.ε
    r := p.R / 2
    L₀ := p.L0 / 3
    L₁ := p.L1 / 3
    G_nonneg := (peak_pos m _ _ h1 hε).le
    r_pos := by positivity
    L₀_nonneg := by have := hp.1; positivity
    L₁_nonneg := by have := hp.2.1; positivity
    convex := ?_
    gradient := composed_gradient π f g hg
    differentiable := ?_
    curvature := composed_curvature π g hgd _ _ hH
    bounded := ?_
    nonnegative := fun x => smooth_nonnegative hm φ _ _ _ h0 h1 hε (coordinateMap π x)
    zero := ?_
    radius := ?_ }
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hh := hc.2 (mem_univ (coordinateMap π x)) (mem_univ (coordinateMap π y)) ha hb hab
    simpa only [map_add, map_smul] using hh
  · exact (coordinateMap π).adjoint.differentiable.comp (hgd.comp (coordinateMap π).differentiable)
  · intro x
    rw [adjoint_norm]
    exact smoothField_norm_bound hm φ _ _ _ h0 h1 hε _
  · rw [projection_adjoint]
    exact smooth_center_zero hm φ _ _ _ h0 h1 hε
  · rw [adjoint_norm]
    have hh := kernel_center_bound hm (p.L0 / 4) (p.L1 / 4) p.ε p.R h1 hR (tuned_shift_norm p hp m hm hmB)
    exact hh.trans (by linarith)

variable (p : LongTails.Setups.GeneralizedSmoothConvexTransient.Params)
    (hp : LongTails.Setups.GeneralizedSmoothConvexTransient.spec.valid p) (m : ℕ) (hm : 0 < m)
    (hmB : m ≤ ⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊ + 1)
    (π : Fin m ↪ Fin p.d)

noncomputable def objective : EuclideanSpace ℝ (Fin p.d) → ℝ :=
  GeneralizedSmoothLocalization.objective (seed p hp m hm hmB π) (p.L0 / 32)

noncomputable def field : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d) :=
  GeneralizedSmoothLocalization.gradient (seed p hp m hm hmB π) (p.L0 / 32)

lemma field_curvature (x : EuclideanSpace ℝ (Fin p.d)) :
    ‖fderiv ℝ (field p hp m hm hmB π) x‖ ≤ p.L0 + p.L1 * ‖field p hp m hm hmB π x‖ := by
  have ha : 0 < p.L0 / 32 := by have := hp.1; positivity
  have hh := GeneralizedSmoothLocalization.gradient_curvature (seed p hp m hm hmB π) _ ha x
  change ‖fderiv ℝ (field p hp m hm hmB π) x‖ ≤
    p.L0 / 3 + 10 * (p.L0 / 32) + 2 * (p.L1 / 3) * ‖field p hp m hm hmB π x‖ at hh
  have hn := mul_nonneg hp.2.1.le (norm_nonneg (field p hp m hm hmB π x))
  have h0 := hp.1
  linarith

lemma admissible : LongTails.Setups.GeneralizedSmoothConvexTransient.spec.admissible p
    (fun x : EuclideanSpace ℝ (Fin p.d) => objective p hp m hm hmB π (x - p.x0))
    (SmoothConvexFiniteLowerBound.oracle p.x0 (field p hp m hm hmB π)) := by
  let s := seed p hp m hm hmB π
  have ha : 0 < p.L0 / 32 := by have := hp.1; positivity
  have hg := GeneralizedSmoothLocalization.objective_gradient s _ ha
  have hd := GeneralizedSmoothLocalization.gradient_differentiable s (p.L0 / 32)
  refine ⟨SmoothConvexFiniteLowerBound.convex_translate p.x0 _
    (GeneralizedSmoothLocalization.objective_convex s _ ha), ?_, ?_, ?_, p.x0 + s.z, ?_, ?_⟩
  · intro k ω x
    exact SmoothConvexFiniteLowerBound.gradient_translate p.x0 _ _ hg x
  · intro k ω
    exact hd.comp (differentiable_id.sub_const p.x0)
  · intro k ω x
    change ‖fderiv ℝ (fun y => field p hp m hm hmB π (y - p.x0)) x‖ ≤ _
    have ht := (hd (x - p.x0)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const p.x0)
    change HasFDerivAt (fun y => field p hp m hm hmB π (y - p.x0)) _ x at ht
    rw [ht.fderiv, ContinuousLinearMap.comp_id]
    exact field_curvature p hp m hm hmB π (x - p.x0)
  · intro x _
    change objective p hp m hm hmB π (p.x0 + s.z - p.x0) ≤ _
    rw [add_sub_cancel_left]
    exact GeneralizedSmoothLocalization.objective_minimizer s _ ha (mem_univ (x - p.x0))
  · change ‖p.x0 - (p.x0 + s.z)‖ ≤ p.R
    simp only [sub_add_cancel_left, norm_neg]
    have hr : ‖s.z‖ ≤ p.R / 2 := s.radius
    have := hp.2.2.1
    linarith

end LongTails.Proofs.GeneralizedSmoothLocalizedChain
