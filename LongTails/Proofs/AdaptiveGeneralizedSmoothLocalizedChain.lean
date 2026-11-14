import LongTails.Proofs.GeneralizedSmoothCoordinateEmbedding
import LongTails.Proofs.GeneralizedSmoothHardChainRadius
import LongTails.Proofs.AdaptiveGeneralizedSmoothLocalization
import LongTails.Proofs.SmoothConvexFiniteLowerBound
import LongTails.Proofs.AdaptiveTransientParameters

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set

namespace LongTails.Proofs.AdaptiveGeneralizedSmoothLocalizedChain

open FiniteSumNondualLowerComponents GeneralizedSmoothCoordinateEmbedding
open GeneralizedSmoothHardChain GeneralizedSmoothSmoothedChain GeneralizedSmoothHardChainRadius

noncomputable def seed (p : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.Params)
    (hp : LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension.spec.valid p) (m : ℕ) (hm : 0 < m)
    (hmB : m ≤ ⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊ + 1)
    (π : Fin m ↪ Fin p.d) : AdaptiveGeneralizedSmoothLocalization.Seed (E := EuclideanSpace ℝ (Fin p.d)) := by
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
    L₀ := p.L0
    L₁ := p.L1
    G_nonneg := (peak_pos m _ _ h1 hε).le
    r_pos := by positivity
    L₀_pos := hp.1
    L₁_pos := hp.2.1
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

open AdaptiveTransientParameters
open LongTails.Setups.GeneralizedSmoothConvexPolynomialDimension

noncomputable def coefficient (p : Params) (m : ℕ) : ℝ :=
  peak m (p.L1 / 4) p.ε / width p + p.L0 / 1000

lemma width_pos (p : Params) (hp : spec.valid p) : 0 < width p := by
  have := hp.2.2.1
  unfold width
  positivity

lemma coefficient_pos (p : Params) (hp : spec.valid p) (m : ℕ) : 0 < coefficient p m := by
  have hG := peak_pos m (p.L1 / 4) p.ε (by have := hp.2.1; positivity) hp.2.2.2.1
  have hB := width_pos p hp
  have h0 := hp.1
  unfold coefficient
  positivity

lemma coefficient_tuning (p : Params) (hp : spec.valid p) (m : ℕ) :
    coefficient p m * width p = peak m (p.L1 / 4) p.ε + p.L0 * width p / 1000 := by
  have hB := (width_pos p hp).ne'
  unfold coefficient
  field_simp

lemma degree_valid (p : Params) (hp : spec.valid p) : 2 ≤ degree p :=
  degree_ge_two _ (by have := hp.2.2.2.2.1; linarith)

lemma width_valid (p : Params) (hp : spec.valid p) :
    256 * ((degree p : ℝ) * (degree p + 1 : ℕ)) ≤ p.L1 * width p := by
  have hq : 1 ≤ p.L1 * p.R := by have := hp.2.2.2.2.1; linarith
  have hh := degree_product _ hq
  change (degree p : ℝ) * (degree p + 1 : ℕ) ≤ 306 * (p.L1 * p.R) at hh
  unfold width
  nlinarith only [hh, hq]

lemma width_radius (p : Params) (hp : spec.valid p) : p.R ≤ width p := by
  have := hp.2.2.1
  unfold width
  linarith

lemma peak_small (p : Params) (hp : spec.valid p) (m : ℕ) (hm : 0 < m)
    (hmB : m ≤ ⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊ + 1) :
    peak m (p.L1 / 4) p.ε * (1 / 2 : ℝ) ^ degree p * p.L1 ≤ p.L0 := by
  have hmq : (m : ℝ) ≤ p.L1 * p.R :=
    (show (m : ℝ) ≤ ((⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊ + 1 : ℕ) : ℝ) by
      exact_mod_cast hmB).trans (GeneralizedSmoothTransientParameters.links_le_q _ hp.2.2.2.2.1)
  have hh := peak_suppression m hm p.L0 p.L1 p.R p.ε hp.1 hp.2.1 hp.2.2.1
    hp.2.2.2.2.2.2.1 hmq (by have := hp.2.2.2.2.1; linarith)
  unfold peak degree
  convert hh using 1
  ring

variable (p : Params) (hp : spec.valid p) (m : ℕ) (hm : 0 < m)
    (hmB : m ≤ ⌊p.L1 * p.R / (4096 * Real.log (2 + p.L1 * p.R))⌋₊ + 1)
    (π : Fin m ↪ Fin p.d)

noncomputable def objective : EuclideanSpace ℝ (Fin p.d) → ℝ :=
  AdaptivePolynomialLocalization.value (seed p hp m hm hmB π).f (degree p)
    (coefficient p m) (width p) (coefficient p m * width p ^ 2)

noncomputable def field : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d) :=
  AdaptivePolynomialLocalization.field (seed p hp m hm hmB π).f (seed p hp m hm hmB π).g (degree p)
    (coefficient p m) (width p) (coefficient p m * width p ^ 2)

lemma field_curvature (x : EuclideanSpace ℝ (Fin p.d)) :
    ‖fderiv ℝ (field p hp m hm hmB π) x‖ ≤ p.L0 + p.L1 * ‖field p hp m hm hmB π x‖ := by
  exact AdaptiveGeneralizedSmoothLocalization.gradient_curvature (seed p hp m hm hmB π)
    (degree p) (degree_valid p hp) (coefficient p m) (width p) (coefficient_pos p hp m)
    (width_pos p hp) (by change 2 * (p.R / 2) ≤ width p; linarith [width_radius p hp]) (width_valid p hp)
    (coefficient_tuning p hp m) (peak_small p hp m hm hmB) x

lemma admissible : spec.admissible p
    (fun x : EuclideanSpace ℝ (Fin p.d) => objective p hp m hm hmB π (x - p.x0))
    (SmoothConvexFiniteLowerBound.oracle p.x0 (field p hp m hm hmB π)) := by
  let s := seed p hp m hm hmB π
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
    ?_, ?_, ?_, p.x0 + s.z, ?_, ?_⟩
  · intro k ω x
    exact SmoothConvexFiniteLowerBound.gradient_translate p.x0 _ _ (fun y => hg y (s.gradient y)) x
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
    exact AdaptiveGeneralizedSmoothLocalization.value_minimizer s (degree p) hn
      (coefficient p m) (width p) ha hB
      (by change p.R / 2 ≤ width p; have := width_radius p hp; have := hp.2.2.1; linarith)
      (mem_univ (x - p.x0))
  · change ‖p.x0 - (p.x0 + s.z)‖ ≤ p.R
    simp only [sub_add_cancel_left, norm_neg]
    have hr : ‖s.z‖ ≤ p.R / 2 := s.radius
    have := hp.2.2.1
    linarith

lemma objective_nonnegative (x : EuclideanSpace ℝ (Fin p.d)) :
    0 ≤ objective p hp m hm hmB π x := by
  exact ((seed p hp m hm hmB π).nonnegative x).trans
    (AdaptivePolynomialLocalization.value_above _ (degree p) (degree_valid p hp) _ _ _
      (by have := coefficient_pos p hp m; positivity) x)

lemma objective_above (x : EuclideanSpace ℝ (Fin p.d)) :
    (seed p hp m hm hmB π).f x ≤ objective p hp m hm hmB π x :=
  AdaptivePolynomialLocalization.value_above _ (degree p) (degree_valid p hp) _ _ _
    (by have := coefficient_pos p hp m; positivity) x

lemma field_exterior (x : EuclideanSpace ℝ (Fin p.d)) (hx : 4 * width p ≤ ‖x‖) :
    field p hp m hm hmB π x = coefficient p m • x := by
  apply AdaptiveGeneralizedSmoothLocalization.field_exterior (seed p hp m hm hmB π) (degree p)
    (coefficient p m) (width p) (coefficient_pos p hp m) (width_pos p hp)
    (by change 2 * (p.R / 2) ≤ width p; linarith [width_radius p hp]) _ x hx
  change peak m (p.L1 / 4) p.ε ≤ coefficient p m * width p
  rw [coefficient_tuning p hp m]
  have hh : 0 ≤ p.L0 * width p / 1000 := by have := hp.1; have := width_pos p hp; positivity
  linarith

lemma objective_zero : objective p hp m hm hmB π (seed p hp m hm hmB π).z = 0 := by
  have hh := AdaptiveGeneralizedSmoothLocalization.value_interior (seed p hp m hm hmB π) (degree p)
    (coefficient p m) (width p) (coefficient_pos p hp m) (width_pos p hp)
    (seed p hp m hm hmB π).z
    ((seed p hp m hm hmB π).radius.trans
      (by change p.R / 2 ≤ width p; have := width_radius p hp; have := hp.2.2.1; linarith))
  exact hh.trans (seed p hp m hm hmB π).zero

end LongTails.Proofs.AdaptiveGeneralizedSmoothLocalizedChain
