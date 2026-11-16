import LongTails.Setups.GapGeneralizedSmoothConvex
import LongTails.Proofs.GapBoundedSmoothParameters
import LongTails.Proofs.GapLocalizedChain
import LongTails.Proofs.GapChainPrefix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.GapSmoothInstance

local instance pointMeasurableSpace (m : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin m)) :=
  WithLp.measurableSpace 2 (Fin m → ℝ)

open LongTails.Setups.GapGeneralizedSmoothConvex
open GapBoundedSmoothParameters

noncomputable def curvature (p : Params) : ℝ := p.L0 / 10000
noncomputable def coefficient (p : Params) (m : ℕ) : ℝ := slope m p.R p.ε / p.R + curvature p
noncomputable def threshold (p : Params) (m : ℕ) : ℝ := spacing m p.R / 4

noncomputable def bump (p : Params) (hp : spec.valid p) (m : ℕ) (hm : 0 < m) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin m)) where
  rIn := spacing m p.R / 256
  rOut := spacing m p.R / 128
  rIn_pos := by have hh := spacing_pos hm p.R hp.2.2.1; positivity
  rIn_lt_rOut := by have hh := spacing_pos hm p.R hp.2.2.1; linarith

noncomputable def seed (p : Params) (hp : spec.valid p) (m : ℕ) (hm : 0 < m) :
    AdaptiveGeneralizedSmoothLocalization.Seed (E := EuclideanSpace ℝ (Fin m)) :=
  GapBoundedSmoothMollification.seed hm (bump p hp m hm) (curvature p) (slope m p.R p.ε) (spacing m p.R)
    (by have hh := hp.1; unfold curvature; positivity)
    (slope_pos hm p.R p.ε hp.2.2.1 hp.2.2.2.1) (spacing_pos hm p.R hp.2.2.1).le

variable (p : Params) (hp : spec.valid p) (m : ℕ) (hm : 0 < m)

include hp hm

lemma seed_radius : (seed p hp m hm).r ≤ p.R / 16 :=
  GapBoundedSmoothParameters.radius hm p.R _ hp.2.2.1 le_rfl

lemma seed_origin_gap : (seed p hp m hm).f 0 ≤ p.Δ := by
  have h0 := hp.1
  have hL : 0 < curvature p := by unfold curvature; positivity
  have hε := hp.2.2.2.1
  have hh := GapBoundedSmoothMollification.origin_gap (bump p hp m hm) (curvature p)
    (slope m p.R p.ε) (spacing m p.R) hL (slope_pos hm p.R p.ε hp.2.2.1 hε)
    (spacing_pos hm p.R hp.2.2.1).le
  have hcal := initial_gap hm p.R p.ε (bump p hp m hm).rOut hp.2.2.1 hε le_rfl
  have hΔ := hp.2.2.2.2.2.1
  exact hh.trans (hcal.trans (by linarith))

lemma separation (hbound : 819200000 * (m : ℝ) ^ 2 * p.ε ≤ p.L0 * p.R ^ 2) :
    4 * slope m p.R p.ε ≤ curvature p * spacing m p.R :=
  GapBoundedSmoothParameters.separation hm p.L0 p.R p.ε hp.2.2.1 hbound

lemma seed_hidden_gap (hbound : 819200000 * (m : ℝ) ^ 2 * p.ε ≤ p.L0 * p.R ^ 2)
    (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) (hx : -threshold p m ≤ x i) :
    3 * p.ε ≤ (seed p hp m hm).f x := by
  have hL : 0 < curvature p := by have hh := hp.1; unfold curvature; positivity
  have hG := slope_pos hm p.R p.ε hp.2.2.1 hp.2.2.2.1
  have hb := spacing_pos hm p.R hp.2.2.1
  have hh := GapBoundedSmoothMollification.hidden_gap (bump p hp m hm) (curvature p)
    (slope m p.R p.ε) (spacing m p.R) (threshold p m) hL hG hb.le x i hx
  apply le_trans _ hh
  exact GapBoundedSmoothParameters.hidden_gap hm (curvature p) p.R p.ε _ hL hp.2.2.1
    hp.2.2.2.1 le_rfl (separation p hp m hm hbound)

lemma seed_curvature (x : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ (seed p hp m hm).g x‖ ≤ curvature p := by
  dsimp only [seed, GapBoundedSmoothMollification.seed]
  exact SmoothConvexMollification.average_curvature (bump p hp m hm) _ (curvature p)
    (by have hh := hp.1; unfold curvature; positivity)
    (GapBoundedSmoothChain.field_lipschitz (curvature p) (slope m p.R p.ε) (spacing m p.R)
      (by have hh := hp.1; unfold curvature; positivity)
      (slope_pos hm p.R p.ε hp.2.2.1 hp.2.2.2.1)) x

lemma coefficient_pos : 0 < coefficient p m := by
  have hG := slope_pos hm p.R p.ε hp.2.2.1 hp.2.2.2.1
  have hR := hp.2.2.1
  have h0 := hp.1
  unfold coefficient curvature
  positivity

omit hm in
lemma coefficient_tuning : coefficient p m * p.R = slope m p.R p.ε + curvature p * p.R := by
  have hR := hp.2.2.1.ne'
  unfold coefficient
  field_simp

lemma localized_curvature (hbound : 819200000 * (m : ℝ) ^ 2 * p.ε ≤ p.L0 * p.R ^ 2)
    (π : Fin m ↪ Fin p.d) (x : EuclideanSpace ℝ (Fin p.d)) :
    ‖fderiv ℝ (AdaptivePolynomialLocalization.field (GapLocalizedChain.liftSeed (seed p hp m hm) π).f
      (GapLocalizedChain.liftSeed (seed p hp m hm) π).g 2 (coefficient p m) p.R
      (coefficient p m * p.R ^ 2)) x‖ ≤ p.L0 := by
  let s := GapLocalizedChain.liftSeed (seed p hp m hm) π
  have hL : 0 < curvature p := by have hh := hp.1; unfold curvature; positivity
  have hr : 2 * s.r ≤ p.R := by
    have hh := seed_radius p hp m hm
    change 2 * (seed p hp m hm).r ≤ p.R
    have hR := hp.2.2.1
    linarith
  have hGa : s.G ≤ coefficient p m * p.R := by
    rw [coefficient_tuning p hp m]
    change slope m p.R p.ε ≤ _
    have hh : 0 ≤ curvature p * p.R := mul_nonneg hL.le hp.2.2.1.le
    linarith
  have hcurv : ∀ y, ‖fderiv ℝ s.g y‖ ≤ curvature p := by
    intro y
    dsimp only [s, GapLocalizedChain.liftSeed]
    have hh := GeneralizedSmoothCoordinateEmbedding.composed_curvature π (seed p hp m hm).g
      (seed p hp m hm).differentiable (curvature p) 0
      (fun z => by simpa only [zero_mul, add_zero] using seed_curvature p hp m hm z) y
    simpa only [zero_mul, add_zero] using hh
  have hh := GapBoundedSmoothLocalization.localized_curvature s (curvature p) (coefficient p m) p.R
    hL.le (coefficient_pos p hp m hm) hp.2.2.1 hr hGa hcurv x
  apply hh.trans
  have ht := localized_curvature_budget hm (curvature p) p.R p.ε hL hp.2.2.1
    (separation p hp m hm hbound)
  simpa only [coefficient, curvature, mul_div_cancel₀ _ (by norm_num : (10000 : ℝ) ≠ 0)] using ht

lemma threshold_pos : 0 < threshold p m := by
  have hb := spacing_pos hm p.R hp.2.2.1
  unfold threshold
  positivity

lemma smoothing_margin : threshold p m + (bump p hp m hm).rOut ≤ spacing m p.R / 3 := by
  have hb := spacing_pos hm p.R hp.2.2.1
  change spacing m p.R / 4 + spacing m p.R / 128 ≤ spacing m p.R / 3
  linarith

lemma separation_valid (hbound : 819200000 * (m : ℝ) ^ 2 * p.ε ≤ p.L0 * p.R ^ 2) :
    slope m p.R p.ε / curvature p + 2 * (spacing m p.R / 3) < spacing m p.R := by
  have hL : 0 < curvature p := by have hh := hp.1; unfold curvature; positivity
  have hb := spacing_pos hm p.R hp.2.2.1
  have hsep := separation p hp m hm hbound
  have hh : slope m p.R p.ε / curvature p ≤ spacing m p.R / 4 := by
    apply (div_le_iff₀ hL).mpr
    linarith
  linarith

lemma seed_prefix (hbound : 819200000 * (m : ℝ) ^ 2 * p.ε ≤ p.L0 * p.R ^ 2)
    (j : Fin m) (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -threshold p m ≤ x j) (hxt : ∀ i, j < i → x i ≤ threshold p m)
    (hyt : ∀ i, j < i → y i ≤ threshold p m) :
    (seed p hp m hm).g x = (seed p hp m hm).g y ∧ (seed p hp m hm).f x = (seed p hp m hm).f y := by
  have hL : 0 < curvature p := by have hh := hp.1; unfold curvature; positivity
  have hG := slope_pos hm p.R p.ε hp.2.2.1 hp.2.2.2.1
  have hb := spacing_pos hm p.R hp.2.2.1
  have hpre := GapChainPrefix.smooth_prefix (curvature p) (slope m p.R p.ε) (spacing m p.R)
    (spacing m p.R / 3) hL hG hb.le (separation_valid p hp m hm hbound) j
  dsimp only [seed, GapBoundedSmoothMollification.seed]
  constructor
  · exact GapChainPrefix.average_prefix (bump p hp m hm) _ (spacing m p.R / 3) (threshold p m)
      (smoothing_margin p hp m hm) j (fun u v huv hu hut hvt => (hpre u v huv hu hut hvt).1)
      x y hxy hxj hxt hyt
  · exact GapChainPrefix.average_prefix (bump p hp m hm) _ (spacing m p.R / 3) (threshold p m)
      (smoothing_margin p hp m hm) j (fun u v huv hu hut hvt => (hpre u v huv hu hut hvt).2)
      x y hxy hxj hxt hyt

lemma seed_tail (hbound : 819200000 * (m : ℝ) ^ 2 * p.ε ≤ p.L0 * p.R ^ 2)
    (j i : Fin m) (hji : j < i) (x : EuclideanSpace ℝ (Fin m))
    (hxj : -threshold p m ≤ x j) (hxi : x i ≤ threshold p m) : (seed p hp m hm).g x i = 0 := by
  have hL : 0 < curvature p := by have hh := hp.1; unfold curvature; positivity
  have hG := slope_pos hm p.R p.ε hp.2.2.1 hp.2.2.2.1
  have hb := spacing_pos hm p.R hp.2.2.1
  dsimp only [seed, GapBoundedSmoothMollification.seed]
  apply GapChainPrefix.average_tail (bump p hp m hm)
    (GapBoundedSmoothChain.field (curvature p) (slope m p.R p.ε) (spacing m p.R))
    (SmoothConvexMollification.field_continuous _ (curvature p)
      (GapBoundedSmoothChain.field_lipschitz (curvature p) (slope m p.R p.ε) (spacing m p.R) hL hG))
    (spacing m p.R / 3) (threshold p m) (smoothing_margin p hp m hm) j i _ x hxj hxi
  intro y hyj hyi
  exact GapBoundedSmoothChain.field_tail_zero (curvature p) (slope m p.R p.ε) (spacing m p.R)
    (spacing m p.R / 3) hL hG hb.le (separation_valid p hp m hm hbound) y j i hji hyj hyi

lemma seed_truncated (hbound : 819200000 * (m : ℝ) ^ 2 * p.ε ≤ p.L0 * p.R ^ 2)
    (j : Fin m) (x : EuclideanSpace ℝ (Fin m)) (hx : ∀ i, j ≤ i → |x i| ≤ threshold p m) :
    (seed p hp m hm).f (GeneralizedSmoothChainPrefix.truncate j.val x) = (seed p hp m hm).f x ∧
    GeneralizedSmoothChainPrefix.truncate j.val ((seed p hp m hm).g (GeneralizedSmoothChainPrefix.truncate j.val x)) =
      (seed p hp m hm).g x := by
  apply GapChainPrefix.truncated_pair _ _ (threshold p m) (threshold_pos p hp m hm).le j
    (seed_prefix p hp m hm hbound j) _ x hx
  intro y i hi hyj hyi
  exact seed_tail p hp m hm hbound j i hi y hyj hyi

end LongTails.Proofs.GapSmoothInstance
