import LongTails.Proofs.GapTransientParameters
import LongTails.Proofs.GapCalibratedMollification
import LongTails.Proofs.GapChainPrefix
import LongTails.Proofs.GapLocalizedChain

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.GapTransientChain

local instance pointMeasurableSpace (m : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin m)) :=
  WithLp.measurableSpace 2 (Fin m → ℝ)

open LongTails.Setups.GapGeneralizedSmoothConvex GapTransientParameters

noncomputable def weights (p : Params) (m : ℕ) : Fin m → ℝ :=
  GapCalibratedWeights.weight m (slope p m) (spacing p m)

noncomputable def amount (p : Params) (m : ℕ) : ℝ :=
  100 * logarithm p / ((p.L1 / 4) * spacing p m)

noncomputable def coordinateRadius (p : Params) (m : ℕ) : ℝ :=
  128 * logarithm p / ((p.L1 / 4) * spacing p m)

noncomputable def bump (p : Params) (hp : spec.valid p) (m : ℕ) (hm : 0 < m) (hq : 1 ≤ scale p) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin m)) where
  rIn := spacing p m / (64 * p.L1)
  rOut := spacing p m / (32 * p.L1)
  rIn_pos := threshold_pos p hp hm hq
  rIn_lt_rOut := by
    have h1 := L1_pos p hp hq
    have ht := spacing_pos p hp hm
    have he : spacing p m / (32 * p.L1) = 2 * (spacing p m / (64 * p.L1)) := by ring
    rw [he]
    have hh : 0 < spacing p m / (64 * p.L1) := by positivity
    linarith

variable (p : Params) (hp : spec.valid p) (m : ℕ) (hm : 0 < m) (hq : 1 ≤ scale p)

include hp hm hq

lemma slope_pos : 0 < slope p m := by
  have h1 := L1_pos p hp hq
  have hε := hp.2.2.2.1
  have ht := spacing_pos p hp hm
  have hw : 0 < logarithm p := by linarith [logarithm_ge_one p hp]
  unfold GapTransientParameters.slope
  positivity

lemma weights_pos (i : Fin m) : 0 < weights p m i :=
  GapCalibratedWeights.weight_pos m (slope p m) (spacing p m) (slope_pos p hp m hm hq) i

lemma weights_bounded (i : Fin m) : weights p m i ≤ peak p m :=
  GapCalibratedWeights.weight_le_peak m (slope p m) (spacing p m)
    (slope_pos p hp m hm hq).le (spacing_pos p hp hm).le i

lemma amount_pos : 0 < amount p m := by
  have h1 := L1_pos p hp hq
  have ht := spacing_pos p hp hm
  have hw : 0 < logarithm p := by linarith [logarithm_ge_one p hp]
  unfold amount
  positivity

lemma coordinateRadius_pos : 0 < coordinateRadius p m := by
  have h1 := L1_pos p hp hq
  have ht := spacing_pos p hp hm
  have hw : 0 < logarithm p := by linarith [logarithm_ge_one p hp]
  unfold coordinateRadius
  positivity

lemma bump_small : (bump p hp m hm hq).rOut ≤ logarithm p / ((p.L1 / 4) * spacing p m) := by
  have h1 := L1_pos p hp hq
  have ht := spacing_pos p hp hm
  have ht1 := spacing_le_one p hp hm
  have hw := logarithm_ge_one p hp
  change spacing p m / (32 * p.L1) ≤ logarithm p / ((p.L1 / 4) * spacing p m)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_left (show spacing p m ^ 2 ≤ 1 by nlinarith) h1.le
  have hw' := mul_le_mul_of_nonneg_left hw h1.le
  nlinarith only [hh, hw', h1]

lemma bump_curvature : (p.L1 / 4) * (bump p hp m hm hq).rOut ≤ 1 / 16 := by
  have h1 := L1_pos p hp hq
  have ht1 := spacing_le_one p hp hm
  have he : (p.L1 / 4) * (bump p hp m hm hq).rOut = spacing p m / 128 := by
    change (p.L1 / 4) * (spacing p m / (32 * p.L1)) = _
    field_simp
    ring
  rw [he]
  linarith

lemma center_bound (hmq : (m : ℝ) ≤ scale p) (i : Fin m) :
    |amount p m + GeneralizedSmoothHardTransfer.shiftCoordinate (p.L0 / 4) (p.L1 / 4)
      (peak p m) (weights p m) i + (bump p hp m hm hq).rOut| ≤ coordinateRadius p m := by
  have h0 := hp.1
  have h1 := L1_pos p hp hq
  have ht := spacing_pos p hp hm
  have hw : 0 < logarithm p := by linarith [logarithm_ge_one p hp]
  have hs := GapCalibratedParameters.total_shift_bound (p.L0 / 4) (p.L1 / 4) (slope p m)
    (spacing p m) (logarithm p) (by positivity) (slope_pos p hp m hm hq) ht
    (spacing_le_one p hp hm) (logarithm_ge_one p hp)
    (GapCalibratedParameters.spacing_bounds hm (gapLog p) (by linarith [gapLog_ge_half p hp])).2.1
    (peak_log p hp hm hq) (entropy_log p hm hmq) i
  have hn := GapCalibratedParameters.shift_nonnegative (p.L0 / 4) (p.L1 / 4) (peak p m)
    (by positivity) (by positivity) (peak_pos p hp hm hq).le (weights p m) (weights_pos p hp m hm hq) i
  have ha := (amount_pos p hp m hm hq).le
  have hρ := (bump p hp m hm hq).rOut_pos
  rw [abs_of_nonneg (by positivity)]
  have hb := bump_small p hp m hm hq
  change amount p m + GeneralizedSmoothHardTransfer.shiftCoordinate (p.L0 / 4) (p.L1 / 4)
    (peak p m) (weights p m) i ≤ 116 * logarithm p / ((p.L1 / 4) * spacing p m) at hs
  unfold amount coordinateRadius at *
  have hpos : 0 ≤ logarithm p / ((p.L1 / 4) * spacing p m) := by positivity
  simp only [div_eq_mul_inv] at hs hb hpos ⊢
  linarith

noncomputable def seed (hmq : (m : ℝ) ≤ scale p) :
    AdaptiveGeneralizedSmoothLocalization.Seed (E := EuclideanSpace ℝ (Fin m)) :=
  GapCalibratedMollification.seed hm (bump p hp m hm hq) (p.L0 / 4) (p.L1 / 4)
    (peak p m) (amount p m) (by have := hp.1; positivity) (by have := L1_pos p hp hq; positivity)
    (weights p m) (weights_pos p hp m hm hq) (peak_pos p hp hm hq).le
    (weights_bounded p hp m hm hq) (coordinateRadius p m) (coordinateRadius_pos p hp m hm hq)
    (bump_curvature p hp m hm hq) (center_bound p hp m hm hq hmq)

lemma seed_radius (hmq : (m : ℝ) ≤ scale p)
    (hlinear : 16384 * (m : ℝ) * logarithm p ≤ scale p)
    (hgap : 32768 * (m : ℝ) * Real.sqrt m * logarithm p ≤ scale p * gapLog p) :
    (seed p hp m hm hq hmq).r ≤ p.R / 32 := by
  have h1 := L1_pos p hp hq
  have hh := GapCalibratedParameters.calibrated_radius hm (p.L1 / 4) p.R (gapLog p)
    (logarithm p) (by positivity) hp.2.2.1 (by linarith [gapLog_ge_half p hp])
    (by dsimp [scale] at hlinear; nlinarith only [hlinear])
    (by dsimp [scale] at hgap; nlinarith only [hgap])
  exact hh

lemma seed_origin_gap (hmq : (m : ℝ) ≤ scale p) : (seed p hp m hm hq hmq).f 0 ≤ p.Δ := by
  have h0 := hp.1
  have h1 := L1_pos p hp hq
  have hε := hp.2.2.2.1
  have ht := spacing_pos p hp hm
  have hb := GapCalibratedParameters.spacing_bounds hm (gapLog p) (by linarith [gapLog_ge_half p hp])
  have horigin := GapCalibratedMollification.origin_gap hm (bump p hp m hm hq)
    (p.L0 / 4) (p.L1 / 4) (peak p m) (amount p m) (by positivity) (by positivity)
    (weights p m) (weights_pos p hp m hm hq) (peak_pos p hp hm hq).le (weights_bounded p hp m hm hq)
    (8 * p.ε * Real.exp ((m : ℝ) * spacing p m)) (by positivity) (fun i =>
      GapCalibratedParameters.smoothed_origin_score (p.L0 / 4) (p.L1 / 4) p.ε (spacing p m)
        (logarithm p) (bump p hp m hm hq).rOut (by positivity) hε ht hb.1
        (logarithm_ge_one p hp) (bump_small p hp m hm hq) hb.2.1
        (peak_log p hp hm hq) (entropy_log p hm hmq) i)
  apply horigin.trans
  exact GapCalibratedWeights.calibrated_gap p.ε p.Δ (spacing p m) m hε
    (by have hh := hp.2.2.2.2.2.1; linarith) hb.2.2

lemma seed_hidden_gap (hmq : (m : ℝ) ≤ scale p) (x : EuclideanSpace ℝ (Fin m))
    (i : Fin m) (hx : -threshold p m ≤ x i) : 4 * p.ε ≤ (seed p hp m hm hq hmq).f x := by
  have h0 := hp.1
  have h1 := L1_pos p hp hq
  have hε := hp.2.2.2.1
  have ht := spacing_pos p hp hm
  have ht1 := spacing_le_one p hp hm
  have hw : 0 < logarithm p := by linarith [logarithm_ge_one p hp]
  have hnoise : threshold p m + (bump p hp m hm hq).rOut ≤ 2 / (p.L1 / 4) := by
    change spacing p m / (64 * p.L1) + spacing p m / (32 * p.L1) ≤ 2 / (p.L1 / 4)
    apply (mul_le_mul_iff_of_pos_right h1).mp
    field_simp
    linarith
  have hscore := GapCalibratedParameters.hidden_score (p.L1 / 4) p.ε (spacing p m)
    (logarithm p) (threshold p m) (bump p hp m hm hq).rOut (by positivity) hε ht hw hnoise i
  exact hscore.trans (GapCalibratedMollification.hidden_gap hm (bump p hp m hm hq)
    (p.L0 / 4) (p.L1 / 4) (peak p m) (amount p m) (by positivity) (by positivity)
    (weights p m) (weights_pos p hp m hm hq) (peak_pos p hp hm hq).le (weights_bounded p hp m hm hq)
    (threshold p m) x i hx)

lemma weight_order (j i : Fin m) (hji : j < i) : weights p m i ≤ weights p m j := by
  have hh := GapCalibratedWeights.ratio_lower m (slope p m) (spacing p m)
    (slope_pos p hp m hm hq).le (spacing_pos p hp hm).le j i hji
  have hn := mul_nonneg (weights_pos p hp m hm hq i).le (spacing_pos p hp hm).le
  change weights p m i * (1 + spacing p m) ≤ weights p m j at hh
  nlinarith only [hh, hn]

lemma separation_margin (j i : Fin m) (hji : j < i) :
    spacing p m / (8 * (p.L1 / 4)) * (weights p m j + weights p m i) <
      2 * (weights p m j - weights p m i) / (p.L1 / 4) :=
  GapCalibratedWeights.margin m (slope p m) (spacing p m) (p.L1 / 4)
    (slope_pos p hp m hm hq) (spacing_pos p hp hm) (spacing_le_one p hp hm)
    (by have := L1_pos p hp hq; positivity) j i hji

lemma smoothing_margin : threshold p m + (bump p hp m hm hq).rOut ≤
    spacing p m / (8 * (p.L1 / 4)) := by
  have h1 := L1_pos p hp hq
  have ht := spacing_pos p hp hm
  change spacing p m / (64 * p.L1) + spacing p m / (32 * p.L1) ≤ spacing p m / (8 * (p.L1 / 4))
  apply (mul_le_mul_iff_of_pos_right h1).mp
  field_simp
  linarith

lemma seed_prefix (hmq : (m : ℝ) ≤ scale p) (j : Fin m)
    (x y : EuclideanSpace ℝ (Fin m)) (hxy : ∀ i, i ≤ j → x i = y i)
    (hxj : -threshold p m ≤ x j) (hxt : ∀ i, j < i → x i ≤ threshold p m)
    (hyt : ∀ i, j < i → y i ≤ threshold p m) :
    (seed p hp m hm hq hmq).g x = (seed p hp m hm hq hmq).g y ∧
      (seed p hp m hm hq hmq).f x = (seed p hp m hm hq hmq).f y := by
  have h0 := hp.1
  have h1 := L1_pos p hp hq
  have hpre := GapChainPrefix.generalized_prefix hm (p.L0 / 4) (p.L1 / 4) (peak p m) (amount p m)
    (spacing p m / (8 * (p.L1 / 4))) (by positivity) (by positivity) (weights p m)
    (weights_pos p hp m hm hq) (peak_pos p hp hm hq).le (weights_bounded p hp m hm hq)
    (amount_pos p hp m hm hq).le j (weight_order p hp m hm hq j) (separation_margin p hp m hm hq j)
  dsimp only [seed, GapCalibratedMollification.seed]
  constructor
  · exact GapChainPrefix.average_prefix (bump p hp m hm hq) _
      (spacing p m / (8 * (p.L1 / 4))) (threshold p m) (smoothing_margin p hp m hm hq) j
      (fun u v huv hu hut hvt => (hpre u v huv hu hut hvt).1) x y hxy hxj hxt hyt
  · exact GapChainPrefix.average_prefix (bump p hp m hm hq) _
      (spacing p m / (8 * (p.L1 / 4))) (threshold p m) (smoothing_margin p hp m hm hq) j
      (fun u v huv hu hut hvt => (hpre u v huv hu hut hvt).2) x y hxy hxj hxt hyt

lemma seed_tail (hmq : (m : ℝ) ≤ scale p) (j i : Fin m) (hji : j < i)
    (x : EuclideanSpace ℝ (Fin m)) (hxj : -threshold p m ≤ x j) (hxi : x i ≤ threshold p m) :
    (seed p hp m hm hq hmq).g x i = 0 := by
  have h0 := hp.1
  have h1 := L1_pos p hp hq
  dsimp only [seed, GapCalibratedMollification.seed]
  apply GapChainPrefix.average_tail (bump p hp m hm hq)
    (GapCalibratedConjugate.field (p.L0 / 4) (p.L1 / 4) (peak p m) (amount p m) (weights p m))
    (GapCalibratedMollification.field_continuous hm (p.L0 / 4) (p.L1 / 4) (peak p m) (amount p m)
      (by positivity) (by positivity) (weights p m) (weights_pos p hp m hm hq)
      (peak_pos p hp hm hq).le (weights_bounded p hp m hm hq))
    (spacing p m / (8 * (p.L1 / 4))) (threshold p m) (smoothing_margin p hp m hm hq) j i
    _ x hxj hxi
  intro y hyj hyi
  exact GapCalibratedConjugate.field_tail_zero hm (p.L0 / 4) (p.L1 / 4) (peak p m) (amount p m)
    (by positivity) (by positivity) (weights p m) (weights_pos p hp m hm hq)
    (peak_pos p hp hm hq).le (weights_bounded p hp m hm hq) (amount_pos p hp m hm hq).le
    _ j i hji (weight_order p hp m hm hq j i hji) y hyj hyi (separation_margin p hp m hm hq j i hji)

lemma seed_truncated (hmq : (m : ℝ) ≤ scale p) (j : Fin m) (x : EuclideanSpace ℝ (Fin m))
    (hx : ∀ i, j ≤ i → |x i| ≤ threshold p m) :
    (seed p hp m hm hq hmq).f (GeneralizedSmoothChainPrefix.truncate j.val x) =
      (seed p hp m hm hq hmq).f x ∧
    GeneralizedSmoothChainPrefix.truncate j.val
      ((seed p hp m hm hq hmq).g (GeneralizedSmoothChainPrefix.truncate j.val x)) =
        (seed p hp m hm hq hmq).g x := by
  apply GapChainPrefix.truncated_pair _ _ (threshold p m) (threshold_pos p hp hm hq).le j
    (seed_prefix p hp m hm hq hmq j) _ x hx
  intro y i hi hyj hyi
  exact seed_tail p hp m hm hq hmq j i hi y hyj hyi

end LongTails.Proofs.GapTransientChain
