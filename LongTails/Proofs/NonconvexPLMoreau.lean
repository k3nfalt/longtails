import LongTails.Proofs.NonconvexPLPath

open Set InnerProductSpace Finset
open scoped RealInnerProductSpace
open LongTails.Setups.StochasticTwoSidedPL
open LongTails.Setups.StochasticNonconvexPL

namespace OracleTemplate.NonconvexPL

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μy : ℝ}

lemma Hyp.isProxPoint_xbar [ProperSpace E] (H : Hyp f gx gy L μy) (z : E) :
    IsProxPoint f L z (xbar f L z) := fun x' => H.xbar_min z x'

lemma Hyp.prox_unique [ProperSpace E] (H : Hyp f gx gy L μy) {z x : E}
    (hx : IsProxPoint f L z x) : x = xbar f L z := by
  have h1 := H.envelope_strong z x
  have h2 := hx (xbar f L z)
  have hL := H.hL
  have h3 : L / 4 * ‖x - xbar f L z‖ ^ 2 ≤ 0 := by
    simp only [envelope, phat] at h1
    linarith
  have h4 : ‖x - xbar f L z‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖x - xbar f L z‖]
  have h5 : ‖x - xbar f L z‖ = 0 := by nlinarith [norm_nonneg (x - xbar f L z)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h5)

lemma Hyp.moreauResidual_eq [ProperSpace E] (H : Hyp f gx gy L μy) (z : E) :
    moreauResidual f L z = 2 * L * ‖z - xbar f L z‖ := by
  have hset : {x | IsProxPoint f L z x} = {xbar f L z} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨H.isProxPoint_xbar z, fun x hx => H.prox_unique hx⟩
  rw [moreauResidual, hset, Metric.infDist_singleton, dist_eq_norm]

lemma Hyp.xbar_lip [ProperSpace E] (H : Hyp f gx gy L μy) (z z' : E) :
    ‖xbar f L z - xbar f L z'‖ ≤ 4 * ‖z - z'‖ := by
  set a := xbar f L z
  set b := xbar f L z'
  have hL := H.hL
  have h1 := H.envelope_strong z b
  have h2 := H.envelope_strong z' a
  simp only [envelope, phat] at h1 h2
  have hn : ‖a - b‖ = ‖b - a‖ := norm_sub_rev _ _
  have e1 : ‖a - z‖ ^ 2 - ‖a - z'‖ ^ 2 + (‖b - z'‖ ^ 2 - ‖b - z‖ ^ 2) = -2 * ⟪a - b, z - z'⟫ := by
    have ea : ‖a - z‖ ^ 2 - ‖a - z'‖ ^ 2 = -2 * ⟪a, z - z'⟫ + (‖z‖ ^ 2 - ‖z'‖ ^ 2) := by
      rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]; ring
    have eb : ‖b - z'‖ ^ 2 - ‖b - z‖ ^ 2 = 2 * ⟪b, z - z'⟫ - (‖z‖ ^ 2 - ‖z'‖ ^ 2) := by
      rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]; ring
    rw [ea, eb, inner_sub_left]; ring
  have hc : ⟪a - b, z - z'⟫ ≤ ‖a - b‖ * ‖z - z'‖ := real_inner_le_norm _ _
  have key : L / 2 * ‖a - b‖ ^ 2 ≤ 2 * L * (‖a - b‖ * ‖z - z'‖) := by
    rw [← hn] at h1
    nlinarith
  by_cases hd : ‖a - b‖ = 0
  · rw [hd]; positivity
  · have hd' : 0 < ‖a - b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    have : L / 2 * ‖a - b‖ ≤ L / 2 * (4 * ‖z - z'‖) := by nlinarith
    exact le_of_mul_le_mul_left this (by positivity)

lemma Hyp.continuous_xbar [ProperSpace E] (H : Hyp f gx gy L μy) :
    Continuous fun z : E => xbar f L z := by
  have : LipschitzWith (Real.toNNReal 4) (fun z : E => xbar f L z) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by norm_num)]
      exact H.xbar_lip a b
  exact this.continuous

lemma Hyp.continuous_moreauResidual [ProperSpace E] (H : Hyp f gx gy L μy) :
    Continuous fun z : E => moreauResidual f L z := by
  have e : (fun z : E => moreauResidual f L z) = fun z => 2 * L * ‖z - xbar f L z‖ := by
    funext z
    exact H.moreauResidual_eq z
  rw [e]
  exact continuous_const.mul (continuous_id.sub H.continuous_xbar).norm

lemma Hyp.moreauResidual_nonneg [ProperSpace E] (H : Hyp f gx gy L μy) (z : E) :
    0 ≤ moreauResidual f L z := by
  rw [H.moreauResidual_eq z]
  have := H.hL
  positivity

lemma Hyp.moreauResidual_le [ProperSpace E] (H : Hyp f gx gy L μy) (z : E) :
    moreauResidual f L z ≤ 2 * L * ‖xbar f L 0‖ + 10 * L * ‖z‖ := by
  rw [H.moreauResidual_eq z]
  have hL := H.hL
  have h1 := H.xbar_lip z 0
  rw [sub_zero] at h1
  have h2 : ‖z - xbar f L z‖ ≤ ‖z‖ + ‖xbar f L z‖ := norm_sub_le _ _
  have h3 : ‖xbar f L z‖ ≤ ‖xbar f L 0‖ + ‖xbar f L z - xbar f L 0‖ := norm_le_insert' _ _
  nlinarith

lemma moreau_scalar {L τ μy a h q k n1 : ℝ} (hL : 0 < L) (hτ : 0 < τ) (hμ : 0 < μy)
    (hμL : μy ≤ L) (ha : 0 ≤ a)
    (h1 : L * a ≤ L * k + (4 / 3 * h + L * τ * n1) + L * q) :
    μy * τ * (2 * L * a) ^ 2 ≤
      2 ^ 19 * L * (τ / 3 * h ^ 2 + τ / 64 * (μy / (2 * L) * (L * q) ^ 2) +
        L * τ * μy / 24576 * k ^ 2) + 24 * L ^ 2 * τ ^ 3 * μy * n1 ^ 2 := by
  have hLa : 0 ≤ L * a := by positivity
  have hsq := mul_self_le_mul_self hLa h1
  have hb : (L * k + (4 / 3 * h + L * τ * n1) + L * q) * (L * k + (4 / 3 * h + L * τ * n1) + L * q) ≤
      3 * (L * k) ^ 2 + 3 * (2 * (16 / 9 * h ^ 2) + 2 * (L * τ * n1) ^ 2) + 3 * (L * q) ^ 2 := by
    nlinarith [sq_nonneg (L * k - (4 / 3 * h + L * τ * n1)), sq_nonneg (L * k - L * q),
      sq_nonneg (4 / 3 * h + L * τ * n1 - L * q), sq_nonneg (4 / 3 * h - L * τ * n1)]
  have hmain : (2 * L * a) ^ 2 ≤ 12 * (L * k) ^ 2 + 128 / 3 * h ^ 2 + 24 * (L * τ * n1) ^ 2 +
      12 * (L * q) ^ 2 := by nlinarith
  have hμτ : 0 < μy * τ := by positivity
  have h2 := mul_le_mul_of_nonneg_left hmain hμτ.le
  have t1 : μy * τ * (12 * (L * k) ^ 2) ≤ 2 ^ 19 * L * (L * τ * μy / 24576 * k ^ 2) := by
    have : 0 ≤ L ^ 2 * τ * μy * k ^ 2 := by positivity
    nlinarith
  have t2 : μy * τ * (128 / 3 * h ^ 2) ≤ 2 ^ 19 * L * (τ / 3 * h ^ 2) := by
    have h0 : 0 ≤ τ * h ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hμL h0]
  have t3 : μy * τ * (12 * (L * q) ^ 2) ≤ 2 ^ 19 * L * (τ / 64 * (μy / (2 * L) * (L * q) ^ 2)) := by
    have e : 2 ^ 19 * L * (τ / 64 * (μy / (2 * L) * (L * q) ^ 2)) = 4096 * (μy * τ * (L * q) ^ 2) := by
      field_simp
      ring
    rw [e]
    have : 0 ≤ μy * τ * (L * q) ^ 2 := by positivity
    nlinarith
  have t4 : μy * τ * (24 * (L * τ * n1) ^ 2) = 24 * L ^ 2 * τ ^ 3 * μy * n1 ^ 2 := by ring
  nlinarith

lemma Hyp.moreau_step [ProperSpace E] (H : Hyp f gx gy L μy) {τ : ℝ} (hτ : 0 < τ)
    (hs : 3 * L * τ ≤ 1) (x z e1 x' : E) (y : F) (hx' : x' = x - τ • (xgrad gx L z x y + e1)) :
    μy * τ * moreauResidual f L z ^ 2 ≤
      2 ^ 19 * L * (τ / 3 * ‖xgrad gx L z x y‖ ^ 2 + τ / 64 * ‖gy (xhat f L y z) y‖ ^ 2 +
        L * τ * μy / 24576 * ‖x' - z‖ ^ 2) + 24 * L ^ 2 * τ ^ 3 * μy * ‖e1‖ ^ 2 := by
  have hL := H.hL
  have hμ := H.hμy
  rw [H.moreauResidual_eq z]
  have hdn := H.dist_next hτ hs x z e1 x' y hx'
  have hxx := H.xhat_sub_xbar y z
  have htri : ‖z - xbar f L z‖ ≤ ‖x' - z‖ + ‖xhat f L y z - x'‖ + ‖xhat f L y z - xbar f L z‖ := by
    have e : z - xbar f L z = -(x' - z) + -(xhat f L y z - x') + (xhat f L y z - xbar f L z) := by
      abel
    rw [e]
    have := norm_add₃_le (a := -(x' - z)) (b := -(xhat f L y z - x'))
      (c := xhat f L y z - xbar f L z)
    simpa only [norm_neg] using this
  have h1 : L * ‖z - xbar f L z‖ ≤ L * ‖x' - z‖ + (4 / 3 * ‖xgrad gx L z x y‖ + L * τ * ‖e1‖) +
      L * ‖xhat f L y z - xbar f L z‖ := by
    have := mul_le_mul_of_nonneg_left htri hL.le
    linarith
  have hsc := moreau_scalar hL hτ hμ H.hμyL (norm_nonneg (z - xbar f L z)) h1
  have hq : μy / (2 * L) * (L * ‖xhat f L y z - xbar f L z‖) ^ 2 ≤ ‖gy (xhat f L y z) y‖ ^ 2 := by
    have e : μy / (2 * L) * (L * ‖xhat f L y z - xbar f L z‖) ^ 2 =
        (L * μy * ‖xhat f L y z - xbar f L z‖ ^ 2) / 2 := by
      field_simp
    rw [e]
    linarith
  have hmono : 2 ^ 19 * L * (τ / 64 * (μy / (2 * L) * (L * ‖xhat f L y z - xbar f L z‖) ^ 2)) ≤
      2 ^ 19 * L * (τ / 64 * ‖gy (xhat f L y z) y‖ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  linarith

lemma Hyp.moreau_sum [ProperSpace E] (H : Hyp f gx gy L μy) {τ : ℝ} (hτ : 0 < τ)
    (hs : 3 * L * τ ≤ 1) (s : ℕ → E × F × E) (e1 : ℕ → E) (e2 : ℕ → F)
    (hrec : ∀ t, s (t + 1) = nextState gx gy L μy τ (s t) (e1 t) (e2 t)) (T : ℕ) :
    ∑ t ∈ range T, μy * τ * moreauResidual f L (s t).2.2 ^ 2 ≤
      2 ^ 19 * L * ((statePotential f L (s 0) - minimaxValue f) +
        ∑ t ∈ range T, (2 * L * τ ^ 2 * (‖e1 t‖ ^ 2 + ‖e2 t‖ ^ 2) -
          martingale f gx gy L τ (s t) (s (t + 1)).1 (e1 t) (e2 t))) +
      ∑ t ∈ range T, 24 * L ^ 2 * τ ^ 3 * μy * ‖e1 t‖ ^ 2 := by
  have hL := H.hL
  have hx' : ∀ t, (s (t + 1)).1 = (s t).1 - τ • (xgrad gx L (s t).2.2 (s t).1 (s t).2.1 + e1 t) := by
    intro t; rw [hrec t]; rfl
  have hstep : ∀ t, decrease f gx gy L μy τ (s t) (s (t + 1)) ≤
      statePotential f L (s t) - statePotential f L (s (t + 1)) +
        (2 * L * τ ^ 2 * (‖e1 t‖ ^ 2 + ‖e2 t‖ ^ 2) -
          martingale f gx gy L τ (s t) (s (t + 1)).1 (e1 t) (e2 t)) := by
    intro t
    have h := H.step hτ hs (s t).1 (s t).2.2 (e1 t) (s (t + 1)).1 (s (t + 1)).2.2 (s t).2.1 (e2 t)
      (s (t + 1)).2.1 (hx' t) (by rw [hrec t]; rfl) (by rw [hrec t]; rfl)
    simp only [decrease, martingale, statePotential]
    linarith
  have hm : ∀ t, μy * τ * moreauResidual f L (s t).2.2 ^ 2 ≤
      2 ^ 19 * L * decrease f gx gy L μy τ (s t) (s (t + 1)) +
        24 * L ^ 2 * τ ^ 3 * μy * ‖e1 t‖ ^ 2 := by
    intro t
    have h := H.moreau_step hτ hs (s t).1 (s t).2.2 (e1 t) (s (t + 1)).1 (s t).2.1 (hx' t)
    simpa only [decrease] using h
  have htel : ∀ T : ℕ, ∑ t ∈ range T, decrease f gx gy L μy τ (s t) (s (t + 1)) ≤
      statePotential f L (s 0) - statePotential f L (s T) +
        ∑ t ∈ range T, (2 * L * τ ^ 2 * (‖e1 t‖ ^ 2 + ‖e2 t‖ ^ 2) -
          martingale f gx gy L τ (s t) (s (t + 1)).1 (e1 t) (e2 t)) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [sum_range_succ, sum_range_succ]
      linarith [hstep T]
  have hlow : minimaxValue f ≤ statePotential f L (s T) := H.minimax_le_potential _ _ _
  have hsum : ∑ t ∈ range T, μy * τ * moreauResidual f L (s t).2.2 ^ 2 ≤
      2 ^ 19 * L * ∑ t ∈ range T, decrease f gx gy L μy τ (s t) (s (t + 1)) +
        ∑ t ∈ range T, 24 * L ^ 2 * τ ^ 3 * μy * ‖e1 t‖ ^ 2 := by
    calc _ ≤ ∑ t ∈ range T, (2 ^ 19 * L * decrease f gx gy L μy τ (s t) (s (t + 1)) +
          24 * L ^ 2 * τ ^ 3 * μy * ‖e1 t‖ ^ 2) := sum_le_sum (fun t _ => hm t)
      _ = _ := by rw [sum_add_distrib, mul_sum]
  have h2 := mul_le_mul_of_nonneg_left (htel T) (by positivity : (0 : ℝ) ≤ 2 ^ 19 * L)
  have h3 : 2 ^ 19 * L * (statePotential f L (s 0) - statePotential f L (s T) +
      ∑ t ∈ range T, (2 * L * τ ^ 2 * (‖e1 t‖ ^ 2 + ‖e2 t‖ ^ 2) -
        martingale f gx gy L τ (s t) (s (t + 1)).1 (e1 t) (e2 t))) ≤
      2 ^ 19 * L * ((statePotential f L (s 0) - minimaxValue f) +
        ∑ t ∈ range T, (2 * L * τ ^ 2 * (‖e1 t‖ ^ 2 + ‖e2 t‖ ^ 2) -
          martingale f gx gy L τ (s t) (s (t + 1)).1 (e1 t) (e2 t))) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  linarith

end OracleTemplate.NonconvexPL
