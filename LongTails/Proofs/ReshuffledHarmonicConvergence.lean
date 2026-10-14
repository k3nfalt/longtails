import LongTails.Proofs.ReshuffledTrajectorySums
import LongTails.Proofs.ReshuffledHarmonicRate

set_option autoImplicit false

open Finset

namespace OracleTemplate.ReshuffledHarmonicConvergence

open ReshuffledConvex ReshuffledTrajectory ReshuffledHarmonic ReshuffledWeighted
open LongTails.Setups.ReshuffledSmoothConvex
  ReshuffledHarmonicRate ReshuffledAnchorMoments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {n K : ℕ} [NeZero n]

lemma centered_total {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℝ) (x0 : E) (hK : 0 < K) (hη : 0 < η) (hstep : η * Lmax * H n ≤ 1 / 40) :
    let X := (path g η x0 : Orders n K → ℕ → E)
    let v := previous (weight (n * K))
    (∑ t ∈ range (n * K), v t * centered f g X xstar t) ≤
      2 * (∑ t ∈ range (n * K), v t * risk f X xstar t) +
        4 * η * H n * (Fintype.card (Orders n K) * σ ^ 2) * ∑ t ∈ range (n * K), v t := by
  dsimp only
  have hn := one_le_H (NeZero.pos n)
  have hsmall : η * Lmax ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hn (mul_nonneg hη.le h.lmax_pos.le)
    nlinarith
  apply centered_weighted (NeZero.pos n) _ _ _ _ hη.le h.lmax_pos.le hn hstep
    (fun t ht => previous_nonneg ht) (fun t ht => centered_nonneg h _ t)
  · intro t ht
    exact reverse_bias h η x0 hη hsmall ht
  · intro t ht
    simpa only [mul_assoc] using moment_bound h (path g η x0 : Orders n K → ℕ → E) ht
  · exact history_previous (NeZero.pos n) hK _ (fun t ht => moment_nonneg _ _ t)

lemma anchor_total {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℝ) (x0 : E) (hK : 0 < K) (hη : 0 < η) (hstep : η * Lmax * H n ≤ 1 / 40) :
    let X := (path g η x0 : Orders n K → ℕ → E)
    let w := weight (n * K)
    (∑ t ∈ range (n * K), w t * moment g (anchors w X xstar) t) ≤
      12 * Lmax * (∑ t ∈ range (n * K), previous w t * risk f X xstar t) +
        3 * (Fintype.card (Orders n K) * σ ^ 2) * ∑ t ∈ range (n * K), w t := by
  dsimp only
  have hT := Nat.mul_pos (NeZero.pos n) hK
  apply summed_anchor_moment hT _ _ _ h.lmax_pos.le
    (by positivity) hstep (fun t ht => centered_nonneg h _ t) (fun t ht => risk_nonneg h _ t)
    (centered_total h η x0 hK hη hstep)
  have hs := sum_le_sum (s := range (n * K)) (fun t ht =>
    anchor_moment h η x0 (weight (n * K)) (mem_range.mp ht)
      (fun u hu => weight_pos (by have := mem_range.mp ht; omega))
      (fun u hu => weight_mono (by have := mem_range.mp ht; omega)))
  simp only [sum_add_distrib, ← mul_sum] at hs
  rw [sum_prefixes] at hs
  simpa only [mul_assoc] using hs

omit [CompleteSpace E] in
lemma distance_total (η : ℝ) (g : Fin n → E → E) (x0 xstar : E) (hK : 0 < K)
    {D : ℝ} (hx0 : ‖x0 - xstar‖ ≤ D) :
    let X := (path g η x0 : Orders n K → ℕ → E)
    let w := weight (n * K)
    let Z := anchors w X xstar
    (∑ t ∈ range (n * K), w t * (distance X Z t - nextDistance X Z t)) ≤
      w 0 * (Fintype.card (Orders n K) * D ^ 2) := by
  dsimp only
  have hT := Nat.mul_pos (NeZero.pos n) hK
  have hs := distance_sum_telescope (weight (n * K))
    (path g η x0 : Orders n K → ℕ → E) xstar hT
    (fun t ht => weight_pos ht) (fun t ht => weight_mono ht)
  have hd := pow_le_pow_left₀ (norm_nonneg _) hx0 2
  have hc := mul_le_mul_of_nonneg_left hd
    (Nat.cast_nonneg (Fintype.card (Orders n K)) : (0 : ℝ) ≤ _)
  have hc' := mul_le_mul_of_nonneg_left hc (weight_pos hT).le
  simp only [path, iterate, sum_const, card_univ, nsmul_eq_mul] at hs
  exact hs.trans hc'

omit [NeZero n] in
lemma objective_total {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (X : Orders n K → ℕ → E) :
    let w := weight (n * K)
    (∑ t ∈ range (n * K), w t * risk f (anchors w X xstar) xstar t) ≤
      ∑ t ∈ range (n * K), (n * K - (t + 1) : ℕ) *
        (w (t + 1) - w t) * risk f X xstar (t + 1) := by
  dsimp only
  have hc : ConvexOn ℝ Set.univ (fun x => LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := (FiniteSum.objective_convex h.convex).2 hx hy ha hb hab
    change LongTails.Setups.FiniteSumSmoothAndConvex.objective f (a • x + b • y) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar ≤
      a * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f x - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) +
        b * (LongTails.Setups.FiniteSumSmoothAndConvex.objective f y - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)
    change LongTails.Setups.FiniteSumSmoothAndConvex.objective f (a • x + b • y) ≤
      a * LongTails.Setups.FiniteSumSmoothAndConvex.objective f x + b * LongTails.Setups.FiniteSumSmoothAndConvex.objective f y at hh
    linear_combination hh + (LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) * hab
  exact objective_sum_anchor hc (weight (n * K)) X xstar (sub_self _) (n * K)
    (fun t ht => weight_pos ht) (fun t ht => weight_mono ht)

set_option maxHeartbeats 1600000 in
lemma sum_gap {f : Fin n → E → ℝ} {g : Fin n → E → E} {ℓ : Fin n → ℝ}
    {Lavg Lmax σ : ℝ} {xstar : E} (h : Hyp f g ℓ Lavg Lmax σ xstar)
    (η : ℝ) (x0 : E) (hK : 0 < K) (hη : 0 < η) {D : ℝ}
    (hx0 : ‖x0 - xstar‖ ≤ D) (hstep : η * Lmax * H n * H (n * K) ≤ 1 / 536) :
    risk f (path g η x0 : Orders n K → ℕ → E) xstar (n * K) ≤
      2 * (Fintype.card (Orders n K) * D ^ 2) / (η * (n * K : ℕ)) +
        66 * η * H n * H (n * K) * (Fintype.card (Orders n K) * σ ^ 2) := by
  let T := n * K
  let w := weight T
  let v := previous w
  let X := (path g η x0 : Orders n K → ℕ → E)
  let Z := anchors w X xstar
  let R := risk f X xstar
  let A := centered f g X xstar
  let M := moment g X
  let N := moment g Z
  let B := bregman f g X Z
  let Φ := risk f Z xstar
  let D2 : ℝ := Fintype.card (Orders n K) * D ^ 2
  let V0 : ℝ := Fintype.card (Orders n K) * σ ^ 2
  let G := ∑ t ∈ range T, w t * (R (t + 1) - Φ t)
  have hn := NeZero.pos n
  have hT : 0 < T := Nat.mul_pos hn hK
  have hH := one_le_H hn
  have hHT := one_le_H hT
  have hsmall : η * Lmax * H n ≤ 1 / 40 := by
    have hh := mul_le_mul_of_nonneg_left hHT
      (show 0 ≤ η * Lmax * H n by have := h.lmax_pos; positivity [H_nonneg n])
    change 1 ≤ H (n * K) at hHT
    change η * Lmax * H n * 1 ≤ η * Lmax * H n * H (n * K) at hh
    nlinarith
  have hηL : η * Lmax ≤ 1 / 6 := by
    have hh := mul_le_mul_of_nonneg_left hH (mul_nonneg hη.le h.lmax_pos.le)
    nlinarith
  have hw : ∀ t, t < T → 0 < w t := fun t ht => weight_pos ht
  have hm : ∀ t, t + 1 < T → w t ≤ w (t + 1) := fun t ht => weight_mono ht
  have hR : ∀ t, 0 ≤ R t := fun t => risk_nonneg h X t
  have hM : ∀ t, 0 ≤ M t := fun t => moment_nonneg g X t
  have hN : ∀ t, 0 ≤ N t := fun t => moment_nonneg g Z t
  have hB : ∀ t, 0 ≤ B t := fun t => bregman_nonneg h X Z t
  have hv : ∀ t, t < T → 0 ≤ v t := fun t ht => previous_nonneg ht
  have hD2 : 0 ≤ D2 := by dsimp [D2]; positivity
  have hV0 : 0 ≤ V0 := by dsimp [V0]; positivity
  have hs : 2 * η * G ≤
      (∑ t ∈ range T, w t * (distance X Z t - nextDistance X Z t)) +
      (4 + η * Lmax) * η ^ 2 * (∑ t ∈ range T, w t * M t) +
      2 * η ^ 2 * (∑ t ∈ range T, w t * N t) +
      (14 / (3 * (n : ℝ))) * η ^ 2 * (∑ t ∈ range T, w t * history n M t) +
      2 * η ^ 2 * Lmax * (∑ t ∈ range T, w t * R t) -
      2 * η * (∑ t ∈ range T, w t * B t) := by
    have hp : ∀ t, t < T → 2 * η * (w t * (R (t + 1) - Φ t)) ≤
        w t * (distance X Z t - nextDistance X Z t) +
        ((4 + η * Lmax) * η ^ 2) * (w t * M t) +
        (2 * η ^ 2) * (w t * N t) +
        ((14 / (3 * (n : ℝ))) * η ^ 2) * (w t * history n M t) +
        (2 * η ^ 2 * Lmax) * (w t * R t) - (2 * η) * (w t * B t) := by
      intro t ht
      have hp := ReshuffledTrajectory.step h η x0 hη hηL w ht
        (fun u hu => hw u (by omega)) (fun u hu => hm u (by omega))
      change 2 * η * (R (t + 1) - Φ t) ≤ distance X Z t - nextDistance X Z t +
        (4 + η * Lmax) * η ^ 2 * M t + 2 * η ^ 2 * N t +
        (14 / (3 * (n : ℝ))) * η ^ 2 * history n M t +
        2 * η ^ 2 * Lmax * R t - 2 * η * B t at hp
      have hp' := mul_le_mul_of_nonneg_left hp (hw t ht).le
      nlinarith
    have hsum := sum_le_sum (s := range T) (fun t ht => hp t (mem_range.mp ht))
    simpa only [G, sum_add_distrib, sum_sub_distrib, ← mul_sum] using hsum
  have hd : (∑ t ∈ range T, w t * (distance X Z t - nextDistance X Z t)) ≤ w 0 * D2 :=
    distance_total η g x0 xstar hK hx0
  have hs' : 2 * η * G ≤ w 0 * D2 +
      (4 + η * Lmax) * η ^ 2 * (∑ t ∈ range T, w t * M t) +
      2 * η ^ 2 * (∑ t ∈ range T, w t * N t) +
      (14 / (3 * (n : ℝ))) * η ^ 2 * (∑ t ∈ range T, w t * history n M t) +
      2 * η ^ 2 * Lmax * (∑ t ∈ range T, w t * R t) -
      2 * η * (∑ t ∈ range T, w t * B t) := by linarith
  have hh : (∑ t ∈ range T, w t * history n M t) ≤
      n * H n * ∑ t ∈ range T, w t * M t :=
    weighted_history (H_nonneg T) hn le_rfl M (fun t ht => hM t)
  have hb : (∑ t ∈ range T, w t * M t) ≤
      4 * Lmax * (∑ t ∈ range T, w t * B t) + 2 * (∑ t ∈ range T, w t * N t) := by
    have hp : ∀ t, t < T → w t * M t ≤ 4 * Lmax * (w t * B t) + 2 * (w t * N t) := by
      intro t ht
      have hb := mul_le_mul_of_nonneg_left (bregman_transfer h X Z t) (hw t ht).le
      change w t * M t ≤ w t * (4 * Lmax * B t + 2 * N t) at hb
      nlinarith
    have hs := sum_le_sum (s := range T) (fun t ht => hp t (mem_range.mp ht))
    simpa only [sum_add_distrib, ← mul_sum] using hs
  have hr : (∑ t ∈ range T, w t * R t) ≤ 2 * (∑ t ∈ range T, v t * R t) := by
    rw [mul_sum]
    apply sum_le_sum
    intro t ht
    have hp := mul_le_mul_of_nonneg_right (weight_le_previous (mem_range.mp ht)) (hR t)
    nlinarith
  have ha : (∑ t ∈ range T, w t * N t) ≤
      12 * Lmax * (∑ t ∈ range T, v t * R t) + 3 * V0 * ∑ t ∈ range T, w t :=
    anchor_total h η x0 hK hη hsmall
  have hu := aggregate_step (ReshuffledConvex.card_pos' n) hη.le h.lmax_pos.le hH
    (sum_nonneg fun t ht => mul_nonneg (hw t (mem_range.mp ht)).le (hM t))
    (sum_nonneg fun t ht => mul_nonneg (hw t (mem_range.mp ht)).le (hN t))
    (sum_nonneg fun t ht => mul_nonneg (hw t (mem_range.mp ht)).le (hB t))
    (sum_nonneg fun t ht => mul_nonneg (hv t (mem_range.mp ht)) (hR t))
    hsmall hs' hh hb hr ha
  have hu' : η * G ≤ w 0 * D2 / 2 +
      134 * H n * η ^ 2 * Lmax * (w 0 * R 0 + ∑ t ∈ range (T - 1), w t * R (t + 1)) +
      33 * H n * η ^ 2 * V0 * ∑ t ∈ range T, w t := by
    simpa only [v, sum_previous hT] using hu
  have hp := weighted_progress_lower hT R Φ (fun t ht => hR t) (objective_total h X)
  have hi : R 0 ≤ Lmax * D2 / 2 := initial_risk h η x0 hx0
  have hf := terminal_absorption hη h.lmax_pos.le hH hHT (hw 0 hT).le hD2
    (sum_nonneg fun t ht => mul_nonneg (hw t (by have := mem_range.mp ht; omega)).le (hR (t + 1)))
    hstep hi hp hu'
  exact rate_extraction hT hη (H_nonneg n) hV0 (hR T) hf

end OracleTemplate.ReshuffledHarmonicConvergence
