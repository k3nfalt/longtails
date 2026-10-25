import LongTails.Proofs.AffineAdamTrajectory

open InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineAdamPath

open OracleTemplate LongTails.Setups.AffineHeavyTailedAdam
open LongTails.Algorithms.BatchedAdam AffineAdamTrajectory AffineAdamGeometry

variable {d : ℕ} (cfg : Config) (hb1 : cfg.β₁ = 9 / 10) (hb2 : cfg.β₂ = 999 / 1000)
    (hη : 0 ≤ cfg.η) (hδ : 0 < cfg.δ) (x0 : Point d) (k : ℕ) (z : ℕ → Point d)
    {f : Point d → ℝ} {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, L1 * maxNorm (y - x) ≤ 1 →
      sumNorm (gradient f y - gradient f x) ≤
        (L0 + L1 * sumNorm (gradient f x)) * maxNorm (y - x))
    (hstep : L1 * (80 * cfg.η) ≤ 1)

include hb1 hb2 hη hδ hL0 hL1 hg hlip hstep in
lemma single_step (t : ℕ) :
    let x := fun t => (trajectory cfg x0 k z t).point
    let g := fun t => gradient f (x t)
    f (x (t + 1)) ≤ f (x t) - cfg.η * sumNorm (g t) +
      cfg.η * (82 * momentumError cfg x0 k z g (t + 1) +
        normalizerError cfg x0 k z g (t + 1) + d * cfg.δ) +
      3200 * cfg.η ^ 2 * (L0 + L1 * sumNorm (g t)) := by
  dsimp only
  let x := fun t => (trajectory cfg x0 k z t).point
  let g := fun t => gradient f (x t)
  have hmove := maxNorm_move cfg hb1 hb2 hη hδ x0 k z t
  have hrad : L1 * maxNorm (x (t + 1) - x t) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hmove hL1).trans hstep
  have hd := local_descent hL1 hg hlip (x t) (x (t + 1) - x t) hrad
  rw [add_sub_cancel] at hd
  have halign := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    coordinate_alignment cfg hb1 hb2 hδ x0 k z t i (g t i))
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at halign
  have hi : ⟪g t, x (t + 1) - x t⟫ =
      -cfg.η * ∑ i, g t i * correctedM cfg x0 k z (t + 1) i /
        (Real.sqrt (correctedV cfg x0 k z (t + 1) i) + cfg.δ) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.sub_apply,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [x, trajectory, coreStep, Adam.direction, correctedM, correctedV,
      PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, trajectory_time]
    simp only [div_eq_mul_inv]
    ring
  have hcurv : 0 ≤ L0 + L1 * sumNorm (g t) :=
    add_nonneg hL0 (mul_nonneg hL1 (sumNorm_nonneg _))
  have hs := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (maxNorm_nonneg (x (t + 1) - x t)) hmove 2)
    (div_nonneg hcurv (by norm_num : (0 : ℝ) ≤ 2))
  have ha := mul_le_mul_of_nonneg_left halign hη
  change f (x (t + 1)) ≤ f (x t) - cfg.η * sumNorm (g t) +
    cfg.η * (82 * momentumError cfg x0 k z g (t + 1) +
      normalizerError cfg x0 k z g (t + 1) + d * cfg.δ) +
    3200 * cfg.η ^ 2 * (L0 + L1 * sumNorm (g t))
  change f (x (t + 1)) ≤ f (x t) + ⟪g t, x (t + 1) - x t⟫ +
    (L0 + L1 * sumNorm (g t)) / 2 * maxNorm (x (t + 1) - x t) ^ 2 at hd
  rw [hi] at hd
  simp only [momentumError, normalizerError, sumNorm] at *
  nlinarith

include hb1 hb2 hη hδ hL0 hL1 hg hlip hstep in
lemma deterministic_bound {Δ : ℝ} (hηpos : 0 < cfg.η)
    (hgap : ∀ x, f x0 - f x ≤ Δ) (T : ℕ) :
    let x := fun t => (trajectory cfg x0 k z t).point
    let g := fun t => gradient f (x t)
    (∑ t ∈ Finset.range T, sumNorm (g t)) ≤ Δ / cfg.η +
      4096 * (∑ t ∈ Finset.range T, sumNorm (z t - g t)) +
      2 ^ 26 * cfg.η * (∑ t ∈ Finset.range T, (L0 + L1 * sumNorm (g t))) + T * d * cfg.δ := by
  dsimp only
  let x := fun t => (trajectory cfg x0 k z t).point
  let g := fun t => gradient f (x t)
  have hD (t : ℕ) : drift g (t + 1) ≤ 80 * cfg.η * (L0 + L1 * sumNorm (g t)) := by
    have hmove := maxNorm_move cfg hb1 hb2 hη hδ x0 k z t
    have hr : L1 * maxNorm (x (t + 1) - x t) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hmove hL1).trans hstep
    have h := hlip (x t) (x (t + 1)) hr
    have hc : 0 ≤ L0 + L1 * sumNorm (g t) :=
      add_nonneg hL0 (mul_nonneg hL1 (sumNorm_nonneg _))
    have hm := mul_le_mul_of_nonneg_left hmove hc
    change sumNorm (g (t + 1) - g t) ≤ _ at h
    change sumNorm (g (t + 1) - g t) ≤ _
    nlinarith
  have hsumD : (∑ t ∈ Finset.range T, drift g t) ≤
      80 * cfg.η * ∑ t ∈ Finset.range T, (L0 + L1 * sumNorm (g t)) := by
    have hsum := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range T) => hD t)
    rw [← Finset.mul_sum] at hsum
    have ht := Finset.sum_range_succ' (drift g) T
    rw [Finset.sum_range_succ] at ht
    have hDn : 0 ≤ drift g T := by cases T <;> simp only [drift]; exact le_rfl; exact sumNorm_nonneg _
    rw [show drift g 0 = 0 from rfl, add_zero] at ht
    linarith
  apply AffineAdamDescent.pathwise_bound (δ := cfg.δ) (fun t => f (x t)) (fun t => sumNorm (g t))
    (fun t => L0 + L1 * sumNorm (g t)) (momentumError cfg x0 k z g)
    (normalizerError cfg x0 k z g) (fun t => sumNorm (z t - g t)) (drift g)
    d T hηpos (hgap (x T))
  · intro t; cases t <;> simp only [momentumError]; exact le_rfl
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · intro t; cases t <;> simp only [normalizerError]; exact le_rfl
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  · intro t; exact sumNorm_nonneg _
  · intro t; exact add_nonneg hL0 (mul_nonneg hL1 (sumNorm_nonneg _))
  · rfl
  · rfl
  · exact momentum_error_recurrence cfg hb1 x0 k z g
  · exact normalizer_error_recurrence cfg hb1 hb2 x0 k z g
  · exact hsumD
  · intro t _; exact single_step cfg hb1 hb2 hη hδ x0 k z hL0 hL1 hg hlip hstep t

include hb1 hb2 hη hδ hL0 hL1 hlip hstep in
lemma finite_gradient_bound (T : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (k : ℕ) (z : ℕ → Point d), sumNorm (gradient f (trajectory cfg x0 k z T).point) ≤ C := by
  induction T with
  | zero => exact ⟨sumNorm (gradient f x0), sumNorm_nonneg _, fun _ _ => le_rfl⟩
  | succ T ih =>
    obtain ⟨C, hC, hbound⟩ := ih
    refine ⟨C + (L0 + L1 * C) * (80 * cfg.η), by positivity, ?_⟩
    intro k z
    let x := fun t => (trajectory cfg x0 k z t).point
    have hmove := maxNorm_move cfg hb1 hb2 hη hδ x0 k z T
    have hr : L1 * maxNorm (x (T + 1) - x T) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hmove hL1).trans hstep
    have hd := hlip (x T) (x (T + 1)) hr
    have hc : 0 ≤ L0 + L1 * sumNorm (gradient f (x T)) :=
      add_nonneg hL0 (mul_nonneg hL1 (sumNorm_nonneg _))
    have hh := mul_le_mul_of_nonneg_left hmove hc
    have hh' := mul_le_mul_of_nonneg_right
      (add_le_add_left (mul_le_mul_of_nonneg_left (hbound k z) hL1) L0)
      (by positivity : 0 ≤ 80 * cfg.η)
    have ht := sumNorm_le_add_sub (gradient f (x (T + 1))) (gradient f (x T))
    change sumNorm (gradient f (x (T + 1))) ≤ _
    linarith [hbound k z]

end LongTails.Proofs.AffineAdamPath
