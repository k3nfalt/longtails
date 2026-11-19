import LongTails.Proofs.MultiscaleAggregateMoments
import LongTails.Proofs.MultiscaleAggregateTracking
import LongTails.Proofs.GdConvex

open MeasureTheory ProbabilityTheory

namespace LongTails.Proofs.MultiscaleAggregateError

open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.MultiscaleAggregate
open MultiscaleAggregateHistory MultiscaleAggregateTrajectory MultiscaleAggregateBudget
open MultiscaleAggregateSampling MultiscaleAggregateCodec MultiscaleAggregateSchedule
open MultiscaleAggregateTracking

variable {p : Params}

lemma rounded_mean (x : Fin p.n → Point p) :
    unpack p (∑ i, localCode p (x i)) =
      (p.n : ℝ)⁻¹ • ∑ i, LongTails.Algorithms.DashaQuantization.rounded p.d false
        (spacing p) (x i) (fun _ => 0) := by
  ext j
  simp [unpack, localCode, aggregateSpacing, LongTails.Algorithms.DashaQuantization.rounded,
    LongTails.Algorithms.DashaQuantization.reconstruct, Finset.mul_sum, div_eq_inv_mul,
    ← mul_assoc, PiLp.smul_apply]

lemma rounding_error (hε : 0 < p.ε) (x : Fin p.n → Point p) :
    ‖unpack p (∑ i, localCode p (x i)) - (p.n : ℝ)⁻¹ • ∑ i, x i‖ ≤ precision p := by
  have he := precision_pos hε
  have hs : 0 < spacing p := by unfold spacing; positivity
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  rw [rounded_mean, ← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hn)]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)).trans
  have hd (i : Fin p.n) := DashaQuantization.vector_initial_error p.d (spacing p) hs (x i) (fun _ => 0)
  calc
    _ ≤ (p.n : ℝ)⁻¹ * ∑ _ : Fin p.n, (p.d : ℝ) * spacing p :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hd i) (inv_nonneg.mpr hn.le)
    _ ≤ precision p := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold spacing
      push_cast
      field_simp
      linarith

lemma error_charge (hε : 0 < p.ε) (g : Fin p.n → Point p → p.Ω → Point p)
    (s : Samples p) (k : ℕ) (G : Point p) :
    ‖raw g s k - G‖ ^ 2 ≤ 2 * (‖unrounded p g s k (point g s k) - G‖ ^ 2 + precision p ^ 2) := by
  have he := precision_pos hε
  have h := rounding_error hε (fun i => batchMean p g s k i (point g s k))
  change ‖raw g s k - unrounded p g s k (point g s k)‖ ≤ precision p at h
  have ht := norm_sub_le_norm_sub_add_norm_sub (raw g s k) (unrounded p g s k (point g s k)) G
  have hb := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ precision p + ‖unrounded p g s k (point g s k) - G‖)).mpr
    (ht.trans (add_le_add h le_rfl))
  nlinarith [sq_nonneg (precision p - ‖unrounded p g s k (point g s k) - G‖)]

lemma tracking_step (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p) (F : Point p → ℝ)
    (hL : 0 < p.L) (hε : 0 < p.ε)
    (hLip : ∀ x y, ‖gradient F x - gradient F y‖ ≤ p.L * ‖x - y‖)
    (k : ℕ) (hk : k < rounds p) (hk₀ : k ≠ 0) :
    let j := (schedule p).pred k
    let e := fun i => ‖estimate g s i - gradient F (point g s i)‖
    let a := fun i => ‖raw g s i - gradient F (point g s i)‖
    overflow (e k) (a k) (radius p k) ≤ overflow (e j) (a j) (radius p j) +
        12 * (a j ^ 2 + a k ^ 2) / radius p k := by
  let j := (schedule p).pred k
  let G := fun i => gradient F (point g s i)
  have he := precision_pos hε
  have hs := scale_parent p k hk hk₀
  have hscale : 2 * radius p k ≤ radius p j := by
    have h := pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hs
    rw [pow_succ] at h
    unfold radius
    dsimp only [j]
    nlinarith [mul_le_mul_of_nonneg_right h he.le]
  have hrad : 0 < radius p k := by unfold radius; positivity
  have hmove := estimate_near_anchor g s hε k
  rw [parent_anchor g s hk hk₀] at hmove
  have hd := parent_drift g s F hLip hL hε hk hk₀
  have hp : ‖estimate g s j - G k‖ ≤ ‖estimate g s j - G j‖ + radius p k := by
    have ht := norm_sub_le_norm_sub_add_norm_sub (estimate g s j) (G j) (G k)
    rw [norm_sub_rev (G j)] at ht
    exact ht.trans (add_le_add le_rfl hd)
  apply overflow_step hrad hscale (norm_nonneg _) (norm_nonneg _)
  · have ht := norm_sub_le_norm_sub_add_norm_sub (estimate g s k) (estimate g s j) (G k)
    change ‖estimate g s k - G k‖ ≤ ‖estimate g s j - G j‖ + 5 * radius p k
    change ‖estimate g s k - estimate g s j‖ ≤ 3 * radius p k at hmove
    linarith
  · intro hprev hraw
    have ht := norm_sub_le_norm_sub_add_norm_sub (raw g s k) (G k) (estimate g s j)
    rw [norm_sub_rev (G k)] at ht
    have hn : ‖raw g s k - anchor g s k‖ ≤ 3 * radius p k := by
      rw [parent_anchor g s hk hk₀]
      change ‖estimate g s j - G j‖ ≤ radius p k at hprev
      change ‖raw g s k - G k‖ ≤ radius p k at hraw
      change ‖raw g s k - estimate g s j‖ ≤ _
      linarith
    change ‖estimate g s k - _‖ ≤ _
    rw [estimate_exact g s hε k hn]

end LongTails.Proofs.MultiscaleAggregateError
