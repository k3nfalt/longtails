import LongTails.Algorithms.DistributedNormalizedDownlink
import LongTails.Proofs.ParameterFreeNsgdmRun
import LongTails.Proofs.DistributedNormalizedCompression
import LongTails.Proofs.DistributedSmoothNonconvex

namespace LongTails.Proofs.DistributedNormalizedPath

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedDownlink

lemma increment_norm (p : Params) (cfg : Config) (hη : 0 ≤ cfg.stepSize) (v : Point p) :
    ‖increment cfg v‖ ≤ cfg.stepSize := by
  simpa [increment, neg_smul] using
    ParameterFreeNsgdmRun.normalized_move_norm cfg.stepSize hη (0 : Point p) v

lemma root_path (p : Params) (cfg : Config) (hη : 0 ≤ cfg.stepSize)
    (draws : Draws p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) (k : ℕ) :
    ‖(trajectory p cfg draws g samples k).root - p.x0‖ ≤ k * cfg.stepSize := by
  induction k with
  | zero => simp [trajectory, initial]
  | succ k ih =>
    let s := trajectory p cfg draws g samples k
    let u := increment cfg (estimator p cfg draws g samples k s)
    change ‖s.root + u - p.x0‖ ≤ (k + 1 : ℕ) * cfg.stepSize
    have hu : ‖u‖ ≤ cfg.stepSize := increment_norm p cfg hη _
    have he : s.root + u - p.x0 = (s.root - p.x0) + u := by abel
    rw [he]
    calc
      _ ≤ ‖s.root - p.x0‖ + ‖u‖ := norm_add_le _ _
      _ ≤ k * cfg.stepSize + cfg.stepSize := add_le_add ih hu
      _ = _ := by push_cast; ring

lemma descent_sum (p : Params) (cfg : Config) (hη : 0 ≤ cfg.stepSize)
    (draws : Draws p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams) (f : Point p → ℝ)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hL : 0 ≤ p.L) (K : ℕ) :
    cfg.stepSize * ∑ k ∈ Finset.range K, ‖gradient f (trajectory p cfg draws g samples k).root‖ ≤
      f p.x0 - f (trajectory p cfg draws g samples K).root +
      2 * cfg.stepSize * ∑ k ∈ Finset.range K,
        ‖estimator p cfg draws g samples k (trajectory p cfg draws g samples k) -
          gradient f (trajectory p cfg draws g samples k).root‖ +
      K * (p.L / 2 * cfg.stepSize ^ 2) := by
  induction K with
  | zero => simp [trajectory, initial]
  | succ K ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add]
    have hstep := ParameterFreeNsgdmRun.descent_step hg hlip hL cfg.stepSize hη
      (trajectory p cfg draws g samples K).root
      (estimator p cfg draws g samples K (trajectory p cfg draws g samples K))
    have he : (trajectory p cfg draws g samples (K + 1)).root =
        (trajectory p cfg draws g samples K).root -
          (cfg.stepSize / ‖estimator p cfg draws g samples K (trajectory p cfg draws g samples K)‖) •
            estimator p cfg draws g samples K (trajectory p cfg draws g samples K) := by
      simp only [trajectory, next, increment, neg_smul, sub_eq_add_neg]
    rw [← he] at hstep
    push_cast
    linarith

lemma downlink_path_step (p : Params) (cfg : Config) (hη : 0 ≤ cfg.stepSize)
    (K : ℕ) (hsi : 0 < cfg.incrementSpacing) (hsr : 0 < cfg.refreshSpacing)
    (hinc : cfg.incrementSpacing ≤ p.d * cfg.stepSize)
    (href : p.d * cfg.refreshSpacing ^ 2 ≤ cfg.stepSize ^ 2 / 16)
    (hcapi : p.d * cfg.stepSize ≤ cfg.incrementSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hcapr : K * cfg.stepSize ≤ cfg.refreshSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (draws : Draws p) (k : ℕ) (i : Fin p.n) (x u previous : Point p)
    (hx : ‖x - p.x0‖ ≤ K * cfg.stepSize) (hu : ‖u‖ ≤ cfg.stepSize) :
    ‖downlinkReceive p cfg draws k i previous (downlinkMessage p cfg draws k i x u) - p.x0‖ ≤
      max (K * cfg.stepSize + cfg.stepSize / 4)
        (‖previous - p.x0‖ + 2 * p.d * cfg.stepSize) := by
  cases hr : refresh cfg k with
  | false =>
    let j := fun q : Fin cfg.downlinkCount => (draws (2 * k + 1) i q.val).1
    let v := fun q : Fin cfg.downlinkCount => (draws (2 * k + 1) i q.val).2
    let z := LongTails.Algorithms.DistributedNormalizedCompression.sparseReceive
      cfg.downlinkWidth cfg.downlinkCount cfg.incrementSpacing j
      (LongTails.Algorithms.DistributedNormalizedCompression.sparseMessage
        cfg.downlinkWidth cfg.downlinkCount cfg.incrementSpacing u j v)
    have hc (a : Fin p.d) : |(p.d : ℝ) * u a| ≤ cfg.incrementSpacing *
        (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg p.d)]
      have ha0 : |u a| ≤ ‖u‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u a
      have ha : |u a| ≤ cfg.stepSize := ha0.trans hu
      exact (mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg p.d)).trans hcapi
    have hz : ‖z‖ ≤ (p.d : ℝ) * ‖u‖ + cfg.incrementSpacing := by
      simpa only [z, List.append_nil] using DistributedNormalizedCompression.sparse_message_norm
        cfg.downlinkWidth cfg.downlinkCount cfg.downlinkCount.pos hsi u j v [] hc
    have hz' : ‖z‖ ≤ 2 * p.d * cfg.stepSize := by
      nlinarith [mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg p.d)]
    simp only [downlinkReceive, downlinkMessage, hr, Bool.false_eq_true, ite_false]
    change ‖previous + z - p.x0‖ ≤ _
    have he : previous + z - p.x0 = (previous - p.x0) + z := by abel
    rw [he]
    exact ((norm_add_le _ _).trans (add_le_add le_rfl hz')).trans (le_max_right _ _)
  | true =>
    let v := fun j : Fin p.d => (draws (2 * k + 1) i j.val).2
    let z := LongTails.Algorithms.DistributedNormalizedCompression.fullReceive p.d
      cfg.downlinkWidth cfg.refreshSpacing
      (LongTails.Algorithms.DistributedRandomRounding.message p.d cfg.downlinkWidth
        cfg.refreshSpacing (x - p.x0) v)
    have hc (a : Fin p.d) : |(x - p.x0) a| ≤ cfg.refreshSpacing *
        (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1) := by
      have ha : |(x - p.x0) a| ≤ ‖x - p.x0‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x - p.x0) a
      exact ha.trans (hx.trans hcapr)
    have he2 : ‖z - (x - p.x0)‖ ^ 2 ≤ p.d * cfg.refreshSpacing ^ 2 := by
      simpa only [z, List.append_nil] using DistributedNormalizedCompression.full_message_error_sq
        p.d cfg.downlinkWidth hsr (x - p.x0) v [] hc
    have he : ‖z - (x - p.x0)‖ ≤ cfg.stepSize / 4 := by
      nlinarith [norm_nonneg (z - (x - p.x0))]
    have hz : ‖z‖ ≤ K * cfg.stepSize + cfg.stepSize / 4 := by
      have ht := norm_add_le (z - (x - p.x0)) (x - p.x0)
      rw [sub_add_cancel] at ht
      linarith
    simp only [downlinkReceive, downlinkMessage, hr, ite_true]
    change ‖p.x0 + z - p.x0‖ ≤ _
    have heq : p.x0 + z - p.x0 = z := by abel
    rw [heq]
    exact hz.trans (le_max_left _ _)

lemma worker_path (p : Params) (cfg : Config) (hη : 0 ≤ cfg.stepSize)
    (K : ℕ) (hsi : 0 < cfg.incrementSpacing) (hsr : 0 < cfg.refreshSpacing)
    (hinc : cfg.incrementSpacing ≤ p.d * cfg.stepSize)
    (href : p.d * cfg.refreshSpacing ^ 2 ≤ cfg.stepSize ^ 2 / 16)
    (hcapi : p.d * cfg.stepSize ≤ cfg.incrementSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hcapr : K * cfg.stepSize ≤ cfg.refreshSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (draws : Draws p) (g : Fin p.n → Point p → p.Ω → Point p)
    (samples : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (k : ℕ) (hk : k ≤ K) (i : Fin p.n) :
    ‖(trajectory p cfg draws g samples k).workers i - p.x0‖ ≤
      K * cfg.stepSize + 2 * p.d * k * cfg.stepSize + cfg.stepSize / 4 := by
  induction k with
  | zero =>
    simp only [trajectory, initial, sub_self, norm_zero, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    positivity
  | succ k ih =>
    have hprev := ih (by omega)
    let s := trajectory p cfg draws g samples k
    let u := increment cfg (estimator p cfg draws g samples k s)
    let x := s.root + u
    have hu : ‖u‖ ≤ cfg.stepSize := increment_norm p cfg hη _
    have hx : ‖x - p.x0‖ ≤ K * cfg.stepSize := by
      have ht := root_path p cfg hη draws g samples (k + 1)
      have hmul := mul_le_mul_of_nonneg_right (show ((k + 1 : ℕ) : ℝ) ≤ K by exact_mod_cast hk) hη
      exact ht.trans hmul
    have ht := downlink_path_step p cfg hη K hsi hsr hinc href hcapi hcapr
      draws k i x u (s.workers i) hx hu
    change ‖downlinkReceive p cfg draws k i (s.workers i)
      (downlinkMessage p cfg draws k i x u) - p.x0‖ ≤ _
    apply ht.trans
    apply max_le
    · have hp : 0 ≤ 2 * (p.d : ℝ) * (k + 1) * cfg.stepSize := by positivity
      push_cast
      nlinarith
    · push_cast
      change ‖s.workers i - p.x0‖ ≤ _ at hprev
      linarith

lemma path_radius_le {d K k : ℕ} {η : ℝ} (hη : 0 ≤ η) (hd : 0 < d) (hk : k ≤ K) :
    (K : ℝ) * η + 2 * d * k * η + η / 4 ≤ 4 * d * (K + 1 : ℕ) * η := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hk' : (k : ℝ) ≤ K := by exact_mod_cast hk
  have h1 := mul_le_mul_of_nonneg_right hk' (show 0 ≤ 2 * (d : ℝ) * η by positivity)
  have h2 := mul_nonneg (sub_nonneg.mpr hd') (show 0 ≤ (K : ℝ) * η by positivity)
  have h3 := mul_nonneg (sub_nonneg.mpr hd') hη
  have h4 : 0 ≤ (d : ℝ) * K * η := by positivity
  have h5 : 0 ≤ (d : ℝ) * η := by positivity
  push_cast
  nlinarith

lemma gradient_at_bounded_point (p : Params) (f : Point p → ℝ) (hL : 0 < p.L)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (lower : ℝ) (hlower : ∀ x, lower ≤ f x) (hgap : f p.x0 - lower ≤ p.Δ)
    (x : Point p) (R : ℝ) (hx : ‖x - p.x0‖ ≤ R) :
    ‖gradient f x‖ ≤ Real.sqrt (2 * p.L * p.Δ) + p.L * R := by
  have h0 := DistributedSmoothNonconvex.initial_gradient_bound (p := p.toParams)
    hL hg hlip lower hlower hgap
  have hnonneg : 0 ≤ 2 * p.L * p.Δ := (sq_nonneg _).trans h0
  have hs : ‖gradient f p.x0‖ ≤ Real.sqrt (2 * p.L * p.Δ) := by
    nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (2 * p.L * p.Δ), norm_nonneg (gradient f p.x0)]
  have ht := norm_add_le (gradient f x - gradient f p.x0) (gradient f p.x0)
  rw [sub_add_cancel] at ht
  have hb := (hlip x p.x0).trans (mul_le_mul_of_nonneg_left hx hL.le)
  linarith

end LongTails.Proofs.DistributedNormalizedPath
