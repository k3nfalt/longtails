import LongTails.Proofs.MultirateStaleness

namespace LongTails.Proofs.MultiratePackets

open LongTails.Setups.DistributedComponentSmoothNonconvex
open LongTails.Setups.BandwidthHeterogeneousSmoothNonconvex (objective)
open LongTails.Algorithms
open MultirateSchedule MultirateTrajectory

variable {p : Params}

noncomputable def average (p : Params) (ys : Fin p.n → List (Point p)) : Point p :=
  (p.n : ℝ)⁻¹ • ∑ i, LeonTrajectory.mean (network p) (ys i)

noncomputable def raw (p : Params) (ys : Fin p.n → List (Point p)) : Code p :=
  LeonTrajectory.totalCodes (network p) (LeonTrajectory.initial (network p)) (level p) ys

noncomputable def received (p : Params) (ys : Fin p.n → List (Point p)) : Code p := fun j =>
  ∑ i, LongTails.Algorithms.DashaModular.decode p.d (width p) (wire (packet p (ys i))) j

lemma received_mod (ys : Fin p.n → List (Point p)) (j : Fin p.d) :
    received p ys j % DashaModular.modulus (width p) = raw p ys j % DashaModular.modulus (width p) := by
  simpa only [received, packet, wire, LongTails.Proofs.DashaModular.decode_encode, raw,
    LeonTrajectory.totalCodes, LeonTrajectory.initial] using
    LongTails.Proofs.DashaModular.sum_residue_mod Finset.univ (width p)
      (fun i => LeonAggregate.localCodes (LeonTuning.spacing (network p)) 0
        (LeonTrajectory.mean (network p) (ys i)) j)

lemma decode_raw (ys : Fin p.n → List (Point p)) :
    estimate p (fun i => wire (packet p (ys i))) =
      LeonAggregate.decode p.n (width p) (LeonTuning.spacing (network p))
        (LeonTuning.radius (network p) (level p)) 0 (raw p ys) := by
  have hh (j : Fin p.d) : DashaModular.restore (width p) (received p ys j) =
      DashaModular.restore (width p) (raw p ys j) := by
    rw [← LongTails.Proofs.DashaModular.restore_mod (width p) (received p ys j),
      received_mod, LongTails.Proofs.DashaModular.restore_mod]
  change LeonAggregate.decode _ _ _ _ _ (received p ys) = _
  simp only [LeonAggregate.decode,hh]

lemma packet_error (hε : 0 < p.ε) (ys : Fin p.n → List (Point p)) (z : Point p)
    (hz : ‖z‖ ≤ 4^(level p) * δ p) :
    ‖estimate p (fun i => wire (packet p (ys i))) - z‖ ≤ 3 / 2 * (δ p + ‖average p ys - z‖) := by
  have h := LeonEstimator.initial_error (network p) hε (level p) z (received p ys) (raw p ys)
    (received_mod ys) hz
  have hr := LeonRounding.raw_error (network p) hε (LeonTrajectory.initial (network p)) (level p) ys
  simp only [LeonTrajectory.initial,zero_add] at hr
  change ‖LeonAggregate.displacement p.n (LeonTuning.spacing (network p)) (raw p ys) - average p ys‖ ≤ δ p at hr
  exact h.trans (mul_le_mul_of_nonneg_left ((norm_sub_le_norm_sub_add_norm_sub _ (average p ys) z).trans
    (add_le_add_left hr _)) (by norm_num))

variable (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)

noncomputable def replies (k : ℕ) (i : Fin p.n) :=
  values p g s i (block p i k) (x g s (anchor p i (block p i k)))

lemma packet_eq (k : ℕ) (i : Fin p.n) : packets g s k i = wire (packet p (replies g s k i)) := by
  simp only [packets, data, replies, source_eq]

lemma gradient_range (hε : 0 < p.ε) (hL : 0 < smoothness p)
    {F : Point p → ℝ} (hF : ∀ z, HasGradientAt F (gradient F z) z)
    (hl : ∀ z w, ‖gradient F z - gradient F w‖ ≤ smoothness p * ‖z-w‖)
    (a : ℝ) (ha : ∀ z, a ≤ F z) (hΔ : F p.x0 - a ≤ p.Δ) (k : ℕ) (hk : k ≤ K p) :
    ‖gradient F (x g s k)‖ ≤ 4 ^ level p * δ p := by
  have hd := LeonBatchTuning.resolution_pos (network p) hε
  have hn : (1 : ℝ) ≤ K p := by
    change 1 ≤ ((4 ^ LeonTuning.height (network p) : ℕ) : ℝ)
    exact_mod_cast (Nat.one_le_pow _ _ (by decide : 0 < 4))
  have hs := DistributedSmoothNonconvex.initial_gradient_bound (p := network p) hL hF hl a ha hΔ
  have hb := (div_le_iff₀ (sq_pos_of_pos hd)).mp (LeonBatchTuning.iterations_lower (network p))
  change 2 * smoothness p * p.Δ ≤ (K p : ℝ) * δ p ^ 2 at hb
  change ‖gradient F p.x0‖ ^ 2 ≤ 2 * smoothness p * p.Δ at hs
  have h₀ : ‖gradient F p.x0‖ ≤ (K p : ℝ) * δ p := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (mul_nonneg (le_trans zero_le_one hn) (sq_nonneg (δ p))),
      mul_nonneg (le_trans zero_le_one hn) hd.le, norm_nonneg (gradient F p.x0)]
  have hm := MultirateStaleness.travel g s hε hL 0 k (Nat.zero_le _)
  change ‖x g s k - p.x0‖ ≤ ((k-0 : ℕ) : ℝ) * (δ p / smoothness p) at hm
  rw [Nat.sub_zero] at hm
  have ht := (hl (x g s k) p.x0).trans (mul_le_mul_of_nonneg_left hm hL.le)
  have hcancel : smoothness p * ((k : ℝ) * (δ p / smoothness p)) = k * δ p := by field_simp
  rw [hcancel] at ht
  have hcast : ((K p : ℕ) : ℝ) = 4^(LeonTuning.height (network p)) := by simp [K,LeonTuning.iterations]
  rw [level,pow_succ,← hcast]
  have hkn : (k : ℝ) * δ p ≤ (K p : ℝ) * δ p := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hd.le
  change 0 < δ p at hd
  have hkδ := mul_nonneg (show (0:ℝ) ≤ K p by positivity) hd.le
  linarith [norm_sub_norm_le (gradient F (x g s k)) (gradient F p.x0)]

end LongTails.Proofs.MultiratePackets
