import LongTails.Algorithms.DistributedNormalizedDownlink

namespace LongTails.Proofs.DistributedNormalizedCausality

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedDownlink

lemma next_congr (p : Params) (cfg : Config) (draws draws' : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples samples' : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (k : ℕ) (s : Iterate p)
    (hup : draws (2 * k) = draws' (2 * k))
    (hdown : draws (2 * k + 1) = draws' (2 * k + 1))
    (hbatch : ∀ (i : Fin p.n) (j : ℕ), j < (cfg.batch : ℕ) → samples i (k * cfg.batch + j) = samples' i (k * cfg.batch + j)) :
    next p cfg draws g samples k s = next p cfg draws' g samples' k s := by
  have hb (i : Fin p.n) : batchMean p cfg g samples k i (s.workers i) =
      batchMean p cfg g samples' k i (s.workers i) := by
    unfold batchMean
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbatch i j (Finset.mem_range.mp hj)]
  have he : estimator p cfg draws g samples k s = estimator p cfg draws' g samples' k s := by
    unfold estimator
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hb i]
    simp only [uplinkReceive, uplinkMessage, hup]
  unfold next
  rw [he]
  simp only [downlinkReceive, downlinkMessage, hdown]

lemma trajectory_prefix (p : Params) (cfg : Config) (draws draws' : Draws p)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (samples samples' : LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams)
    (k : ℕ) (hdraws : ∀ t, t < 2 * k → draws t = draws' t)
    (hsamples : ∀ i j, j < k * cfg.batch → samples i j = samples' i j) :
    trajectory p cfg draws g samples k = trajectory p cfg draws' g samples' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkb : k * (cfg.batch : ℕ) ≤ (k + 1) * cfg.batch := Nat.mul_le_mul_right _ (Nat.le_succ k)
    have hprev := ih (fun t ht => hdraws t (by omega))
      (fun i j hj => hsamples i j (lt_of_lt_of_le hj hkb))
    rw [trajectory, trajectory, hprev]
    apply next_congr p cfg draws draws' g samples samples' k
      (trajectory p cfg draws' g samples' k)
    · exact hdraws (2 * k) (by omega)
    · exact hdraws (2 * k + 1) (by omega)
    · intro i j hj
      apply hsamples i (k * cfg.batch + j)
      have he : (k + 1) * (cfg.batch : ℕ) = k * cfg.batch + cfg.batch := by
        simp only [Nat.add_mul, Nat.one_mul]
      rw [he]
      omega

end LongTails.Proofs.DistributedNormalizedCausality
