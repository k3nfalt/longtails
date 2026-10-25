import LongTails.Proofs.AdamHistory
import LongTails.Proofs.AdamNoiseCoupling

namespace LongTails.Proofs.AdamNoiseHistory

open LongTails.Setups.SpectralSmoothAdamComparison
open LongTails.Proofs.AdamHistory

lemma history_coupling {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (a : AdamTuning) (ha : a.Valid) (t : ℕ) (e : Ω ≃ Ω)
    (N : Ω → ℝ) (g k : Ω → ℕ → ℝ) (past : ℕ → ℝ) (μ h B s : ℝ)
    (hprefix : ∀ ω j, j < t → k ω j = past j)
    (hlast : ∀ ω, k ω t = μ + N ω)
    (hdiff : ∀ ω j, j < t + 1 → |g ω j - k ω j| ≤ h)
    (hNsym : ∀ ω, N (e ω) = -N ω) (hNbound : ∀ ω, |N ω| ≤ s)
    (hnoise : (Fintype.card Ω : ℝ) * s ≤ B * ∑ ω, |N ω|)
    (hB : 0 < B) (hs : 0 < s) (hhs : s ≤ h) :
    ∑ ω, |direction a (g ω) (t + 1) - direction a (k ω) (t + 1)| ≤
      (8 * h * B * (t + 1 : ℕ) ^ 2 / s) *
        ∑ ω, |direction a (k ω) (t + 1)| := by
  obtain ⟨hη, hb₁, hb₁', hb₂, hb₂', hb, hτ⟩ := ha
  let α := (1 - a.β₁) / (1 - a.β₁ ^ (t + 1))
  let w := (1 - a.β₂) / (1 - a.β₂ ^ (t + 1))
  let M := a.β₁ * ema a.β₁ past t / (1 - a.β₁ ^ (t + 1))
  let V := a.β₂ * ema a.β₂ (fun j => past j ^ 2) t / (1 - a.β₂ ^ (t + 1))
  have hα := latest_weight_bounds hb₁ hb₁' t
  have hw := latest_weight_bounds hb₂ hb₂' t
  have hden : 0 < 1 - a.β₂ ^ (t + 1) := sub_pos.mpr (pow_lt_one₀ hb₂ hb₂' (by omega))
  have hV : 0 ≤ V := div_nonneg
    (mul_nonneg hb₂ (ema_nonneg hb₂ hb₂'.le _ (fun j => sq_nonneg _) t)) hden.le
  have hm (ω : Ω) : ema a.β₁ (k ω) (t + 1) / (1 - a.β₁ ^ (t + 1)) =
      M + α * (μ + N ω) := by
    rw [corrected_ema_step, ema_congr a.β₁ (k ω) past t (hprefix ω), hlast]
  have hv (ω : Ω) : ema a.β₂ (fun j => k ω j ^ 2) (t + 1) / (1 - a.β₂ ^ (t + 1)) =
      V + w * (μ + N ω) ^ 2 := by
    rw [corrected_ema_step, ema_congr a.β₂ (fun j => k ω j ^ 2) (fun j => past j ^ 2) t
      (fun j hj => by rw [hprefix ω j hj]), hlast]
  have hd (ω : Ω) : direction a (k ω) (t + 1) =
      (M + α * (μ + N ω)) / (Real.sqrt (V + w * (μ + N ω) ^ 2) + a.τ) := by
    rw [direction, hm, hv]
  have hp (ω : Ω) := direction_pair_envelope a
    ⟨hη, hb₁, hb₁', hb₂, hb₂', hb, hτ⟩ (g ω) (k ω) h (hs.le.trans hhs)
    (Nat.succ_pos t) (hdiff ω)
  have h := AdamNoiseCoupling.bounded_history_coupling e N
    (fun ω => direction a (g ω) (t + 1) - direction a (k ω) (t + 1))
    M μ V α w a.τ h (t + 1) B s hNsym hNbound hnoise hV hw.1 hw.2.1 hτ
    hα.1.le hα.2.2 (by exact_mod_cast Nat.le_add_left 1 t) hB hs hhs
    (fun ω => by simpa using (hp ω).1)
    (fun ω => by simpa only [hv, Nat.cast_succ] using (hp ω).2)
    (fun ω => by simpa only [hm, hv, Nat.cast_add, Nat.cast_one] using
      corrected_mean_rms hb₁ hb₂ hb₁' hb₂' hb (k ω) (t + 1))
  simpa only [← hd, Nat.cast_add, Nat.cast_one] using h

end LongTails.Proofs.AdamNoiseHistory
