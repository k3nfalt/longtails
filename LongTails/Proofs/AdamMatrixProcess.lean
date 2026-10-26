import LongTails.Proofs.AdamScalarProcess
import LongTails.Proofs.AdamExecution

namespace LongTails.Proofs.AdamMatrixProcess

open LongTails.Algorithms.MatrixPolar
open LongTails.Setups.SpectralSmoothAdamComparison LongTails.Setups.BatchedSpectralSmooth
open LongTails.Proofs.AdamMatrixGeometry LongTails.Proofs.AdamScalarProcess

lemma history_coordinate {r : ℕ} (hr : 0 < r) (a : AdamTuning) (ℓ c w D : ℝ)
    (noise : ℕ → ℝ) (j : ℕ) (i k : Fin r) :
    mixedProjection r (ℓ * (trajectory a r ℓ c w D noise j).stiff + noise j)
      (quietGradient c w D (trajectory a r ℓ c w D noise j)) (i, k) =
        if i = k then diagHistory a r ℓ c w D noise j else offHistory a r ℓ c w D noise j := by
  rw [mixedProjection_apply]
  have hr' : (r : ℝ) ≠ 0 := by positivity
  split_ifs
  · dsimp [diagHistory, offHistory, diagGradient, offGradient]
    field_simp
    ring
  · rfl

lemma direction_matches {r B t : ℕ} (hr : 0 < r) (a : AdamTuning) (ℓ c w D : ℝ)
    (noise : ℕ → ℝ) (reply : ℕ → Space r r)
    (hbatch : ∀ j < t + 1, batchMean B reply j =
      mixedProjection r (ℓ * (trajectory a r ℓ c w D noise j).stiff + noise j)
        (quietGradient c w D (trajectory a r ℓ c w D noise j))) :
    adamDirection a B reply t =
      mixedProjection r
        ((r : ℝ) * offDirection a r ℓ c w D noise t +
          (diagDirection a r ℓ c w D noise t - offDirection a r ℓ c w D noise t))
        (diagDirection a r ℓ c w D noise t - offDirection a r ℓ c w D noise t) := by
  ext ⟨i,k⟩
  change (firstMoment a.β₁ B reply (t + 1) (i,k) / (1 - a.β₁ ^ (t + 1))) /
    (Real.sqrt (secondMoment a.β₂ B reply (t + 1) (i,k) / (1 - a.β₂ ^ (t + 1))) + a.τ) = _
  rw [AdamHistory.firstMoment_coordinate, AdamHistory.secondMoment_coordinate, mixedProjection_apply]
  have hg (j : ℕ) (hj : j < t + 1) := congrArg (fun X : Space r r => X (i,k)) (hbatch j hj)
  simp only [history_coordinate hr] at hg
  have hr' : (r : ℝ) ≠ 0 := by positivity
  by_cases hik : i = k
  · simp only [hik, ↓reduceIte] at hg ⊢
    rw [AdamHistory.ema_congr a.β₁ _ (diagHistory a r ℓ c w D noise) (t + 1) hg,
      AdamHistory.ema_congr a.β₂ _ (fun j => diagHistory a r ℓ c w D noise j ^ 2) (t + 1)
        (fun j hj => by rw [hg j hj])]
    change diagDirection a r ℓ c w D noise t = _
    field_simp
    ring
  · simp only [hik, ↓reduceIte] at hg ⊢
    rw [AdamHistory.ema_congr a.β₁ _ (offHistory a r ℓ c w D noise) (t + 1) hg,
      AdamHistory.ema_congr a.β₂ _ (fun j => offHistory a r ℓ c w D noise j ^ 2) (t + 1)
        (fun j hj => by rw [hg j hj])]
    change offDirection a r ℓ c w D noise t = _
    field_simp
    ring

lemma iterate_matches {r B t : ℕ} (hr : 0 < r) (a : AdamTuning) (ℓ c w D : ℝ)
    (noise : ℕ → ℝ) (reply : ℕ → Space r r) (x0 : Space r r)
    (hbatch : ∀ j < t, batchMean B reply j =
      mixedProjection r (ℓ * (trajectory a r ℓ c w D noise j).stiff + noise j)
        (quietGradient c w D (trajectory a r ℓ c w D noise j))) :
    adamIterate a B x0 reply t = x0 + mixedProjection r
      (trajectory a r ℓ c w D noise t).stiff (trajectory a r ℓ c w D noise t).quiet := by
  induction t with
  | zero => simp [adamIterate, trajectory, mixedProjection]
  | succ t ih =>
    rw [adamIterate, ih (fun j hj => hbatch j (by omega)),
      direction_matches hr a ℓ c w D noise reply hbatch,
      (trajectory_step_coordinates a r ℓ c w D noise t).1,
      (trajectory_step_coordinates a r ℓ c w D noise t).2]
    unfold mixedProjection
    module

end LongTails.Proofs.AdamMatrixProcess
