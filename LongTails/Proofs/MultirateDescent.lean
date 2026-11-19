import LongTails.Proofs.MultirateDrift
import LongTails.Proofs.ParameterFreeNsgdmRun
import LongTails.Proofs.DistributedSmoothNonconvex

namespace LongTails.Proofs.MultirateDescent

open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Algorithms.MultirateTrajectory LongTails.Algorithms.MultirateCalendar
open LongTails.Algorithms.MultiscaleAggregate (precision radius)
open MultirateDrift

variable {p : Params} (g : Fin p.n → Point p → p.Ω → Point p) (s : Samples p)
    (f : Point p → ℝ) (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hl : ∀ x y, ‖gradient f x - gradient f y‖ ≤ (aggregate p).L * ‖x-y‖)
    (hL : 0 < (aggregate p).L) (hε : 0 < p.ε)

include hf hl hL hε

lemma gradient_range (a : ℝ) (ha : ∀ x, a ≤ f x) (hgap : f p.x0 - a ≤ p.Δ)
    {k : ℕ} (hk : k ≤ steps p) : ‖gradient f (point g s k)‖ ≤ 2 * radius (aggregate p) 0 := by
  have h₀ := DistributedSmoothNonconvex.initial_gradient_bound
    (p := MultiscaleAggregateSampling.streamParams (aggregate p)) hL hf hl a ha hgap
  have hR := MultiscaleAggregateBudget.initial_radius (p := aggregate p) hε h₀
  have hD := (hl (point g s k) p.x0).trans (range_bound g s hL hε hk)
  have ht := norm_sub_norm_le (gradient f (point g s k)) (gradient f p.x0)
  change ‖gradient f p.x0‖ ≤ _ at hR
  linarith

lemma estimated_sum (a : ℝ) (ha : ∀ x, a ≤ f x) (hgap : f p.x0 - a ≤ p.Δ) :
    (∑ i : Fin (steps p), ‖estimate g s i‖) ≤ steps p * precision (aggregate p) +
      3 * ∑ i : Fin (steps p), ‖estimate g s i - gradient f (point g s i)‖ := by
  let η := stepSize p
  let δ := precision (aggregate p)
  let L := (aggregate p).L
  let K := steps p
  let x := point g s
  let v := estimate g s
  have he : 0 < δ := MultiscaleAggregateCodec.precision_pos (p := aggregate p) hε
  have hη : 0 < η := div_pos he hL
  have hd (t : ℕ) : η * ‖v t‖ ≤ f (x t) - f (x (t+1)) + 3 * η * ‖v t - gradient f (x t)‖ + L/2*η^2 := by
    have hb := ParameterFreeNsgdmRun.descent_step hf hl hL.le η hη.le (x t) (v t)
    have hstep : x (t+1) = x t - (η / ‖v t‖) • v t := step_eq g s t
    rw [← hstep] at hb
    have hi := norm_sub_norm_le (v t) (gradient f (x t))
    nlinarith [mul_le_mul_of_nonneg_left hi hη.le]
  have htel (t : ℕ) : η * (∑ j ∈ Finset.range t, ‖v j‖) ≤ f p.x0 - f (x t) +
      3 * η * (∑ j ∈ Finset.range t, ‖v j - gradient f (x j)‖) + (t : ℝ)* (L/2*η^2) := by
    induction t with
    | zero => simp; rfl
    | succ t ih =>
      simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, mul_add, add_mul, one_mul]
      linarith [hd t]
  have hbudget := (div_le_iff₀ (sq_pos_of_pos he)).mp (MultiscaleAggregateBudget.round_count_lower (p := aggregate p))
  have hηL : η * L = δ := div_mul_cancel₀ _ hL.ne'
  have hg₀ : f p.x0 - f (x K) ≤ p.Δ := by linarith [ha (x K)]
  have hΔ : p.Δ ≤ (K : ℝ) * δ * η / 2 := by
    apply (mul_le_mul_iff_left₀ hL).mp
    change 2 * L * p.Δ ≤ (K : ℝ) * δ ^ 2 at hbudget
    calc
      p.Δ * L ≤ ((K : ℝ) * δ^2) / 2 := by linarith
      _ = ((K : ℝ) * δ * η / 2) * L := by rw [← hηL]; ring
  have hcurv : L / 2 * η ^ 2 = δ * η / 2 := by rw [← hηL]; ring
  rw [Fin.sum_univ_eq_sum_range (fun j => ‖v j‖), Fin.sum_univ_eq_sum_range (fun j => ‖v j - gradient f (x j)‖)]
  change (∑ j ∈ Finset.range K, ‖v j‖) ≤ K * δ + 3 * ∑ j ∈ Finset.range K, ‖v j - gradient f (x j)‖
  apply le_of_mul_le_mul_left (a := η) _ hη
  have h := htel K
  rw [hcurv] at h
  nlinarith only [h, hg₀, hΔ]

end LongTails.Proofs.MultirateDescent
