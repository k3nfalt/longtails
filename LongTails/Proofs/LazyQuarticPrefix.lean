import LongTails.Proofs.LazyQuarticCurvature

namespace LongTails.Proofs.LazyQuarticPrefix

open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric
open LongTails.Proofs.LazyQuarticCurvature

lemma value_decrease (F : ℕ → ℝ) (q : ℝ) (t : ℕ)
    (h : ∀ i < t, F (i + 1) ≤ F i - q) : F t ≤ F 0 - t * q := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hh := ih (fun i hi => h i (by omega))
    have ht := h t (by omega)
    push_cast
    linarith

lemma active_bounds (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ) (x : ℕ → p.E) (hx0 : x 0 = p.x0)
    (t : ℕ) (ht : t ≤ stages p)
    (hd : ∀ i < t, f (x (i + 1)) ≤ f (x i) - decrease p)
    (he : ∀ i < t, alpha p * ‖x (i + 1) - x i‖ ^ 2 ≤
      16384 * (f (x i) - f (x (i + 1)))) :
    f (x t) ≤ f p.x0 ∧ t * decrease p ≤ f p.x0 - f (x t) ∧
      ‖x t - p.x0‖ ^ 2 ≤ pathCap p := by
  have hv := value_decrease (fun i => f (x i)) (decrease p) t hd
  rw [hx0] at hv
  have hq := LazyQuarticParameters.decrease_pos p hp
  have hn : 0 ≤ (t : ℝ) * decrease p := mul_nonneg (Nat.cast_nonneg _) hq.le
  refine ⟨by linarith, by linarith, ?_⟩
  have hΔ := hp.2.1
  have ha := LazyQuarticParameters.alpha_pos p hp
  have hh := QuarticPrefixPath.prefix_distance x (fun i => f (x i)) ha.le (by norm_num : (0 : ℝ) ≤ 16384)
    t he (by simpa only [hx0] using hgap (x t))
  rw [hx0] at hh
  have hT := (Nat.cast_le.mpr ht : (t : ℝ) ≤ stages p).trans (stages_upper p hp)
  have hk : alpha p ^ 2 * condition p ^ 2 = beta p ^ 2 := by
    unfold condition
    field_simp
  have h₁ := mul_le_mul_of_nonneg_left hh (sq_nonneg (alpha p))
  have h₂ := mul_le_mul_of_nonneg_left hT (show 0 ≤ 16384 * alpha p ^ 2 * p.Δ by positivity)
  apply path_cap p hp
  have h₃ := congrArg (fun z : ℝ => 2 ^ 26 * p.Δ * z) hk
  nlinarith only [h₁, h₂, h₃]

end LongTails.Proofs.LazyQuarticPrefix
