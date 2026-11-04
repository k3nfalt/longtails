import LongTails.Proofs.CappedMomentumProcess
import LongTails.Proofs.MinimaxLmoDescent

namespace LongTails.Proofs.UscgSharpTracking

open LongTails.Setups.UscgConstant
open OracleTemplate.NormBallLMO OracleTemplate.MinimaxLmo

variable {d : ℕ} {N : Seminorm ℝ (Space d)} {R : ℝ}

noncomputable def mean (α : ℝ) (u : ℕ → Space d) (t : ℕ) : Space d :=
  CappedMomentumProcess.ema α (fun k (_ : Unit) => u k) t ()

noncomputable def bias (α : ℝ) (u : ℕ → Space d) (t : ℕ) : Space d := mean α u (t + 1) - u t

lemma bias_zero (α : ℝ) (u : ℕ → Space d) : bias α u 0 = -(1 - α) • u 0 := by
  simp only [bias, mean, CappedMomentumProcess.ema, smul_zero, zero_add]
  module

lemma bias_succ (α : ℝ) (u : ℕ → Space d) (t : ℕ) :
    bias α u (t + 1) = (1 - α) • bias α u t + (1 - α) • (u t - u (t + 1)) := by
  simp only [bias, mean, CappedMomentumProcess.ema]
  module

lemma decay_sum {B : ℕ → ℝ} {α D : ℝ} (hα : 0 < α)
    (hB : ∀ t, 0 ≤ B t) (hstep : ∀ t, B (t + 1) ≤ (1 - α) * B t + D) (n : ℕ) :
    ∑ t ∈ Finset.range n, B t ≤ (B 0 + n * D) / α := by
  have ht : ∀ n, B n + α * ∑ t ∈ Finset.range n, B t ≤ B 0 + n * D := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := hstep n
      simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
      nlinarith
  apply (le_div_iff₀ hα).mpr
  have hh := ht n
  have hb := hB n
  nlinarith

lemma bias_sum (hR : ∀ v, N v ≤ 1 → ‖v‖ ≤ R) {α D : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hD : 0 ≤ D) (u : ℕ → Space d)
    (hmove : ∀ t, dualNorm N (u t - u (t + 1)) ≤ D) (n : ℕ) :
    ∑ t ∈ Finset.range n, dualNorm N (bias α u t) ≤
      (dualNorm N (u 0) + n * D) / α := by
  have hβ : 0 ≤ 1 - α := by linarith
  have hstep : ∀ t, dualNorm N (bias α u (t + 1)) ≤
      (1 - α) * dualNorm N (bias α u t) + D := by
    intro t
    rw [bias_succ]
    have hb := dualNorm_add_le hR ((1 - α) • bias α u t) ((1 - α) • (u t - u (t + 1)))
    have h₁ := dualNorm_smul_le hR hβ (bias α u t)
    have h₂ := dualNorm_smul_le hR hβ (u t - u (t + 1))
    have h₃ := mul_le_mul_of_nonneg_left (hmove t) hβ
    have h₄ : (1 - α) * D ≤ D := by nlinarith
    linarith
  have hh := decay_sum hα (fun t => dualNorm_nonneg hR _) hstep n
  have hinit : dualNorm N (bias α u 0) ≤ dualNorm N (u 0) := by
    rw [bias_zero, neg_smul, dualNorm_neg hR]
    have h := dualNorm_smul_le hR hβ (u 0)
    have hg := dualNorm_nonneg hR (u 0)
    nlinarith
  exact hh.trans ((div_le_div_iff_of_pos_right hα).mpr (by linarith))

lemma mean_add (α : ℝ) (u v : ℕ → Space d) (t : ℕ) :
    mean α (fun k => u k + v k) t = mean α u t + mean α v t := by
  induction t with
  | zero => simp [mean, CappedMomentumProcess.ema]
  | succ t ih =>
    change (1 - α) • mean α (fun k => u k + v k) t + α • (u t + v t) = _
    rw [ih]
    change _ = ((1 - α) • mean α u t + α • u t) +
      ((1 - α) • mean α v t + α • v t)
    module

lemma mean_eval {Ω : Type*} (α : ℝ) (Y : ℕ → Ω → Space d) (ω : Ω) (t : ℕ) :
    mean α (fun k => Y k ω) t = CappedMomentumProcess.ema α Y t ω := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (1 - α) • mean α (fun k => Y k ω) t + α • Y t ω = _
    rw [ih]
    rfl

lemma tracking_decomposition (α : ℝ) (samples u : ℕ → Space d) (t : ℕ) :
    mean α samples (t + 1) - u t =
      mean α (fun k => samples k - u k) (t + 1) + bias α u t := by
  have he : samples = fun k => (samples k - u k) + u k := by
    funext k
    abel
  conv_lhs => rw [he, mean_add]
  unfold bias
  abel

end LongTails.Proofs.UscgSharpTracking
