import LongTails.Proofs.BacktrackingAcceleratedCount
import LongTails.Proofs.Execution
import Mathlib.Analysis.Complex.ExponentialBounds

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ParameterFreeGeneralized

open LongTails.Setups.GeneralizedSmoothParameterFree

lemma two_queries (p : Public) (g : p.E → p.E) (s : Core p.E) :
    (fun state => (algorithm p).update state (g (((algorithm p).query state).2)))^[2]
      (.ready s) = .ready (trial g s) := rfl

lemma execute_algorithm (p : Public) (g : p.E → p.E) (N : ℕ) :
    execute { answer := fun _ (_, x) _ => g x } (algorithm p) (fun _ => (2 * N)) =
      ((trial g)^[N] ⟨0, p.x0, p.x0, p.h0⟩).x := by
  let T := fun state => (algorithm p).update state (g (((algorithm p).query state).2))
  have hi : ∀ n, T^[2 * n] ((algorithm p).initial ()) =
      .ready ((trial g)^[n] ⟨0, p.x0, p.x0, p.h0⟩) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 + 2 * n by omega, Function.iterate_add_apply, ih]
      exact (two_queries p g _).trans
        (congrArg State.ready (Function.iterate_succ_apply' (trial g) n _).symm)
  erw [execute_iterate]
  change (algorithm p).output (T^[2 * N] ((algorithm p).initial ())) = _
  rw [hi]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma eta_inv_le {f : E → ℝ} {g : E → E} {L0 L1 Δ h0 : ℝ} {u x0 : E}
    (H : Hyp f g L0 L1 u) (hh0 : 0 < h0) (hgap : f x0 - f u ≤ Δ) :
    1 / eta g x0 L0 L1 h0 ≤ 1 / h0 + 16 * L0 + 80 * L1 ^ 2 * Δ := by
  have hL0 := H.L0_pos
  have hL1 := H.L1_nonneg
  have hG : L1 * ‖g x0‖ ≤ L0 + 10 * L1 ^ 2 * Δ := by
    have h1 := gradient_gap_bound H x0
    have h2 := mul_le_mul_of_nonneg_left hgap (by positivity : 0 ≤ 10 * L1 ^ 2)
    linarith
  have hnorm : 0 < L0 + L1 * ‖g x0‖ := by positivity
  have hΔ : 0 ≤ Δ := le_trans (sub_nonneg.mpr (H.min (mem_univ x0))) hgap
  have hpos : 0 ≤ 80 * L1 ^ 2 * Δ := by positivity
  have hh : 0 < 1 / h0 := by positivity
  unfold eta
  rcases le_total h0 (1 / (8 * (L0 + L1 * ‖g x0‖))) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h, one_div_one_div]
    linarith

lemma budget_bound {f : E → ℝ} {g : E → E} {L0 L1 R Δ h0 ε : ℝ} {u x0 : E}
    (H : Hyp f g L0 L1 u) (hR : 0 < R) (hh0 : 0 < h0) (hε : 0 < ε)
    (hgap : f x0 - f u ≤ Δ) :
    2 * (2 + (1 + sigma L1 R) *
          Real.log (1 + cap L0 * sigma L1 R ^ 2 / eta g x0 L0 L1 h0) +
        2 * Real.sqrt (R ^ 2 / (2 * ε)) / Real.sqrt (cap L0)) +
      Real.logb 2 (h0 / min (cap L0) (eta g x0 L0 L1 h0 / sigma L1 R ^ 2)) ≤
    4 + 2 * (3 + 13 * L1 * R) * Real.log (1 + (2 + 13 * L1 * R) ^ 2 *
        (1 / (64 * L0 * h0) + 1 / 4 + 5 * L1 ^ 2 * Δ / (4 * L0))) +
      4 * Real.sqrt (32 * L0 * R ^ 2 / ε) +
      Real.logb 2 ((2 + 13 * L1 * R) ^ 2 * (1 + 16 * L0 * h0 + 80 * L1 ^ 2 * Δ * h0)) := by
  have hL0 := H.L0_pos
  have hL1 := H.L1_nonneg
  have hσe : 2 + 13 * L1 * R = sigma L1 R := by
    unfold sigma
    ring
  have e3 : 3 + 13 * L1 * R = 1 + sigma L1 R := by
    unfold sigma
    ring
  rw [e3, hσe]
  have hσ : 2 ≤ sigma L1 R := by
    unfold sigma
    have := mul_nonneg hL1 hR.le
    linarith
  generalize sigma L1 R = σ at hσ ⊢
  have hσ0 : 0 < σ := by linarith
  have hσ2 : 4 ≤ σ ^ 2 := by nlinarith
  have hc : 0 < cap L0 := by
    unfold cap
    positivity
  have hnorm : 0 < L0 + L1 * ‖g x0‖ := by positivity
  have hη : 0 < eta g x0 L0 L1 h0 := lt_min hh0 (by positivity)
  have hinv := eta_inv_le H hh0 hgap
  have hΔ : 0 ≤ Δ := le_trans (sub_nonneg.mpr (H.min (mem_univ x0))) hgap
  generalize eta g x0 L0 L1 h0 = η at hη hinv ⊢
  have hratio : cap L0 * σ ^ 2 / η ≤
      σ ^ 2 * (1 / (64 * L0 * h0) + 1 / 4 + 5 * L1 ^ 2 * Δ / (4 * L0)) := by
    have h1 : cap L0 * σ ^ 2 / η = cap L0 * σ ^ 2 * (1 / η) := by ring
    have h2 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ cap L0 * σ ^ 2)
    have h3 : cap L0 * σ ^ 2 * (1 / h0 + 16 * L0 + 80 * L1 ^ 2 * Δ) =
        σ ^ 2 * (1 / (64 * L0 * h0) + 1 / 4 + 5 * L1 ^ 2 * Δ / (4 * L0)) := by
      unfold cap
      field_simp
      ring
    linarith
  have hqpos : 0 < cap L0 * σ ^ 2 / η := by positivity
  have hlog : Real.log (1 + cap L0 * σ ^ 2 / η) ≤
      Real.log (1 + σ ^ 2 * (1 / (64 * L0 * h0) + 1 / 4 + 5 * L1 ^ 2 * Δ / (4 * L0))) :=
    Real.log_le_log (by linarith) (by linarith)
  have hsqrt : Real.sqrt (R ^ 2 / (2 * ε)) / Real.sqrt (cap L0) =
      Real.sqrt (32 * L0 * R ^ 2 / ε) := by
    rw [← Real.sqrt_div (by positivity)]
    congr 1
    unfold cap
    field_simp
    ring
  have hminpos : 0 < min (cap L0) (η / σ ^ 2) := lt_min hc (by positivity)
  have hstep : h0 / min (cap L0) (η / σ ^ 2) ≤
      σ ^ 2 * (1 + 16 * L0 * h0 + 80 * L1 ^ 2 * Δ * h0) := by
    rw [div_le_iff₀ hminpos]
    have hB : 0 ≤ 80 * L1 ^ 2 * Δ * h0 := by positivity
    have hB2 : 0 < 16 * L0 * h0 := by positivity
    rcases le_total (cap L0) (η / σ ^ 2) with h | h
    · rw [min_eq_left h]
      have h4 : σ ^ 2 * (1 + 16 * L0 * h0 + 80 * L1 ^ 2 * Δ * h0) * cap L0 =
          σ ^ 2 * ((1 + 80 * L1 ^ 2 * Δ * h0) / (64 * L0)) + σ ^ 2 * h0 / 4 := by
        unfold cap
        field_simp
        ring
      have h5 : 0 ≤ σ ^ 2 * ((1 + 80 * L1 ^ 2 * Δ * h0) / (64 * L0)) := by positivity
      nlinarith
    · rw [min_eq_right h]
      have h4 : σ ^ 2 * (1 + 16 * L0 * h0 + 80 * L1 ^ 2 * Δ * h0) * (η / σ ^ 2) =
          (1 + 16 * L0 * h0 + 80 * L1 ^ 2 * Δ * h0) * η := by
        field_simp
      rw [h4]
      have h5 := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ h0 * η)
      have h6 : h0 * η * (1 / η) = h0 := by
        field_simp
      have h7 : h0 * η * (1 / h0 + 16 * L0 + 80 * L1 ^ 2 * Δ) =
          (1 + 16 * L0 * h0 + 80 * L1 ^ 2 * Δ * h0) * η := by
        field_simp
      linarith
  have hlogb : Real.logb 2 (h0 / min (cap L0) (η / σ ^ 2)) ≤
      Real.logb 2 (σ ^ 2 * (1 + 16 * L0 * h0 + 80 * L1 ^ 2 * Δ * h0)) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) hstep
  have hmul := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ 2 * (1 + σ))
  have hdiv : 2 * Real.sqrt (R ^ 2 / (2 * ε)) / Real.sqrt (cap L0) =
      2 * Real.sqrt (32 * L0 * R ^ 2 / ε) := by
    rw [mul_div_assoc, hsqrt]
  rw [hdiv]
  linarith

lemma budget_merge {L0 L1 R Δ h0 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hR : 0 < R) (hΔ : 0 ≤ Δ)
    (hh0 : 0 < h0) :
    2 * (3 + 13 * L1 * R) * Real.log (1 + (2 + 13 * L1 * R) ^ 2 *
        (1 / (64 * L0 * h0) + 1 / 4 + 5 * L1 ^ 2 * Δ / (4 * L0))) +
      Real.logb 2 ((2 + 13 * L1 * R) ^ 2 * (1 + 16 * L0 * h0 + 80 * L1 ^ 2 * Δ * h0)) ≤
    26 * (1 + L1 * R) * Real.log (1 + (2 + 13 * L1 * R) ^ 2 *
      (2 + 1 / (64 * L0 * h0) + 16 * L0 * h0 + 5 * L1 ^ 2 * Δ / (4 * L0) +
        80 * L1 ^ 2 * Δ * h0)) := by
  have ht : 0 ≤ L1 * R := by positivity
  have ht' : 0 ≤ 13 * L1 * R := by positivity
  have hσ : 0 < (2 + 13 * L1 * R) ^ 2 := by positivity
  have ha : 0 < 1 / (64 * L0 * h0) := by positivity
  have hb : 0 < 16 * L0 * h0 := by positivity
  have hd : 0 ≤ 5 * L1 ^ 2 * Δ / (4 * L0) := by positivity
  have he : 0 ≤ 80 * L1 ^ 2 * Δ * h0 := by positivity
  have hP : 0 ≤ (2 + 13 * L1 * R) ^ 2 * (1 / (64 * L0 * h0) + 1 / 4 + 5 * L1 ^ 2 * Δ / (4 * L0)) := by
    positivity
  have hQ : 0 < (2 + 13 * L1 * R) ^ 2 * (1 + 16 * L0 * h0 + 80 * L1 ^ 2 * Δ * h0) := by positivity
  have hPS := mul_le_mul_of_nonneg_left
    (show 1 / (64 * L0 * h0) + 1 / 4 + 5 * L1 ^ 2 * Δ / (4 * L0) ≤
      2 + 1 / (64 * L0 * h0) + 16 * L0 * h0 + 5 * L1 ^ 2 * Δ / (4 * L0) + 80 * L1 ^ 2 * Δ * h0 by
        linarith) hσ.le
  have hQS := mul_le_mul_of_nonneg_left
    (show 1 + 16 * L0 * h0 + 80 * L1 ^ 2 * Δ * h0 ≤
      2 + 1 / (64 * L0 * h0) + 16 * L0 * h0 + 5 * L1 ^ 2 * Δ / (4 * L0) + 80 * L1 ^ 2 * Δ * h0 by
        linarith) hσ.le
  have h1 := Real.log_le_log (by linarith :
      0 < 1 + (2 + 13 * L1 * R) ^ 2 * (1 / (64 * L0 * h0) + 1 / 4 + 5 * L1 ^ 2 * Δ / (4 * L0)))
    (by linarith : _ ≤ 1 + (2 + 13 * L1 * R) ^ 2 *
      (2 + 1 / (64 * L0 * h0) + 16 * L0 * h0 + 5 * L1 ^ 2 * Δ / (4 * L0) + 80 * L1 ^ 2 * Δ * h0))
  have h2 := Real.log_le_log hQ
    (by linarith : _ ≤ 1 + (2 + 13 * L1 * R) ^ 2 *
      (2 + 1 / (64 * L0 * h0) + 16 * L0 * h0 + 5 * L1 ^ 2 * Δ / (4 * L0) + 80 * L1 ^ 2 * Δ * h0))
  have hLg : 0 ≤ Real.log (1 + (2 + 13 * L1 * R) ^ 2 *
      (2 + 1 / (64 * L0 * h0) + 16 * L0 * h0 + 5 * L1 ^ 2 * Δ / (4 * L0) + 80 * L1 ^ 2 * Δ * h0)) :=
    Real.log_nonneg (by linarith)
  generalize Real.log (1 + (2 + 13 * L1 * R) ^ 2 *
      (2 + 1 / (64 * L0 * h0) + 16 * L0 * h0 + 5 * L1 ^ 2 * Δ / (4 * L0) + 80 * L1 ^ 2 * Δ * h0)) =
    Lg at h1 h2 hLg ⊢
  have h3 : Real.logb 2 ((2 + 13 * L1 * R) ^ 2 * (1 + 16 * L0 * h0 + 80 * L1 ^ 2 * Δ * h0)) ≤
      2 * Lg := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
    have hl2 := Real.log_two_gt_d9
    have := mul_nonneg hLg (by linarith : (0 : ℝ) ≤ Real.log 2 - 1 / 2)
    linarith
  have h4 := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 2 * (3 + 13 * L1 * R))
  have h5 := mul_nonneg ht hLg
  linarith

end OracleTemplate.ParameterFreeGeneralized
