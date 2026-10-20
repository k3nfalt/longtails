import LongTails.Proofs.NonEuclideanExtragradientStep
import LongTails.Proofs.Execution

namespace LongTails.Proofs.NonEuclideanExtragradientRun

open LongTails.Setups.NonEuclideanWeakMinty
open LongTails.Algorithms.NonEuclideanExtragradient
open LongTails.Proofs.NonEuclideanExtragradientStep
open LongTails.Proofs.NonEuclideanWeakMintyGeometry

noncomputable def advance (d : Public) (F : d.E → d.E →L[ℝ] ℝ) (s : State d) : State d :=
  step d s (F (if s.correction then s.y else s.x))

lemma advance_twice (d : Public) (F : d.E → d.E →L[ℝ] ℝ) (s : State d)
    (hs : s.correction = false) :
    advance d F (advance d F s) =
      { s with
        x := mirror d s.x (F (predictor d s.x (F s.x)))
        y := predictor d s.x (F s.x)
        best := if s.seen = false ∨ ‖F s.x‖ ≤ s.bestNorm then s.x else s.best
        bestNorm := if s.seen = false ∨ ‖F s.x‖ ≤ s.bestNorm then ‖F s.x‖ else s.bestNorm
        seen := true
        correction := false } := by
  classical
  simp [advance, step, hs]

noncomputable def state (d : Public) (F : d.E → d.E →L[ℝ] ℝ) (n : ℕ) : State d :=
  (advance d F)^[2 * n] ⟨d.x0, d.x0, d.x0, 0, false, false⟩

lemma state_zero (d : Public) (F : d.E → d.E →L[ℝ] ℝ) :
    state d F 0 = ⟨d.x0, d.x0, d.x0, 0, false, false⟩ := rfl

lemma state_succ (d : Public) (F : d.E → d.E →L[ℝ] ℝ) (n : ℕ) :
    state d F (n + 1) = advance d F (advance d F (state d F n)) := by
  simp only [state, Nat.mul_add, Nat.mul_one, Function.iterate_succ_apply']

lemma state_phase (d : Public) (F : d.E → d.E →L[ℝ] ℝ) (n : ℕ) :
    (state d F n).correction = false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [state_succ, advance_twice d F _ ih]

lemma state_seen (d : Public) (F : d.E → d.E →L[ℝ] ℝ) (n : ℕ) :
    (state d F (n + 1)).seen = true := by
  rw [state_succ, advance_twice d F _ (state_phase d F n)]

lemma state_best_norm (d : Public) (F : d.E → d.E →L[ℝ] ℝ) (n : ℕ) :
    (state d F (n + 1)).bestNorm = ‖F (state d F (n + 1)).best‖ := by
  classical
  induction n with
  | zero =>
    rw [state_succ, advance_twice d F _ (state_phase d F 0)]
    simp [state_zero]
  | succ n ih =>
    rw [state_succ, advance_twice d F _ (state_phase d F (n + 1))]
    dsimp only
    split_ifs with h
    · rfl
    · exact ih

lemma state_best_nonneg (d : Public) (F : d.E → d.E →L[ℝ] ℝ) (n : ℕ) :
    0 ≤ (state d F n).bestNorm := by
  cases n with
  | zero => exact le_refl 0
  | succ n => rw [state_best_norm]; exact norm_nonneg _

lemma state_energy (d : Public) (hd : d.Valid) (F : d.E → d.E →L[ℝ] ℝ)
    (hlip : ∀ x y, ‖F x - F y‖ ≤ d.L * ‖x - y‖)
    (u : d.E) (hminty : ∀ x, -d.ρ * ‖F x‖ ^ 2 ≤ F x (x - u)) (n : ℕ) :
    d.bregman u (state d F n).x +
      (n : ℝ) * (d.μ / (400 * d.L ^ 2)) * (state d F n).bestNorm ^ 2 ≤
      d.bregman u d.x0 := by
  classical
  induction n with
  | zero => simp [state_zero]
  | succ n ih =>
    have hnew : (state d F (n + 1)).bestNorm ≤ ‖F (state d F n).x‖ := by
      rw [state_succ, advance_twice d F _ (state_phase d F n)]
      dsimp only
      split_ifs with h
      · exact le_refl _
      · exact (not_le.mp (not_or.mp h).2).le
    have hold : n = 0 ∨ (state d F (n + 1)).bestNorm ≤ (state d F n).bestNorm := by
      by_cases hn : n = 0
      · exact Or.inl hn
      · right
        rw [state_succ, advance_twice d F _ (state_phase d F n)]
        dsimp only
        split_ifs with h
        · rcases h with h | h
          · cases n with
            | zero => contradiction
            | succ k => simp [state_seen] at h
          · exact h
        · exact le_refl _
    have hstep : d.bregman u (state d F (n + 1)).x ≤
        d.bregman u (state d F n).x -
          d.μ / (400 * d.L ^ 2) * ‖F (state d F n).x‖ ^ 2 := by
      rw [state_succ, advance_twice d F _ (state_phase d F n)]
      exact step_descent d hd F hlip u hminty _
    have hc : 0 ≤ d.μ / (400 * d.L ^ 2) :=
      div_nonneg hd.2.2.2.1.le (mul_nonneg (by norm_num) (sq_nonneg _))
    have he := running_best_energy n hc (norm_nonneg _) (state_best_nonneg d F n)
      (state_best_nonneg d F (n + 1)) hnew hold hstep
    push_cast
    exact he.trans ih

lemma state_accuracy (d : Public) (hd : d.Valid) (F : d.E → d.E →L[ℝ] ℝ)
    (hlip : ∀ x y, ‖F x - F y‖ ≤ d.L * ‖x - y‖)
    (u : d.E) (hminty : ∀ x, -d.ρ * ‖F x‖ ^ 2 ≤ F x (x - u))
    {D ε : ℝ} (hD : d.bregman u d.x0 ≤ D) (hε : 0 < ε)
    (n : ℕ) (hn : 0 < n) (hbudget : 400 * d.L ^ 2 * D / (d.μ * ε ^ 2) ≤ n) :
    ‖F (state d F n).best‖ ≤ ε := by
  have hL := hd.1
  have hμ := hd.2.2.2.1
  have he := state_energy d hd F hlip u hminty n
  have hnonneg : 0 ≤ d.bregman u (state d F n).x :=
    (mul_nonneg (div_nonneg hμ.le (by norm_num)) (sq_nonneg _)).trans
      (hd.2.2.2.2.2 _ _)
  have hnorm : (state d F n).bestNorm = ‖F (state d F n).best‖ := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact state_best_norm d F k
  rw [hnorm] at he
  have hfactor : 0 < (n : ℝ) * (d.μ / (400 * d.L ^ 2)) := by positivity
  have htarget : D ≤ (n : ℝ) * (d.μ / (400 * d.L ^ 2)) * ε ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hbudget
      (show 0 ≤ d.μ / (400 * d.L ^ 2) * ε ^ 2 by positivity)
    have heq : (400 * d.L ^ 2 * D / (d.μ * ε ^ 2)) *
        (d.μ / (400 * d.L ^ 2) * ε ^ 2) = D := by
      field_simp
    rw [heq] at hh
    nlinarith only [hh]
  have hs : ‖F (state d F n).best‖ ^ 2 ≤ ε ^ 2 := by
    apply (mul_le_mul_iff_right₀ hfactor).mp
    linarith
  exact (sq_le_sq₀ (norm_nonneg _) hε.le).mp hs

lemma execute_accuracy (d : Public) (hd : d.Valid) (F : d.E → d.E →L[ℝ] ℝ)
    (hlip : ∀ x y, ‖F x - F y‖ ≤ d.L * ‖x - y‖)
    (u : d.E) (hminty : ∀ x, -d.ρ * ‖F x‖ ^ 2 ≤ F x (x - u))
    {D ε : ℝ} (hD : d.bregman u d.x0 ≤ D) (hε : 0 < ε)
    (n : ℕ) (hn : 0 < n) (hbudget : 400 * d.L ^ 2 * D / (d.μ * ε ^ 2) ≤ n)
    (O : OracleTemplate.Oracle d.E (d.E →L[ℝ] ℝ))
    (hO : ∀ k seed x, O.answer k (0, x) seed = F x)
    (seed : (algorithm d).Seed) (ξ : (k : ℕ) → O.Seed k) :
    ‖F (OracleTemplate.execute O (algorithm d) (fun _ => 2 * n) seed ξ)‖ ≤ ε := by
  rw [OracleTemplate.execute_eq_of_answer_eq O F (fun k x seed => hO k seed x),
    OracleTemplate.execute_iterate]
  exact state_accuracy d hd F hlip u hminty hD hε n hn hbudget

end LongTails.Proofs.NonEuclideanExtragradientRun
