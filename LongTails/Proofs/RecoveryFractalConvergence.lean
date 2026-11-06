import LongTails.Proofs.RecoveryFractalCompleted

namespace LongTails.Proofs.RecoveryFractalConvergence

open OracleTemplate
open LongTails.Setups.SmoothHessianLipschitzGd LongTails.Algorithms.RecoveryFractalGd
open LongTails.Proofs.RecoveryFractalExecution

noncomputable def Ready (p : Params) (f : p.E → ℝ) (T : ℕ) : Prop :=
  (traj p f T).control = idle ∨
    ((traj p f T).control = ⟨2 * epochLength p, false, 0⟩ ∧
      ‖gradient f (traj p f T).point‖ ≤ 8 * threshold p)

lemma ready_zero (p : Params) (f : p.E → ℝ) : Ready p f 0 := by
  exact Or.inl rfl

lemma ready_entrance (p : Params) (f : p.E → ℝ) (T : ℕ) (h : Ready p f T) :
    (traj p f T).control.recovering = false ∧
      ((traj p f T).control.phase = 0 ∨ 2 * epochLength p ≤ (traj p f T).control.phase) := by
  rcases h with h | ⟨h, _⟩ <;> simp [h, idle]

lemma ready_plain_rule (p : Params) (hk : 2 ≤ level p) (f : p.E → ℝ) (T : ℕ)
    (h : Ready p f T) (hg : threshold p < ‖gradient f (traj p f T).point‖) :
    rule p (traj p f T).control (gradient f (traj p f T).point) = (1 / p.L, idle) := by
  rcases h with h | ⟨h, hgate⟩
  · simp [h, rule, idle, not_lt.mpr hk, hg]
  · simp [h, rule, not_lt.mpr hk, not_lt.mpr hgate, hg]

lemma ready_plain_step (p : Params) (hk : 2 ≤ level p) (f : p.E → ℝ) (T : ℕ)
    (h : Ready p f T) (hg : threshold p < ‖gradient f (traj p f T).point‖) :
    (traj p f (T + 1)).control = idle ∧
      (traj p f (T + 1)).point = (traj p f T).point - (1 / p.L) • gradient f (traj p f T).point := by
  have hh := ready_plain_rule p hk f T h hg
  constructor
  · rw [traj_succ]
    change (rule p (traj p f T).control (gradient f (traj p f T).point)).2 = idle
    rw [hh]
  · rw [traj_point, hh]

lemma plain_group_decrease (p : Params) (hL : 0 < p.L) (hG : 0 ≤ threshold p)
    (hk : 2 ≤ level p) (f : p.E → ℝ) (hf : Differentiable ℝ f)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (T : ℕ) (h : Ready p f T) (hg : threshold p < ‖gradient f (traj p f T).point‖) :
    Ready p f (T + 1) ∧ f (traj p f (T + 1)).point - f (traj p f T).point ≤
      -(threshold p ^ 2) / (2 * p.L) := by
  obtain ⟨hcontrol, hpoint⟩ := ready_plain_step p hk f T h hg
  refine ⟨Or.inl hcontrol, ?_⟩
  rw [hpoint]
  have hd := OracleTemplate.Gradient.descent hL (fun x => (hf x).hasGradientAt) hlip (traj p f T).point
  have hs := pow_le_pow_left₀ hG hg.le 2
  have hm := mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr hL.le)
  simp only [div_eq_mul_inv, mul_inv_rev] at hd ⊢
  norm_num at hd ⊢
  nlinarith only [hd, hm]

open LongTails.Proofs.RecoveryFractalTuning LongTails.Proofs.RecoveryFractalRecovery
open LongTails.Proofs.RecoveryFractalCompleted

noncomputable def progressRate (p : Params) : ℝ :=
  (blockLength p : ℝ) * p.ε ^ 2 / (1024 * repetitions p * p.L)

noncomputable def maxGroup (p : Params) : ℕ := 2 * epochLength p + recoveryLength p

lemma progressRate_pos (p : Params) (hL : 0 < p.L) (hε : 0 < p.ε) : 0 < progressRate p := by
  have hn : 0 < (blockLength p : ℝ) := by exact_mod_cast blockLength_pos p
  unfold progressRate repetitions
  positivity

lemma progressRate_le_plain (p : Params) (hL : 0 < p.L) :
    progressRate p ≤ threshold p ^ 2 / (2 * p.L) := by
  have hG : threshold p ^ 2 = (blockLength p : ℝ) * p.ε ^ 2 := by
    simp [threshold, mul_pow, Real.sq_sqrt (Nat.cast_nonneg (blockLength p))]
  have hm : (1 : ℝ) ≤ repetitions p := by
    have hh : 1 ≤ repetitions p := by unfold repetitions; omega
    exact_mod_cast hh
  unfold progressRate
  rw [← hG]
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  have hh := mul_le_mul_of_nonneg_right hm hL.le
  nlinarith

lemma progressRate_le_recovery (p : Params) (hL : 0 < p.L) :
    progressRate p ≤ threshold p ^ 2 / p.L := by
  apply (progressRate_le_plain p hL).trans
  exact div_le_div_of_nonneg_left (sq_nonneg _) hL (by linarith)

lemma completed_progress_identity (p : Params) (hL : 0 < p.L) :
    (2 * epochLength p : ℝ) * progressRate p = p.ε ^ 2 / (512 * lowerCurvature p) := by
  have hn : (blockLength p : ℝ) ≠ 0 := by exact_mod_cast (blockLength_pos p).ne'
  have hm : (repetitions p : ℝ) ≠ 0 := by unfold repetitions; positivity
  unfold progressRate lowerCurvature epochLength
  push_cast
  field_simp
  ring

lemma one_group_progress (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ) (hε : 0 < p.ε)
    (hk : 2 ≤ level p) (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (T : ℕ) (hready : Ready p f T)
    (hfail : ∀ i ≤ maxGroup p, p.ε < ‖gradient f (traj p f (T + i)).point‖) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ maxGroup p ∧ Ready p f (T + d) ∧
      f (traj p f (T + d)).point ≤ f (traj p f T).point - progressRate p * d := by
  classical
  have hG : 0 ≤ threshold p := by unfold threshold; positivity
  have hN : 0 < epochLength p := by
    unfold epochLength repetitions
    exact Nat.mul_pos (blockLength_pos p) (by omega)
  have hB : 1 ≤ maxGroup p := by unfold maxGroup; have hh := recoveryLength_pos p; omega
  by_cases hplain : threshold p < ‖gradient f (traj p f T).point‖
  · obtain ⟨hnext, hdec⟩ := plain_group_decrease p hL hG hk f
      (hf.differentiable (by norm_num)) hlip T hready hplain
    refine ⟨1, by omega, hB, hnext, ?_⟩
    have hh := progressRate_le_plain p hL
    norm_num
    simp only [div_eq_mul_inv] at hh hdec
    linarith
  · have h0 := le_of_not_gt hplain
    obtain ⟨hr, hc⟩ := ready_entrance p f T hready
    by_cases hex : ∃ i, 1 ≤ i ∧ i ≤ 2 * epochLength p ∧
        8 * threshold p < ‖gradient f (traj p f (T + i)).point‖
    · let t := Nat.find hex
      obtain ⟨ht0, ht, habort⟩ := Nat.find_spec hex
      have hgate (i : ℕ) (hi : i < t) : ‖gradient f (traj p f (T + i)).point‖ ≤ 8 * threshold p := by
        by_cases hi0 : i = 0
        · subst i
          simp only [Nat.add_zero]
          linarith
        · by_contra hh
          have hle := Nat.find_min' hex ⟨by omega, by omega, lt_of_not_ge hh⟩
          change t ≤ i at hle
          omega
      obtain ⟨n, hn0, hnM, hcontrol, hdec⟩ := aborted_trial_recovers_tuned p hL hρ hk hε f hf hH hlip
        T t ht0 ht hr hc h0 hgate habort
      refine ⟨t + n, by omega, ?_, ?_, ?_⟩
      · unfold maxGroup
        omega
      · apply Or.inl
        simpa only [Nat.add_assoc] using hcontrol
      · have hh := mul_le_mul_of_nonneg_left (progressRate_le_recovery p hL)
          (show 0 ≤ ((t + n : ℕ) : ℝ) by positivity)
        simp only [Nat.add_assoc] at hdec
        simp only [div_eq_mul_inv] at hh hdec
        nlinarith only [hh, hdec]
    · have hgate (i : ℕ) (hi : i ≤ 2 * epochLength p) :
          ‖gradient f (traj p f (T + i)).point‖ ≤ 8 * threshold p := by
        by_cases hi0 : i = 0
        · subst i
          simp only [Nat.add_zero]
          linarith
        · by_contra hh
          exact hex ⟨i, by omega, hi, lt_of_not_ge hh⟩
      have hm := hfail (epochLength p) (by unfold maxGroup; omega)
      obtain ⟨hcontrol, hdec⟩ := completed_trial_execution_tuned p hL hρ hε.le hk f hf hH hlip
        T hr hc (fun i hi => hgate i hi.le) h0 hm
      refine ⟨2 * epochLength p, by omega, by unfold maxGroup; omega, Or.inr ⟨hcontrol, hgate _ le_rfl⟩, ?_⟩
      have hh := completed_progress_identity p hL
      push_cast
      simp only [div_eq_mul_inv] at hh hdec
      nlinarith only [hh, hdec]

lemma finite_progress_impossible (V : ℕ → ℝ) (Ready : ℕ → Prop) (r Δ : ℝ)
    (hr : 0 < r) (Q B : ℕ) (hQ : Δ ≤ r * Q)
    (hgap : ∀ t, V 0 - Δ ≤ V t) (hstart : Ready 0)
    (hstep : ∀ t ≤ Q, Ready t → ∃ d : ℕ, 1 ≤ d ∧ d ≤ B ∧ Ready (t + d) ∧
      V (t + d) ≤ V t - r * d) : False := by
  classical
  let Good := fun t => t ≤ Q + B ∧ Ready t ∧ V t ≤ V 0 - r * t
  let M := Nat.findGreatest Good (Q + B)
  have h0 : Good 0 := by simp [Good, hstart]
  have hM : Good M := Nat.findGreatest_spec (Nat.zero_le _) h0
  have hnot : ¬ M ≤ Q := by
    intro hMQ
    obtain ⟨d, hd0, hdB, hdReady, hdV⟩ := hstep M hMQ hM.2.1
    have hnext : Good (M + d) := by
      refine ⟨by omega, hdReady, ?_⟩
      have hh := hM.2.2
      push_cast
      linarith
    have hmax := Nat.le_findGreatest (show M + d ≤ Q + B by omega) hnext
    change M + d ≤ M at hmax
    omega
  have hQM : (Q : ℝ) < M := by exact_mod_cast (show Q < M by omega)
  have hstrict := mul_lt_mul_of_pos_left hQM hr
  have hval := hM.2.2
  have hbound := hgap M
  linarith

noncomputable def selectedBudget (p : Params) : ℕ := ⌈p.Δ / progressRate p⌉₊ + maxGroup p + 1

lemma selected_stationarity (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ) (hε : 0 < p.ε)
    (hk : 2 ≤ level p) (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ) :
    ∃ i < selectedBudget p, ‖gradient f (traj p f i).point‖ ≤ p.ε := by
  classical
  by_contra hn
  push Not at hn
  have hr := progressRate_pos p hL hε
  have hQ : p.Δ ≤ progressRate p * (⌈p.Δ / progressRate p⌉₊ : ℝ) := by
    have hh := (div_le_iff₀ hr).mp (Nat.le_ceil (p.Δ / progressRate p))
    nlinarith only [hh]
  apply finite_progress_impossible (fun t => f (traj p f t).point) (Ready p f)
    (progressRate p) p.Δ hr ⌈p.Δ / progressRate p⌉₊ (maxGroup p) hQ
    (fun t => by
      have hh := hgap (traj p f t).point
      rw [traj_zero]
      dsimp only
      linarith) (ready_zero p f)
  intro T hT hReady
  apply one_group_progress p hL hρ hε hk f hf hH hlip T hReady
  intro i hi
  apply hn (T + i)
  unfold selectedBudget
  omega

lemma selected_output_accuracy (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ) (hε : 0 < p.ε)
    (hk : 2 ≤ level p) (f : p.E → ℝ) (hf : ContDiff ℝ 2 f)
    (hH : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ) (O : Oracle p.E p.E)
    (hO : ∀ history x seed, O.answer history (0, x) seed = gradient f x)
    (K : ℕ) (hK : selectedBudget p ≤ K) (seed : (method p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    ‖gradient f (execute O (method p) (fun _ => K) seed ξ)‖ ≤ p.ε := by
  obtain ⟨i, hi, hg⟩ := selected_stationarity p hL hρ hε hk f hf hH hlip hgap
  have hh := execute_gradient_le p f O hO K i (hi.trans_le hK) seed ξ
  have hs := pow_le_pow_left₀ (norm_nonneg _) hg 2
  nlinarith [norm_nonneg (gradient f (execute O (method p) (fun _ => K) seed ξ))]

lemma fallback_stationarity (p : Params) (hL : 0 < p.L) (hε : 0 < p.ε)
    (hk : level p < 2) (f : p.E → ℝ) (hf : Differentiable ℝ f)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ) (K : ℕ)
    (hK : 2 * p.L * p.Δ / p.ε ^ 2 < K) :
    ∃ i < K, ‖gradient f (traj p f i).point‖ ≤ p.ε := by
  classical
  by_contra hn
  push Not at hn
  have hstep (i : ℕ) (_ : i < K) : (traj p f (i + 1)).point =
      (traj p f i).point - (1 / p.L) • gradient f (traj p f i).point := by
    rw [traj_point]
    simp [rule, hk]
  have hd := plain_objective_descent f hf p.L hL hlip (fun i => (traj p f i).point) K hstep
  have hsum : (K : ℝ) * p.ε ^ 2 ≤ ∑ i ∈ Finset.range K, ‖gradient f (traj p f i).point‖ ^ 2 := by
    calc
      _ = ∑ _i ∈ Finset.range K, p.ε ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i hi =>
        pow_le_pow_left₀ hε.le (hn i (Finset.mem_range.mp hi)).le 2
  have hgapK := hgap (traj p f K).point
  rw [traj_zero] at hd
  dsimp only at hd
  have hbound : (∑ i ∈ Finset.range K, ‖gradient f (traj p f i).point‖ ^ 2) / (2 * p.L) ≤ p.Δ := by
    linarith
  have hb := (div_le_iff₀ (by positivity : 0 < 2 * p.L)).mp hbound
  have hc := (div_lt_iff₀ (by positivity : 0 < p.ε ^ 2)).mp hK
  nlinarith only [hsum, hb, hc]

lemma fallback_output_accuracy (p : Params) (hL : 0 < p.L) (hε : 0 < p.ε)
    (hk : level p < 2) (f : p.E → ℝ) (hf : Differentiable ℝ f)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ p.L * ‖x - y‖)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ) (O : Oracle p.E p.E)
    (hO : ∀ history x seed, O.answer history (0, x) seed = gradient f x)
    (K : ℕ) (hK : 2 * p.L * p.Δ / p.ε ^ 2 < K)
    (seed : (method p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    ‖gradient f (execute O (method p) (fun _ => K) seed ξ)‖ ≤ p.ε := by
  obtain ⟨i, hi, hg⟩ := fallback_stationarity p hL hε hk f hf hlip hgap K hK
  have hh := execute_gradient_le p f O hO K i hi seed ξ
  have hs := pow_le_pow_left₀ (norm_nonneg _) hg 2
  nlinarith [norm_nonneg (gradient f (execute O (method p) (fun _ => K) seed ξ))]

end LongTails.Proofs.RecoveryFractalConvergence
