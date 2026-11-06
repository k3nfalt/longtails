import LongTails.Algorithms.RecoveryFractalGd
import LongTails.Proofs.FractalChebyshevSchedule
import LongTails.Proofs.Execution

namespace LongTails.Proofs.RecoveryFractalExecution

open OracleTemplate
open LongTails.Setups.SmoothHessianLipschitzGd
open LongTails.Algorithms.RecoveryFractalGd

lemma blockLength_pos (p : Params) : 0 < blockLength p := by
  unfold blockLength
  positivity

lemma lowerCurvature_pos (p : Params) (hL : 0 < p.L) : 0 < lowerCurvature p := by
  unfold lowerCurvature
  have hn : (0 : ℝ) < blockLength p := by exact_mod_cast blockLength_pos p
  positivity

lemma lowerCurvature_lt (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p) :
    lowerCurvature p < p.L := by
  have hn : 4 ≤ blockLength p := by
    unfold blockLength
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ level p := Nat.pow_le_pow_right (by norm_num) hk
  have hn' : (4 : ℝ) ≤ blockLength p := by exact_mod_cast hn
  unfold lowerCurvature
  exact div_lt_self hL (by nlinarith)

lemma fractalStep_pos (p : Params) (hL : 0 < p.L) (hk : 2 ≤ level p) (i : ℕ) :
    0 < fractalStep p i := by
  unfold fractalStep
  exact (one_div_pos.mpr hL).trans_le
    (FractalChebyshev.stepOf_bounds (lowerCurvature_pos p hL) (lowerCurvature_lt p hL hk) _).1

lemma rule_pos (p : Params) (hL : 0 < p.L) (c : Control) (reply : p.E) :
    0 < (rule p c reply).1 := by
  unfold rule
  split_ifs
  all_goals first | exact one_div_pos.mpr hL | exact fractalStep_pos p hL (by omega) _

lemma allowed (p : Params) (hL : 0 < p.L) : adaptiveGdFamily p (method p) :=
  ⟨State.point, State.best, State.bestNorm, State.count, fun s r => (rule p s.control r).1,
    fun s r => rule_pos p hL s.control r, fun _ => ⟨rfl, rfl, rfl⟩, fun _ => rfl,
    fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ => rfl⟩

noncomputable def traj (p : Params) (f : p.E → ℝ) (t : ℕ) : State p.E :=
  (fun s => (method p).update s (gradient f ((method p).query s).2))^[t]
    ((method p).initial ())

lemma traj_succ (p : Params) (f : p.E → ℝ) (t : ℕ) :
    traj p f (t + 1) = (method p).update (traj p f t) (gradient f (traj p f t).point) := by
  unfold traj
  rw [Function.iterate_succ_apply']
  rfl

lemma traj_count (p : Params) (f : p.E → ℝ) (t : ℕ) : (traj p f t).count = t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [traj_succ]; simp [method, ih]

lemma traj_zero (p : Params) (f : p.E → ℝ) :
    traj p f 0 = ⟨p.x0, p.x0, 0, 0, idle⟩ := rfl

lemma traj_point (p : Params) (f : p.E → ℝ) (t : ℕ) :
    (traj p f (t + 1)).point = (traj p f t).point -
      (rule p (traj p f t).control (gradient f (traj p f t).point)).1 •
        gradient f (traj p f t).point := by
  rw [traj_succ]
  rfl

lemma traj_best (p : Params) (f : p.E → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    ‖gradient f (traj p f t).best‖ ^ 2 = (traj p f t).bestNorm ∧
      ∀ i < t, (traj p f t).bestNorm ≤ ‖gradient f (traj p f i).point‖ ^ 2 := by
  induction t with
  | zero => omega
  | succ t ih =>
    rw [traj_succ]
    rcases Nat.eq_zero_or_pos t with rfl | ht'
    · simp only [method, traj_zero, true_or, ite_true]
      refine ⟨trivial, fun i hi => ?_⟩
      have : i = 0 := by omega
      subst i
      simp [traj_zero]
    · obtain ⟨h1, h2⟩ := ih ht'
      have hc : (traj p f t).count ≠ 0 := by rw [traj_count]; omega
      simp only [method, hc, false_or]
      split_ifs with hle
      · refine ⟨rfl, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact hle.trans (h2 i hi)
        · exact le_rfl
      · refine ⟨h1, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact h2 i hi
        · exact (lt_of_not_ge hle).le

lemma execute_eq_best (p : Params) (f : p.E → ℝ) (O : Oracle p.E p.E)
    (hO : ∀ history x seed, O.answer history (0, x) seed = gradient f x)
    (K : ℕ) (seed : (method p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (method p) (fun _ => K) seed ξ = (traj p f K).best := by
  rw [execute_eq_of_answer_eq O (gradient f) hO, execute_iterate]
  rfl

lemma execute_gradient_le (p : Params) (f : p.E → ℝ) (O : Oracle p.E p.E)
    (hO : ∀ history x seed, O.answer history (0, x) seed = gradient f x)
    (K i : ℕ) (hi : i < K) (seed : (method p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    ‖gradient f (execute O (method p) (fun _ => K) seed ξ)‖ ^ 2 ≤
      ‖gradient f (traj p f i).point‖ ^ 2 := by
  rw [execute_eq_best p f O hO K seed ξ]
  obtain ⟨he, hb⟩ := traj_best p f K (by omega)
  rw [he]
  exact hb i hi

lemma rule_trial (p : Params) (hk : 2 ≤ level p) (i : ℕ) (hi : i < 2 * epochLength p)
    (reply : p.E) (hg : ‖reply‖ ≤ if i = 0 then threshold p else 8 * threshold p) :
    rule p ⟨i, false, 0⟩ reply = (fractalStep p i, ⟨i + 1, false, 0⟩) := by
  by_cases h0 : i = 0
  · subst i
    simp only [ite_true] at hg
    simp [rule, not_lt.mpr hk, not_lt.mpr hg]
  · simp only [h0, ite_false] at hg
    simp [rule, not_lt.mpr hk, h0, not_lt.mpr hg, not_le.mpr hi]

lemma rule_trial_start (p : Params) (hk : 2 ≤ level p) (hG : 0 ≤ threshold p)
    (c : Control) (hr : c.recovering = false) (hc : c.phase = 0 ∨ 2 * epochLength p ≤ c.phase)
    (reply : p.E) (hg : ‖reply‖ ≤ threshold p) :
    rule p c reply = (fractalStep p 0, ⟨1, false, 0⟩) := by
  have hg8 : ‖reply‖ ≤ 8 * threshold p := by linarith
  simp [rule, not_lt.mpr hk, hr, not_lt.mpr hg8, hc, not_lt.mpr hg]

lemma trial_trace (p : Params) (hk : 2 ≤ level p) (hG : 0 ≤ threshold p)
    (f : p.E → ℝ) (T t : ℕ) (ht : t ≤ 2 * epochLength p)
    (hr : (traj p f T).control.recovering = false)
    (hc : (traj p f T).control.phase = 0 ∨ 2 * epochLength p ≤ (traj p f T).control.phase)
    (h0 : ‖gradient f (traj p f T).point‖ ≤ threshold p)
    (hg : ∀ i < t, ‖gradient f (traj p f (T + i)).point‖ ≤ 8 * threshold p) :
    (∀ i, 1 ≤ i → i ≤ t → (traj p f (T + i)).control = ⟨i, false, 0⟩) ∧
    (∀ i < t, (traj p f (T + (i + 1))).point = (traj p f (T + i)).point -
      fractalStep p i • gradient f (traj p f (T + i)).point) := by
  have hstart := rule_trial_start p hk hG (traj p f T).control hr hc
    (gradient f (traj p f T).point) h0
  have hphase (i : ℕ) (hi : i < t) :
      rule p ⟨i, false, 0⟩ (gradient f (traj p f (T + i)).point) =
        (fractalStep p i, ⟨i + 1, false, 0⟩) := by
    apply rule_trial p hk i (hi.trans_le ht)
    by_cases he : i = 0
    · subst i
      simpa using h0
    · simpa [he] using hg i hi
  have hcontrol (i : ℕ) (hi0 : 1 ≤ i) (hi : i ≤ t) :
      (traj p f (T + i)).control = ⟨i, false, 0⟩ := by
    induction i with
    | zero => omega
    | succ i ih =>
      rw [show T + (i + 1) = (T + i) + 1 by omega, traj_succ]
      change (rule p (traj p f (T + i)).control (gradient f (traj p f (T + i)).point)).2 = _
      by_cases he : i = 0
      · subst i
        simpa using congrArg Prod.snd hstart
      · rw [ih (by omega) (by omega), hphase i (by omega)]
  refine ⟨hcontrol, ?_⟩
  intro i hi
  rw [show T + (i + 1) = (T + i) + 1 by omega, traj_point]
  by_cases he : i = 0
  · subst i
    simp only [Nat.add_zero, hstart]
  · rw [hcontrol i (by omega) hi.le, hphase i hi]

noncomputable def recoveryEnergy (p : Params) (f : p.E → ℝ) (T n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ‖gradient f (traj p f (T + i)).point‖ ^ 2

lemma recoveryEnergy_zero (p : Params) (f : p.E → ℝ) (T : ℕ) : recoveryEnergy p f T 0 = 0 := by
  simp [recoveryEnergy]

lemma recoveryEnergy_succ (p : Params) (f : p.E → ℝ) (T n : ℕ) :
    recoveryEnergy p f T (n + 1) = recoveryEnergy p f T n +
      ‖gradient f (traj p f (T + n)).point‖ ^ 2 := by
  exact Finset.sum_range_succ _ _

lemma rule_recovery (p : Params) (hk : 2 ≤ level p) (c : Control)
    (hr : c.recovering = true) (reply : p.E) :
    rule p c reply = (1 / p.L, recoveryControl p (c.recoverySum + ‖reply‖ ^ 2)) := by
  simp [rule, not_lt.mpr hk, hr]

lemma rule_abort (p : Params) (hk : 2 ≤ level p) (c : Control)
    (hr : c.recovering = false) (hc : c.phase ≠ 0) (reply : p.E)
    (hg : 8 * threshold p < ‖reply‖) :
    rule p c reply = (1 / p.L, recoveryControl p (‖reply‖ ^ 2)) := by
  simp [rule, not_lt.mpr hk, hr, hc, hg]

lemma rule_recovery_control (p : Params) (hk : 2 ≤ level p) (s : ℝ)
    (hs : s < recoveryTarget p) (reply : p.E) :
    rule p (recoveryControl p s) reply = (1 / p.L, recoveryControl p (s + ‖reply‖ ^ 2)) := by
  have he : recoveryControl p s = ⟨0, true, s⟩ := by
    simp [recoveryControl, not_le.mpr hs]
  rw [he]
  exact rule_recovery p hk _ rfl reply

lemma recovery_trace (p : Params) (hk : 2 ≤ level p) (f : p.E → ℝ) (T n : ℕ)
    (hstart : rule p (traj p f T).control (gradient f (traj p f T).point) =
      (1 / p.L, recoveryControl p (‖gradient f (traj p f T).point‖ ^ 2)))
    (hsmall : ∀ i, 1 ≤ i → i < n → recoveryEnergy p f T i < recoveryTarget p) :
    (∀ i, 1 ≤ i → i ≤ n →
      (traj p f (T + i)).control = recoveryControl p (recoveryEnergy p f T i)) ∧
    (∀ i < n, (traj p f (T + (i + 1))).point = (traj p f (T + i)).point -
      (1 / p.L) • gradient f (traj p f (T + i)).point) := by
  have hcontrol (i : ℕ) (hi0 : 1 ≤ i) (hi : i ≤ n) :
      (traj p f (T + i)).control = recoveryControl p (recoveryEnergy p f T i) := by
    induction i with
    | zero => omega
    | succ i ih =>
      rw [show T + (i + 1) = (T + i) + 1 by omega, traj_succ]
      change (rule p (traj p f (T + i)).control (gradient f (traj p f (T + i)).point)).2 = _
      by_cases he : i = 0
      · subst i
        simpa [recoveryEnergy_succ, recoveryEnergy_zero] using congrArg Prod.snd hstart
      · rw [ih (by omega) (by omega), rule_recovery_control p hk _
          (hsmall i (by omega) (by omega)), recoveryEnergy_succ]
  refine ⟨hcontrol, ?_⟩
  intro i hi
  rw [show T + (i + 1) = (T + i) + 1 by omega, traj_point]
  by_cases he : i = 0
  · subst i
    simp only [Nat.add_zero, hstart]
  · rw [hcontrol i (by omega) hi.le, rule_recovery_control p hk _
      (hsmall i (by omega) hi)]

end LongTails.Proofs.RecoveryFractalExecution
