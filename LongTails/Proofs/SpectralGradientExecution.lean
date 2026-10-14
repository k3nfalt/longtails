import LongTails.Algorithms.SpectralGradient
import LongTails.Proofs.Execution
import Mathlib.Tactic

namespace OracleTemplate.SpectralGradient

open LongTails.Setups.MinimizerRegularHessian

lemma probePoint_zero (p : Params) (g : p.E → p.E) (x : p.E) :
    probePoint p g x 0 = x := rfl

lemma probePoint_succ (p : Params) (g : p.E → p.E) (x : p.E) (n : ℕ) :
    probePoint p g x (n + 1) = probePoint p g x n - (1 / (2 * p.L)) • g (probePoint p g x n) :=
  Function.iterate_succ_apply' _ _ _

lemma probeHistory_succ (p : Params) (g : p.E → p.E) (x : p.E) (n : ℕ) :
    probeHistory p g x (n + 1) = probeHistory p g x n ++ [g (probePoint p g x n)] := by
  simp only [probeHistory, List.ofFn_succ_last]
  rfl

lemma warmup_execution (p : Params) (g : p.E → p.E) (x : p.E) (n : ℕ) :
    (fun s : State p => update p s (g s.point))^[n] ⟨x, n, [], []⟩ =
      ⟨probePoint p g x n, 0, [], []⟩ := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have he : update p ⟨x, n + 1, [], []⟩ (g x) =
        ⟨x - (1 / (2 * p.L)) • g x, n, [], []⟩ := by simp [update]
    rw [he, ih]
    rfl

lemma probes_execution (p : Params) (g : p.E → p.E) (x : p.E) (n : ℕ)
    (hn : n ≤ Module.finrank ℝ p.E) :
    (fun s : State p => update p s (g s.point))^[n] ⟨x, 0, [], []⟩ =
      ⟨probePoint p g x n, 0, probeHistory p g x n, []⟩ := by
  induction n with
  | zero => simp [probeHistory, probePoint]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hl : (probeHistory p g x n).length < Module.finrank ℝ p.E := by
      simp only [probeHistory, List.length_ofFn]
      omega
    simp [update, hl, probePoint_succ, probeHistory_succ]

lemma corrections_execution (p : Params) (g : p.E → p.E) (x : p.E) (rs : List ℝ) :
    (fun s : State p => update p s (g s.point))^[rs.length] ⟨x, 0, [], rs⟩ =
      ⟨gradientSteps g rs x, 0, [], []⟩ := by
  induction rs generalizing x with
  | nil => rfl
  | cons η rs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    have he : update p ⟨x, 0, [], η :: rs⟩ (g x) = ⟨x - η • g x, 0, [], rs⟩ := by
      simp [update]
    rw [he, ih]
    rfl

lemma window_execution (p : Params) (g : p.E → p.E) (x : p.E) :
    (fun s : State p => update p s (g s.point))^[2 * Module.finrank ℝ p.E] ⟨x, 0, [], []⟩ =
      ⟨window p g x, 0, [], []⟩ := by
  let d := Module.finrank ℝ p.E
  have hd : 0 < d := Module.finrank_pos
  have hlen : (spectralSteps p (probeHistory p g x (d + 1))).length = d := by
    simp [spectralSteps, d]
  rw [show 2 * Module.finrank ℝ p.E = d + d by dsimp [d]; omega,
    Function.iterate_add_apply, probes_execution p g x d le_rfl]
  cases he : spectralSteps p (probeHistory p g x (d + 1)) with
  | nil => simp only [he, List.length_nil] at hlen; omega
  | cons η rs =>
    have hcount : d = rs.length + 1 := by simpa only [he, List.length_cons] using hlen.symm
    have hu : update p ⟨probePoint p g x d, 0, probeHistory p g x d, []⟩
        (g (probePoint p g x d)) =
        ⟨probePoint p g x d - η • g (probePoint p g x d), 0, [], rs⟩ := by
      have hhist : (probeHistory p g x d).length = Module.finrank ℝ p.E := by simp [probeHistory, d]
      simp only [update, hhist, Nat.lt_irrefl, ↓reduceIte]
      rw [← probeHistory_succ, he]
      rfl
    conv_lhs => arg 2; rw [hcount]
    rw [Function.iterate_succ_apply, hu, corrections_execution]
    dsimp only [d] at he ⊢
    simp only [window, he, gradientSteps]

lemma windows_execution (p : Params) (g : p.E → p.E) (x : p.E) (n : ℕ) :
    (fun s : State p => update p s (g s.point))^[n * (2 * Module.finrank ℝ p.E)] ⟨x, 0, [], []⟩ =
      ⟨(window p g)^[n] x, 0, [], []⟩ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Function.iterate_add_apply, window_execution, ih,
      Function.iterate_succ_apply]

lemma complete_execution (p : Params) (g : p.E → p.E) (w n : ℕ)
    (O : Oracle p.E p.E) (hO : ∀ k x seed, O.answer k (0, x) seed = g x)
    (seed : (spectralGradient p w).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (spectralGradient p w) (fun _ => (w + n * (2 * Module.finrank ℝ p.E))) seed ξ =
      (window p g)^[n] (probePoint p g p.x0 w) := by
  rw [execute_eq_of_answer_eq O g hO, execute_iterate]
  change ((fun s : State p => update p s (g s.point))^[w + n * (2 * Module.finrank ℝ p.E)]
    ⟨p.x0, w, [], []⟩).point = _
  rw [Nat.add_comm w, Function.iterate_add_apply, warmup_execution, windows_execution]

end OracleTemplate.SpectralGradient
