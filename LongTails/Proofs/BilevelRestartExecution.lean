import LongTails.Proofs.BilevelTrajectory
import LongTails.Proofs.BilevelExecution

namespace LongTails.Proofs.BilevelRestartExecution

open LongTails.Setups.HigherSmoothBilevel LongTails.Algorithms.BilevelAccelerated BilevelTrajectory

structure RunInvariant (p : Params) (t : Tuning) (F : p.X → ℝ) (g : p.X → p.X)
    (σ d C ε : ℝ) (n : ℕ) (s : OuterState p.X) where
  failures : ℕ
  trace : EpochTrace p t g σ s
  index_le : s.index ≤ t.K
  unfinished_index : s.finished = false → s.index < t.K
  step_count : s.finished = false → n ≤ t.K * failures + s.index
  potential : F s.start ≤ F p.x0 - (failures : ℝ) * d
  radius : ‖s.start - p.x0‖ ≤ (failures : ℝ) * C
  accuracy : s.finished = true → ‖g s.result‖ ≤ ε

noncomputable def initialInvariant (p : Params) (t : Tuning) (F : p.X → ℝ) (g : p.X → p.X)
    (σ d C ε : ℝ) (hK : 0 < t.K) : RunInvariant p t F g σ d C ε 0 (initial p.x0) where
  failures := 0
  trace := initialTrace p t g σ p.x0
  index_le := Nat.zero_le _
  unfinished_index := by simpa [initial] using hK
  step_count := by simp [initial]
  potential := by simp [initial]
  radius := by simp [initial]
  accuracy := by simp [initial]

lemma failures_bound {p : Params} {t : Tuning} {F : p.X → ℝ} {g : p.X → p.X}
    {σ d C ε Δ : ℝ} {n : ℕ} {s : OuterState p.X}
    (I : RunInvariant p t F g σ d C ε n s) (hd : 0 < d)
    (hgap : ∀ x, F p.x0 - F x ≤ Δ) : I.failures < ⌊Δ / d⌋₊ + 1 := by
  have hh : (I.failures : ℝ) * d ≤ Δ := by linarith [I.potential, hgap s.start]
  have hf : I.failures ≤ ⌊Δ / d⌋₊ := Nat.le_floor ((le_div_iff₀ hd).mpr hh)
  omega

lemma invariant_query_radius {p : Params} {t : Tuning} {F : p.X → ℝ} {g : p.X → p.X}
    {σ d C ε Δ : ℝ} {n : ℕ} {s : OuterState p.X}
    (I : RunInvariant p t F g σ d C ε n s) (hd : 0 < d) (hC : 0 ≤ C)
    (hB : 0 ≤ t.B) (hθ : 0 ≤ t.θ) (hθ1 : t.θ ≤ 1)
    (hgap : ∀ x, F p.x0 - F x ≤ Δ) :
    ‖context p t s - p.x0‖ ≤ ((⌊Δ / d⌋₊ + 1 : ℕ) : ℝ) * C + 2 * t.B := by
  cases hs : s.finished with
  | true => simp only [context, hs, ↓reduceIte, sub_self, norm_zero]; positivity
  | false =>
    have hq := query_radius I.trace hs hB hθ hθ1
    have hh : ‖context p t s - p.x0‖ ≤ ‖context p t s - s.start‖ + ‖s.start - p.x0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hf : (I.failures : ℝ) ≤ ((⌊Δ / d⌋₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast (failures_bound I hd hgap).le
    have hfC := mul_le_mul_of_nonneg_right hf hC
    linarith [I.radius]

lemma terminal_invariant {p : Params} {t : Tuning} {F : p.X → ℝ} {g : p.X → p.X}
    {σ d C ε Δ : ℝ} {s : OuterState p.X}
    (I : RunInvariant p t F g σ d C ε (t.K * (⌊Δ / d⌋₊ + 1)) s)
    (hd : 0 < d) (hgap : ∀ x, F p.x0 - F x ≤ Δ) : ‖g s.result‖ ≤ ε := by
  cases hs : s.finished with
  | true => exact I.accuracy hs
  | false =>
    have hf := failures_bound I hd hgap
    have hi := I.unfinished_index hs
    have hn := I.step_count hs
    have hh : t.K * I.failures + s.index < t.K * (I.failures + 1) := by nlinarith
    have hh' := Nat.mul_le_mul_left t.K (show I.failures + 1 ≤ ⌊Δ / d⌋₊ + 1 by omega)
    omega

noncomputable def stepInvariant {p : Params} {t : Tuning} {F : p.X → ℝ} {g : p.X → p.X}
    {σ d C ε M : ℝ} {n : ℕ} {s : OuterState p.X}
    (I : RunInvariant p t F g σ d C ε n s) (v : p.X)
    (hK : 0 < t.K) (hη : 0 ≤ t.η) (hB : 0 ≤ t.B) (hθ : 0 ≤ t.θ) (hθ1 : t.θ ≤ 1)
    (hC : C = 2 * t.B + t.η * (M + σ))
    (herr : s.finished = false → ‖v - g (context p t s)‖ ≤ σ)
    (hv : s.finished = false → ‖v‖ ≤ M + σ)
    (hdrop : s.finished = false → t.B ^ 2 < ((s.index + 1 : ℕ) : ℝ) *
      (s.movement + ‖context p t s - t.η • v - s.x‖ ^ 2) →
      F (context p t s - t.η • v) - F s.start ≤ -d)
    (hsuccess : ∀ s' : OuterState p.X, EpochTrace p t g σ s' → s'.index = t.K →
      s'.result = s'.bestOutput → ‖g s'.result‖ ≤ ε) :
    RunInvariant p t F g σ d C ε (n + 1) (advance p t s v) := by
  classical
  cases hs : s.finished with
  | true =>
    rw [advance_frozen v hs]
    exact {
      failures := I.failures
      trace := I.trace
      index_le := I.index_le
      unfinished_index := I.unfinished_index
      step_count := by simp [hs]
      potential := I.potential
      radius := I.radius
      accuracy := I.accuracy }
  | false =>
    by_cases hexit : t.B ^ 2 < ((s.index + 1 : ℕ) : ℝ) *
        (s.movement + ‖context p t s - t.η • v - s.x‖ ^ 2)
    · rw [advance_restart v hs hexit]
      refine {
        failures := I.failures + 1
        trace := initialTrace p t g σ _
        index_le := Nat.zero_le _
        unfinished_index := by simpa [initial] using hK
        step_count := ?_
        potential := ?_
        radius := ?_
        accuracy := by simp [initial] }
      · intro _
        change n + 1 ≤ t.K * (I.failures + 1) + 0
        rw [Nat.mul_add, Nat.mul_one]
        have hn := I.step_count hs
        have hi := I.unfinished_index hs
        omega
      · change F (context p t s - t.η • v) ≤ _
        push_cast
        linarith [I.potential, hdrop hs hexit]
      · change ‖(context p t s - t.η • v) - p.x0‖ ≤ _
        have hq := query_radius I.trace hs hB hθ hθ1
        have heq : (context p t s - t.η • v) - s.start = (context p t s - s.start) - t.η • v := by module
        have he : ‖(context p t s - t.η • v) - s.start‖ ≤ C := by
          rw [heq]
          have hh := norm_sub_le (context p t s - s.start) (t.η • v)
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at hh
          have hv' := mul_le_mul_of_nonneg_left (hv hs) hη
          rw [hC]
          linarith
        have hh := norm_sub_le_norm_sub_add_norm_sub (context p t s - t.η • v) s.start p.x0
        push_cast
        linarith [I.radius]
    · have hstay := le_of_not_gt hexit
      have hsfields := advance_retained_fields v hs hstay
      refine {
        failures := I.failures
        trace := retainedTrace I.trace v hs (herr hs) hstay
        index_le := ?_
        unfinished_index := ?_
        step_count := ?_
        potential := ?_
        radius := ?_
        accuracy := ?_ }
      · rw [hsfields.1]
        exact I.unfinished_index hs
      · intro hfalse
        rw [hsfields.1]
        have hne : s.index + 1 ≠ t.K := by
          intro heq
          simp [hsfields.2.2.1, heq] at hfalse
        have hi := I.unfinished_index hs
        omega
      · intro _
        rw [hsfields.1]
        have hn := I.step_count hs
        omega
      · rw [hsfields.2.1]
        exact I.potential
      · rw [hsfields.2.1]
        exact I.radius
      · intro htrue
        apply hsuccess _ (retainedTrace I.trace v hs (herr hs) hstay) _ hsfields.2.2.2
        rw [hsfields.1]
        have hh : decide (s.index + 1 = t.K) = true := hsfields.2.2.1.symm.trans htrue
        exact of_decide_eq_true hh

lemma finite_run_accuracy {p : Params} {t : Tuning} {F : p.X → ℝ} {g V : p.X → p.X}
    {σ d ε Δ M : ℝ} (hK : 0 < t.K) (hη : 0 ≤ t.η) (hB : 0 ≤ t.B)
    (hθ : 0 ≤ t.θ) (hθ1 : t.θ ≤ 1) (hσ : 0 ≤ σ) (hd : 0 < d)
    (hgap : ∀ x, F p.x0 - F x ≤ Δ) (hgnorm : ∀ x, ‖g x‖ ≤ M)
    (horacle : ∀ x, ‖x - p.x0‖ ≤ ((⌊Δ / d⌋₊ + 1 : ℕ) : ℝ) *
      (2 * t.B + t.η * (M + σ)) + 2 * t.B → ‖V x - g x‖ ≤ σ)
    (hdrop : ∀ (s : OuterState p.X), EpochTrace p t g σ s → ∀ v,
      s.finished = false → s.index < t.K → ‖v - g (context p t s)‖ ≤ σ →
      t.B ^ 2 < ((s.index + 1 : ℕ) : ℝ) * (s.movement + ‖context p t s - t.η • v - s.x‖ ^ 2) →
      F (context p t s - t.η • v) - F s.start ≤ -d)
    (hsuccess : ∀ s : OuterState p.X, EpochTrace p t g σ s → s.index = t.K →
      s.result = s.bestOutput → ‖g s.result‖ ≤ ε) :
    ‖g (((fun s => advance p t s (V (context p t s)))^[t.K * (⌊Δ / d⌋₊ + 1)] (initial p.x0)).result)‖ ≤ ε := by
  let C := 2 * t.B + t.η * (M + σ)
  let step := fun s => advance p t s (V (context p t s))
  have hM : 0 ≤ M := (norm_nonneg (g p.x0)).trans (hgnorm p.x0)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hrun : ∀ n, Nonempty (RunInvariant p t F g σ d C ε n (step^[n] (initial p.x0))) := by
    intro n
    induction n with
    | zero => exact ⟨initialInvariant p t F g σ d C ε hK⟩
    | succ n ih =>
      obtain ⟨I⟩ := ih
      rw [Function.iterate_succ_apply']
      have herror : ‖V (context p t (step^[n] (initial p.x0))) - g (context p t (step^[n] (initial p.x0)))‖ ≤ σ :=
        horacle _ (invariant_query_radius I hd hC hB hθ hθ1 hgap)
      have hv : ‖V (context p t (step^[n] (initial p.x0)))‖ ≤ M + σ := by
        have hh := norm_add_le (g (context p t (step^[n] (initial p.x0))))
          (V (context p t (step^[n] (initial p.x0))) - g (context p t (step^[n] (initial p.x0))))
        have heq : g (context p t (step^[n] (initial p.x0))) +
            (V (context p t (step^[n] (initial p.x0))) - g (context p t (step^[n] (initial p.x0)))) =
            V (context p t (step^[n] (initial p.x0))) := by abel
        rw [heq] at hh
        linarith [hgnorm (context p t (step^[n] (initial p.x0)))]
      exact ⟨stepInvariant I _ hK hη hB hθ hθ1 rfl (fun _ => herror) (fun _ => hv)
        (fun hs hexit => hdrop _ I.trace _ hs (I.unfinished_index hs) herror hexit) hsuccess⟩
  obtain ⟨I⟩ := hrun (t.K * (⌊Δ / d⌋₊ + 1))
  exact terminal_invariant I hd hgap

end LongTails.Proofs.BilevelRestartExecution
