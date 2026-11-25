import LongTails.Proofs.HessianReuseModelFlowDescent
import LongTails.Proofs.EnergyHessianExecution
import Mathlib.Algebra.Order.Floor.Semifield

namespace LongTails.Proofs.HessianReuseModelFlowExecution

open OracleTemplate OracleTemplate.QueryPlan LongTails.Setups.GradientDependentHessian
open LongTails.Algorithms.HessianReuseModelFlow
open EnergyHessianExecution (counts counts_bind counts_map replies)
open HessianReuseModelFlowPath HessianReuseModelFlowDescent

variable {p : Params}

private lemma steps_fresh (j : ℕ) (h : j % p.m = 0) :
    steps p (j+1) = ⟨_, QueryPlan.bind (steps p j).2 (fresh p)⟩ := by
  rw [steps]
  exact ite_eq_left h

private lemma steps_reuse (j : ℕ) (h : j % p.m ≠ 0) :
    steps p (j+1) = ⟨_, QueryPlan.bind (steps p j).2 (reuse p)⟩ := by
  rw [steps]
  exact ite_eq_right h

private def Invariant (f : p.E → ℝ) (j : ℕ) : State p → Prop
  | .done x => ‖gradient f x‖ ≤ p.ε
  | .active x B => f x + j * decrease p ≤ f p.x0 ∧
      (j % p.m ≠ 0 → ‖fderiv ℝ (gradient f) x - B‖ ≤ (j % p.m : ℕ) * radius p * curvature p)

private lemma advance_invariant (hp : spec.valid p) {f : p.E → ℝ} (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    (j : ℕ) (s : State p) (H : p.E →L[ℝ] p.E) (hs : Invariant f j s)
    (hB : ‖fderiv ℝ (gradient f) (point s) - H‖ ≤ (j % p.m : ℕ) * radius p * curvature p) :
    Invariant f (j+1) (advance p s (gradient f (point s)) H) := by
  cases s with
  | done x => exact hs
  | active x B =>
    let g := gradient f x
    let τ := stopTime p g H
    let y := x + displacement g H τ
    have hm : 0 < p.m := hp.2.2.2.2.2
    have hj := Nat.mod_lt j hm
    by_cases hn : ‖g‖ ≤ p.ε
    · change Invariant f _ (if ‖g‖ ≤ p.ε then .done x else _)
      rw [ite_eq_left hn]
      exact hn
    · obtain ⟨he, hH, hd⟩ := stopped_estimates hp hf hT x H (j % p.m) hj hB (lt_of_not_ge hn)
      obtain ⟨_, _, hend⟩ := stop_spec g H hp (lt_of_not_ge hn)
      change ‖gradient f y - velocity g H τ‖ ≤ allowance p at he
      change f y + energy g H τ - allowance p * radius p / 2 ≤ f x at hd
      change ‖velocity g H τ‖ ≤ threshold p ∨ energy g H τ = energyCap p at hend
      change Invariant f (j+1) (if ‖g‖ ≤ p.ε then _ else
        if ‖velocity g H τ‖ ≤ threshold p then .done y else .active y H)
      rw [ite_eq_right hn]
      split_ifs with hit
      · apply (norm_le_norm_sub_add _ _).trans
        exact (add_le_add he hit).trans (by unfold allowance threshold; linarith)
      · refine ⟨?_, ?_⟩
        · rw [hend.resolve_left hit] at hd
          have htotal := hs.1
          dsimp only [energyCap] at hd
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          unfold decrease at *
          linarith only [htotal, hd, show (threshold p - allowance p / 2) * radius p =
            threshold p * radius p - allowance p * radius p / 2 by ring]
        · intro hnonzero
          have hmod : (j+1) % p.m = j % p.m + 1 := by
            rw [← Nat.mod_add_mod]
            apply Nat.mod_eq_of_lt
            by_contra! h
            have eq : j % p.m + 1 = p.m := by omega
            exact hnonzero (by rw [← Nat.mod_add_mod, eq, Nat.mod_self])
          rw [hmod, Nat.cast_add, Nat.cast_one]
          exact hH

lemma steps_invariant (hp : spec.valid p) {f : p.E → ℝ} (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    (j : ℕ) : Invariant f j (eval (replies p f) (steps p j).2) := by
  induction j with
  | zero => simp [steps, eval, Invariant]
  | succ j ih =>
    let s := eval (replies p f) (steps p j).2
    change Invariant f j s at ih
    by_cases h : j % p.m = 0
    · rw [steps_fresh j h]
      simp only [eval_bind, fresh, eval, replies, ite_true,
        show (1 : Fin 2) ≠ 0 by decide, ite_false,
        Algorithms.EnergyHessianReuse.readGradient, Algorithms.EnergyHessianReuse.readHessian]
      apply advance_invariant hp hf hT j s _ ih
      simp [h, s]
    · rw [steps_reuse j h]
      simp only [eval_bind, reuse, eval, replies, ite_true,
        Algorithms.EnergyHessianReuse.readGradient]
      change Invariant f _ (advance p s (gradient f (point s)) (stored s))
      cases hs : s with
      | done x => rw [hs] at ih; exact ih
      | active x B =>
        rw [hs] at ih
        apply advance_invariant hp hf hT j (.active x B) B ih
        exact ih.2 h

lemma steps_accuracy (hp : spec.valid p) {f : p.E → ℝ} (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    (hgap : ∀ x, f p.x0 - f x ≤ p.Δ) :
    ‖gradient f (point (eval (replies p f) (steps p (horizon p)).2))‖ ≤ p.ε := by
  have hi := steps_invariant hp hf hT (horizon p)
  cases hs : eval (replies p f) (steps p (horizon p)).2 with
  | done x => rw [hs] at hi; exact hi
  | active x B =>
    rw [hs] at hi
    have hd : 0 < decrease p := by
      apply mul_pos _ (radius_pos hp)
      unfold threshold allowance
      linarith [hp.2.2.2.2.1]
    have hlt := Nat.lt_floor_add_one (p.Δ / decrease p)
    have hgt : p.Δ < (horizon p : ℝ) * decrease p := (div_lt_iff₀ hd).mp
      (by simpa [horizon] using hlt)
    linarith only [hi.1, hgap x, hgt]

lemma counts_steps (f : p.E → ℝ) (j : ℕ) (i : Fin 2) :
    counts (replies p f) (steps p (j+1)).2 i = if i = 0 then j+1 else j / p.m + 1 := by
  have hFresh (s : State p) : counts (replies p f) (fresh p s) i = 1 := by
    fin_cases i <;> simp [fresh, counts]
  have hReuse (s : State p) :
      counts (replies p f) (reuse p s) i = if i = 0 then 1 else 0 := by
    simp [reuse, counts]
  induction j with
  | zero => simp [steps, counts_bind, hFresh, counts]
  | succ j ih =>
    by_cases h : (j+1) % p.m = 0
    · have hd := Nat.dvd_of_mod_eq_zero h
      rw [steps_fresh _ h]
      simp only [counts_bind, hFresh, ih, Nat.succ_div_of_dvd hd]
      split_ifs <;> omega
    · have hd : ¬p.m ∣ j+1 := fun hd => h (Nat.mod_eq_zero_of_dvd hd)
      rw [steps_reuse _ h]
      simp only [counts_bind, hReuse, ih, Nat.succ_div_of_not_dvd hd]
      split_ifs <;> omega

lemma ratio (hp : spec.valid p) :
    p.Δ / decrease p = 9 / (2 * Real.sqrt 2) * Real.sqrt p.m *
      (p.Δ * Real.sqrt (curvature p) / (p.ε * Real.sqrt p.ε)) := by
  have hm := m_pos hp
  have hA := curvature_pos hp
  have he := hp.2.2.2.2.1
  have hd : threshold p - allowance p / 2 = 2 * p.ε / 3 := by
    unfold threshold allowance
    ring
  rw [decrease, hd, radius, allowance, Real.sqrt_div (by positivity),
    Real.sqrt_mul hm.le, Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num [Real.sqrt_div]
  field_simp
  ring

end LongTails.Proofs.HessianReuseModelFlowExecution
