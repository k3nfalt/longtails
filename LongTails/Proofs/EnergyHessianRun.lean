import LongTails.Proofs.EnergyHessianBlock
import LongTails.Proofs.EnergyHessianExecution
import LongTails.Proofs.EnergyHessianLedger

namespace LongTails.Proofs.EnergyHessianRun

open LongTails.Setups.GradientDependentHessian LongTails.Algorithms.EnergyHessianReuse
open OracleTemplate OracleTemplate.QueryPlan
open EnergyHessianBlock EnergyHessianExecution
open scoped RealInnerProductSpace

lemma lazy_run (p : Params) (f : p.E → ℝ) (B : p.E →L[ℝ] p.E)
    (hv : spec.valid p) (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    (hB : ∀ x y : p.E, ⟪x, B y⟫ = ⟪B x, y⟫)
    {b σstart : ℝ} (hb : 0 < b) (N j : ℕ) (a : Point p) (path : ℝ)
    (v : Previous) (t : EnergyHessianLedger.Totals)
    (hI : Invariant p f B a t.E path v) (hC : Correct p f a)
    (hV : EnergyHessianLedger.Valid t p.L₀ p.L₁ p.m (Real.sqrt (p.m * p.L₁))
      (radius p) b p.ε σstart (coefficient p a) path j)
    (hbest : p.ε < (eval (replies p f) (lazySteps p B N a t.E path)).bestNorm) :
    ∃ t' : EnergyHessianLedger.Totals, ∃ path' : ℝ, ∃ v' : Previous,
      let out := eval (replies p f) (lazySteps p B N a t.E path)
      Invariant p f B out t'.E path' v' ∧
      EnergyHessianLedger.Valid t' p.L₀ p.L₁ p.m (Real.sqrt (p.m * p.L₁))
        (radius p) b p.ε σstart (coefficient p out) path' (j + N) ∧
      f out.x - f a.x ≤ -(t'.E - t.E) / 3 ∧ Correct p f out := by
  induction N generalizing j a path v t with
  | zero =>
    refine ⟨t, path, v, hI, ?_, ?_, hC⟩
    · simpa only [Nat.add_zero, lazySteps, eval] using hV
    · simp [lazySteps, eval]
  | succ N ih =>
    let δ := damping p t.E path
    let σ := coefficient p a
    let z := selectedStep p a.g B δ σ
    let next := move p a z.1 (gradient f (a.x + z.1))
    let tnext := EnergyHessianLedger.push t p.L₁ σ ‖z.1‖ z.2 δ (‖gradient f (a.x + z.1)‖)
    let pathnext := path + ‖z.1‖
    let vnext : Previous := ⟨δ, ‖z.1‖, z.2⟩
    have heval : eval (replies p f) (lazySteps p B (N + 1) a t.E path) =
        eval (replies p f) (lazySteps p B N next tnext.E pathnext) := by
      simp only [lazySteps, eval, replies, ite_true, readGradient]
      rfl
    have hCnext : Correct p f next := correct_move p f a z.1 hC
    have hbestnext : p.ε < (eval (replies p f) (lazySteps p B N next tnext.E pathnext)).bestNorm :=
      heval ▸ hbest
    have hgn : a.g ≠ 0 := by
      have hh := (hbest.trans_le (eval_lazy_correct p f B (N + 1) a t.E path hC).2).trans_le hC.best_le
      intro hz
      rw [hz, norm_zero] at hh
      linarith [hv.2.2.2.2.1]
    obtain ⟨hInext, hdescent⟩ := reused_step p f B a t.E path v hv hf hT hB hI hgn
    have hInext' : Invariant p f B next tnext.E pathnext vnext := hInext
    have hglower : p.ε ≤ ‖gradient f (a.x + z.1)‖ :=
      ((hbestnext.trans_le (eval_lazy_correct p f B N next tnext.E pathnext hCnext).2).trans_le
        hCnext.best_le).le
    obtain ⟨_, hμ, _, hcap, _⟩ := EnergyHessianParameters.step_certificate p a.g B δ σ
      hv.2.2.1 hv.2.2.2.2.1 hv.2.1 hgn hB
    have hσ : 0 ≤ σ := EnergyHessianParameters.coefficient_nonneg p a hv.1.le hv.2.1
    have hδ : 0 ≤ δ := by
      have he := hV.E_nonneg
      have hp := hV.path_nonneg
      have hL₀ := hv.1.le
      have hL₁ := hv.2.1
      dsimp [δ, damping]
      positivity
    have hfloor : 100 * (p.m : ℝ) * p.L₀ ≤ σ := by
      have hh := EnergyHessianParameters.coefficient_lower p a
      have hp := mul_nonneg hv.2.1 (norm_nonneg a.g)
      dsimp [σ]
      nlinarith
    have hgrad : ‖gradient f (a.x + z.1)‖ ≤ 4 * (σ * ‖z.1‖ ^ 2 + δ * ‖z.1‖ + z.2 * ‖z.1‖) :=
      hInext'.gradient_bound
    have hVnext : EnergyHessianLedger.Valid tnext p.L₀ p.L₁ p.m (Real.sqrt (p.m * p.L₁))
        (radius p) b p.ε σstart (coefficient p next) pathnext (j + 1) := by
      apply EnergyHessianLedger.push_valid t hV hv.1.le hv.2.1 hb
        (EnergyHessianParameters.radius_pos p hv.2.2.1 hv.2.2.2.2.1 hv.2.1)
        hv.2.2.2.2.1.le (norm_nonneg z.1) hμ hσ rfl hfloor hgrad hglower
      · exact GradientDependentEnergy.cap_energy_bound
          (EnergyHessianParameters.radius_pos p hv.2.2.1 hv.2.2.2.2.1 hv.2.1)
          (norm_nonneg z.1) hσ hδ hcap
      · exact EnergyHessianParameters.coefficient_transition p a z.1 (gradient f (a.x + z.1)) hv.1.le hv.2.1
    obtain ⟨t', path', v', hIfinal, hVfinal, hd, hCfinal⟩ :=
      ih (j + 1) next pathnext vnext tnext hInext' hCnext hVnext hbestnext
    refine ⟨t', path', v', ?_⟩
    dsimp only
    rw [heval]
    refine ⟨hIfinal, ?_, ?_, hCfinal⟩
    · convert hVfinal using 1; omega
    · have he : tnext.E = t.E + stepEnergy σ δ z := rfl
      change f next.x - f a.x ≤ -stepEnergy σ δ z / 3 at hdescent
      nlinarith

lemma block_run (p : Params) (f : p.E → ℝ)
    (hv : spec.valid p) (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    {b : ℝ} (hb : 0 < b) (a : Point p) (hC : Correct p f a)
    (hbest : p.ε < (eval (replies p f) (block p a)).bestNorm) :
    ∃ t : EnergyHessianLedger.Totals, ∃ path : ℝ,
      let out := eval (replies p f) (block p a)
      EnergyHessianLedger.Valid t p.L₀ p.L₁ p.m (Real.sqrt (p.m * p.L₁))
        (radius p) b p.ε (coefficient p a) (coefficient p out) path p.m ∧
      f out.x - f a.x ≤ -t.E / 3 ∧ Correct p f out := by
  let σ := coefficient p a
  let B := fderiv ℝ (gradient f) a.x
  let z := selectedStep p a.g B 0 σ
  let next := move p a z.1 (gradient f (a.x + z.1))
  let t := EnergyHessianLedger.initial σ ‖z.1‖ z.2 ‖gradient f next.x‖
  let Bnext := fderiv ℝ (gradient f) next.x
  have hCnext : Correct p f next := correct_move p f a z.1 hC
  have heval : eval (replies p f) (block p a) =
      eval (replies p f) (lazySteps p Bnext p.m next t.E 0) := by
    simp only [block, eval, replies, show (1 : Fin 2) ≠ 0 by decide, ite_false,
      ite_true, readHessian, readGradient]
    congr 1
    simp [t, EnergyHessianLedger.initial, stepEnergy, z, σ, B, Bnext, next]
  have hbestnext : p.ε < (eval (replies p f) (lazySteps p Bnext p.m next t.E 0)).bestNorm := heval ▸ hbest
  have hgn : a.g ≠ 0 := by
    have hh := (hbest.trans_le (eval_block_correct p f a hC).2).trans_le hC.best_le
    intro hz
    rw [hz, norm_zero] at hh
    linarith [hv.2.2.2.2.1]
  obtain ⟨hI, hdescent⟩ := prep_invariant p f a hv hf hT hC.gradient_eq hgn
  have hI' : Invariant p f Bnext next t.E 0 ⟨0, ‖z.1‖, z.2⟩ := by
    simpa only [t, EnergyHessianLedger.initial, Bnext, next, z, B, σ, stepEnergy, mul_zero, zero_mul, add_zero] using hI
  have hglower : p.ε ≤ ‖gradient f next.x‖ :=
    ((hbestnext.trans_le (eval_lazy_correct p f Bnext p.m next t.E 0 hCnext).2).trans_le hCnext.best_le).le
  have hB : ∀ x y : p.E, ⟪x, B y⟫ = ⟪B x, y⟫ := by
    intro x y
    exact (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
      (hf.of_le (by norm_num)) a.x x y).symm
  obtain ⟨_, hμ, _, hcap, _⟩ := EnergyHessianParameters.step_certificate p a.g B 0 σ
    hv.2.2.1 hv.2.2.2.2.1 hv.2.1 hgn hB
  have hσ : 0 ≤ σ := EnergyHessianParameters.coefficient_nonneg p a hv.1.le hv.2.1
  have hcap' : z.2 * ‖z.1‖ ≤ (σ * ‖z.1‖ ^ 3 + z.2 * ‖z.1‖ ^ 2) / radius p := by
    simpa using GradientDependentEnergy.cap_energy_bound
      (EnergyHessianParameters.radius_pos p hv.2.2.1 hv.2.2.2.2.1 hv.2.1)
      (norm_nonneg z.1) hσ (show (0 : ℝ) ≤ 0 by rfl) hcap
  have hV : EnergyHessianLedger.Valid t p.L₀ p.L₁ p.m (Real.sqrt (p.m * p.L₁))
      (radius p) b p.ε σ (coefficient p next) 0 0 := by
    apply EnergyHessianLedger.initial_valid hb hv.2.2.2.2.1.le (norm_nonneg z.1) hμ hσ
    · simpa only [next, move, σ, mul_zero, zero_mul, add_zero] using hI'.gradient_bound
    · exact hglower
    · exact hcap'
    · exact EnergyHessianParameters.coefficient_transition p a z.1 (gradient f (a.x + z.1)) hv.1.le hv.2.1
  have hBnext : ∀ x y : p.E, ⟪x, Bnext y⟫ = ⟪Bnext x, y⟫ := by
    intro x y
    exact (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
      (hf.of_le (by norm_num)) next.x x y).symm
  obtain ⟨t', path', v', _, hVfinal, hd, hCfinal⟩ :=
    lazy_run p f Bnext hv hf hT hBnext hb p.m 0 next 0 ⟨0, ‖z.1‖, z.2⟩ t hI' hCnext hV hbestnext
  refine ⟨t', path', ?_⟩
  dsimp only
  rw [heval]
  refine ⟨by simpa using hVfinal, ?_, hCfinal⟩
  have he : stepEnergy σ 0 z = t.E := by simp [t, EnergyHessianLedger.initial, stepEnergy]
  change f next.x - f a.x ≤ -stepEnergy σ 0 z / 3 at hdescent
  rw [he] at hdescent
  nlinarith

lemma burn_run (p : Params) (f : p.E → ℝ)
    (hv : spec.valid p) (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    (N j : ℕ) (a : Point p) (E σstart : ℝ) (hE : 0 ≤ E) (hC : Correct p f a)
    (hcoef : coefficient p a ≤ (3 / 4) ^ j * σstart + 400 * p.m * p.L₀ +
      20000 * p.L₁ * Real.sqrt p.L₁ * E)
    (hbest : p.ε < (eval (replies p f) (iteratePlans (fresh p) N a)).bestNorm) :
    ∃ E' : ℝ, let out := eval (replies p f) (iteratePlans (fresh p) N a)
      0 ≤ E' ∧ f out.x - f a.x ≤ -(E' - E) / 3 ∧
      coefficient p out ≤ (3 / 4) ^ (j + N) * σstart + 400 * p.m * p.L₀ +
        20000 * p.L₁ * Real.sqrt p.L₁ * E' ∧ Correct p f out := by
  induction N generalizing j a E with
  | zero =>
    refine ⟨E, hE, ?_, ?_, hC⟩
    · simp [iteratePlans, eval]
    · simpa only [Nat.add_zero, iteratePlans, eval] using hcoef
  | succ N ih =>
    let σ := coefficient p a
    let B := fderiv ℝ (gradient f) a.x
    let z := selectedStep p a.g B 0 σ
    let e := stepEnergy σ 0 z
    let next := move p a z.1 (gradient f (a.x + z.1))
    have hnext : eval (replies p f) (fresh p a) = next := by
      simp [fresh, eval, replies, readGradient, readHessian, next, z, B, σ]
    have heval : eval (replies p f) (iteratePlans (fresh p) (N + 1) a) =
        eval (replies p f) (iteratePlans (fresh p) N next) := by
      rw [iteratePlans, eval_bind, hnext]
    have hgn : a.g ≠ 0 := by
      have hh := (hbest.trans_le (eval_iterate_correct f (fresh p)
        (fun a h => eval_fresh_correct p f a h) (N + 1) a hC).2).trans_le hC.best_le
      intro hz
      rw [hz, norm_zero] at hh
      linarith [hv.2.2.2.2.1]
    have hB : ∀ x y : p.E, ⟪x, B y⟫ = ⟪B x, y⟫ := by
      intro x y
      exact (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
        (hf.of_le (by norm_num)) a.x x y).symm
    obtain ⟨_, hμ, _, _, _⟩ := EnergyHessianParameters.step_certificate p a.g B 0 σ
      hv.2.2.1 hv.2.2.2.2.1 hv.2.1 hgn hB
    have hσ : 0 ≤ σ := EnergyHessianParameters.coefficient_nonneg p a hv.1.le hv.2.1
    have he : 0 ≤ e := by dsimp [e, stepEnergy]; positivity
    obtain ⟨hdescent, hrec⟩ := EnergyHessianStep.fresh_step p f a hv hf hT hC.gradient_eq hgn
    have hcoefnext : coefficient p next ≤ (3 / 4) ^ (j + 1) * σstart + 400 * p.m * p.L₀ +
        20000 * p.L₁ * Real.sqrt p.L₁ * (E + e) := by
      have hp : 0 ≤ 20000 * p.L₁ * Real.sqrt p.L₁ * E := by
        have hL := hv.2.1
        positivity
      change coefficient p next ≤ (3 / 4) * σ + 100 * p.m * p.L₀ +
        20000 * p.L₁ * Real.sqrt p.L₁ * e at hrec
      rw [pow_succ]
      nlinarith
    have hCnext := correct_move p f a z.1 hC
    have hbestnext : p.ε < (eval (replies p f) (iteratePlans (fresh p) N next)).bestNorm := heval ▸ hbest
    obtain ⟨E', hE', hd, hc, hCfinal⟩ :=
      ih (j + 1) next (E + e) (add_nonneg hE he) hCnext hcoefnext hbestnext
    refine ⟨E', ?_⟩
    dsimp only
    rw [heval]
    refine ⟨hE', ?_, ?_, hCfinal⟩
    · change f next.x - f a.x ≤ -e / 3 at hdescent
      nlinarith
    · simpa only [Nat.add_assoc, Nat.add_comm 1 N] using hc

lemma blocks_run (p : Params) (f : p.E → ℝ)
    (hv : spec.valid p) (hf : ContDiff ℝ 3 f)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ p.L₀ + p.L₁ * ‖gradient f x‖)
    {b : ℝ} (hb : 0 < b) (N : ℕ) (a : Point p) (hC : Correct p f a)
    (hbest : p.ε < (eval (replies p f) (iteratePlans (block p) N a)).bestNorm) :
    ∃ S C E : ℝ, let out := eval (replies p f) (iteratePlans (block p) N a)
      0 ≤ S ∧ 0 ≤ C ∧ 0 ≤ E ∧ f out.x - f a.x ≤ -E / 3 ∧
      C ≤ 2 * b ^ 2 * (coefficient p a - coefficient p out) +
        200 * b ^ 2 * (N * (p.m + 1)) * p.m * p.L₀ + 200 * b ^ 2 * p.L₁ * S + E / b ∧
      S ≤ 4 * C + 4 * (C / 25 + 10 * Real.sqrt (p.m * p.L₁) * E) + 4 * E / radius p ∧
      (N * (p.m + 1)) * p.ε ≤ S ∧ Correct p f out := by
  induction N generalizing a with
  | zero =>
    refine ⟨0, 0, 0, ?_⟩
    simpa [iteratePlans, eval] using hC
  | succ N ih =>
    let next := eval (replies p f) (block p a)
    have hCnext : Correct p f next := (eval_block_correct p f a hC).1
    have heval : eval (replies p f) (iteratePlans (block p) (N + 1) a) =
        eval (replies p f) (iteratePlans (block p) N next) := by rw [iteratePlans, eval_bind]
    have hbestnext : p.ε < (eval (replies p f) (iteratePlans (block p) N next)).bestNorm := heval ▸ hbest
    have hbestblock : p.ε < next.bestNorm := hbestnext.trans_le
      (eval_iterate_correct f (block p) (fun a h => eval_block_correct p f a h) N next hCnext).2
    obtain ⟨t, path, hV, hd, _⟩ := block_run p f hv hf hT hb a hC hbestblock
    obtain ⟨S, C, E, hS, hCn, hE, hdescent, hcubic, hbalance, hlower, hCfinal⟩ := ih next hCnext hbestnext
    have hbal := EnergyHessianLedger.final_balance t hV hv.1.le hv.2.1 hv.2.2.2.2.2
      (Real.sqrt_nonneg _) (Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg p.m) hv.2.1))
    refine ⟨t.S + S, t.C + C, t.E + E, ?_⟩
    dsimp only
    rw [heval]
    refine ⟨add_nonneg hV.S_nonneg hS, add_nonneg hV.C_nonneg hCn,
      add_nonneg hV.E_nonneg hE, ?_, ?_, ?_, ?_, hCfinal⟩
    · change f next.x - f a.x ≤ -t.E / 3 at hd
      nlinarith
    · have hh := hV.cubic
      change t.C ≤ 2 * b ^ 2 * (coefficient p a - coefficient p next) +
        200 * b ^ 2 * ((p.m : ℝ) + 1) * p.m * p.L₀ + 200 * b ^ 2 * p.L₁ * t.S + t.E / b at hh
      push_cast
      rw [add_div]
      nlinarith
    · simp only [mul_add, add_div]
      nlinarith
    · have hh := hV.lower
      push_cast
      nlinarith

end LongTails.Proofs.EnergyHessianRun
