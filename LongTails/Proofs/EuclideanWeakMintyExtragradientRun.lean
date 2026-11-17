import LongTails.Algorithms.EuclideanWeakMintyExtragradient
import LongTails.Proofs.NonEuclideanExtragradientRun
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Proofs.EuclideanWeakMintyExtragradientRun

open LongTails.Setups.EuclideanWeakMinty LongTails.Algorithms.EuclideanWeakMintyExtragradient

lemma bregman_eq (p : Params) (u x : EuclideanSpace ℝ (Fin p.d)) :
    (mirrorData p).bregman u x = ‖u - x‖ ^ 2 / 2 := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul (1 / 2 : ℝ)
  have hfun : (fun y : EuclideanSpace ℝ (Fin p.d) => ‖y‖ ^ 2 / 2) =
      fun y => 1 / 2 * ‖y‖ ^ 2 := by
    funext y
    ring
  have hder : (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin p.d) => ‖y‖ ^ 2 / 2) x) (u - x) =
      ⟪x, u - x⟫ := by
    rw [hfun, h.fderiv]
    rw [smul_apply, smul_apply, innerSL_apply_apply, nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
  change ‖u‖ ^ 2 / 2 - ‖x‖ ^ 2 / 2 -
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin p.d) => ‖y‖ ^ 2 / 2) x (u - x) = _
  rw [hder, norm_sub_sq_real, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm u x]
  ring

lemma mirror_valid (p : Params) (hp : spec.valid p) : (mirrorData p).Valid := by
  obtain ⟨hL, hρ, hρL, -, -, -⟩ := hp
  refine ⟨hL, hρ, hρL, one_pos, ?_, ?_⟩
  · intro x
    have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul (1 / 2 : ℝ)
    have hfun : (fun y : EuclideanSpace ℝ (Fin p.d) => 1 / 2 * ‖y‖ ^ 2) = (mirrorData p).h := by
      funext y
      change _ = ‖y‖ ^ 2 / 2
      ring
    rw [← hfun]
    exact h.differentiableAt
  · intro x u
    change 1 / 2 * ‖u - x‖ ^ 2 ≤ (mirrorData p).bregman u x
    rw [bregman_eq]
    linarith

noncomputable def dualOracle (p : Params)
    (F : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d)) :
    Oracle (mirrorData p).E ((mirrorData p).E →L[ℝ] ℝ) where
  answer _ q _ := innerSL ℝ (F q.2)

lemma execute_eq (p : Params) (F : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d))
    (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)))
    (hO : ∀ k seed x, O.answer k (0, x) seed = F x) (n : ℕ) (seed : (algorithm p).Seed)
    (ξ : (k : ℕ) → O.Seed k) :
    execute O (algorithm p) (fun _ => n) seed ξ =
      execute (dualOracle p F) (LongTails.Algorithms.NonEuclideanExtragradient.algorithm
        (mirrorData p)) (fun _ => n) () (fun _ => ()) := by
  rw [OracleTemplate.execute_eq_of_answer_eq O F (fun k x seed => hO k seed x),
    OracleTemplate.execute_iterate,
    OracleTemplate.execute_eq_of_answer_eq (dualOracle p F) (fun x => innerSL ℝ (F x))
      (fun _ _ _ => rfl)]
  exact (OracleTemplate.execute_iterate (fun x => innerSL ℝ (F x))
    (LongTails.Algorithms.NonEuclideanExtragradient.algorithm (mirrorData p)) n ()).symm

lemma execute_accuracy (p : Params) (hp : spec.valid p)
    (F : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d))
    (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)))
    (had : spec.admissible p F O) (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    ‖F (execute O (algorithm p) (fun _ => 2 + 2 * ⌈200 * p.L ^ 2 * p.R ^ 2 / p.ε ^ 2⌉₊)
      seed ξ)‖ ≤ p.ε := by
  obtain ⟨hO, hlip, u, -, hu, hminty⟩ := had
  have hε : 0 < p.ε := hp.2.2.2.1
  let n : ℕ := 1 + ⌈200 * p.L ^ 2 * p.R ^ 2 / p.ε ^ 2⌉₊
  have hn : 0 < n := by omega
  have heq : (2 + 2 * ⌈200 * p.L ^ 2 * p.R ^ 2 / p.ε ^ 2⌉₊ : ℕ) = 2 * n := by omega
  rw [heq, execute_eq p F O hO]
  have hD : (mirrorData p).bregman u (mirrorData p).x0 ≤ p.R ^ 2 / 2 := by
    rw [bregman_eq]
    change ‖u - p.x0‖ ^ 2 / 2 ≤ p.R ^ 2 / 2
    have h := pow_le_pow_left₀ (norm_nonneg _) hu 2
    linarith
  have hbudget : 400 * (mirrorData p).L ^ 2 * (p.R ^ 2 / 2) / ((mirrorData p).μ * p.ε ^ 2) ≤
      (n : ℝ) := by
    change 400 * p.L ^ 2 * (p.R ^ 2 / 2) / (1 * p.ε ^ 2) ≤ (n : ℝ)
    have hc := Nat.le_ceil (200 * p.L ^ 2 * p.R ^ 2 / p.ε ^ 2)
    have e : 400 * p.L ^ 2 * (p.R ^ 2 / 2) / (1 * p.ε ^ 2) = 200 * p.L ^ 2 * p.R ^ 2 / p.ε ^ 2 := by
      ring
    rw [e]
    dsimp only [n]
    push_cast
    linarith
  have hlip' : ∀ x y : (mirrorData p).E,
      ‖innerSL ℝ (F x) - innerSL ℝ (F y)‖ ≤ (mirrorData p).L * ‖x - y‖ := by
    intro x y
    calc
      ‖innerSL ℝ (F x) - innerSL ℝ (F y)‖ = ‖innerSL ℝ (F x - F y)‖ := by rw [map_sub]
      _ = ‖F x - F y‖ := innerSL_apply_norm ℝ _
      _ ≤ (mirrorData p).L * ‖x - y‖ := hlip x y
  have hminty' : ∀ x : (mirrorData p).E,
      -(mirrorData p).ρ * ‖innerSL ℝ (F x)‖ ^ 2 ≤ innerSL ℝ (F x) (x - u) := by
    intro x
    have e1 : ‖innerSL ℝ (F x)‖ = ‖F x‖ := innerSL_apply_norm ℝ _
    have e2 : innerSL ℝ (F x) (x - u) = ⟪F x, x - u⟫ := innerSL_apply_apply ℝ _ _
    rw [e1, e2]
    exact hminty x
  have h := LongTails.Proofs.NonEuclideanExtragradientRun.execute_accuracy (mirrorData p)
    (mirror_valid p hp) (fun x => innerSL ℝ (F x)) hlip' u hminty' hD hε n hn hbudget
    (dualOracle p F) (fun _ _ _ => rfl) () (fun _ => ())
  have e3 : ‖innerSL ℝ (F (execute (dualOracle p F)
      (LongTails.Algorithms.NonEuclideanExtragradient.algorithm (mirrorData p)) (fun _ => 2 * n)
      () (fun _ => ())))‖ = ‖F (execute (dualOracle p F)
      (LongTails.Algorithms.NonEuclideanExtragradient.algorithm (mirrorData p)) (fun _ => 2 * n)
      () (fun _ => ()))‖ := innerSL_apply_norm ℝ _
  rw [← e3]
  exact h

lemma success (p : Params) (hp : spec.valid p)
    (F : EuclideanSpace ℝ (Fin p.d) → EuclideanSpace ℝ (Fin p.d))
    (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)))
    (had : spec.admissible p F O) :
    spec.successful p F (fun w : (algorithm p).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (algorithm p) (fun _ => 2 + 2 * ⌈200 * p.L ^ 2 * p.R ^ 2 / p.ε ^ 2⌉₊) w.1 w.2)
      ⟨((algorithm p).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  let c := execute (dualOracle p F)
    (LongTails.Algorithms.NonEuclideanExtragradient.algorithm (mirrorData p))
    (fun _ => 2 + 2 * ⌈200 * p.L ^ 2 * p.R ^ 2 / p.ε ^ 2⌉₊) () (fun _ => ())
  have hconst : (fun w : (algorithm p).Seed × ((k : ℕ) → O.Seed k) =>
      ‖F (execute O (algorithm p) (fun _ => 2 + 2 * ⌈200 * p.L ^ 2 * p.R ^ 2 / p.ε ^ 2⌉₊)
        w.1 w.2)‖) = fun _ => ‖F c‖ := by
    funext w
    rw [execute_eq p F O had.1]
  have hle (w : (algorithm p).Seed × ((k : ℕ) → O.Seed k)) :
      ‖F (execute O (algorithm p) (fun _ => 2 + 2 * ⌈200 * p.L ^ 2 * p.R ^ 2 / p.ε ^ 2⌉₊)
        w.1 w.2)‖ ≤ p.ε :=
    execute_accuracy p hp F O had w.1 w.2
  have hint : Integrable (fun w : (algorithm p).Seed × ((k : ℕ) → O.Seed k) =>
      ‖F (execute O (algorithm p) (fun _ => 2 + 2 * ⌈200 * p.L ^ 2 * p.R ^ 2 / p.ε ^ 2⌉₊)
        w.1 w.2)‖)
      (((algorithm p).law : Measure _).prod (O.law : Measure _)) := by
    rw [hconst]
    exact integrable_const _
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ _ : (algorithm p).Seed × ((k : ℕ) → O.Seed k), p.ε
        ∂(((algorithm p).law : Measure _).prod (O.law : Measure _)) :=
      integral_mono hint (integrable_const _) hle
    _ = p.ε := by simp

end LongTails.Proofs.EuclideanWeakMintyExtragradientRun
