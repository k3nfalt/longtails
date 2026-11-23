import LongTails.Algorithms.CubicNewtonPL
import LongTails.Proofs.CubicNewtonPLDescent
import LongTails.Proofs.CubicNewtonPLRecursion
import LongTails.Proofs.Execution

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CubicNewtonPLConvergence

open OracleTemplate LongTails.Setups.HessianLipschitzPL LongTails.Algorithms.CubicNewtonPL
open CubicNewtonPLRecursion CubicNewtonPLDescent OracleTemplate.PLMinimax

section Iteration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def advance (f : E → ℝ) (H : ℝ) (x : E) : E :=
  x + envelopeCubicStep (gradient f x) (fderiv ℝ (gradient f) x) H

noncomputable def iterate (f : E → ℝ) (H : ℝ) (x0 : E) (k : ℕ) : E := (advance f H)^[k] x0

noncomputable def stride (f : E → ℝ) (H : ℝ) (x0 : E) (k : ℕ) : ℝ :=
  ‖envelopeCubicStep (gradient f (iterate f H x0 k))
    (fderiv ℝ (gradient f) (iterate f H x0 k)) H‖

noncomputable def unit (H μ : ℝ) : ℝ := 8 * μ / (27 * H)

noncomputable def level (H μ : ℝ) : ℝ := 512 * μ ^ 3 / (59049 * H ^ 2)

lemma iterate_succ (f : E → ℝ) (H : ℝ) (x0 : E) (k : ℕ) :
    iterate f H x0 (k + 1) = advance f H (iterate f H x0 k) := by
  unfold iterate
  rw [Function.iterate_succ_apply']

lemma trace {f : E → ℝ} {H μ : ℝ} {x0 xstar : E} (hH : 0 < H) (hμ : 0 < μ)
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hg : Differentiable ℝ (gradient f))
    (hLip : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ H * ‖x - y‖)
    (hmin : IsMinOn f Set.univ xstar)
    (hPL : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2) :
    Trace (fun k => (f (iterate f H x0 k) - f xstar) / level H μ)
      (fun k => stride f H x0 k / unit H μ) := by
  have hω : 0 < level H μ := by unfold level; positivity
  have hℓ : 0 < unit H μ := by unfold unit; positivity
  have hstep (k : ℕ) := step_bounds hH hf hg hLip (iterate f H x0 k)
  refine ⟨fun k => div_nonneg (sub_nonneg.mpr (hmin (Set.mem_univ _))) hω.le,
    fun k => div_nonneg (norm_nonneg _) hℓ.le, ?_, ?_⟩
  · intro k
    obtain ⟨_, hgrad⟩ := hstep k
    rw [iterate_succ]
    change ‖gradient f (advance f H (iterate f H x0 k))‖ ≤ 3 * H / 2 * stride f H x0 k ^ 2 at hgrad
    have hp := hPL (advance f H (iterate f H x0 k))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hgrad 2
    have he : (stride f H x0 k / unit H μ) ^ 4 * level H μ =
        (3 * H / 2 * stride f H x0 k ^ 2) ^ 2 / (2 * μ) := by
      unfold unit level
      field_simp
      ring
    rw [div_le_iff₀ hω, he, le_div_iff₀ (by positivity)]
    linarith
  · intro k
    obtain ⟨hdesc, _⟩ := hstep k
    rw [iterate_succ]
    change f (advance f H (iterate f H x0 k)) ≤
      f (iterate f H x0 k) - H / 3 * stride f H x0 k ^ 3 at hdesc
    have he : (stride f H x0 k / unit H μ) ^ 3 = H / 3 * stride f H x0 k ^ 3 / level H μ := by
      unfold unit level
      field_simp
      ring
    rw [he, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hω.le

lemma fourth_root_pow {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
  have h : (1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = 1 := by norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, h, Real.rpow_one]

lemma doubling (y : ℝ) (hy : 0 ≤ y) :
    ∃ j : ℕ, 1 + y ≤ (2 : ℝ) ^ j ∧ 3 * (j : ℝ) ≤ 5 * Real.log (1 + y) + 3 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 0 ≤ Real.log (1 + y) := Real.log_nonneg (by linarith)
  refine ⟨⌈Real.log (1 + y) / Real.log 2⌉₊, ?_, ?_⟩
  · have hj : Real.log (1 + y) / Real.log 2 ≤ (⌈Real.log (1 + y) / Real.log 2⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hj' := (div_le_iff₀ hlog2).mp hj
    have h := Real.exp_le_exp.mpr hj'
    rwa [Real.exp_log (by linarith), Real.exp_nat_mul, Real.exp_log (by norm_num)] at h
  · have hj : (⌈Real.log (1 + y) / Real.log 2⌉₊ : ℝ) < Real.log (1 + y) / Real.log 2 + 1 :=
      Nat.ceil_lt_add_one (div_nonneg hl hlog2.le)
    have h2 := Real.log_two_gt_d9
    have hd : Real.log (1 + y) / Real.log 2 ≤ Real.log (1 + y) / (3 / 5) :=
      div_le_div_of_nonneg_left hl (by norm_num) (by linarith)
    have he : Real.log (1 + y) / (3 / 5) = 5 / 3 * Real.log (1 + y) := by ring
    linarith

theorem iterate_accuracy {f : E → ℝ} {H μ Δ ε : ℝ} {x0 xstar : E} (hH : 0 < H) (hμ : 0 < μ)
    (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hf : ∀ x, HasGradientAt f (gradient f x) x)
    (hg : Differentiable ℝ (gradient f))
    (hLip : ∀ x y, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ H * ‖x - y‖)
    (hmin : IsMinOn f Set.univ xstar) (hgap : f x0 - f xstar ≤ Δ)
    (hPL : ∀ x, 2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2) (K : ℕ)
    (hK : 53 * (H ^ 2 * Δ / μ ^ 3) ^ (1 / 4 : ℝ) +
      5 * Real.log (1 + Real.log (1 + μ ^ 3 / (H ^ 2 * ε))) + 4 ≤ K) :
    f (iterate f H x0 K) - f xstar ≤ ε := by
  have hω : 0 < level H μ := by unfold level; positivity
  have htr := trace (x0 := x0) hH hμ hf hg hLip hmin hPL
  have hϑ : 0 ≤ H ^ 2 * Δ / μ ^ 3 := by positivity
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (H ^ 2 * Δ / μ ^ 3) ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact Real.rpow_nonneg hϑ _
  have hθ4 : θ ^ 4 = H ^ 2 * Δ / μ ^ 3 := by rw [hθ]; exact fourth_root_pow hϑ
  rw [← hθ] at hK
  have hX : 0 < μ ^ 3 / (H ^ 2 * ε) := by positivity
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.log (1 + μ ^ 3 / (H ^ 2 * ε)) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; exact Real.log_nonneg (by linarith)
  rw [← hy] at hK
  obtain ⟨j, hj1, hj2⟩ := doubling y hy0
  have h0 : (f (iterate f H x0 0) - f xstar) / level H μ ≤ (33 / 10 * θ) ^ 4 := by
    change (f x0 - f xstar) / level H μ ≤ (33 / 10 * θ) ^ 4
    rw [div_le_iff₀ hω, mul_pow, hθ4]
    have he : (33 / 10 : ℝ) ^ 4 * (H ^ 2 * Δ / μ ^ 3) * level H μ =
        (33 / 10 : ℝ) ^ 4 * 512 / 59049 * Δ := by
      unfold level
      field_simp
    rw [he]
    have hc : (1 : ℝ) ≤ (33 / 10 : ℝ) ^ 4 * 512 / 59049 := by norm_num
    nlinarith
  have hb := trace_bound htr (T0 := 33 / 10 * θ) (by positivity) h0 j K (by linarith)
  change (f (iterate f H x0 K) - f xstar) / level H μ ≤ Real.exp (-(2 : ℝ) ^ j) at hb
  have hexp : Real.exp (-(2 : ℝ) ^ j) ≤ (1 + μ ^ 3 / (H ^ 2 * ε))⁻¹ := by
    have hy' : Real.exp (-y) = (1 + μ ^ 3 / (H ^ 2 * ε))⁻¹ := by
      rw [Real.exp_neg, hy, Real.exp_log (by linarith)]
    exact (Real.exp_le_exp.mpr (by linarith)).trans_eq hy'
  have hfin := (div_le_iff₀ hω).mp (hb.trans hexp)
  have hle : (1 + μ ^ 3 / (H ^ 2 * ε))⁻¹ * level H μ ≤ ε := by
    rw [inv_mul_le_iff₀ (by linarith)]
    have he : ε * (μ ^ 3 / (H ^ 2 * ε)) = μ ^ 3 / H ^ 2 := by
      field_simp
    have h2 : (1 + μ ^ 3 / (H ^ 2 * ε)) * ε = ε + μ ^ 3 / H ^ 2 := by
      rw [← he]
      ring
    have hl : level H μ = 512 / 59049 * (μ ^ 3 / H ^ 2) := by
      unfold level
      ring
    have hq : 0 ≤ μ ^ 3 / H ^ 2 := by positivity
    rw [hl, h2]
    linarith
  linarith

end Iteration

lemma constant_success {E Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : ProbabilityMeasure Ω) {f : E → ℝ} {c xstar : E} {ε : ℝ}
    (hmin : IsMinOn f Set.univ xstar) (h : f c - f xstar ≤ ε) :
    Measurable (fun _ : Ω => c) ∧
      ∃ xstar, IsMinOn f Set.univ xstar ∧
        Integrable (fun _ : Ω => f c - f xstar) (P : Measure Ω) ∧
        ∫ _ : Ω, f c - f xstar ∂(P : Measure Ω) ≤ ε := by
  refine ⟨measurable_const, xstar, hmin, integrable_const _, ?_⟩
  simp only [integral_const, probReal_univ, one_smul]
  exact h

theorem convergence : Convergence spec (fun p _ =>
    ⌈53 * (p.H ^ 2 * p.Δ / p.μ ^ 3) ^ (1 / 4 : ℝ) +
      5 * Real.log (1 + Real.log (1 + p.μ ^ 3 / (p.H ^ 2 * p.ε))) + 4⌉₊) := by
  apply convergence_of_call_budget (S := spec) (fun p =>
    ⌈53 * (p.H ^ 2 * p.Δ / p.μ ^ 3) ^ (1 / 4 : ℝ) +
      5 * Real.log (1 + Real.log (1 + p.μ ^ 3 / (p.H ^ 2 * p.ε))) + 4⌉₊)
  refine ⟨method, ?_, fun _ _ => trivial⟩
  intro p hv K hK f O hadm
  obtain ⟨hH, hμ, hΔ, hε⟩ := hv
  obtain ⟨hf, hg, hLip, ⟨xstar, hmin, hgap, hPL⟩, hO⟩ := hadm
  have hexec : (fun seed : (method p.toPublic).Seed × ((k : ℕ) → O.Seed k) =>
      execute O (method p.toPublic) (fun _ => K) seed.1 seed.2) =
      fun _ => iterate f p.H p.x0 K := by
    funext seed
    have h1 := execute_eq_of_answer_eq O
      (fun x => (f x, gradient f x, fderiv ℝ (gradient f) x))
      (fun k query s => hO k s query) (method p.toPublic) K seed.1 seed.2
    have h2 := execute_iterate (fun x : p.E => (f x, gradient f x, fderiv ℝ (gradient f) x))
      (method p.toPublic) K seed.1
    exact h1.trans h2
  have hKr : 53 * (p.H ^ 2 * p.Δ / p.μ ^ 3) ^ (1 / 4 : ℝ) +
      5 * Real.log (1 + Real.log (1 + p.μ ^ 3 / (p.H ^ 2 * p.ε))) + 4 ≤ K :=
    (Nat.le_ceil _).trans (by exact_mod_cast hK)
  have hacc := iterate_accuracy hH hμ hΔ hε hf hg hLip hmin hgap hPL K hKr
  change Measurable _ ∧ ∃ xstar, IsMinOn f Set.univ xstar ∧ _ ∧ _
  rw [hexec]
  exact constant_success _ hmin hacc

end LongTails.Proofs.CubicNewtonPLConvergence
