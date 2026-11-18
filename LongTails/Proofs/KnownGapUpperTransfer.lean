import LongTails.Setups.GeneralizedSmoothConvexKnownGapPolynomialDimension
import LongTails.Proofs.Execution
import LongTails.Proofs.RadiusFreeSherpaBudget
import LongTails.Proofs.GeneralizedConvergence
import LongTails.Proofs.DampedGeneralizedExecution
import LongTails.Algorithms.KnownGapSelection

open MeasureTheory

namespace OracleTemplate.RadiusFreeSherpa

open LongTails.Setups.RadiusOnlyGeneralizedSmoothConvex

lemma sherpa_gap (q : Params) (hq : spec.valid q) (N : ℕ)
    (hN : ⌈64 * Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + 32768 * (1 + q.L1 * q.R) * Real.log (2 + q.L1 * q.R)⌉₊ ≤ N)
    (f : q.E → ℝ) (oracle : Oracle q.E q.E) (hadm : spec.admissible q f oracle) :
    ∃ u, IsMinOn f Set.univ u ∧ ∀ (seed : (algorithm q.toPublic).Seed) (ξ : (k : ℕ) → oracle.Seed k),
      f (execute oracle (algorithm q.toPublic) (fun _ => N) seed ξ) - f u ≤ q.ε := by
  obtain ⟨hL0, hL1, hR, hε⟩ := hq
  obtain ⟨hc, hg, hgd, hH, u, hmin, hdist⟩ := hadm
  let seed0 := (Classical.choice oracle.law.nonempty) 0
  let g := fun x => oracle.answer [] (0, x) seed0
  have H : Hyp f g q.L0 q.L1 u := ⟨hL0, hL1.le, hc, hg [] seed0, hgd [] seed0, hH [] seed0, hmin⟩
  set qq := q.L1 * q.R with hqq
  have hqpos : 0 < qq := by positivity
  have hexec (seed : (algorithm q.toPublic).Seed) (ξ : (k : ℕ) → oracle.Seed k) :
      execute oracle (algorithm q.toPublic) (fun _ => N) seed ξ =
        stateOutput ((T q.L0 q.L1 g)^[N] (initState q.x0)) := by
    rw [execute_eq_of_answer_eq oracle g
      (fun k x sample => (hg k sample x).unique (hg [] seed0 x))]
    exact execute_algorithm q.toPublic g N
  have hacc : f (stateOutput ((T q.L0 q.L1 g)^[N] (initState q.x0))) - f u ≤ q.ε := by
    have hNreal : ((⌈64 * Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + 32768 * (1 + qq) * Real.log (2 + qq)⌉₊ : ℕ) : ℝ) ≤ N := by
      exact_mod_cast hN
    have hceil : 64 * Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + 32768 * (1 + qq) * Real.log (2 + qq) ≤
        ((⌈64 * Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + 32768 * (1 + qq) * Real.log (2 + qq)⌉₊ : ℕ) : ℝ) :=
      Nat.le_ceil _
    have hsteps := phaseSteps_le hqpos.le
    have hp2 := phase2_bound_le (A := q.L0 * q.R ^ 2 / q.ε) hqpos.le
    have hlogpos := log2q_pos hqpos.le
    rcases run_dichotomy H hL1 hqq hR hdist N with ⟨ph, hstate, hinv⟩ | ⟨z, c1, hc1, hz, hc1le, hstate⟩
    · exfalso
      have h1 := hinv.steps_le
      have : (N : ℝ) ≤ 15700 * (1 + qq) * Real.log (2 + qq) := h1.trans hsteps
      have hsq : 0 ≤ Real.sqrt (q.L0 * q.R ^ 2 / q.ε) := Real.sqrt_nonneg _
      nlinarith [mul_nonneg hqpos.le hlogpos.le]
    · rw [hstate]
      simp only [exitState]
      rw [T_second_iterate, output_second]
      have hgap := hz.gap H
      have hzd : ‖z - u‖ ≤ q.R := hz.1
      have hh0 : (0 : ℝ) < 1 / q.L0 := by positivity
      apply ParameterFreeGeneralized.trial_accuracy H hR hh0 hε hzd
      have hb := ParameterFreeGeneralized.budget_bound (Δ := q.L0 * q.R / (4 * q.L1)) H hR hh0 hε hgap
      have h4L0 : (4 * q.L0 : ℝ) ≠ 0 := (mul_pos (by norm_num) hL0).ne'
      have h4L1 : (4 * q.L1 : ℝ) ≠ 0 := (mul_pos (by norm_num) hL1).ne'
      have e1 : 1 / (64 * q.L0 * (1 / q.L0)) = (1 : ℝ) / 64 := by
        rw [mul_one_div, mul_div_assoc, div_self hL0.ne', mul_one]
      have e2 : 5 * q.L1 ^ 2 * (q.L0 * q.R / (4 * q.L1)) / (4 * q.L0) = 5 * qq / 16 := by
        rw [hqq, div_eq_iff h4L0, mul_div_assoc', div_eq_iff h4L1]; ring
      have e3 : 16 * q.L0 * (1 / q.L0) = (16 : ℝ) := by
        rw [mul_one_div, mul_div_assoc, div_self hL0.ne', mul_one]
      have e4 : 80 * q.L1 ^ 2 * (q.L0 * q.R / (4 * q.L1)) * (1 / q.L0) = 20 * qq := by
        rw [hqq, mul_one_div, div_eq_iff hL0.ne', mul_div_assoc', div_eq_iff h4L1]; ring
      have e7 : 13 * q.L1 * q.R = 13 * qq := by rw [hqq]; ring
      have e8 : 32 * q.L0 * q.R ^ 2 / q.ε = 32 * (q.L0 * q.R ^ 2 / q.ε) := by ring
      rw [e1, e2, e3, e4, e7, e8] at hb
      have hb' : 2 * (2 + (1 + ParameterFreeGeneralized.sigma q.L1 q.R) *
            Real.log (1 + ParameterFreeGeneralized.cap q.L0 * ParameterFreeGeneralized.sigma q.L1 q.R ^ 2 /
              ParameterFreeGeneralized.eta g z q.L0 q.L1 (1 / q.L0)) +
          2 * Real.sqrt (q.R ^ 2 / (2 * q.ε)) / Real.sqrt (ParameterFreeGeneralized.cap q.L0)) +
        Real.logb 2 ((1 / q.L0) / min (ParameterFreeGeneralized.cap q.L0)
          (ParameterFreeGeneralized.eta g z q.L0 q.L1 (1 / q.L0) / ParameterFreeGeneralized.sigma q.L1 q.R ^ 2)) ≤
        23 * Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + 262 * (1 + qq) * Real.log (2 + qq) := by
        have e5 : 1 + 16 + 20 * qq = 17 + 20 * qq := by ring
        rw [e5] at hb
        linarith [hb, hp2]
      have hc1r : (c1 : ℝ) ≤ phaseSteps qq + 1 := hc1le
      have hdiv : (((N - c1) / 2 : ℕ) : ℝ) ≥ ((N : ℝ) - c1 - 1) / 2 := by
        have h2 := Nat.div_add_mod (N - c1) 2
        have hmod : (N - c1) % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
        have hc : ((2 * ((N - c1) / 2) + (N - c1) % 2 : ℕ) : ℝ) = ((N - c1 : ℕ) : ℝ) := by
          exact_mod_cast h2
        have hm : (((N - c1) % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hmod
        rw [Nat.cast_sub hc1] at hc
        push_cast at hc
        linarith
      have hsq : 0 ≤ Real.sqrt (q.L0 * q.R ^ 2 / q.ε) := Real.sqrt_nonneg _
      have hfinal : 23 * Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + 262 * (1 + qq) * Real.log (2 + qq) <
          (((N - c1) / 2 : ℕ) : ℝ) := by
        have := one_le_log2q hqpos.le
        nlinarith [mul_nonneg hqpos.le hlogpos.le]
      exact lt_of_le_of_lt hb' hfinal
  refine ⟨u, hmin, fun seed ξ => ?_⟩
  rw [hexec seed ξ]
  exact hacc

end OracleTemplate.RadiusFreeSherpa

namespace OracleTemplate.GeneralizedAccelerated

open LongTails.Setups.GeneralizedSmoothAndConvex

lemma accelerated_gap (q : Params) (hq : spec.valid q) (K : ℕ)
    (hK : 4096 * (1 + Real.sqrt (q.L0 * q.R ^ 2 / q.ε) +
      (⌈(q.L1 * q.R) ^ (2 / 3 : ℝ)⌉₊ : ℝ) * Real.log (4 + 4 * q.Δ / q.ε)) ≤ K)
    (f : q.E → ℝ) (oracle : Oracle q.E q.E) (hadm : spec.admissible q f oracle) :
    ∃ u, IsMinOn f Set.univ u ∧ ∀ (seed : (algorithm q.toPublic).Seed) (ξ : (k : ℕ) → oracle.Seed k),
      f (execute oracle (algorithm q.toPublic) (fun _ => 2 * K) seed ξ) - f u ≤ q.ε := by
  obtain ⟨hL0, hL1, hR, hΔ, hε⟩ := hq
  obtain ⟨hc, hg, hgd, hH, u, hmin, hdist, hgap⟩ := hadm
  let seed0 := (Classical.choice oracle.law.nonempty) 0
  let g := fun x => oracle.answer [] (0, x) seed0
  have hacc := run_accuracy hL0 hL1 hR hΔ hε hc (hg [] seed0) (hgd [] seed0)
    (hH [] seed0) q.x0 u hmin hdist hgap K hK
  refine ⟨u, hmin, fun seed ξ => ?_⟩
  have hexec := execute_gradient_oracle q.toPublic f g oracle (hg [] seed0) hg hL0 hL1 hΔ K seed ξ
  rw [hexec]
  exact hacc

end OracleTemplate.GeneralizedAccelerated

namespace LongTails.Proofs.KnownGapUpperTransfer

open OracleTemplate OracleTemplate.KnownGapSelection MeasureTheory

variable {E : Type*}

lemma combine_iterate_left (c : Prop) [Decidable c] (A B : Algorithm E E E) (g : E → E)
    (s : A.State) (K : ℕ) :
    (fun t => (combine c A B).update t (g ((combine c A B).query t).2))^[K] (Sum.inl s) =
      Sum.inl ((fun t => A.update t (g (A.query t).2))^[K] s) := by
  induction K generalizing s with
  | zero => rfl
  | succ K ih =>
    have h1 := Function.iterate_succ_apply
      (fun t => (combine c A B).update t (g ((combine c A B).query t).2)) K (Sum.inl s)
    have h2 := Function.iterate_succ_apply (fun t => A.update t (g (A.query t).2)) K s
    rw [h1, h2]
    exact ih _

lemma combine_iterate_right (c : Prop) [Decidable c] (A B : Algorithm E E E) (g : E → E)
    (s : B.State) (K : ℕ) :
    (fun t => (combine c A B).update t (g ((combine c A B).query t).2))^[K] (Sum.inr s) =
      Sum.inr ((fun t => B.update t (g (B.query t).2))^[K] s) := by
  induction K generalizing s with
  | zero => rfl
  | succ K ih =>
    have h1 := Function.iterate_succ_apply
      (fun t => (combine c A B).update t (g ((combine c A B).query t).2)) K (Sum.inr s)
    have h2 := Function.iterate_succ_apply (fun t => B.update t (g (B.query t).2)) K s
    rw [h1, h2]
    exact ih _

lemma combine_execute_left (c : Prop) [Decidable c] (hc : c) (A B : Algorithm E E E) (g : E → E)
    (K : ℕ) (seed : (combine c A B).Seed) :
    execute { answer := fun _ query _ => g query.2 } (combine c A B) (fun _ => K) seed =
      execute { answer := fun _ query _ => g query.2 } A (fun _ => K)
        (Classical.choice A.law.nonempty) := by
  have hinit : (combine c A B).initial seed = Sum.inl (A.initial (Classical.choice A.law.nonempty)) := by
    simp only [combine, hc, ↓reduceIte]
  rw [execute_iterate, execute_iterate, hinit, combine_iterate_left]
  rfl

lemma combine_execute_right (c : Prop) [Decidable c] (hc : ¬ c) (A B : Algorithm E E E) (g : E → E)
    (K : ℕ) (seed : (combine c A B).Seed) :
    execute { answer := fun _ query _ => g query.2 } (combine c A B) (fun _ => K) seed =
      execute { answer := fun _ query _ => g query.2 } B (fun _ => K)
        (Classical.choice B.law.nonempty) := by
  have hinit : (combine c A B).initial seed = Sum.inr (B.initial (Classical.choice B.law.nonempty)) := by
    simp only [combine, hc, ↓reduceIte]
  rw [execute_iterate, execute_iterate, hinit, combine_iterate_right]
  rfl

lemma constant_success {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (output : Ω → EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (ε : ℝ) (v : EuclideanSpace ℝ (Fin d))
    (hc : ∀ ω, output ω = v) (h : f v - f u ≤ ε) :
    Integrable (fun ω => f (output ω) - f u) (P : Measure Ω) ∧
      (∫ ω, f (output ω) - f u ∂(P : Measure Ω)) ≤ ε := by
  have he : (fun ω => f (output ω) - f u) = fun _ => f v - f u := by
    funext ω
    rw [hc ω]
  rw [he]
  refine ⟨integrable_const _, ?_⟩
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  exact h

end LongTails.Proofs.KnownGapUpperTransfer
