import LongTails.Proofs.AbcSgdRate
import LongTails.Algorithms.AbcSgd
import LongTails.Setups.AbcNoiseNonconvex
import LongTails.Setups.HighDimensionalAbcNoiseNonconvex
import LongTails.Proofs.Execution
import LongTails.Proofs.MixedNoiseSelectors
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory OracleTemplate
open scoped BigOperators

namespace LongTails.Proofs.AbcSgdUpper

open LongTails.Proofs.AbcSgdRate LongTails.Algorithms.AbcSgd

section Iterates

variable {E : Type} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def sgdIter (g : E → Ω → E) (η : ℝ) (x0 : E) (ξ : ℕ → Ω) : ℕ → E
  | 0 => x0
  | t + 1 => sgdIter g η x0 ξ t - η • g (sgdIter g η x0 ξ t) (ξ t)

lemma sgdIter_succ_shift (g : E → Ω → E) (η : ℝ) (x0 : E) (ξ : ℕ → Ω) (t : ℕ) :
    sgdIter g η x0 ξ (t + 1) = sgdIter g η (x0 - η • g x0 (ξ 0)) (fun i => ξ (i + 1)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [sgdIter, ih]
    rfl

lemma gradLoss_eq_sum [CompleteSpace E] (f : E → ℝ) (g : E → Ω → E) (η : ℝ) (K : ℕ) (x0 : E)
    (ξ : ℕ → Ω) :
    gradLoss f g η K x0 (fun i : Fin K => ξ i) =
      ∑ t ∈ Finset.range K, ‖gradient f (sgdIter g η x0 ξ t)‖ ^ 2 := by
  induction K generalizing x0 ξ with
  | zero => rfl
  | succ K ih =>
    rw [Finset.sum_range_succ', gradLoss]
    have h := ih (x0 - η • g x0 (ξ 0)) (fun i => ξ (i + 1))
    have he : (fun i : Fin K => (fun i : Fin (K + 1) => ξ i) i.succ) =
        fun i : Fin K => (fun i => ξ (i + 1)) (i : ℕ) := by
      funext i; simp [Fin.val_succ]
    simp only [Fin.val_zero] at h ⊢
    rw [he, h]
    simp only [sgdIter_succ_shift]
    rw [show sgdIter g η x0 ξ 0 = x0 from rfl]
    ring

lemma execute_sampledSgd {Ω : Type} [MeasurableSpace Ω] (g : E → Ω → E) (η : ℝ) (K : ℕ)
    (x0 : E) (law : ProbabilityMeasure (ℕ → Ω)) (τ : Fin (K + 1)) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω }
      (sampledSgd η K x0) (fun _ => K + 1) τ ξ = sgdIter g η x0 ξ τ.val := by
  rw [execute_indexed_of_answer
    ({ Seed := fun _ => Ω, law := law, answer := fun _ (_, x) ω => g x ω } : Oracle E E)
    (sampledSgd η K x0) (K + 1) τ ξ (fun t query => g query.2 (ξ t))
    (fun _ query => by cases query; rfl)]
  have hstate : ∀ t, ((fun sc : (sampledSgd η K x0).State × ℕ =>
      ((sampledSgd η K x0).update sc.1 (g ((sampledSgd η K x0).query sc.1).2 (ξ sc.2)),
        sc.2 + 1))^[t] ((sampledSgd η K x0).initial τ, 0)) =
      ((τ, t, sgdIter g η x0 ξ t, if τ.val < t then sgdIter g η x0 ξ τ.val else x0), t) := by
    intro t
    induction t with
    | zero => simp [sampledSgd, sgdIter]
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [sampledSgd, Prod.mk.injEq, true_and, and_true]
      refine ⟨rfl, ?_⟩
      by_cases h1 : t = τ.val
      · subst h1; simp
      · rw [ite_eq_right h1]
        by_cases h2 : τ.val < t
        · rw [ite_eq_left h2, ite_eq_left (by omega)]
        · rw [ite_eq_right h2, ite_eq_right (by omega)]
  rw [hstate]
  simp [sampledSgd, τ.isLt]

end Iterates

section Rate

variable {E : Type} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma sgdIter_measurable {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (η : ℝ)
    (x0 : E) (t : ℕ) : Measurable (fun ξ : ℕ → Ω => sgdIter g η x0 ξ t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    exact ih.sub ((hg.comp (ih.prodMk (measurable_pi_apply t))).const_smul η)

lemma exp_le_three : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le

lemma rho_pow_le (c : ℝ) (hc : 0 ≤ c) (M : ℕ) (hM : (M : ℝ) * c ≤ 1) : (1 + c) ^ M ≤ 3 := by
  have h1 : (1 + c) ^ M ≤ (Real.exp c) ^ M :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp c]) M
  rw [← Real.exp_nat_mul] at h1
  have h2 : Real.exp (M * c) ≤ Real.exp 1 := Real.exp_le_exp.mpr hM
  exact h1.trans (h2.trans exp_le_three)

end Rate

end LongTails.Proofs.AbcSgdUpper
