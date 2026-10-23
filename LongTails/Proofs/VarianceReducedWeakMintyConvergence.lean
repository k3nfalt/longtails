import LongTails.Proofs.VarianceReducedWeakMintyEpoch
import LongTails.Proofs.VarianceReducedWeakMintyTuning
import LongTails.Proofs.Execution
import Mathlib.MeasureTheory.Integral.Prod

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace OracleTemplate.VarianceReducedWeakMinty

open LongTails.Setups.FiniteSumWeakMintyInclusion

lemma tuned_residual_bound (p : Params) [NeZero p.n] (hp : spec.valid p)
    (F : Fin p.n → p.E → p.E) (J : ℝ → p.E → p.E) (A : p.E → Set p.E) (xstar : p.E)
    (hJ : ∀ η z, 0 < η → η⁻¹ • (z - J η z) ∈ A (J η z))
    (hA : ∀ x y, ∀ a ∈ A x, ∀ b ∈ A y, 0 ≤ ⟪a - b, x - y⟫)
    (hF : ∀ u v, ‖operator F u - operator F v‖ ≤ p.L * ‖u - v‖)
    (hvar : ∀ u v, (p.n : ℝ)⁻¹ * ∑ i, ‖F i u - F i v‖ ^ 2 ≤ p.Λ ^ 2 * ‖u - v‖ ^ 2)
    (hwm : ∀ y, ∀ v ∈ A y, -p.ρ * ‖operator F y + v‖ ^ 2 ≤ ⟪operator F y + v, y - xstar⟫)
    (hradius : ‖p.x0 - xstar‖ ≤ p.R) :
    let η := (2 - margin p) / (2 * p.L)
    let s := margin p / (2 - margin p)
    let a := (epochLength p : ℝ)⁻¹
    (𝔼 ξ : Seeds p.n (batchSize p) (innerLength p) (epochLength p) (epochCount p),
      ‖operator F (QueryPlan.eval (answer F J) (outputPlan (useExact p) η s a p.x0 (ξ.epochs, ξ.selection))).1 +
        (QueryPlan.eval (answer F J) (outputPlan (useExact p) η s a p.x0 (ξ.epochs, ξ.selection))).2‖ ^ 2) ≤
      p.ε ^ 2 := by
  dsimp only
  obtain ⟨hδ, hδ1⟩ := valid_margin p hp
  obtain ⟨hη, hs, hs1, hsδ, hηL, hhlo, hhhi, hprod⟩ := tuning_parameters hδ hδ1 hp.2.1
  have ha : (epochLength p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [← one_div, div_le_iff₀ (by exact_mod_cast NeZero.pos (epochLength p))]
    have hh : (2 : ℝ) ≤ epochLength p := by exact_mod_cast epoch_length_two p
    linarith
  have hrel : p.ρ = (2 - margin p) / (2 * p.L) * (1 - margin p / (2 - margin p)) := by
    have hd : 2 - margin p ≠ 0 := by linarith
    field_simp [hp.2.1.ne', hd]
    dsimp [margin]
    ring
  rw [seeds_expectation (fun ξ =>
    ‖operator F (QueryPlan.eval (answer F J) (outputPlan (useExact p)
      ((2 - margin p) / (2 * p.L)) (margin p / (2 - margin p))
      (epochLength p : ℝ)⁻¹ p.x0 ξ)).1 +
      (QueryPlan.eval (answer F J) (outputPlan (useExact p)
      ((2 - margin p) / (2 * p.L)) (margin p / (2 - margin p))
      (epochLength p : ℝ)⁻¹ p.x0 ξ)).2‖ ^ 2)]
  have hh := outputPlan_residual_bound (q := epochLength p) (M := epochCount p) (b := batchSize p) (k := innerLength p - 1) (useExact p) F J A p.x0 xstar
    hη hp.2.1 hηL hs hs1 rfl ha hrel (by linarith) rfl (batch_size_pos p hp) (tuned_noise p hp)
    (by simpa only [innerLength, Nat.add_sub_cancel] using tuning_power hδ hδ1 hhlo hhhi hsδ)
    hJ hA hF hvar hwm hradius
  have hj : innerLength p - 1 + 1 = innerLength p := by unfold innerLength; omega
  rw [hj] at hh
  refine hh.trans ?_
  have hid : 32 * p.R ^ 2 /
      ((margin p / (2 - margin p)) ^ 2 * ((2 - margin p) / (2 * p.L)) ^ 2 *
        (epochLength p * epochCount p : ℕ)) =
      128 * p.L ^ 2 * p.R ^ 2 / (margin p ^ 2 * (epochLength p * epochCount p : ℕ)) := by
    rw [← mul_pow, hprod]
    field_simp
    ring
  rw [hid]
  apply tuning_iterations hδ hp.2.1 hp.2.2.2.2.2.2 (NeZero.pos _) (NeZero.pos _)
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_max_right _ _))

lemma algorithm_success (p : Params) [NeZero p.n] (hp : spec.valid p)
    (I : spec.Instance p) (oracle : Oracle (spec.Query p) (spec.Reply p))
    (hadm : spec.admissible p I oracle) {K : ℕ}
    (hK : (stepCost (useExact p) p.n (batchSize p) (innerLength p) * epochLength p + p.n) *
      epochCount p ≤ K) :
    let η := (2 - margin p) / (2 * p.L)
    let s := margin p / (2 - margin p)
    let a := algorithm (useExact p) η s (epochLength p : ℝ)⁻¹ p.x0
      (batchSize p) (innerLength p) (epochLength p) (epochCount p)
    spec.successful p I
      (fun seed : a.Seed × ((k : ℕ) → oracle.Seed k) => execute oracle a (fun _ => K) seed.1 seed.2)
      ⟨(a.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩ := by
  rcases hadm with ⟨J, hcomp, hprox, hJ, hA, hF, hvar, xstar, _, hradius, hwm⟩
  let η := (2 - margin p) / (2 * p.L)
  let s := margin p / (2 - margin p)
  let a := (epochLength p : ℝ)⁻¹
  let Ω := Seeds p.n (batchSize p) (innerLength p) (epochLength p) (epochCount p)
  let Y := fun ξ : Ω => QueryPlan.eval (answer I.1 J)
    (outputPlan (useExact p) η s a p.x0 (ξ.epochs, ξ.selection))
  have hanswer : ∀ history query seed, oracle.answer history (0, query) seed = answer I.1 J query := by
    intro history query seed
    rcases query with ⟨i, x⟩ | ⟨step, z⟩
    · exact hcomp history seed i x
    · exact hprox history seed step z
  have hexec (ξ : Ω) (oracleSeed : (k : ℕ) → oracle.Seed k) :
      execute oracle (algorithm (useExact p) η s a p.x0 (batchSize p)
        (innerLength p) (epochLength p) (epochCount p)) (fun _ => K) ξ oracleSeed = Y ξ := by
    erw [execute_eq_of_answer_eq oracle (answer I.1 J) hanswer, execute_algorithm _ _ _ _ _ _ _ _ hK]
  change spec.successful p I
    (fun seed : Ω × ((k : ℕ) → oracle.Seed k) =>
      execute oracle (algorithm (useExact p) η s a p.x0 (batchSize p)
        (innerLength p) (epochLength p) (epochCount p)) (fun _ => K) seed.1 seed.2)
    ⟨(PMF.uniformOfFintype Ω).toMeasure.prod (oracle.law : Measure _), inferInstance⟩
  simp only [hexec]
  change Measurable (fun seed : Ω × ((k : ℕ) → oracle.Seed k) => Y seed.1) ∧ _
  refine ⟨(measurable_from_top : Measurable Y).comp measurable_fst, ?_, ?_, ?_⟩
  · apply Filter.Eventually.of_forall
    intro ξ
    have hη := (tuning_parameters (valid_margin p hp).1 (valid_margin p hp).2 hp.2.1).1
    exact eval_outputPlan_member (useExact p) I.1 J I.2 hη (fun z => hJ η z hη)
      s a p.x0 (by unfold innerLength; omega) (ξ.1.epochs, ξ.1.selection)
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun ξ : Ω => ‖operator I.1 (Y ξ).1 + (Y ξ).2‖ ^ 2)
        (μ := (PMF.uniformOfFintype Ω).toMeasure))
  · change (∫ ξ : Ω × ((k : ℕ) → oracle.Seed k),
      ‖operator I.1 (Y ξ.1).1 + (Y ξ.1).2‖ ^ 2
      ∂(PMF.uniformOfFintype Ω).toMeasure.prod (oracle.law : Measure _)) ≤ p.ε ^ 2
    rw [integral_fun_fst (fun ξ : Ω => ‖operator I.1 (Y ξ).1 + (Y ξ).2‖ ^ 2)]
    simp only [probReal_univ, one_smul]
    rw [FiniteSum.uniform_integral]
    exact tuned_residual_bound p hp I.1 J I.2 xstar hJ hA hF hvar hwm hradius

end OracleTemplate.VarianceReducedWeakMinty
