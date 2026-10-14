import LongTails.Proofs.Execution
import LongTails.Proofs.ReshuffledHarmonicConvergence
import LongTails.Proofs.ReshuffledConstantStepParameters
import LongTails.Proofs.ReshuffledExecution

set_option autoImplicit false

open Finset MeasureTheory

namespace OracleTemplate.ConstantStepReshuffledConvex

open LongTails.Setups.ConstantStepReshuffledSmoothConvex

open ReshuffledConvex

set_option maxHeartbeats 1000000 in
lemma convergence : Convergence spec (fun p _ => p.n * epochCount p) := by
  apply convergence_of_public_budget (S := spec) (fun p => p.n * epochCount p)
  refine ⟨algorithm, ?_, fun p hp => ⟨epochCount p, stepSize p, (parameters p hp).2.1, rfl⟩⟩
  intro p hp f O hadm
  obtain ⟨hK, hη, hcap, htune⟩ := parameters p hp
  rcases hp with ⟨hLa, hLm, hR, hσ, hε⟩
  rcases hadm with ⟨hconv, hgrad, ⟨ℓ, hℓ0, hℓmax, havg, hlip⟩, xstar, hmin, hdist, hnoise⟩
  let ξ0 := Classical.choice O.law.nonempty
  let g : Fin p.n → p.E → p.E := fun i x => gradient (f i) x
  have hans : ∀ k (q : Fin p.n × p.E) seed, O.answer k (0, q) seed = g q.1 q.2 :=
    fun k q seed => (hgrad k seed q.1 q.2).gradient.symm
  have hgradg : ∀ i x, HasGradientAt (f i) (g i x) x := fun i x => by
    have hh := hgrad 0 (ξ0 0) i x
    rw [hans 0 (i, x) (ξ0 0)] at hh
    exact hh
  have hyp : Hyp f g ℓ p.Lavg p.Lmax p.σ xstar :=
    ⟨hLa, hLm, hconv, hgradg, hℓ0, hℓmax, havg, hlip, hmin, hnoise⟩
  let out := fun seed : Orders p.n (epochCount p) =>
    iterate g (schedule seed) (fun _ => stepSize p) p.x0 (p.n * epochCount p)
  have hexec : ∀ (seed : Orders p.n (epochCount p)) (ξ : (k : ℕ) → O.Seed k),
      execute O (algorithm p) (fun _ => (p.n * epochCount p)) seed ξ = out seed := by
    intro seed ξ
    have he := execute_eq_of_answer_eq O (fun q => g q.1 q.2) (fun k q s => hans k q s)
      (algorithm p) (p.n * epochCount p) seed ξ
    exact he.trans (execute_reshuffled g (epochCount p) _ p.x0 (p.n * epochCount p) seed)
  have hbound : ∑ seed : Orders p.n (epochCount p),
      (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) ≤
      Fintype.card (Orders p.n (epochCount p)) * p.ε := by
    have hb := ReshuffledHarmonicConvergence.sum_gap hyp (stepSize p) p.x0 hK hη hdist hcap
    change (∑ seed : Orders p.n (epochCount p),
        (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)) ≤ _ at hb
    have he : 2 * ((Fintype.card (Orders p.n (epochCount p)) : ℝ) * p.R ^ 2) /
        (stepSize p * (p.n * epochCount p : ℕ)) +
        66 * stepSize p * ReshuffledHarmonic.H p.n * ReshuffledHarmonic.H (p.n * epochCount p) *
          ((Fintype.card (Orders p.n (epochCount p)) : ℝ) * p.σ ^ 2) =
        (Fintype.card (Orders p.n (epochCount p)) : ℝ) *
          (2 * p.R ^ 2 / (stepSize p * (p.n * epochCount p : ℕ)) +
            66 * stepSize p * ReshuffledHarmonic.H p.n * ReshuffledHarmonic.H (p.n * epochCount p) * p.σ ^ 2) := by ring
    rw [he] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left htune (Nat.cast_nonneg _))
  have hNpos : (0 : ℝ) < Fintype.card (Orders p.n (epochCount p)) := by
    exact_mod_cast Fintype.card_pos
  have hres : ∀ seed : Orders p.n (epochCount p) × ((k : ℕ) → O.Seed k),
      execute O (algorithm p) (fun _ => (p.n * epochCount p)) seed.1 seed.2 = out seed.1 :=
    fun seed => hexec seed.1 seed.2
  change spec.successful p f
      (fun seed => (execute O (algorithm p) (fun _ => (p.n * epochCount p)) seed.1 seed.2))
      ⟨(PMF.uniformOfFintype (Orders p.n (epochCount p))).toMeasure.prod
        (O.law : Measure ((k : ℕ) → O.Seed k)), inferInstance⟩
  simp only [hres]
  change Measurable (fun seed : Orders p.n (epochCount p) × ((k : ℕ) → O.Seed k) => out seed.1) ∧ _
  refine ⟨(measurable_from_top : Measurable out).comp measurable_fst, xstar, hmin, ?_, ?_⟩
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun seed : Orders p.n (epochCount p) =>
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)
        (μ := (PMF.uniformOfFintype (Orders p.n (epochCount p))).toMeasure))
  · change (∫ seed : Orders p.n (epochCount p) × ((k : ℕ) → O.Seed k),
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed.1) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar
        ∂(PMF.uniformOfFintype (Orders p.n (epochCount p))).toMeasure.prod
          (O.law : Measure ((k : ℕ) → O.Seed k))) ≤ p.ε
    rw [integral_fun_fst (fun seed => LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)]
    simp only [probReal_univ, one_smul]
    have hint : (∫ seed : Orders p.n (epochCount p),
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar
        ∂(PMF.uniformOfFintype (Orders p.n (epochCount p))).toMeasure) =
        (Fintype.card (Orders p.n (epochCount p)) : ℝ)⁻¹ * ∑ seed : Orders p.n (epochCount p),
          (LongTails.Setups.FiniteSumSmoothAndConvex.objective f (out seed) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar) := by
      simp [PMF.integral_eq_sum, PMF.uniformOfFintype_apply, ← Finset.mul_sum]
    rw [hint]
    calc
      _ ≤ (Fintype.card (Orders p.n (epochCount p)) : ℝ)⁻¹ *
          (Fintype.card (Orders p.n (epochCount p)) * p.ε) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hNpos.le)
      _ = p.ε := by rw [← mul_assoc, inv_mul_cancel₀ hNpos.ne', one_mul]

end OracleTemplate.ConstantStepReshuffledConvex
