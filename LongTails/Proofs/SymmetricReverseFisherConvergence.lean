import LongTails.Proofs.SymmetricReverseFisherAccuracy
import LongTails.Proofs.SymmetricReverseFisherInitialization
open MeasureTheory OracleTemplate Set
open scoped RealInnerProductSpace
namespace LongTails.Proofs.SymmetricReverseFisherConvergence
open LongTails.Setups.SymmetricGaussianReverseFisher
open LongTails.Algorithms.SymmetricReverseFisherGD
open LongTails.Proofs.SymmetricReverseFisherDynamics
open LongTails.Proofs.SymmetricReverseFisherExecution
open LongTails.Proofs.SymmetricReverseFisherInitialization
open LongTails.Proofs.SymmetricReverseFisherBudget
open LongTails.Proofs.SymmetricReverseFisherAccuracy
lemma output_success (p : Params) (hp : spec.valid p) (μ : Space p)
    (oracle : Oracle (Space p) (Space p)) (ho : spec.admissible p μ oracle) :
    spec.successful p μ
      (fun z : (algorithm p).Seed × ((k : ℕ) → oracle.Seed k) =>
        output p oracle (iterations p.dimension p.lower p.upper p.failure p.accuracy) z.1 z.2)
      ⟨((algorithm p).law : Measure _).prod (oracle.law : Measure _), inferInstance⟩ := by
  rcases hp with ⟨hs, hsB, hε, hε1, hδ, hδ1⟩
  rcases ho with ⟨hsa, haB, horacle⟩
  let K := iterations p.dimension p.lower p.upper p.failure p.accuracy
  have hd : 1 ≤ (p.dimension : ℝ) := by exact_mod_cast p.dimension.pos
  refine ⟨output_measurable p μ oracle horacle K, ?_⟩
  change ENNReal.ofReal (1-p.failure) ≤
    ((Measure.pi (fun _ : Fin p.dimension => (coordinateLaw : Measure ℝ))).prod (oracle.law : Measure _))
      {z | min (‖output p oracle K z.1 z.2 - μ‖^2) (‖output p oracle K z.1 z.2 + μ‖^2) ≤ p.accuracy}
  by_cases hμ : μ = 0
  · have hgood (z : (Fin p.dimension → ℝ) × ((k : ℕ) → oracle.Seed k)) :
        min (‖output p oracle K z.1 z.2 - μ‖^2) (‖output p oracle K z.1 z.2 + μ‖^2) ≤ p.accuracy := by
      rw [output_eq_iterate p μ oracle horacle K]
      change min (‖(gdStep μ (1/(48+20*p.upper)))^[K] (initial p z.1)-μ‖^2)
        (‖(gdStep μ (1/(48+20*p.upper)))^[K] (initial p z.1)+μ‖^2) ≤ p.accuracy
      apply (min_le_left _ _).trans
      exact small_accuracy_public μ (initial p z.1) hd hs hsa haB hδ hδ1 hε hε1
        (by simp only [hμ, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]; positivity) (initial_norm p z.1)
    have hevent : {z : (Fin p.dimension → ℝ) × ((k : ℕ) → oracle.Seed k) |
        min (‖output p oracle K z.1 z.2 - μ‖^2) (‖output p oracle K z.1 z.2 + μ‖^2) ≤ p.accuracy} = univ := by
      ext z
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact hgood z
    rw [hevent, measure_univ]
    exact ENNReal.ofReal_le_one.mpr (by linarith)
  · let e := ‖μ‖⁻¹ • μ
    have ha : 0 < ‖μ‖ := norm_pos_iff.mpr hμ
    have he : ‖e‖ = 1 := by
      dsimp [e]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ha, inv_mul_cancel₀ ha.ne']
    let S : Set (Fin p.dimension → ℝ) := {z | p.failure/(p.dimension : ℝ) ≤ |⟪initial p z,e⟫|}
    have hsubset : S ×ˢ (univ : Set ((k : ℕ) → oracle.Seed k)) ⊆
        {z | min (‖output p oracle K z.1 z.2 - μ‖^2) (‖output p oracle K z.1 z.2 + μ‖^2) ≤ p.accuracy} := by
      rintro ⟨z,ξ⟩ ⟨hz,_⟩
      rw [mem_ofPred_eq, output_eq_iterate p μ oracle horacle K]
      exact accuracy_of_projection μ (initial p z) hd hs hsa haB hδ hδ1 hε hε1 hμ (initial_norm p z) hz
    have hm := measure_mono (μ := (Measure.pi (fun _ : Fin p.dimension => (coordinateLaw : Measure ℝ))).prod (oracle.law : Measure _)) hsubset
    rw [Measure.prod_prod, measure_univ, mul_one] at hm
    exact (initial_projection_probability e he hδ).trans hm
end LongTails.Proofs.SymmetricReverseFisherConvergence
