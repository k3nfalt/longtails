import LongTails.Proofs.NoisyTwoSamplePerceptronCoordinates
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
open LongTails.Setups.FiniteLogisticTwoTap (Weights)
open LongTails.Setups.NoisyTwoSamplePerceptron
open LongTails.Proofs.FiniteLogisticTwoTapCoordinates
open LongTails.Proofs.FiniteLogisticTwoTapEntry
open LongTails.Proofs.NoisyTwoSamplePerceptronComplement
open LongTails.Proofs.NoisyTwoSamplePerceptronCoordinates

namespace LongTails.Proofs.NoisyTwoSamplePerceptronGaussian

noncomputable def component {d : ℕ} (i : Fin d) (k : Fin 5) : StrongDual ℝ (Weights d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w =>
        let z := coords i w
        ![z.p,z.q,z.u,z.r,z.v] k
      map_add' := fun x y => by
        have H := coords_euler i x y 0 1 0
        simp only [one_smul,zero_smul,add_zero] at H
        rw [H]
        fin_cases k <;> simp
      map_smul' := fun t x => by
        rw [coord_smul]
        fin_cases k <;> rfl }

lemma component_norm {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (hi : finRotate d i ≠ i) (k : Fin 5) :
    ‖component i k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul,Real.norm_eq_abs]
  have h01 : (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin d) ≠ .inl 1 :=
    fun h => (by decide : (0 : Fin 2) ≠ 1) (Sum.inl.inj h)
  by_cases h : d=2
  · subst d
    fin_cases k
    · simpa [component,coords] using pair_coordinate _ _ h01 1 (by norm_num) x
    · have H := abs_real_inner_le_norm
        (LongTails.Setups.FiniteLogisticTwoTap.liftReadout (LongTails.Setups.TwoSampleQuadraticPerceptron.ones 2)) x
      rw [inner_background,FiniteLogisticTwoTapSpectrum.norm_lift,TwoSampleQuadraticPerceptronEmbedding.norm_ones] at H
      change |readSum x / Real.sqrt (2:ℕ)| ≤ _
      rw [abs_div,abs_of_nonneg (Real.sqrt_nonneg _),div_le_iff₀ (by positivity)]
      linarith
    · simp [component,coords]
    · simpa [component,coords,sub_eq_add_neg] using pair_coordinate _ _ h01 (-1) (by norm_num) x
    · have hj : (Sum.inr (finRotate 2 i) : Fin 2 ⊕ Fin 2) ≠ .inr i := fun h => hi (Sum.inr.inj h)
      simpa [component,coords,sub_eq_add_neg] using pair_coordinate _ _ hj (-1) (by norm_num) x
  · obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := coordinate_bounds (by omega) i hi x
    fin_cases k <;> assumption

lemma projected_bounds {d : ℕ} (i : Fin d) (x : Weights d) (R : ℝ)
    (h : ∀ k, |component i k x| ≤ R) :
    ‖proj (coords i x)‖^2 + (slowProjection i x)^2 ≤ 5*R^2 := by
  have H (k : Fin 5) := pow_le_pow_left₀ (abs_nonneg _) (h k) 2
  simp only [sq_abs] at H
  have h₁ : (coords i x).p^2 ≤ R^2 := H 0
  have h₂ : (coords i x).q^2 ≤ R^2 := H 1
  have h₃ : (coords i x).u^2 ≤ R^2 := H 2
  have h₄ : (coords i x).r^2 ≤ R^2 := H 3
  have h₅ : (coords i x).v^2 ≤ R^2 := H 4
  rw [norm_sq,slow_coords]
  simp [proj,vec,div_pow]
  nlinarith

lemma dual_law {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (L : StrongDual ℝ E) :
    (stdGaussian E).map L = gaussianReal 0 (‖L‖^2).toNNReal := by
  rw [IsGaussian.map_eq_gaussianReal,variance_dual_stdGaussian]
  simp [ContinuousLinearMap.integral_comp_comm _ IsGaussian.integrable_fun_id]

lemma component_tail {d : ℕ} (hd : 2 ≤ d) (i : Fin d) (hi : finRotate d i ≠ i)
    (k : Fin 5) {a : ℝ} (ha : 0 ≤ a) :
    stdGaussian (Weights d) {x | a < |component i k x|} ≤ ENNReal.ofReal (2*Real.exp (-a^2/2)) := by
  let L := component i k
  let P := stdGaussian (Weights d)
  have hl : ‖L‖ ≤ 1 := component_norm hd i hi k
  have hsub : HasSubgaussianMGF L 1 P := by
    have H : HasSubgaussianMGF id 1 (P.map L) := by
      rw [dual_law]
      refine ⟨fun t => integrable_exp_mul_gaussianReal t,fun t => ?_⟩
      rw [mgf_id_gaussianReal]
      simp only [zero_mul,zero_add,NNReal.coe_one,one_mul,Real.toNNReal_of_nonneg (sq_nonneg _)]
      apply Real.exp_le_exp.mpr
      change ‖L‖^2*t^2/2 ≤ _
      nlinarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg L) hl 2) (sq_nonneg t)]
    exact HasSubgaussianMGF.of_map (X := id) (Y := (L : Weights d → ℝ)) L.continuous.aemeasurable H
  have h₁ := hsub.measure_ge_le ha
  have h₂ := hsub.neg.measure_ge_le ha
  simp only [NNReal.coe_one,mul_one] at h₁ h₂
  have hu : {x | a < |L x|} ⊆ {x | a ≤ L x} ∪ {x | a ≤ (-L x)} := by
    intro x hx
    change a < |L x| at hx
    rcases lt_abs.mp hx with h|h
    · exact Or.inl h.le
    · exact Or.inr h.le
  apply le_trans (measure_mono hu)
  apply (measure_union_le ..).trans
  rw [← ofReal_measureReal,← ofReal_measureReal,
    ← ENNReal.ofReal_add (measureReal_nonneg) (measureReal_nonneg)]
  apply ENNReal.ofReal_le_ofReal
  change P.real {x | a ≤ L x}+P.real {x | a ≤ (-L x)} ≤ _
  change P.real {x | a ≤ (-L x)} ≤ _ at h₂
  linarith

end LongTails.Proofs.NoisyTwoSamplePerceptronGaussian
