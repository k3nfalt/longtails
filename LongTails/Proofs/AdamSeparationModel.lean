import LongTails.Proofs.AdamSeparationInstance
import LongTails.Setups.SpectralSmoothAdamComparison
import LongTails.Proofs.GaussianBlocks
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace LongTails.Proofs.AdamSeparationModel

open MeasureTheory ProbabilityTheory
open LongTails.Algorithms.MatrixPolar
open LongTails.Proofs.AdamMatrixGeometry

noncomputable def signLaw : ProbabilityMeasure Bool :=
  ⟨(PMF.uniformOfFintype Bool).toMeasure, inferInstance⟩

def sign (b : Bool) : ℝ := if b then 1 else -1

lemma sign_abs (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]

lemma bool_integrable {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] (f : Bool → E) :
    Integrable f (signLaw : Measure Bool) := by
  apply Integrable.of_bound ((measurable_of_finite f).aestronglyMeasurable) (‖f true‖ + ‖f false‖)
  exact Filter.Eventually.of_forall fun b => by cases b <;> simp [norm_nonneg]

lemma integral_sign : (∫ b, sign b ∂(signLaw : Measure Bool)) = 0 := by
  simp [signLaw, PMF.integral_eq_sum, PMF.uniformOfFintype_apply, sign]

noncomputable def sample {r : ℕ} (f : Space r r → ℝ) (s : ℝ) (X : Space r r) (b : Bool) :
    Space r r := gradient f X + (s * sign b) • denseProjection r

lemma sample_measurable {r : ℕ} (f : Space r r → ℝ) (s : ℝ) :
    Measurable (Function.uncurry (sample f s)) := by
  exact ((LongTails.Proofs.MuonProcess.measurable_gradient f).comp measurable_fst).add
    ((measurable_const.mul ((measurable_of_finite sign).comp measurable_snd)).smul_const _)

lemma sample_unbiased {r : ℕ} (f : Space r r → ℝ) (s : ℝ) (X : Space r r) :
    (∫ b, sample f s X b ∂(signLaw : Measure Bool)) = gradient f X := by
  unfold sample
  rw [integral_add (integrable_const _) (bool_integrable _), integral_const,
    integral_smul_const, integral_const_mul, integral_sign]
  simp only [probReal_univ, one_smul, mul_zero, zero_smul, add_zero]

noncomputable def gradientModel {r : ℕ} (hr : 0 < r) (f : Space r r → ℝ)
    (s : ℝ) (hs : 0 ≤ s) : LongTails.Setups.FiniteVarianceSpectralSmooth.GradientModel f s where
  Ω := Bool
  law := signLaw
  sample := sample f s
  jointly_measurable := sample_measurable f s
  integrable X := bool_integrable _
  unbiased := sample_unbiased f s
  row_profile := by
    classical
    obtain ⟨b, hb⟩ := exists_basis_unitOnes hr
    let i₀ : Fin r := ⟨0, hr⟩
    refine ⟨b, (fun i => if i = i₀ then s else 0), (fun i => by dsimp only; split_ifs <;> positivity),
      by simp, ?_⟩
    intro X i
    have heq (ω : Bool) :
        ‖(operatorEquiv r r (sample f s X ω - gradient f X)).adjoint (b i)‖ =
          if i = i₀ then s else 0 := by
      simp only [sample, add_sub_cancel_left, norm_adjoint_dense_basis hr b i₀ hb,
        abs_mul, sign_abs, abs_of_nonneg hs, mul_one]
    constructor
    · apply MemLp.of_bound (measurable_of_finite _).aestronglyMeasurable s
      exact Filter.Eventually.of_forall fun ω => by rw [heq]; split_ifs <;> simp [hs]
    · simp_rw [heq]
      rw [integral_const, probReal_univ, one_smul]

noncomputable def signStream : ProbabilityMeasure (ℕ → Bool) :=
  ⟨Measure.infinitePi (fun _ : ℕ => (signLaw : Measure Bool)), inferInstance⟩

lemma signStream_iid : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
    (fun k (ξ : ℕ → Bool) => ξ k) (signLaw : Measure Bool) (signStream : Measure _) := by
  refine ⟨fun k => measurable_pi_apply k, ?_, ?_⟩
  · exact iIndepFun_infinitePi (X := fun _ (b : Bool) => b) (fun _ => measurable_id)
  · intro k
    exact Measure.infinitePi_map_eval _ _

open OracleTemplate LongTails.Setups.SpectralSmoothAdamComparison

noncomputable def hardObjective (p : Public) : Space p.r p.r → ℝ :=
  AdamSeparationInstance.objective (p.L / 2) (4 * p.ε / ((p.r : ℝ) - 1))
    (8 * p.ε / p.L) (p.Δ / (4 * p.ε)) p.x0

noncomputable def hardOracle (p : Public) : Oracle (Space p.r p.r) (Space p.r p.r) where
  Seed := fun _ => Bool
  law := signStream
  answer := fun _ (_, X) ω => sample (hardObjective p) p.ε X ω

lemma hard_admissible {p : Public} (hp : spec.valid p) :
    LongTails.Setups.BatchedSpectralSmooth.spec.admissible p.toBase (hardObjective p) (hardOracle p) := by
  obtain ⟨hr, hL, hΔ, hε, hgap⟩ := hp
  have hr₁ : 1 < p.r := by omega
  have hr' : 0 < (p.r : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) < p.r - 1 by omega)
  have hw : 0 < 8 * p.ε / p.L := by positivity
  have hc : 0 ≤ 4 * p.ε / ((p.r : ℝ) - 1) := by positivity
  dsimp only [LongTails.Setups.BatchedSpectralSmooth.spec, Public.toBase]
  refine ⟨?_, ?_, ⟨0, ?_, ?_⟩,
    gradientModel (by omega) (hardObjective p) p.ε hε.le, signStream, signStream_iid, rfl⟩
  · intro X
    unfold hardObjective
    rw [AdamSeparationInstance.gradient_objective hr₁ _ _ _ hw]
    exact AdamSeparationInstance.hasGradientAt_objective hr₁ _ _ _ hw _ _
  · intro X Y
    have h := AdamSeparationInstance.lipschitz_objective hr₁ (by positivity : 0 ≤ p.L / 2)
      hc hw (p.Δ / (4 * p.ε)) p.x0 X Y
    have heq : p.L / 2 + ((p.r : ℝ) - 1) * (4 * p.ε / ((p.r : ℝ) - 1)) /
        (8 * p.ε / p.L) = p.L := by
      field_simp
      ring
    rw [heq] at h
    exact h
  · intro X
    exact AdamSeparationInstance.objective_nonneg hr₁ (by positivity) hc hw.le _ _ _
  · have h := AdamSeparationInstance.objective_start_le hr₁ (p.L / 2) hc hw.le
      (by positivity : 0 ≤ p.Δ / (4 * p.ε)) p.x0
    have heq : (4 * p.ε / ((p.r : ℝ) - 1)) * ((p.r : ℝ) - 1) * (p.Δ / (4 * p.ε)) = p.Δ := by
      field_simp
    rw [heq] at h
    simpa only [sub_zero, hardObjective] using h

end LongTails.Proofs.AdamSeparationModel
