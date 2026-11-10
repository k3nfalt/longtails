import LongTails.Proofs.ProximalEf21TrajectoryGeometry

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21InnerTrajectory

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21MomentCalculus
open LongTails.Proofs.ProximalEf21StochasticContraction
open LongTails.Proofs.ProximalEf21TrajectoryGeometry
open LongTails.Proofs.ProximalEf21ScalarCore
open LongTails.Proofs.ProximalEf21Schedule

variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {n : ℕ} {μ M τ γ δ variance : ℝ}

structure Trajectory (P : Measure Ω) (G : InnerGeometry (E := E) n μ M)
    (τ γ δ variance : ℝ) (b : E) where
  x : ℕ → Ω → E
  m : ℕ → Fin n → Ω → E
  v : ℕ → Fin n → Ω → E
  noise : ℕ → Fin n → Ω → E
  correction : ℕ → Fin n → Ω → E
  beforeSample : ℕ → MeasurableSpace Ω
  beforeCompress : ℕ → MeasurableSpace Ω
  beforeSample_le : ∀ t, beforeSample t ≤ ‹MeasurableSpace Ω›
  beforeCompress_le : ∀ t, beforeCompress t ≤ ‹MeasurableSpace Ω›
  sample_before_compress : ∀ t, beforeSample t ≤ beforeCompress t
  feasible : ∀ t, ∀ᵐ ω ∂P, x t ω ∈ G.domain
  proximal_update : ∀ t, ∀ᵐ ω ∂P,
    x (t + 1) ω = G.prox γ (x t ω - γ • workerMean (fun i => v t i ω))
  momentum_update : ∀ t i, ∀ᵐ ω ∂P,
    m (t + 1) i ω = (1 - μ * γ) • m t i ω +
      (μ * γ) • (G.grad i (x (t + 1) ω) + b + noise t i ω)
  compression_update : ∀ t i, ∀ᵐ ω ∂P,
    v (t + 1) i ω = v t i ω + correction t i ω
  centered_noise : ∀ t i,
    condExp (beforeSample t) P (noise t i) =ᵐ[P] (fun _ => 0)
  variance_bound : ∀ t i, ∀ᵐ ω ∂P,
    condExp (beforeSample t) P (fun ω' => ‖noise t i ω'‖ ^ 2) ω ≤ variance
  contractive_compression : ∀ t i, ∀ᵐ ω ∂P,
    condExp (beforeCompress t) P (fun ω' =>
      ‖correction t i ω' - (m (t + 1) i ω' - v t i ω')‖ ^ 2) ω ≤
      (1 - δ) * ‖m (t + 1) i ω - v t i ω‖ ^ 2
  x_lp : ∀ t, MemLp (x t) 2 P
  m_lp : ∀ t i, MemLp (m t i) 2 P
  v_lp : ∀ t i, MemLp (v t i) 2 P
  noise_lp : ∀ t i, MemLp (noise t i) 2 P
  gradient_lp : ∀ t i, MemLp (fun ω => G.grad i (x (t + 1) ω)) 2 P
  auxiliary_lp : ∀ t, MemLp
    (fun ω => G.auxiliary τ (x t ω) (fun i => m t i ω)) 2 P
  gap_integrable : ∀ t, Integrable (fun ω => G.gap (x t ω)) P
  regularizer_integrable : ∀ t, Integrable (fun ω => G.ψ (x t ω)) P
  auxiliary_regularizer_integrable : ∀ t, Integrable
    (fun ω => G.ψ (G.auxiliary τ (x t ω) (fun i => m t i ω))) P
  x_predictable : ∀ t, AEStronglyMeasurable[beforeSample t] (x t) P
  next_x_predictable : ∀ t, AEStronglyMeasurable[beforeSample t] (x (t + 1)) P
  m_predictable : ∀ t i, AEStronglyMeasurable[beforeSample t] (m t i) P
  v_predictable : ∀ t i, AEStronglyMeasurable[beforeSample t] (v t i) P
  gradient_predictable : ∀ t i,
    AEStronglyMeasurable[beforeSample t] (fun ω => G.grad i (x (t + 1) ω)) P
  auxiliary_predictable : ∀ t, AEStronglyMeasurable[beforeSample t]
    (fun ω => G.auxiliary τ (x t ω) (fun i => m t i ω)) P

namespace Trajectory

variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (G : InnerGeometry (E := E) n μ M) (b : E)
variable (r : Trajectory P G τ γ δ variance b)

lemma m_mean_lp (t : ℕ) :
    MemLp (fun ω => workerMean (fun i => r.m t i ω)) 2 P :=
  workerMean_memLp P (r.m t) (r.m_lp t)

lemma v_mean_lp (t : ℕ) :
    MemLp (fun ω => workerMean (fun i => r.v t i ω)) 2 P :=
  workerMean_memLp P (r.v t) (r.v_lp t)

lemma gradient_mean_lp (t : ℕ) :
    MemLp (fun ω => G.smoothGradient (r.x (t + 1) ω)) 2 P :=
  workerMean_memLp P _ (r.gradient_lp t)

lemma W_integrable (t : ℕ) :
    Integrable (fun ω => G.W (fun i => r.m t i ω)) P := by
  apply weightedSquare_integrable
  intro i
  have h := (r.m_lp t i).sub (memLp_const (G.grad i G.xstar))
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

lemma V_integrable (t : ℕ) :
    Integrable (fun ω => G.V (fun i => r.m t i ω) (fun i => r.v t i ω)) P := by
  apply weightedSquare_integrable
  intro i
  have h := (r.v_lp t i).sub (r.m_lp t i)
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

lemma model_integrable (t : ℕ) :
    Integrable (fun ω => modelDecrease G.ψ τ (r.x t ω)
      (workerMean (fun i => r.m t i ω))
      (G.auxiliary τ (r.x t ω) (fun i => r.m t i ω))) P := by
  have hdiff := (r.auxiliary_lp t).sub (r.x_lp t)
  have hi := integrable_inner_of_memLp_two P _ _ (r.m_mean_lp P G b t) hdiff
  have hs := (memLp_two_iff_integrable_sq_norm hdiff.aestronglyMeasurable).mp hdiff
  exact (((r.regularizer_integrable t).sub (r.auxiliary_regularizer_integrable t)).sub hi).sub
    (hs.div_const (2 * τ))

lemma energy_integrable (t : ℕ) :
    Integrable (fun ω => G.energy τ (r.x t ω) (fun i => r.m t i ω)) P := by
  have hi := integrable_inner_of_memLp_two P _ _ (r.m_mean_lp P G b t)
    ((r.x_lp t).sub (memLp_const G.xstar))
  exact ((r.gap_integrable t).sub
    ((((r.regularizer_integrable t).sub (integrable_const _)).add hi).div_const 8)).add
      ((r.model_integrable P G b t).div_const (μ * τ))

lemma potential_integrable (t : ℕ) :
    Integrable (fun ω => G.potential τ (r.x t ω)
      (fun i => r.m t i ω) (fun i => r.v t i ω)) P := by
  exact ((r.energy_integrable P G b t).add ((r.V_integrable P G b t).div_const μ)).add
    ((r.W_integrable P G b t).div_const (64 * M))

lemma integral_potential (t : ℕ) :
    (∫ ω, G.potential τ (r.x t ω) (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) =
      (∫ ω, G.energy τ (r.x t ω) (fun i => r.m t i ω) ∂P) +
      (∫ ω, G.V (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) / μ +
      (∫ ω, G.W (fun i => r.m t i ω) ∂P) / (64 * M) := by
  unfold InnerGeometry.potential
  rw [integral_add ((r.energy_integrable P G b t).add
      ((r.V_integrable P G b t).div_const μ))
      ((r.W_integrable P G b t).div_const (64 * M)),
    integral_add (r.energy_integrable P G b t) ((r.V_integrable P G b t).div_const μ),
    integral_div, integral_div]

lemma displacement_integrable (t : ℕ) :
    Integrable (fun ω => ‖r.x (t + 1) ω - r.x t ω‖ ^ 2) P := by
  have h := (r.x_lp (t + 1)).sub (r.x_lp t)
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

lemma proximal_subgradient_lp (t : ℕ) :
    MemLp (fun ω => γ⁻¹ • (r.x t ω - r.x (t + 1) ω) -
      workerMean (fun i => r.v t i ω)) 2 P :=
  ((((r.x_lp t).sub (r.x_lp (t + 1))).const_smul γ⁻¹).sub
    (r.v_mean_lp P G b t))

lemma first_remainder_integrable (t : ℕ) :
    Integrable (fun ω =>
      ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x (t + 1) ω - G.xstar⟫_ℝ - G.ψ (r.x (t + 1) ω) + G.ψ G.xstar) P := by
  have hi := integrable_inner_of_memLp_two P _ _ (r.proximal_subgradient_lp P G b t)
    ((r.x_lp (t + 1)).sub (memLp_const G.xstar))
  exact (hi.sub (r.regularizer_integrable (t + 1))).add (integrable_const _)

lemma second_remainder_integrable (t : ℕ) :
    Integrable (fun ω => G.ψ (r.x t ω) - G.ψ (r.x (t + 1) ω) -
      ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x t ω - r.x (t + 1) ω⟫_ℝ) P := by
  have hi := integrable_inner_of_memLp_two P _ _ (r.proximal_subgradient_lp P G b t)
    ((r.x_lp t).sub (r.x_lp (t + 1)))
  exact ((r.regularizer_integrable t).sub (r.regularizer_integrable (t + 1))).sub hi

lemma aggregate_momentum_update (t : ℕ) :
    ∀ᵐ ω ∂P,
      workerMean (fun i => r.m (t + 1) i ω) = workerMean (fun i => r.m t i ω) +
        (μ * γ) • (G.smoothGradient (r.x (t + 1) ω) -
          workerMean (fun i => r.m t i ω) + b + workerMean (fun i => r.noise t i ω)) := by
  have hall : ∀ᵐ ω ∂P, ∀ i, r.m (t + 1) i ω =
      (1 - μ * γ) • r.m t i ω +
        (μ * γ) • (G.grad i (r.x (t + 1) ω) + b + r.noise t i ω) :=
    ae_all_iff.mpr (r.momentum_update t)
  filter_upwards [hall] with ω hω
  simp_rw [hω]
  exact workerMean_momentum G.hn (μ * γ) _ _ _ b

lemma aggregate_gradient_integrable (t : ℕ) :
    Integrable (fun ω => weightedSquare G.weights
      (fun i => G.grad i (r.x (t + 1) ω) - G.grad i G.xstar)) P := by
  apply weightedSquare_integrable
  intro i
  have h := (r.gradient_lp t i).sub (memLp_const (G.grad i G.xstar))
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h

lemma integral_gradient_interpolation (t : ℕ) :
    (n : ℝ)⁻¹ * ∑ i, G.weights i *
      (∫ ω, ‖G.grad i (r.x (t + 1) ω) - G.grad i G.xstar‖ ^ 2 ∂P) ≤
      2 * M * (∫ ω, G.gap (r.x (t + 1) ω) ∂P) := by
  have hp : ∀ᵐ ω ∂P, weightedSquare G.weights
      (fun i => G.grad i (r.x (t + 1) ω) - G.grad i G.xstar) ≤
      2 * M * G.gap (r.x (t + 1) ω) := by
    filter_upwards [r.feasible (t + 1)] with ω hω
    exact G.weighted_gradient_interpolation (r.x (t + 1) ω) hω
  have h := integral_mono_ae (r.aggregate_gradient_integrable P G b t)
    ((r.gap_integrable (t + 1)).const_mul (2 * M)) hp
  rw [integral_const_mul] at h
  rw [integral_weightedSquare P G.weights _ (fun i =>
    (memLp_two_iff_integrable_sq_norm
      ((r.gradient_lp t i).sub (memLp_const (G.grad i G.xstar))).aestronglyMeasurable).mp
      ((r.gradient_lp t i).sub (memLp_const (G.grad i G.xstar))))] at h
  exact h

lemma integral_compression_contractiveness (t : ℕ) (i : Fin n) :
    (∫ ω, ‖r.v (t + 1) i ω - r.m (t + 1) i ω‖ ^ 2 ∂P) ≤
      (1 - δ) * (∫ ω, ‖r.m (t + 1) i ω - r.v t i ω‖ ^ 2 ∂P) := by
  have hi := ((r.m_lp (t + 1) i).sub (r.v_lp t i))
  have hisq := (memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable).mp hi
  have heq : (fun ω => ‖r.v (t + 1) i ω - r.m (t + 1) i ω‖ ^ 2) =ᵐ[P]
      (fun ω => ‖r.correction t i ω - (r.m (t + 1) i ω - r.v t i ω)‖ ^ 2) := by
    filter_upwards [r.compression_update t i] with ω hω
    rw [hω]
    congr 1
    abel
  rw [integral_congr_ae heq]
  calc
    (∫ ω, ‖r.correction t i ω - (r.m (t + 1) i ω - r.v t i ω)‖ ^ 2 ∂P) =
        ∫ ω, condExp (r.beforeCompress t) P (fun ω' =>
          ‖r.correction t i ω' - (r.m (t + 1) i ω' - r.v t i ω')‖ ^ 2) ω ∂P :=
      (integral_condExp (r.beforeCompress_le t)).symm
    _ ≤ ∫ ω, (1 - δ) * ‖r.m (t + 1) i ω - r.v t i ω‖ ^ 2 ∂P :=
      integral_mono_ae integrable_condExp (hisq.const_mul _) (r.contractive_compression t i)
    _ = _ := integral_const_mul _ _

lemma momentum_recurrence (hα0 : 0 ≤ μ * γ) (hα1 : μ * γ ≤ 1)
    (hvar : 0 ≤ variance) (t : ℕ) :
    (∫ ω, G.W (fun i => r.m (t + 1) i ω) ∂P) ≤
      (1 - μ * γ) * (∫ ω, G.W (fun i => r.m t i ω) ∂P) +
      4 * (μ * γ) * M * (∫ ω, G.gap (r.x (t + 1) ω) ∂P) +
      2 * (μ * γ) * ‖b‖ ^ 2 + (μ * γ) ^ 2 * variance := by
  have hw := weighted_momentum_recurrence G.hn P (r.beforeSample t) (r.beforeSample_le t)
    G.weights (fun i => (G.weights_positive i).le) G.weights_le_one
    (r.m t) (fun i ω => G.grad i (r.x (t + 1) ω)) (r.noise t) (r.m (t + 1))
    (fun i => G.grad i G.xstar) b hα0 hα1 hvar
    (r.m_lp t) (r.gradient_lp t) (r.noise_lp t) (r.m_lp (t + 1))
    (r.m_predictable t) (r.gradient_predictable t) (r.centered_noise t)
    (r.variance_bound t) (r.momentum_update t) (r.integral_gradient_interpolation P G b t)
  have hW (k : ℕ) : (∫ ω, G.W (fun i => r.m k i ω) ∂P) =
      (n : ℝ)⁻¹ * ∑ i, G.weights i * (∫ ω, ‖r.m k i ω - G.grad i G.xstar‖ ^ 2 ∂P) :=
    integral_weightedSquare P G.weights _ (fun i =>
      (memLp_two_iff_integrable_sq_norm
        ((r.m_lp k i).sub (memLp_const (G.grad i G.xstar))).aestronglyMeasurable).mp
        ((r.m_lp k i).sub (memLp_const (G.grad i G.xstar))))
  simpa only [hW] using hw

lemma compression_recurrence (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hvar : 0 ≤ variance) (t : ℕ) :
    (∫ ω, G.V (fun i => r.m (t + 1) i ω) (fun i => r.v (t + 1) i ω) ∂P) ≤
      (1 - δ / 2) * (∫ ω, G.V (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) +
      6 * (μ * γ) ^ 2 / δ * (∫ ω, G.W (fun i => r.m t i ω) ∂P) +
      12 * (μ * γ) ^ 2 * M / δ * (∫ ω, G.gap (r.x (t + 1) ω) ∂P) +
      6 * (μ * γ) ^ 2 / δ * ‖b‖ ^ 2 + (μ * γ) ^ 2 * variance := by
  have hv := weighted_compression_recurrence G.hn P (r.beforeSample t) (r.beforeSample_le t)
    G.weights (fun i => (G.weights_positive i).le) G.weights_le_one
    (r.m t) (r.v t) (fun i ω => G.grad i (r.x (t + 1) ω))
    (r.noise t) (r.m (t + 1)) (r.v (t + 1)) (fun i => G.grad i G.xstar) b
    hδ hδ1 hvar (r.m_lp t) (r.v_lp t) (r.gradient_lp t) (r.noise_lp t)
    (r.m_predictable t) (r.v_predictable t) (r.gradient_predictable t)
    (r.centered_noise t) (r.variance_bound t) (r.momentum_update t)
    (r.integral_compression_contractiveness P G b t)
    (r.integral_gradient_interpolation P G b t)
  have hV (k : ℕ) : (∫ ω, G.V (fun i => r.m k i ω) (fun i => r.v k i ω) ∂P) =
      (n : ℝ)⁻¹ * ∑ i, G.weights i * (∫ ω, ‖r.v k i ω - r.m k i ω‖ ^ 2 ∂P) :=
    integral_weightedSquare P G.weights _ (fun i =>
      (memLp_two_iff_integrable_sq_norm
        ((r.v_lp k i).sub (r.m_lp k i)).aestronglyMeasurable).mp
        ((r.v_lp k i).sub (r.m_lp k i)))
  have hW (k : ℕ) : (∫ ω, G.W (fun i => r.m k i ω) ∂P) =
      (n : ℝ)⁻¹ * ∑ i, G.weights i * (∫ ω, ‖r.m k i ω - G.grad i G.xstar‖ ^ 2 ∂P) :=
    integral_weightedSquare P G.weights _ (fun i =>
      (memLp_two_iff_integrable_sq_norm
        ((r.m_lp k i).sub (memLp_const (G.grad i G.xstar))).aestronglyMeasurable).mp
        ((r.m_lp k i).sub (memLp_const (G.grad i G.xstar))))
  simpa only [hV, hW] using hv

lemma functional_progress (hτ : 0 < τ) (hγ : 0 < γ)
    (hγτ : γ ≤ τ / 2) (hμτ : μ * τ ≤ 1 / 4096) (t : ℕ) :
    (∫ ω, G.energy τ (r.x (t + 1) ω) (fun i => r.m (t + 1) i ω) ∂P) ≤
      (∫ ω, G.energy τ (r.x t ω) (fun i => r.m t i ω) ∂P) -
      (μ * γ) * (1 / 8 - 15 * M * τ / 2) *
        (∫ ω, G.gap (r.x (t + 1) ω) ∂P) -
      5 / (8 * γ) * (∫ ω, ‖r.x (t + 1) ω - r.x t ω‖ ^ 2 ∂P) -
      (μ * γ) / 8 * (∫ ω,
        ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
          r.x (t + 1) ω - G.xstar⟫_ℝ - G.ψ (r.x (t + 1) ω) + G.ψ G.xstar ∂P) -
      1 / (μ * τ) * (∫ ω, G.ψ (r.x t ω) - G.ψ (r.x (t + 1) ω) -
        ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
          r.x t ω - r.x (t + 1) ω⟫_ℝ ∂P) +
      15 * (μ * γ) * τ / 2 * (∫ ω, G.W (fun i => r.m t i ω) ∂P) +
      5 * γ / (μ * τ) * (∫ ω, G.V (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) +
      5 * γ * ‖b‖ ^ 2 + μ * γ ^ 2 / 2 * variance := by
  let ζ : Ω → E := fun ω => workerMean (fun i => r.noise t i ω)
  have hζ := workerMean_memLp P (r.noise t) (r.noise_lp t)
  have hζsq := (memLp_two_iff_integrable_sq_norm hζ.aestronglyMeasurable).mp hζ
  have hu1 := (r.x_lp t).sub (r.auxiliary_lp t)
  have hu2 := (r.x_lp (t + 1)).sub (memLp_const G.xstar)
  have hu3 := ((r.gradient_mean_lp P G b t).sub (r.m_mean_lp P G b t)).add (memLp_const b)
  have hp1 := (r.x_predictable t).sub (r.auxiliary_predictable t)
  have hp2 := (r.next_x_predictable t).sub aestronglyMeasurable_const
  have hp3 := ((workerMean_predictable P (r.beforeSample t) _ (r.gradient_predictable t)).sub
    (workerMean_predictable P (r.beforeSample t) _ (r.m_predictable t))).add
      aestronglyMeasurable_const
  have hz1 := mean_noise_orthogonal P (r.beforeSample t) (r.beforeSample_le t)
    (r.noise t) (r.noise_lp t) (r.centered_noise t) _ hu1 hp1
  have hz2 := mean_noise_orthogonal P (r.beforeSample t) (r.beforeSample_le t)
    (r.noise t) (r.noise_lp t) (r.centered_noise t) _ hu2 hp2
  have hz3 := mean_noise_orthogonal P (r.beforeSample t) (r.beforeSample_le t)
    (r.noise t) (r.noise_lp t) (r.centered_noise t) _ hu3 hp3
  have hvariance := mean_noise_second_moment G.hn P (r.noise t) variance
    (r.noise_lp t) (fun i => conditional_variance_to_integral P (r.beforeSample t)
      (r.beforeSample_le t) (r.noise t i) variance (r.variance_bound t i))
  apply integrated_functional_progress P G.smoothValue G.ψ G.hμ G.M_pos hτ hγ
    hγτ hμτ rfl G.xstar (G.smoothGradient G.xstar) b
    (r.x t) (r.x (t + 1))
    (fun ω => workerMean (fun i => r.m t i ω))
    (fun ω => workerMean (fun i => r.v t i ω))
    (fun ω => G.auxiliary τ (r.x t ω) (fun i => r.m t i ω))
    (fun ω => G.smoothGradient (r.x (t + 1) ω))
    (fun ω => workerMean (fun i => r.m (t + 1) i ω))
    (fun ω => G.auxiliary τ (r.x (t + 1) ω) (fun i => r.m (t + 1) i ω)) ζ
    (fun ω => G.W (fun i => r.m t i ω))
    (fun ω => G.V (fun i => r.m t i ω) (fun i => r.v t i ω))
  · exact Filter.Eventually.of_forall (fun ω => G.W_nonnegative _)
  · exact Filter.Eventually.of_forall (fun ω => G.V_nonnegative _ _)
  · exact r.W_integrable P G b t
  · exact r.V_integrable P G b t
  · exact r.energy_integrable P G b t
  · exact r.energy_integrable P G b (t + 1)
  · exact r.gap_integrable (t + 1)
  · exact r.displacement_integrable P G b t
  · exact r.first_remainder_integrable P G b t
  · exact r.second_remainder_integrable P G b t
  · exact integrable_inner_of_memLp_two P _ ζ hu1 hζ
  · exact integrable_inner_of_memLp_two P _ ζ hu2 hζ
  · exact integrable_inner_of_memLp_two P _ ζ hu3 hζ
  · exact hζsq
  · exact hz1
  · exact hz2
  · exact hz3
  · exact hvariance
  · exact r.aggregate_momentum_update P G b t
  · exact Filter.Eventually.of_forall (fun ω => by
      have hs := G.average_strong (r.x (t + 1) ω) (r.x t ω)
      change G.smoothValue (r.x (t + 1) ω) +
        ⟪G.smoothGradient (r.x (t + 1) ω), r.x t ω - r.x (t + 1) ω⟫_ℝ +
        μ / 2 * ‖r.x t ω - r.x (t + 1) ω‖ ^ 2 ≤ G.smoothValue (r.x t ω) at hs
      rw [norm_sub_rev (r.x t ω) (r.x (t + 1) ω)] at hs
      linarith)
  · exact Filter.Eventually.of_forall (fun ω => G.prox_support_step hτ _ _ _
      (G.prox_mem τ hτ _))
  · filter_upwards [r.proximal_update t, r.feasible t] with ω hu hx
    have hs := G.prox_support_step hγ (r.x t ω) (workerMean (fun i => r.v t i ω)) _ hx
    rw [← hu] at hs
    linarith
  · exact Filter.Eventually.of_forall (fun ω => G.average_strong (r.x (t + 1) ω) G.xstar)
  · filter_upwards [r.proximal_update t, r.feasible (t + 1)] with ω hu hy
    have hxy := G.prox_support_step hγ (r.x t ω)
      (workerMean (fun i => r.v t i ω)) _ (G.prox_mem τ hτ _)
    rw [← hu] at hxy
    have hyx := G.prox_support_step hτ (r.x t ω)
      (workerMean (fun i => r.m t i ω)) (r.x (t + 1) ω) hy
    exact subgradient_monotonicity G.ψ _ _ _ _ hxy hyx
  · filter_upwards [r.feasible (t + 1)] with ω hω
    exact G.global_gradient_interpolation _ hω
  · exact Filter.Eventually.of_forall (fun ω => G.average_momentum_control _)
  · exact Filter.Eventually.of_forall (fun ω => G.average_compression_control _ _)

lemma upper_comparison (hτ : 0 < τ) (hγ : 0 < γ)
    (hμγ : μ * γ ≤ 1) (hμτ : μ * τ ≤ 1)
    (hsmall : μ * γ + 2 * μ * M * γ ^ 2 ≤ 3) (t : ℕ) :
    (∫ ω, G.energy τ (r.x t ω) (fun i => r.m t i ω) ∂P) ≤
      3 * (∫ ω, G.gap (r.x (t + 1) ω) ∂P) +
      5 / (μ * γ ^ 2) * (∫ ω, ‖r.x (t + 1) ω - r.x t ω‖ ^ 2 ∂P) +
      (∫ ω, ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x (t + 1) ω - G.xstar⟫_ℝ - G.ψ (r.x (t + 1) ω) + G.ψ G.xstar ∂P) / 8 +
      2 / (μ * τ) * (∫ ω, G.ψ (r.x t ω) - G.ψ (r.x (t + 1) ω) -
        ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
          r.x t ω - r.x (t + 1) ω⟫_ℝ ∂P) +
      (∫ ω, G.W (fun i => r.m t i ω) ∂P) / M +
      4 / μ * (∫ ω, G.V (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) := by
  apply integrated_upper_comparison P G.smoothValue G.ψ G.hμ G.M_pos hτ hγ
    G.hμM hμγ hμτ hsmall G.xstar (G.smoothGradient G.xstar)
    (r.x t) (r.x (t + 1))
    (fun ω => workerMean (fun i => r.m t i ω))
    (fun ω => workerMean (fun i => r.v t i ω))
    (fun ω => G.auxiliary τ (r.x t ω) (fun i => r.m t i ω))
    (fun ω => G.smoothGradient (r.x (t + 1) ω))
    (fun ω => G.W (fun i => r.m t i ω))
    (fun ω => G.V (fun i => r.m t i ω) (fun i => r.v t i ω))
  · exact r.energy_integrable P G b t
  · exact r.gap_integrable (t + 1)
  · exact r.displacement_integrable P G b t
  · exact r.first_remainder_integrable P G b t
  · exact r.second_remainder_integrable P G b t
  · exact r.W_integrable P G b t
  · exact r.V_integrable P G b t
  · filter_upwards [r.proximal_update t] with ω hu
    have hs := G.prox_support_step hγ (r.x t ω)
      (workerMean (fun i => r.v t i ω)) _ (G.prox_mem τ hτ _)
    simpa only [← hu] using hs
  · filter_upwards [r.proximal_update t, r.feasible t] with ω hu hx
    have hs := G.prox_support_step hγ (r.x t ω)
      (workerMean (fun i => r.v t i ω)) _ hx
    rw [← hu] at hs
    linarith
  · filter_upwards [r.feasible (t + 1)] with ω hx
    exact G.strong_gap _ hx
  · exact Filter.Eventually.of_forall (fun ω => G.smooth_upper (r.x (t + 1) ω) (r.x t ω))
  · filter_upwards [r.feasible (t + 1)] with ω hx
    exact G.global_gradient_interpolation _ hx
  · exact Filter.Eventually.of_forall (fun ω => G.average_momentum_control _)
  · exact Filter.Eventually.of_forall (fun ω => G.average_compression_control _ _)

lemma objective_control (hτ : 0 < τ) (hμτ : μ * τ ≤ 1) (t : ℕ) :
    (∫ ω, G.gap (r.x t ω) ∂P) ≤
      (8 / 7 : ℝ) * (∫ ω, G.potential τ (r.x t ω)
        (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) := by
  have hp : ∀ᵐ ω ∂P, G.gap (r.x t ω) ≤
      (8 / 7 : ℝ) * G.potential τ (r.x t ω)
        (fun i => r.m t i ω) (fun i => r.v t i ω) := by
    filter_upwards [r.feasible t] with ω hx
    have h := G.potential_lower hτ hμτ (r.x t ω) hx _ _
    have hm := G.model_nonnegative hτ (r.x t ω) hx (fun i => r.m t i ω)
    have hv := G.V_nonnegative (fun i => r.m t i ω) (fun i => r.v t i ω)
    have hw := G.W_nonnegative (fun i => r.m t i ω)
    have ht : 0 ≤ modelDecrease G.ψ τ (r.x t ω)
        (workerMean (fun i => r.m t i ω))
        (G.auxiliary τ (r.x t ω) (fun i => r.m t i ω)) / (μ * τ) := by positivity
    have hvt : 0 ≤ G.V (fun i => r.m t i ω) (fun i => r.v t i ω) / μ := by positivity
    have hwt : 0 ≤ G.W (fun i => r.m t i ω) / (64 * M) := by positivity
    linarith
  have h := integral_mono_ae (r.gap_integrable t)
    ((r.potential_integrable P G b t).const_mul (8 / 7)) hp
  simpa only [integral_const_mul] using h

lemma contraction (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hτ : τ = 1 / (4096 * M)) (hγ : 0 < γ)
    (hγbound : γ ≤ δ * τ / 128) (hvar : 0 ≤ variance) (t : ℕ) :
    (∫ ω, G.potential τ (r.x (t + 1) ω)
      (fun i => r.m (t + 1) i ω) (fun i => r.v (t + 1) i ω) ∂P) ≤
      (1 - μ * γ / 512) *
        (∫ ω, G.potential τ (r.x t ω) (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) +
      6 * γ * ‖b‖ ^ 2 + 2 * μ * γ ^ 2 * variance := by
  obtain ⟨hM, hτpos, hMτ, hMγδ, hγτ, hαpos, hαδ, hα1⟩ :=
    tuning_bounds G.hμ G.hμM hδ hδ1 hτ hγ hγbound (α := μ * γ) rfl
  have hhalf : γ ≤ τ / 2 := by
    have hg : γ ≤ τ / 128 :=
      hγbound.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hδ1 hτpos.le) (by norm_num))
    linarith
  have hμτ : μ * τ ≤ 1 / 4096 := by
    have h := mul_le_mul_of_nonneg_right G.hμM hτpos.le
    linarith
  have hμτ1 : μ * τ ≤ 1 := by linarith
  have hMg : M * γ ≤ 1 := by
    have h := (div_le_iff₀ hδ).mp hMγδ
    nlinarith
  have hμg : μ * γ ≤ 1 := hα1
  have hsmall : μ * γ + 2 * μ * M * γ ^ 2 ≤ 3 := by
    have hprod : (μ * γ) * (M * γ) ≤ 1 :=
      (mul_le_mul hμg hMg (mul_nonneg G.hμ.le hγ.le) (by norm_num))
    nlinarith only [hprod, hμg]
  have hE := r.functional_progress P G b hτpos hγ hhalf hμτ t
  have hW := r.momentum_recurrence P G b hαpos.le hα1 hvar t
  have hV := r.compression_recurrence P G b hδ hδ1 hvar t
  have hg : 0 ≤ ∫ ω, G.gap (r.x (t + 1) ω) ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [r.feasible (t + 1)] with ω hx
    exact G.gap_nonnegative _ hx
  have hdn : 0 ≤ ∫ ω, ‖r.x (t + 1) ω - r.x t ω‖ ^ 2 ∂P :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hwn : 0 ≤ ∫ ω, G.W (fun i => r.m t i ω) ∂P :=
    integral_nonneg (fun _ => G.W_nonnegative _)
  have hvn : 0 ≤ ∫ ω, G.V (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P :=
    integral_nonneg (fun _ => G.V_nonnegative _ _)
  have hrem1 : 0 ≤ ∫ ω,
      ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x (t + 1) ω - G.xstar⟫_ℝ - G.ψ (r.x (t + 1) ω) + G.ψ G.xstar ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [r.proximal_update t] with ω hu
    have hs := G.prox_support_step hγ (r.x t ω)
      (workerMean (fun i => r.v t i ω)) G.xstar G.optimum_mem
    rw [← hu, show G.xstar - r.x (t + 1) ω = -(r.x (t + 1) ω - G.xstar) by abel,
      inner_neg_right] at hs
    linarith
  have hrem2 : 0 ≤ ∫ ω, G.ψ (r.x t ω) - G.ψ (r.x (t + 1) ω) -
      ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x t ω - r.x (t + 1) ω⟫_ℝ ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [r.proximal_update t, r.feasible t] with ω hu hx
    have hs := G.prox_support_step hγ (r.x t ω)
      (workerMean (fun i => r.v t i ω)) (r.x t ω) hx
    rw [← hu] at hs
    linarith
  have hdescent := assembled_descent G.hμ G.hμM hδ hτ hγ hγbound
    (α := μ * γ) rfl hg hdn hwn hvn (sq_nonneg ‖b‖) hvar hE hW hV
  have hu := r.upper_comparison P G b hτpos hγ hμg hμτ1 hsmall t
  have hupper :
      (∫ ω, G.potential τ (r.x t ω) (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) ≤
      3 * (∫ ω, G.gap (r.x (t + 1) ω) ∂P) +
      5 / (μ * γ ^ 2) * (∫ ω, ‖r.x (t + 1) ω - r.x t ω‖ ^ 2 ∂P) +
      (∫ ω, ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
        r.x (t + 1) ω - G.xstar⟫_ℝ - G.ψ (r.x (t + 1) ω) + G.ψ G.xstar ∂P) / 8 +
      2 / (μ * τ) * (∫ ω, G.ψ (r.x t ω) - G.ψ (r.x (t + 1) ω) -
        ⟪γ⁻¹ • (r.x t ω - r.x (t + 1) ω) - workerMean (fun i => r.v t i ω),
          r.x t ω - r.x (t + 1) ω⟫_ℝ ∂P) +
      2 / M * (∫ ω, G.W (fun i => r.m t i ω) ∂P) +
      5 / μ * (∫ ω, G.V (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P) := by
    rw [r.integral_potential P G b t]
    have hwc : (1 / M + 1 / (64 * M) : ℝ) ≤ 2 / M := by
      apply (mul_le_mul_right hM).mp
      field_simp [ne_of_gt hM]
      norm_num
    have hwterm := mul_le_mul_of_nonneg_right hwc hwn
    nlinarith only [hu, hwterm]
  rw [← r.integral_potential P G b t, ← r.integral_potential P G b (t + 1)] at hdescent
  have hαδ' : 5 * (μ * γ) ≤ 128 * δ := by nlinarith only [hαδ, hδ.le]
  exact contraction_from_dissipation G.hμ hM hγ hτpos rfl hα1 hαδ'
    hg hdn hrem1 hrem2 hwn hvn hupper hdescent

lemma inner_contraction_unrolled (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hτ : τ = 1 / (4096 * M)) (hγ : 0 < γ)
    (hγbound : γ ≤ δ * τ / 128) (hvar : 0 ≤ variance) (K : ℕ) :
    (∫ ω, G.potential τ (r.x K ω) (fun i => r.m K i ω) (fun i => r.v K i ω) ∂P) ≤
      Real.exp (-μ * γ * K / 512) *
        (∫ ω, G.potential τ (r.x 0 ω) (fun i => r.m 0 i ω) (fun i => r.v 0 i ω) ∂P) +
      3072 * ‖b‖ ^ 2 / μ + 1024 * γ * variance := by
  obtain ⟨hM, hτpos, hMτ, _, _, _, _, hα1⟩ :=
    tuning_bounds G.hμ G.hμM hδ hδ1 hτ hγ hγbound (α := μ * γ) rfl
  have hμτ : μ * τ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right G.hμM hτpos.le
    linarith
  have hΛ0 : 0 ≤ ∫ ω, G.potential τ (r.x 0 ω)
      (fun i => r.m 0 i ω) (fun i => r.v 0 i ω) ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [r.feasible 0] with ω hx
    exact G.potential_nonnegative hτpos hμτ _ hx _ _
  have h := inner_polynomial_bound_to_exponential
    (fun t => ∫ ω, G.potential τ (r.x t ω)
      (fun i => r.m t i ω) (fun i => r.v t i ω) ∂P)
    G.hμ hγ (B := 1) (by norm_num) (by linarith)
    hΛ0 hvar (sq_nonneg ‖b‖)
    (by intro t; simpa only [div_one] using r.contraction P G b hδ hδ1 hτ hγ hγbound hvar t) K
  simpa only [div_one] using h

end Trajectory

end LongTails.Proofs.ProximalEf21InnerTrajectory
