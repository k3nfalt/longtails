import LongTails.Proofs.DashaScalingPotential
import LongTails.Proofs.DashaInitialization

namespace LongTails.Proofs.DashaScalingInitialization

open MeasureTheory
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaScalingPotential

variable {p : Params} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma initial_potential_moment (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (codes : Ω → Fin p.n → Fin p.d → ℤ) (lower B : ℝ)
    (hind : ProbabilityTheory.iIndepFun
      (fun i ω => localError c f (p.x0, codes ω) i) P)
    (hi : ∀ i, Integrable (fun ω => localError c f (p.x0, codes ω) i) P)
    (hi2 : ∀ i, Integrable (fun ω => ‖localError c f (p.x0, codes ω) i‖ ^ 2) P)
    (hz : ∀ i, (∫ ω, localError c f (p.x0, codes ω) i ∂P) = 0)
    (hb : ∀ i, (∫ ω, ‖localError c f (p.x0, codes ω) i‖ ^ 2 ∂P) ≤ B) :
    Integrable (fun ω => potential c f lower (p.x0, codes ω)) P ∧
    (∫ ω, potential c f lower (p.x0, codes ω) ∂P) ≤
      objective p f p.x0 - lower +
        (stepSize p c / momentum p c + 2 * stepSize p c * variance p c) * B / p.n := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  have hγ := DashaScalingParameters.stepSize_pos c hL hH
  have ha := DashaScalingParameters.momentum_pos c
  have hw := DashaScalingParameters.variance_nonneg c
  have hsum := OracleTemplate.RobustGradient.independent_sum_second_moment
    (fun i ω => localError c f (p.x0, codes ω) i) hind hi hi2 hz
  have hE : Integrable (fun ω => aggregateEnergy c f (p.x0, codes ω)) P := by
    simp_rw [aggregateEnergy_eq c f hg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    exact hsum.1.const_mul _
  have hV : Integrable (fun ω => localEnergy c f (p.x0, codes ω)) P :=
    (integrable_finsetSum _ (fun i _ => hi2 i)).const_mul _
  have hEI : (∫ ω, aggregateEnergy c f (p.x0, codes ω) ∂P) =
      (1 / (p.n : ℝ)) ^ 2 * ∑ i, ∫ ω, ‖localError c f (p.x0, codes ω) i‖ ^ 2 ∂P := by
    simp_rw [aggregateEnergy_eq c f hg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [integral_const_mul, hsum.2]
  have hVI : (∫ ω, localEnergy c f (p.x0, codes ω) ∂P) =
      (1 / (p.n : ℝ)) * ∑ i, ∫ ω, ‖localError c f (p.x0, codes ω) i‖ ^ 2 ∂P := by
    unfold localEnergy
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi2 i)]
  have hB : (∑ i, ∫ ω, ‖localError c f (p.x0, codes ω) i‖ ^ 2 ∂P) ≤ (p.n : ℝ) * B := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hb i)
  have hEB : (∫ ω, aggregateEnergy c f (p.x0, codes ω) ∂P) ≤ B / p.n := by
    rw [hEI]
    calc
      _ ≤ (1 / (p.n : ℝ)) ^ 2 * ((p.n : ℝ) * B) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by field_simp
  have hVB : (∫ ω, localEnergy c f (p.x0, codes ω) ∂P) ≤ B := by
    rw [hVI]
    calc
      _ ≤ (1 / (p.n : ℝ)) * ((p.n : ℝ) * B) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by field_simp
  have hEc := hE.const_mul (stepSize p c / momentum p c)
  have hVc := hV.const_mul (2 * stepSize p c * variance p c / p.n)
  have hC : Integrable (fun _ : Ω => objective p f p.x0 - lower) P := integrable_const _
  have hCE : Integrable (fun ω => objective p f p.x0 - lower +
      stepSize p c / momentum p c * aggregateEnergy c f (p.x0, codes ω)) P := hC.add hEc
  refine ⟨hCE.add hVc, ?_⟩
  unfold potential
  rw [integral_add hCE hVc, integral_add hC hEc, integral_const, integral_const_mul, integral_const_mul]
  simp only [probReal_univ, one_smul]
  have he := mul_le_mul_of_nonneg_left hEB (show 0 ≤ stepSize p c / momentum p c by positivity)
  have hv := mul_le_mul_of_nonneg_left hVB (show 0 ≤ 2 * stepSize p c * variance p c / p.n by positivity)
  calc
    _ ≤ objective p f p.x0 - lower + stepSize p c / momentum p c * (B / p.n) +
        2 * stepSize p c * variance p c / p.n * B := add_le_add (add_le_add le_rfl he) hv
    _ = _ := by ring

lemma sparse_initial_potential (c initializer : Choice p) (hε : 0 < p.ε)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G) (lower : ℝ) :
    Integrable (fun seed => potential c f lower (reduce p (sparseInitialIterate p c initializer f seed)))
      (sampleLaw p : Measure _) ∧
    (∫ seed, potential c f lower (reduce p (sparseInitialIterate p c initializer f seed))
      ∂(sampleLaw p : Measure _)) ≤ objective p f p.x0 - lower +
        stepSize p c * initialPenalty p c initializer + stepSize p c * p.ε ^ 2 / 32 := by
  have hω := DashaScalingParameters.variance_nonneg initializer
  have hγ := DashaScalingParameters.stepSize_pos c hL hH
  have ha := DashaScalingParameters.momentum_pos c
  let codes := fun seed : Sample p => (sparseInitialIterate p c initializer f seed).localCode
  have hm := DashaCompression.replicated_error_moments initializer.block initializer.precision
    (spacing p c) (fun i => gradient (f i) p.x0) (DashaScalingParameters.spacing_pos c hε).ne'
  have hb (i : Fin p.n) :
      (∫ seed : Sample p, ‖localError c f (p.x0, codes seed) i‖ ^ 2 ∂(sampleLaw p : Measure _)) ≤
        variance p initializer * p.G ^ 2 + 2 * (initializer.block.val + 1) * spacing p c ^ 2 := by
    have hGi : 0 ≤ p.G := (norm_nonneg _).trans (hG i)
    have hsq := (sq_le_sq₀ (norm_nonneg _) hGi).mpr (hG i)
    have hscaled := mul_le_mul_of_nonneg_left hsq hω
    have h := (hm i).2.2.2
    change (∫ seed : Sample p,
      ‖LongTails.Algorithms.DashaCyclic.compress initializer.block initializer.precision
        (spacing p c) (gradient (f i) p.x0) (seed i) - gradient (f i) p.x0‖ ^ 2
        ∂(sampleLaw p : Measure _)) ≤ _
    simp only [sampleLaw, ProbabilityMeasure.coe_mk]
    change _ ≤ variance p initializer * ‖gradient (f i) p.x0‖ ^ 2 +
      2 * (initializer.block.val + 1) * spacing p c ^ 2 at h
    linarith only [h, hscaled]
  have hinit := initial_potential_moment (P := (sampleLaw p : Measure _)) c hL hH f hg codes lower
    (variance p initializer * p.G ^ 2 + 2 * (initializer.block.val + 1) * spacing p c ^ 2)
    (DashaCompression.independent_compression_errors initializer.block initializer.precision
      (spacing p c) (fun i => gradient (f i) p.x0))
    (fun i => (hm i).1) (fun i => (hm i).2.2.1) (fun i => (hm i).2.1) hb
  have hnoise := DashaScalingParameters.initialization_noise_bound c initializer hL hH
  have he : (stepSize p c / momentum p c + 2 * stepSize p c * variance p c) *
      (variance p initializer * p.G ^ 2 + 2 * (initializer.block.val + 1) * spacing p c ^ 2) / p.n =
      stepSize p c * initialPenalty p c initializer +
      (stepSize p c / momentum p c + 2 * stepSize p c * variance p c) *
        (2 * (initializer.block.val + 1) * spacing p c ^ 2 / p.n) := by
    unfold initialPenalty momentum
    field_simp
    ring
  rw [he] at hinit
  refine ⟨hinit.1, ?_⟩
  change (∫ seed, potential c f lower (p.x0, codes seed) ∂(sampleLaw p : Measure _)) ≤ _
  linarith only [hinit.2, hnoise]

lemma dense_initial_potential (c : Choice p) (hε : 0 < p.ε)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (lower : ℝ) :
    Integrable (fun seed => potential c f lower (initialReduced p c f seed)) (sampleLaw p : Measure _) ∧
    (∫ seed, potential c f lower (initialReduced p c f seed) ∂(sampleLaw p : Measure _)) ≤
      objective p f p.x0 - lower + stepSize p c * p.ε ^ 2 / 64 := by
  let codes := fun seed : Sample p => (initialIterate p c f seed).localCode
  have hm := DashaInitialization.replicated_fine_moments (spacing p c)
    (DashaScalingParameters.spacing_pos c hε) (fun i => gradient (f i) p.x0)
  have hinit := initial_potential_moment (P := (sampleLaw p : Measure _)) c hL hH f hg codes lower
    ((p.d : ℝ) * spacing p c ^ 2)
    (DashaInitialization.independent_fine_errors (spacing p c) (fun i => gradient (f i) p.x0))
    (fun i => (hm i).1) (fun i => (hm i).2.2.1) (fun i => (hm i).2.1) (fun i => (hm i).2.2.2)
  have hnoise := DashaScalingParameters.initial_noise_bound c hL hH
  rw [← mul_div_assoc] at hnoise
  refine ⟨hinit.1, ?_⟩
  exact hinit.2.trans (add_le_add le_rfl hnoise)

end LongTails.Proofs.DashaScalingInitialization
