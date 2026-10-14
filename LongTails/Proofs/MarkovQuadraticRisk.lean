import LongTails.Proofs.MarkovQuadraticRenewal
import LongTails.Proofs.MarkovQuadraticExecution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000

open MeasureTheory ProbabilityTheory Function Preorder
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.MarkovProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma covariance_quadratic_le_norm (M : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) (v : E) :
    (inner ℂ v (M 1 v)).re ≤ ‖M‖ * ‖v‖ ^ 2 := by
  have hi : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hM : ‖M 1‖ ≤ ‖M‖ := by
    apply (M.le_opNorm 1).trans
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left hi (norm_nonneg M))
  calc
    _ ≤ ‖inner ℂ v (M 1 v)‖ := Complex.re_le_norm _
    _ ≤ ‖v‖ * ‖M 1 v‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖M‖ * ‖v‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg v)
      exact ((M 1).le_opNorm v).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg v))
    _ = _ := by ring

lemma finite_covariance_source_bound {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (W : Ω → E →L[ℂ] E)
    (A : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E)) (θ : E → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hsource : ∀ v, θ v ≤ C * (inner ℂ v (A 1 v)).re) (v : E) :
    (∑ ω, w ω * θ (W ω v)) ≤ C * ‖finiteCovariance w W * A‖ * ‖v‖ ^ 2 := by
  have he : (∑ ω, w ω * (inner ℂ (W ω v) (A 1 (W ω v))).re) =
      (inner ℂ v ((finiteCovariance w W * A) 1 v)).re := by
    rw [mul_apply_eq_comp, inner_finiteCovariance]
    change _ = Complex.reCLM (∑ ω, (w ω : ℂ) * inner ℂ (W ω v) (A 1 (W ω v)))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  calc
    _ ≤ ∑ ω, w ω * (C * (inner ℂ (W ω v) (A 1 (W ω v))).re) := by
      apply Finset.sum_le_sum
      intro ω hω
      exact mul_le_mul_of_nonneg_left (hsource _) (hw ω)
    _ = C * (∑ ω, w ω * (inner ℂ (W ω v) (A 1 (W ω v))).re) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      ring
    _ ≤ _ := by rw [he]; nlinarith [covariance_quadratic_le_norm (finiteCovariance w W * A) v]

end OracleTemplate.MarkovProduct

noncomputable section

open LongTails.Setups.MarkovQuadraticInterpolation
open OracleTemplate OracleTemplate.MarkovProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private local instance : NormedSpace ℂ (Complexified E →L[ℂ] Complexified E) :=
  ContinuousLinearMap.toNormedSpace
private local instance : Module ℝ (Complexified E →L[ℂ] Complexified E) := Module.complexToReal _
private local instance : NormedSpace ℝ (Complexified E →L[ℂ] Complexified E) := NormedSpace.complexToReal
private local instance : NormedSpace ℂ ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
    (Complexified E →L[ℂ] Complexified E)) := ContinuousLinearMap.toNormedSpace
private local instance : Module ℝ ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
    (Complexified E →L[ℂ] Complexified E)) := Module.complexToReal _
private local instance : NormedSpace ℝ ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
    (Complexified E →L[ℂ] Complexified E)) := NormedSpace.complexToReal

namespace OracleTemplate.MarkovQuadratic

omit [CompleteSpace E] in
lemma liftedProduct_iterate {S : Type*} (H : S → E →L[ℝ] E) (η : ℝ)
    (x0 u : E) (ξ : ℕ → S) (n : ℕ) :
    liftedProduct η (fun k => H (ξ k)) n (Complexified.pair (x0 - u) 0) =
      Complexified.pair (iterate (fun x i => H i (x - u)) η x0 ξ n - u) 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [liftedProduct, mul_apply_eq_comp, ih]
    apply Complexified.ext
    · simp only [liftedStep, Complexified.lift_apply, Complexified.real_pair, Complexified.imag_pair,
        sub_apply, smul_apply, ContinuousLinearMap.id_apply, iterate]
      abel
    · simp [liftedStep]

omit [CompleteSpace E] in
lemma iterate_congr_samples {S : Type*} (g : E → S → E) (η : ℝ) (x0 : E)
    (ξ ζ : ℕ → S) (n : ℕ) (he : ∀ k < n, ξ k = ζ k) :
    iterate g η x0 ξ n = iterate g η x0 ζ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate, iterate, ih (fun k hk => he k (by omega)), he n (by omega)]

omit [CompleteSpace E] in
lemma iterate_prefix {S : Type} (g : E → S → E) (η : ℝ) (x0 : E) (ξ : ℕ → S) (n : ℕ) :
    iterate g η x0 (extendHistory (frestrictLe n ξ)) n = iterate g η x0 ξ n := by
  apply iterate_congr_samples
  intro k hk
  rw [extendHistory_eq _ (by omega)]
  rfl

omit [CompleteSpace E] in
lemma integral_iterate_finite_prefix {S : Type} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (P : ProbabilityMeasure (ℕ → S))
    (g : E → S → E) (η : ℝ) (x0 : E) (f : E → ℝ) (n : ℕ) :
    (∫ ξ, f (iterate g η x0 ξ n) ∂(P : Measure (ℕ → S))) =
      ∑ h, ((P : Measure (ℕ → S)).map (frestrictLe n)).real {h} *
        f (iterate g η x0 (extendHistory h) n) := by
  have he := finite_integral ((P : Measure (ℕ → S)).map (frestrictLe n))
    (fun h => f (iterate g η x0 (extendHistory h) n))
  simp only [smul_eq_mul] at he
  rw [← he]
  rw [integral_map (by fun_prop) (StronglyMeasurable.of_discrete.aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [iterate_prefix]

end OracleTemplate.MarkovQuadratic

namespace LongTails.Setups.MarkovQuadraticInterpolation.Model

open OracleTemplate.MarkovQuadratic

lemma iterate_risk_bound {q : Params} {m : ℕ} {π : ProbabilityMeasure (Fin m)}
    {κ : Kernel (Fin m) (Fin m)} [IsMarkovKernel κ]
    {H : Fin m → q.E →L[ℝ] q.E} {f : q.E → ℝ} {u : q.E}
    (model : Model q m π κ H f u) (μ : ProbabilityMeasure (Fin m))
    (Q : Kernel (Fin m) (Fin m)) [IsMarkovKernel Q]
    (hstat : Q ∘ₘ (π : Measure (Fin m)) = π)
    (hdec : ∀ i j, (κ i).real {j} = (1 - q.α) * (Q i).real {j} + q.α * (π : Measure (Fin m)).real {j})
    (hL : 0 < q.L) (hα : 0 < q.α) (hα1 : q.α ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    (∫ ξ, f (iterate (fun x i => H i (x - u)) (q.α / (10000 * q.L)) q.x0 ξ n) - f u
      ∂(LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ : Measure (ℕ → Fin m))) ≤
      5000000000000000 * q.L * q.R ^ 2 / (q.α * n) := by
  let η := q.α / (10000 * q.L)
  let Ψ := geometricMean (1 - q.α) (markovCovariance η H Q π)
  let A := 1 - Ψ
  let v := Complexified.pair (q.x0 - u) 0
  let θ : Complexified q.E → ℝ := fun y =>
    ∑ i, (π : Measure (Fin m)).real {i} * (inner ℂ y (Complexified.lift (H i) y)).re
  let P := LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ
  let w : (Finset.Iic n → Fin m) → ℝ := fun h => ((P : Measure (ℕ → Fin m)).map (frestrictLe n)).real {h}
  let W : (Finset.Iic n → Fin m) → Complexified q.E →L[ℂ] Complexified q.E :=
    fun h => liftedProduct η (fun k => H (extendHistory h k)) n
  have hsource (y : Complexified q.E) : θ y ≤ (30000 * q.L) * (inner ℂ y (A 1 y)).re := by
    have hh := stationary_geometric_source_tuned Q π hstat H hL hα hα1
      model.symmetric model.positive model.smooth y
    have he : (inner ℂ y (A 1 y)).re = ‖y‖ ^ 2 - (inner ℂ y (Ψ 1 y)).re := by
      simp only [A, sub_apply, one_apply_eq_self, inner_sub_right, Complex.sub_re]
      rw [show (inner ℂ y y).re = ‖y‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) y]
    rw [he]
    exact hh
  have hθ (h : Finset.Iic n → Fin m) : θ (W h v) =
      2 * (f (iterate (fun x i => H i (x - u)) η q.x0 (extendHistory h) n) - f u) := by
    dsimp [θ, W, v]
    rw [liftedProduct_iterate, model.population, finite_integral]
    simp only [Complexified.real_pair, Complexified.imag_pair, map_zero, inner_zero_left, add_zero, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hfinite := finite_covariance_source_bound w (fun h => measureReal_nonneg) W A θ
    (by positivity : 0 ≤ 30000 * q.L) hsource v
  have heq : (∑ h, w h * θ (W h v)) = 2 *
      (∫ ξ, f (iterate (fun x i => H i (x - u)) η q.x0 ξ n) - f u ∂(P : Measure (ℕ → Fin m))) := by
    rw [integral_iterate_finite_prefix P (fun x i => H i (x - u)) η q.x0 (fun x => f x - f u) n]
    simp_rw [hθ]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    dsimp [w]
    ring
  rw [heq] at hfinite
  have hcov : finiteCovariance w W = markovCovariance η H κ μ n := by
    symm
    exact markovCovariance_prefix η H κ μ n n (by omega)
  rw [hcov] at hfinite
  have hrate := markovCovariance_arbitrary_source_rate H κ Q π μ hstat hL hα hα1
    model.symmetric model.positive model.smooth hdec n hn
  have hv : ‖v‖ ≤ q.R := by simpa only [v, Complexified.norm_pair_zero] using model.radius
  have hv2 : ‖v‖ ^ 2 ≤ q.R ^ 2 := by nlinarith [norm_nonneg v]
  have hupper : (30000 * q.L) * ‖markovCovariance η H κ μ n * A‖ * ‖v‖ ^ 2 ≤
      (30000 * q.L) * (300000000000 / (q.α * n)) * q.R ^ 2 := by gcongr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound := hfinite.trans hupper
  change _ ≤ _ at hbound
  calc
    _ ≤ ((30000 * q.L) * (300000000000 / (q.α * n)) * q.R ^ 2) / 2 := by
      dsimp [η, P] at hbound
      linarith
    _ = 4500000000000000 * q.L * q.R ^ 2 / (q.α * n) := by ring
    _ ≤ _ := by gcongr; norm_num

lemma iterate_accuracy {q : Params} {m : ℕ} {π : ProbabilityMeasure (Fin m)}
    {κ : Kernel (Fin m) (Fin m)} [IsMarkovKernel κ]
    {H : Fin m → q.E →L[ℝ] q.E} {f : q.E → ℝ} {u : q.E}
    (model : Model q m π κ H f u) (μ : ProbabilityMeasure (Fin m))
    (hL : 0 < q.L) (hα : 0 < q.α) (hα1 : q.α ≤ 1) (hε : 0 < q.ε) (K : ℕ) (hbudget : ⌈10000000000000000 * q.L * q.R ^ 2 / (q.α * q.ε)⌉₊ + 1 ≤ K) :
    (∫ ξ, f (iterate (fun x i => H i (x - u)) (q.α / (10000 * q.L)) q.x0 ξ K) - f u
      ∂(LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ : Measure (ℕ → Fin m))) ≤ q.ε := by
  have hK : 1 ≤ K := by omega
  obtain ⟨Q, hQ, hQs, hQstat, hdec⟩ := finite_residual_transition
    (fun i => (π : Measure (Fin m)).real {i}) (fun i j => (κ i).real {j})
    (finite_probability_weights _).1 (finite_probability_weights _).2
    (fun i => (finite_probability_weights (κ i)).2)
    (finite_stationary_weights κ π model.stationary) hα hα1
    (finite_refresh_weights κ π hα.le model.refresh)
  have : IsMarkovKernel (finiteWeightKernel Q) := finiteWeightKernel_markov Q hQ hQs
  have hstat := finiteWeightKernel_stationary Q hQ hQs π hQstat
  have hdec' : ∀ i j, (κ i).real {j} = (1 - q.α) * (finiteWeightKernel Q i).real {j} +
      q.α * (π : Measure (Fin m)).real {j} := by simpa only [finiteWeightKernel_real Q hQ] using hdec
  have hrisk := model.iterate_risk_bound μ (finiteWeightKernel Q) hstat hdec' hL hα hα1 K hK
  have hceil : 10000000000000000 * q.L * q.R ^ 2 / (q.α * q.ε) ≤ (K : ℝ) := by
    have hh := Nat.le_ceil (10000000000000000 * q.L * q.R ^ 2 / (q.α * q.ε))
    have hk : ((⌈10000000000000000 * q.L * q.R ^ 2 / (q.α * q.ε)⌉₊ + 1 : ℕ) : ℝ) ≤ K := Nat.cast_le.mpr hbudget
    push_cast at hk
    linarith
  have hmul := (div_le_iff₀ (mul_pos hα hε)).mp hceil
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  apply hrisk.trans
  apply (div_le_iff₀ (mul_pos hα hKpos)).mpr
  nlinarith [mul_nonneg hL.le (sq_nonneg q.R)]

end LongTails.Setups.MarkovQuadraticInterpolation.Model

end
