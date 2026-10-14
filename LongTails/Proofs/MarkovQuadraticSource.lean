import LongTails.Proofs.MarkovCovarianceEstimates
import LongTails.Proofs.MarkovQuadraticEnergy

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.MarkovQuadratic

noncomputable section

open MarkovProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private local instance : NormedSpace ℂ (Complexified E →L[ℂ] Complexified E) :=
  ContinuousLinearMap.toNormedSpace
private local instance : Module ℝ (Complexified E →L[ℂ] Complexified E) :=
  Module.complexToReal _
private local instance : NormedSpace ℝ (Complexified E →L[ℂ] Complexified E) :=
  NormedSpace.complexToReal
private local instance : NormedSpace ℂ ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
    (Complexified E →L[ℂ] Complexified E)) := ContinuousLinearMap.toNormedSpace
private local instance : Module ℝ ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
    (Complexified E →L[ℂ] Complexified E)) := Module.complexToReal _
private local instance : NormedSpace ℝ ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
    (Complexified E →L[ℂ] Complexified E)) := NormedSpace.complexToReal


omit [CompleteSpace E] in
lemma liftedProduct_real_step (H : ℕ → E →L[ℝ] E) (η : ℝ) (v : Complexified E) (k : ℕ) :
    Complexified.realPart (liftedProduct η H (k + 1) v) =
      Complexified.realPart (liftedProduct η H k v) -
        η • H k (Complexified.realPart (liftedProduct η H k v)) := by
  simp only [liftedProduct, mul_apply_eq_comp, liftedStep, Complexified.lift_apply,
    Complexified.real_pair, sub_apply, ContinuousLinearMap.id_apply, smul_apply]

omit [CompleteSpace E] in
lemma liftedProduct_imag_step (H : ℕ → E →L[ℝ] E) (η : ℝ) (v : Complexified E) (k : ℕ) :
    Complexified.imagPart (liftedProduct η H (k + 1) v) =
      Complexified.imagPart (liftedProduct η H k v) -
        η • H k (Complexified.imagPart (liftedProduct η H k v)) := by
  simp only [liftedProduct, mul_apply_eq_comp, liftedStep, Complexified.lift_apply,
    Complexified.imag_pair, sub_apply, ContinuousLinearMap.id_apply, smul_apply]

lemma geometric_liftedProduct_source (H : ℕ → E →L[ℝ] E) {L η q : ℝ}
    (hL : 0 < L) (hη : 0 ≤ η) (hηL : η * L ≤ 1) (hq : 0 ≤ q) (hq1 : q < 1)
    (hs : ∀ k, (H k).adjoint = H k) (hp : ∀ k x, 0 ≤ ⟪x, H k x⟫)
    (hb : ∀ k x, ⟪x, H k x⟫ ≤ L * ‖x‖ ^ 2) (v : Complexified E) (n : ℕ) :
    (1 - q) ^ 2 * (η * ∑ k ∈ Finset.range n,
      q ^ k * (inner ℂ v (Complexified.lift (H k) v)).re) ≤
      (2 * (1 - q) ^ 2 + 8 * (η * L) ^ 2) *
        (‖v‖ ^ 2 - censoredMean q n (fun k => ‖liftedProduct η H k v‖ ^ 2)) := by
  have hr : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hr2 : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq
  have hr1 : Real.sqrt q ≤ 1 := by nlinarith
  have hreal := geometric_quadratic_source H
    (fun k => Complexified.realPart (liftedProduct η H k v)) hL hη hηL hr hr1 hs hp hb
    (liftedProduct_real_step H η v) n
  have himag := geometric_quadratic_source H
    (fun k => Complexified.imagPart (liftedProduct η H k v)) hL hη hηL hr hr1 hs hp hb
    (liftedProduct_imag_step H η v) n
  have hpow (k : ℕ) : Real.sqrt q ^ (2 * k) = q ^ k := by rw [pow_mul, hr2]
  simp only [hr2, hpow, liftedProduct, one_apply_eq_self] at hreal himag
  have hsum := add_le_add hreal himag
  have hloss := censored_loss_identity q (fun k => liftedProduct η H k v) n
  simp only [liftedProduct, one_apply_eq_self] at hloss
  rw [hloss]
  simp only [Complexified.inner_re, Complexified.lift_apply,
    Complexified.real_pair, Complexified.imag_pair, Complexified.norm_sq]
  simp only [Finset.mul_sum, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib] at hsum ⊢
  linarith

lemma censoredCovariance_one_re {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (H : Ω → ℕ → E →L[ℝ] E) (η q : ℝ) (n : ℕ) (v : Complexified E) :
    (inner ℂ v (censoredCovariance w H η q n 1 v)).re =
      ∑ ω, w ω * censoredMean q n (fun k => ‖liftedProduct η (H ω) k v‖ ^ 2) := by
  rw [censoredCovariance, finiteCovariance_one_re]
  exact sum_censored_product_weights w q n (fun ω k => ‖liftedProduct η (H ω) k v‖ ^ 2)

lemma finite_geometric_source {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hws : ∑ ω, w ω = 1) (H : Ω → ℕ → E →L[ℝ] E)
    {L η q : ℝ} (hL : 0 < L) (hη : 0 ≤ η) (hηL : η * L ≤ 1)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hs : ∀ ω k, (H ω k).adjoint = H ω k) (hp : ∀ ω k x, 0 ≤ ⟪x, H ω k x⟫)
    (hb : ∀ ω k x, ⟪x, H ω k x⟫ ≤ L * ‖x‖ ^ 2) (v : Complexified E) (n : ℕ)
    (θ : ℝ) (hmean : ∀ k < n, ∑ ω, w ω * (inner ℂ v (Complexified.lift (H ω k) v)).re = θ) :
    (1 - q) * η * (1 - q ^ n) * θ ≤ (2 * (1 - q) ^ 2 + 8 * (η * L) ^ 2) *
      (‖v‖ ^ 2 - (inner ℂ v (censoredCovariance w H η q n 1 v)).re) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left
      (geometric_liftedProduct_source (H ω) hL hη hηL hq hq1 (hs ω) (hp ω) (hb ω) v n) (hw ω))
  have hl : (∑ ω, w ω * ((1 - q) ^ 2 * (η * ∑ k ∈ Finset.range n,
      q ^ k * (inner ℂ v (Complexified.lift (H ω k) v)).re))) =
      (1 - q) * η * (1 - q ^ n) * θ := by
    calc
      _ = (1 - q) ^ 2 * η * ∑ k ∈ Finset.range n, q ^ k *
          (∑ ω, w ω * (inner ℂ v (Complexified.lift (H ω k) v)).re) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro ω hω
        ring
      _ = (1 - q) ^ 2 * η * ((∑ k ∈ Finset.range n, q ^ k) * θ) := by
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        rw [hmean k (Finset.mem_range.mp hk)]
      _ = _ := by
        calc
          _ = (1 - q) * η * (((∑ k ∈ Finset.range n, q ^ k) * (1 - q)) * θ) := by ring
          _ = _ := by rw [geom_sum_mul_neg]; ring
  have hr : (∑ ω, w ω * ((2 * (1 - q) ^ 2 + 8 * (η * L) ^ 2) *
      (‖v‖ ^ 2 - censoredMean q n (fun k => ‖liftedProduct η (H ω) k v‖ ^ 2)))) =
      (2 * (1 - q) ^ 2 + 8 * (η * L) ^ 2) *
        (‖v‖ ^ 2 - (inner ℂ v (censoredCovariance w H η q n 1 v)).re) := by
    rw [censoredCovariance_one_re]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    · calc
        _ = (2 * (1 - q) ^ 2 + 8 * (η * L) ^ 2) * ‖v‖ ^ 2 * ∑ ω, w ω := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω hω
          ring
        _ = _ := by rw [hws]; ring
    · apply Finset.sum_congr rfl
      intro ω hω
      ring
  rwa [hl, hr] at h

open MeasureTheory ProbabilityTheory Function Preorder

lemma stationary_prefix_average {S : Type} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (κ : Kernel S S) [IsMarkovKernel κ]
    (π : ProbabilityMeasure S) (hstat : κ ∘ₘ (π : Measure S) = π)
    (g : S → ℝ) (n k : ℕ) (hk : k ≤ n) :
    (∑ h, ((LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ π : Measure (ℕ → S)).map
      (frestrictLe n)).real {h} * g (extendHistory h k)) =
      ∑ i, (π : Measure S).real {i} * g i := by
  have he : (∫ h, g (extendHistory h k)
      ∂((LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ π : Measure (ℕ → S)).map (frestrictLe n))) =
      ∫ i, g i ∂(π : Measure S) := by
    rw [integral_map (by fun_prop) (StronglyMeasurable.of_discrete.aestronglyMeasurable)]
    have hm := HeavyTailedMarkovGradient.pathLaw_stationary_marginal κ π hstat k
    rw [← hm, integral_map (measurable_pi_apply k).aemeasurable (StronglyMeasurable.of_discrete.aestronglyMeasurable)]
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [extendHistory_eq _ hk]
    rfl
  simpa only [finite_integral, smul_eq_mul] using he

lemma stationary_censored_source {S : Type} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (κ : Kernel S S) [IsMarkovKernel κ]
    (π : ProbabilityMeasure S) (hstat : κ ∘ₘ (π : Measure S) = π)
    (H : S → E →L[ℝ] E) {L η q : ℝ} (hL : 0 < L) (hη : 0 ≤ η) (hηL : η * L ≤ 1)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hs : ∀ i, (H i).adjoint = H i) (hp : ∀ i x, 0 ≤ ⟪x, H i x⟫)
    (hb : ∀ i x, ⟪x, H i x⟫ ≤ L * ‖x‖ ^ 2) (v : Complexified E) (n : ℕ) :
    (1 - q) * η * (1 - q ^ n) *
      (∑ i, (π : Measure S).real {i} * (inner ℂ v (Complexified.lift (H i) v)).re) ≤
      (2 * (1 - q) ^ 2 + 8 * (η * L) ^ 2) *
        (‖v‖ ^ 2 - (inner ℂ v (censoredMean q n (markovCovariance η H κ π) 1 v)).re) := by
  have h := finite_geometric_source
    (fun h => ((LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ π : Measure (ℕ → S)).map
      (frestrictLe n)).real {h})
    (finite_probability_weights _).1 (finite_probability_weights _).2
    (fun h k => H (extendHistory h k)) hL hη hηL hq hq1
    (fun h k => hs _) (fun h k => hp _) (fun h k => hb _) v n
    (∑ i, (π : Measure S).real {i} * (inner ℂ v (Complexified.lift (H i) v)).re)
    (fun k hk => stationary_prefix_average κ π hstat
      (fun i => (inner ℂ v (Complexified.lift (H i) v)).re) n k (by omega))
  rw [censoredMarkovCovariance_eq_mean] at h
  exact h

set_option synthInstance.maxHeartbeats 100000 in
lemma stationary_geometric_source {S : Type} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (κ : Kernel S S) [IsMarkovKernel κ]
    (π : ProbabilityMeasure S) (hstat : κ ∘ₘ (π : Measure S) = π)
    (H : S → E →L[ℝ] E) {L η q : ℝ} (hL : 0 < L) (hη : 0 ≤ η) (hηL : η * L ≤ 1)
    (hq : 0 ≤ q) (hq1 : q < 1)
    (hs : ∀ i, (H i).adjoint = H i) (hp : ∀ i x, 0 ≤ ⟪x, H i x⟫)
    (hb : ∀ i x, ⟪x, H i x⟫ ≤ L * ‖x‖ ^ 2) (v : Complexified E) :
    (1 - q) * η *
      (∑ i, (π : Measure S).real {i} * (inner ℂ v (Complexified.lift (H i) v)).re) ≤
      (2 * (1 - q) ^ 2 + 8 * (η * L) ^ 2) *
        (‖v‖ ^ 2 - (inner ℂ v (geometricMean q (markovCovariance η H κ π) 1 v)).re) := by
  have hc := tendsto_censoredMean hq hq1 (markovCovariance η H κ π)
    (norm_markovCovariance_le_one η H κ π hL hs hp hb hη (by linarith))
  let F : ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
      (Complexified E →L[ℂ] Complexified E)) → ℝ := fun A => (inner ℂ v (A 1 v)).re
  have hF : Continuous F := by
    have ha : Continuous (fun A : ((Complexified E →L[ℂ] Complexified E) →L[ℂ]
        (Complexified E →L[ℂ] Complexified E)) => A 1 v) :=
      (continuous_id.clm_apply continuous_const).clm_apply continuous_const
    exact Complex.continuous_re.comp (continuous_inner.comp (continuous_const.prodMk ha))
  have hv := hF.continuousAt.tendsto.comp hc
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1
  have hl := ((tendsto_const_nhds (x := (1 : ℝ))).sub hpow).const_mul ((1 - q) * η)
  have hl' := hl.mul_const
    (∑ i, (π : Measure S).real {i} * (inner ℂ v (Complexified.lift (H i) v)).re)
  have hr := ((tendsto_const_nhds (x := ‖v‖ ^ 2)).sub hv).const_mul
    (2 * (1 - q) ^ 2 + 8 * (η * L) ^ 2)
  have hlim := le_of_tendsto_of_tendsto hl' hr (Filter.Eventually.of_forall
    (stationary_censored_source κ π hstat H hL hη hηL hq hq1 hs hp hb v))
  simpa only [sub_zero, mul_one, F] using hlim

lemma quadratic_source_tuning {α L θ D : ℝ} (hα : 0 < α) (hL : 0 < L) (hθ : 0 ≤ θ)
    (h : α * (α / (10000 * L)) * θ ≤
      (2 * α ^ 2 + 8 * ((α / (10000 * L)) * L) ^ 2) * D) : θ ≤ 30000 * L * D := by
  have hβ : α / (10000 * L) * L = α / 10000 := by field_simp
  rw [hβ] at h
  have hcoef : 0 < 2 * α ^ 2 + 8 * (α / 10000) ^ 2 := by positivity
  have hlhs : 0 ≤ α * (α / (10000 * L)) * θ := by positivity
  have hD : 0 ≤ D := nonneg_of_mul_nonneg_right (hlhs.trans h) hcoef
  have hsmall : (2 * α ^ 2 + 8 * (α / 10000) ^ 2) * D ≤ 3 * α ^ 2 * D := by
    apply mul_le_mul_of_nonneg_right _ hD
    nlinarith [sq_nonneg α]
  have hs := h.trans hsmall
  have he : α * (α / (10000 * L)) = α ^ 2 / (10000 * L) := by ring
  rw [he, div_mul_eq_mul_div] at hs
  have hc := (div_le_iff₀ (by positivity : 0 < 10000 * L)).mp hs
  have hh : α ^ 2 * θ ≤ α ^ 2 * (30000 * L * D) := by nlinarith [hc]
  exact le_of_mul_le_mul_left hh (sq_pos_of_pos hα)

lemma stationary_geometric_source_tuned {S : Type} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (κ : Kernel S S) [IsMarkovKernel κ]
    (π : ProbabilityMeasure S) (hstat : κ ∘ₘ (π : Measure S) = π)
    (H : S → E →L[ℝ] E) {L α : ℝ} (hL : 0 < L) (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : ∀ i, (H i).adjoint = H i) (hp : ∀ i x, 0 ≤ ⟪x, H i x⟫)
    (hb : ∀ i x, ⟪x, H i x⟫ ≤ L * ‖x‖ ^ 2) (v : Complexified E) :
    (∑ i, (π : Measure S).real {i} * (inner ℂ v (Complexified.lift (H i) v)).re) ≤
      30000 * L * (‖v‖ ^ 2 - (inner ℂ v
        (geometricMean (1 - α) (markovCovariance (α / (10000 * L)) H κ π) 1 v)).re) := by
  have hη : 0 ≤ α / (10000 * L) := by positivity
  have hηL : α / (10000 * L) * L ≤ 1 := by
    have he : α / (10000 * L) * L = α / 10000 := by field_simp
    rw [he]
    linarith
  apply quadratic_source_tuning hα hL
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (measureReal_nonneg) (Complexified.lift_positive (H i) (hp i) v)
  · have h := stationary_geometric_source κ π hstat H hL hη hηL
      (sub_nonneg.mpr hα1) (by linarith : 1 - α < 1) hs hp hb v
    simpa only [sub_sub_cancel] using h

end

end OracleTemplate.MarkovQuadratic
