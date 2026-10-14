import LongTails.Proofs.Execution
import LongTails.Proofs.ClippedSubgradientLyapunov
import LongTails.Proofs.ClippedSubgradientTuning
import LongTails.Proofs.FixedBatchConfidenceProbability
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory
open scoped RealInnerProductSpace BigOperators
open OracleTemplate.ContinuizedSimilarQuasar

namespace OracleTemplate.WeaklyConvexHeavyTailed

open LongTails.Setups.WeaklyConvexHeavyTailed

section Sum

variable (q : Params) {g : q.E → q.Ω → q.E} {projection : q.E → q.E} {D : Set q.E}

lemma acc_eq_sum (hx0 : q.x0 ∈ D) (hprojD : ∀ y, projection y ∈ D) (prox : q.E → q.E)
    (ξ : ℕ → q.Ω) (k : ℕ) :
    (iterateSamples (accumulatingTransition (advanceD q (g := g) hprojD)
      (increment q prox)) k (⟨q.x0, hx0⟩, 0) (fun i : Fin k => ξ i.val)).2 =
      ∑ t ∈ Finset.range k,
        ‖trajectory q g projection ξ t - prox (trajectory q g projection ξ t)‖ ^ 2 := by
  let x : ℕ → {y : q.E // y ∈ D} := fun t =>
    ⟨trajectory q g projection ξ t, trajectory_mem q g projection hx0 hprojD ξ t⟩
  have hx : ∀ t, x (t + 1) = advanceD q (g := g) hprojD (x t) (ξ t) := fun t => rfl
  have h := accumulated_along (advanceD q (g := g) hprojD) (increment q prox) x ξ hx k 0
  have hx0' : x 0 = ⟨q.x0, hx0⟩ := rfl
  rw [hx0'] at h
  rw [h]
  simp only [increment, zero_add]
  rfl

lemma acc_nonneg (hprojD : ∀ y, projection y ∈ D) (prox : q.E → q.E) (k : ℕ) :
    ∀ (s : {x : q.E // x ∈ D} × ℝ) (η : Fin k → q.Ω), 0 ≤ s.2 →
      0 ≤ (iterateSamples (accumulatingTransition (advanceD q (g := g) hprojD)
        (increment q prox)) k s η).2 := by
  induction k with
  | zero => intro s η hs; exact hs
  | succ k ih =>
    intro s η hs
    apply ih
    simp only [accumulatingTransition, increment]
    positivity

lemma sum_bound (hD : Convex ℝ D) {f : q.E → ℝ} {v : q.E → q.E}
    (hv : WeakSubgradientOn D q.ρ f v) (hG : ∀ x ∈ D, ‖v x‖ ≤ q.G) (hρ : 0 < q.ρ)
    (hG0 : 0 < q.G) (hσ : 0 ≤ q.σ) (hα : 1 < q.α) (hα2 : q.α ≤ 2) (hε : 0 < q.ε)
    {prox : q.E → q.E} (hprox : IsProx f D q.ρ prox)
    (hg : Measurable (Function.uncurry g)) (hp : Measurable projection)
    (hproj : ∀ y, ∀ u ∈ D, ⟪y - projection y, u - projection y⟫ ≤ 0)
    (hprojD : ∀ y, projection y ∈ D) (hx0 : q.x0 ∈ D)
    (ν : ProbabilityMeasure q.Ω)
    (hgi : ∀ x ∈ D, Integrable (g x) (ν : Measure _))
    (hmean : ∀ x ∈ D, ∫ ω, g x ω ∂(ν : Measure _) = v x)
    (hmi : ∀ x ∈ D, Integrable (fun ω => ‖g x ω - v x‖ ^ q.α) (ν : Measure _))
    (hm : ∀ x ∈ D, (∫ ω, ‖g x ω - v x‖ ^ q.α ∂(ν : Measure _)) ≤ q.σ ^ q.α)
    {lower : ℝ} (hlow : ∀ y ∈ D, lower ≤ f y) (hgap : f q.x0 - lower ≤ q.Δ) (k : ℕ) :
    Integrable (fun η : Fin k → q.Ω =>
      (iterateSamples (accumulatingTransition (advanceD q (g := g) hprojD)
        (increment q prox)) k (⟨q.x0, hx0⟩, 0) η).2)
      (Measure.pi fun _ : Fin k => (ν : Measure q.Ω)) ∧
    (∫ η : Fin k → q.Ω,
      (iterateSamples (accumulatingTransition (advanceD q (g := g) hprojD)
        (increment q prox)) k (⟨q.x0, hx0⟩, 0) η).2
      ∂(Measure.pi fun _ : Fin k => (ν : Measure q.Ω))) ≤
      (q.Δ + k * (stepSize q * (q.σ ^ q.α / (threshold q / 2) ^ (q.α - 1)) ^ 2 +
          2 * q.ρ * stepSize q ^ 2 * noiseScale q)) / (q.ρ ^ 2 * stepSize q) := by
  have henv : Continuous (envelope f q.ρ prox) := continuous_envelope hD hv hG hρ hG0.le hprox
  have hpc : Continuous prox := (prox_lipschitzWith hD hv hρ hprox).continuous
  have hγ := stepSize_pos q hρ hG0 hσ hε
  have hc : 0 < q.ρ ^ 2 * stepSize q := mul_pos (pow_pos hρ 2) hγ
  have hr0 : 0 ≤ stepSize q * (q.σ ^ q.α / (threshold q / 2) ^ (q.α - 1)) ^ 2 +
      2 * q.ρ * stepSize q ^ 2 * noiseScale q :=
    add_nonneg (mul_nonneg hγ.le (sq_nonneg _))
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hρ.le) (sq_nonneg _))
        (noiseScale_pos q hG0 hσ hε).le)
  have hadv : Measurable (fun z : ({x : q.E // x ∈ D} × ℝ) × q.Ω =>
      accumulatingTransition (advanceD q (g := g) hprojD) (increment q prox) z.1 z.2) :=
    accumulatingTransition_measurable (advanceD_measurable q hg hp hprojD)
      (increment_measurable q hpc)
  have hmain := GapStrongGrowth.iterateSamples_measurable_integral hadv ν
    (lyapunov q f prox lower (q.ρ ^ 2 * stepSize q)) (lyapunov_measurable q henv _ _)
    (lyapunov_nonneg q hρ.le hprox hc.le hlow) zero_le_one
    (fun s => lyapunov_step q hD hv hG hρ hG0 hσ hα hα2 hε hprox hg hp hproj hprojD hgi hmean hmi hm s)
    k (⟨q.x0, hx0⟩, 0)
  simp only [one_pow, one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hmain
  have hV0 : lyapunov q f prox lower (q.ρ ^ 2 * stepSize q) (⟨q.x0, hx0⟩, 0) ≤ q.Δ := by
    simp only [lyapunov, abs_zero, mul_zero, add_zero]
    have := envelope_le_f hprox hx0
    linarith
  have hFm : Measurable (fun η : Fin k → q.Ω =>
      (iterateSamples (accumulatingTransition (advanceD q (g := g) hprojD)
        (increment q prox)) k (⟨q.x0, hx0⟩, 0) η).2) :=
    ((GapStrongGrowth.iterateSamples_measurable hadv k).comp
      (measurable_const.prodMk measurable_id)).snd
  have hFle : ∀ η : Fin k → q.Ω, q.ρ ^ 2 * stepSize q *
      (iterateSamples (accumulatingTransition (advanceD q (g := g) hprojD)
        (increment q prox)) k (⟨q.x0, hx0⟩, 0) η).2 ≤
      lyapunov q f prox lower (q.ρ ^ 2 * stepSize q)
        (iterateSamples (accumulatingTransition (advanceD q (g := g) hprojD)
          (increment q prox)) k (⟨q.x0, hx0⟩, 0) η) := by
    intro η
    unfold lyapunov
    have h1 := envelope_ge hρ.le hprox hlow
      (iterateSamples (accumulatingTransition (advanceD q (g := g) hprojD)
        (increment q prox)) k (⟨q.x0, hx0⟩, 0) η).1.val
    have h2 := le_abs_self (iterateSamples (accumulatingTransition
      (advanceD q (g := g) hprojD) (increment q prox)) k (⟨q.x0, hx0⟩, 0) η).2
    nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]
  have hF0 : ∀ η : Fin k → q.Ω, 0 ≤ (iterateSamples (accumulatingTransition
      (advanceD q (g := g) hprojD) (increment q prox)) k (⟨q.x0, hx0⟩, 0) η).2 :=
    fun η => acc_nonneg q hprojD prox k _ η le_rfl
  have hFint : Integrable (fun η : Fin k → q.Ω =>
      (iterateSamples (accumulatingTransition (advanceD q (g := g) hprojD)
        (increment q prox)) k (⟨q.x0, hx0⟩, 0) η).2)
      (Measure.pi fun _ : Fin k => (ν : Measure q.Ω)) := by
    refine Integrable.mono' (hmain.1.div_const (q.ρ ^ 2 * stepSize q)) hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun η => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 η), le_div_iff₀ hc, mul_comm]
    exact hFle η
  refine ⟨hFint, ?_⟩
  have hI := integral_mono (hFint.const_mul (q.ρ ^ 2 * stepSize q)) hmain.1 hFle
  rw [integral_const_mul] at hI
  rw [le_div_iff₀ hc, mul_comm]
  linarith [hI, hmain.2]

end Sum

section Main

lemma output_measurable (q : Params) {g : q.E → q.Ω → q.E} (hg : Measurable (Function.uncurry g))
    {projection : q.E → q.E} (hp : Measurable projection) :
    Measurable (fun seed : Fin (steps q + 1) × (ℕ → q.Ω) =>
      trajectory q g projection (fun n => seed.2 (2 * n)) seed.1.val) := by
  refine measurable_from_prod_countable_right (fun j => ?_)
  exact (trajectory_measurable q hg hp j.val).comp
    (Measurable.of_eval (f := fun ξ : ℕ → q.Ω => fun n => ξ (2 * n))
      (fun n => measurable_pi_apply (2 * n)))

lemma convergence : Convergence spec (fun q _ => 2 * steps q) := by
  apply convergence_of_public_budget (S := spec) (fun q => 2 * steps q)
  refine ⟨fun q => algorithm q, ?_, ?_⟩
  rotate_left
  · rintro q ⟨hρ, hG, hσ, _, _, _, hε⟩
    exact ⟨steps q, stepSize q, threshold q,
      stepSize_pos q hρ hG hσ hε, threshold_pos q hG hσ hε, rfl⟩
  rintro q ⟨hρ, hG, hσ, hα, hα2, hΔ, hε⟩ I O ⟨g, v, projection, ν, P, hIID, hO, hD, hDc, hx0, hv,
    hGv, ⟨lower, hlow, hgap⟩, hpm, hprojD, hproj, hgm, hgi, hmean, hmi, hm⟩
  subst hO
  have hexec : ∀ seed : (algorithm q).Seed × ((k : ℕ) → q.Ω),
      execute (sampleOracle q g projection P) (algorithm q) (fun _ => (2 * steps q)) seed.1 seed.2 =
        trajectory q g projection (fun n => seed.2 (2 * n)) seed.1.val :=
    fun seed => execute_algorithm q g projection P seed.1 seed.2
  change spec.successful q I
      (fun seed : (algorithm q).Seed × ((k : ℕ) → q.Ω) =>
        (execute (sampleOracle q g projection P) (algorithm q) (fun _ => (2 * steps q)) seed.1 seed.2))
      ⟨((algorithm q).law : Measure _).prod (P : Measure (ℕ → q.Ω)), inferInstance⟩
  simp only [hexec]
  have hex : ∀ x, ∃ xh ∈ I.domain, IsMinOn (proxObj I.f q.ρ x) I.domain xh :=
    fun x => exists_prox hDc hv hGv hρ hG.le hx0 x
  choose prox0 hprox0D hprox0 using hex
  have hprox0' : IsProx I.f I.domain q.ρ prox0 := fun x => ⟨hprox0D x, hprox0 x⟩
  refine ⟨output_measurable q hgm hpm, fun seed => trajectory_mem q g projection hx0 hprojD _ _,
    ⟨prox0, hprox0'⟩, fun prox hprox => ?_⟩
  set k := steps q + 1 with hk
  have hkpos : (0 : ℝ) < k := by rw [hk]; positivity
  have hpc : Continuous prox := (prox_lipschitzWith hD hv hρ hprox).continuous
  have hbound : ∀ x ∈ I.domain, (2 * q.ρ) ^ 2 * ‖x - prox x‖ ^ 2 ≤ 4 * q.G ^ 2 := by
    intro x hx
    have h1 := prox_dist_le hD hv hGv hρ hx (hprox x).1 (hprox x).2
    rw [norm_sub_rev] at h1
    have h2 : ‖x - prox x‖ ^ 2 ≤ (q.G / q.ρ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (2 * q.ρ) ^ 2 * (q.G / q.ρ) ^ 2 = 4 * q.G ^ 2 := by field_simp; ring
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg (2 * q.ρ))]
  let out : Fin k × (ℕ → q.Ω) → q.E := fun seed =>
    trajectory q g projection (fun n => seed.2 (2 * n)) seed.1.val
  let F : Fin k × (ℕ → q.Ω) → ℝ := fun seed => (2 * q.ρ) ^ 2 * ‖out seed - prox (out seed)‖ ^ 2
  have houtm : Measurable out := output_measurable q hgm hpm
  have hFm : Measurable F :=
    ((houtm.sub (hpc.measurable.comp houtm)).norm.pow_const 2).const_mul _
  have hF0 : ∀ seed, 0 ≤ F seed := fun seed => by positivity
  have hFb : ∀ seed, F seed ≤ 4 * q.G ^ 2 :=
    fun seed => hbound _ (trajectory_mem q g projection hx0 hprojD _ _)
  let μ : Measure (Fin k) := (PMF.uniformOfFintype (Fin k)).toMeasure
  have : IsProbabilityMeasure μ := PMF.toMeasure.isProbabilityMeasure _
  have hFint : Integrable F (μ.prod (P : Measure (ℕ → q.Ω))) :=
    Integrable.of_bound hFm.aestronglyMeasurable (4 * q.G ^ 2)
      (Filter.Eventually.of_forall (fun seed => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 seed)]; exact hFb seed))
  have hFjint : ∀ j : Fin k, Integrable (fun ξ => F (j, ξ)) (P : Measure (ℕ → q.Ω)) := by
    intro j
    refine Integrable.of_bound (hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (4 * q.G ^ 2) (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 _)]; exact hFb _
  refine ⟨hFint, ?_⟩
  change (∫ seed, F seed ∂(μ.prod (P : Measure (ℕ → q.Ω)))) ≤ q.ε ^ 2
  rw [integral_prod F hFint]
  have hsum : (∫ j : Fin k, (∫ ξ, F (j, ξ) ∂(P : Measure (ℕ → q.Ω))) ∂μ) =
      (k : ℝ)⁻¹ * ∑ j : Fin k, ∫ ξ, F (j, ξ) ∂(P : Measure (ℕ → q.Ω)) := by
    simp [μ, PMF.integral_eq_sum, PMF.uniformOfFintype_apply, ← Finset.mul_sum]
  rw [hsum, ← integral_finsetSum _ (fun j _ => hFjint j)]
  let Φ : (ℕ → q.Ω) → (Fin k → q.Ω) := fun ξ i => ξ (2 * i.val)
  have hΦ : MeasurePreserving Φ (P : Measure (ℕ → q.Ω)) (Measure.pi fun _ : Fin k => (ν : Measure q.Ω)) := by
    simpa only [Nat.zero_add] using
      FixedBatchConfidence.iid_finite_block_law (even_samples_iid hIID) 0 k
  let acc : (Fin k → q.Ω) → ℝ := fun η =>
    (iterateSamples (accumulatingTransition (advanceD q (g := g) hprojD)
      (increment q prox)) k (⟨q.x0, hx0⟩, 0) η).2
  have hsumF : ∀ ξ : ℕ → q.Ω, (∑ j : Fin k, F (j, ξ)) = (2 * q.ρ) ^ 2 * acc (Φ ξ) := by
    intro ξ
    simp only [F, out, acc, Φ]
    rw [acc_eq_sum q hx0 hprojD prox (fun n => ξ (2 * n)) k, Finset.mul_sum]
    rw [← Fin.sum_univ_eq_sum_range (fun t =>
      (2 * q.ρ) ^ 2 * ‖trajectory q g projection (fun n => ξ (2 * n)) t -
        prox (trajectory q g projection (fun n => ξ (2 * n)) t)‖ ^ 2) k]
  have hsb := sum_bound q hD hv hGv hρ hG hσ hα hα2 hε hprox hgm hpm hproj hprojD hx0 ν hgi hmean hmi hm
    hlow hgap k
  have hacc : (∫ ξ, acc (Φ ξ) ∂(P : Measure (ℕ → q.Ω))) =
      ∫ η, acc η ∂(Measure.pi fun _ : Fin k => (ν : Measure q.Ω)) := by
    rw [← hΦ.map_eq]
    have haccm : Measurable acc :=
      ((GapStrongGrowth.iterateSamples_measurable (accumulatingTransition_measurable
        (advanceD_measurable q hgm hpm hprojD) (increment_measurable q hpc)) k).comp
        (measurable_const.prodMk measurable_id)).snd
    rw [integral_map hΦ.measurable.aemeasurable haccm.aestronglyMeasurable]
  have hint2 : (∫ ξ, ∑ j : Fin k, F (j, ξ) ∂(P : Measure (ℕ → q.Ω))) =
      (2 * q.ρ) ^ 2 * ∫ η, acc η ∂(Measure.pi fun _ : Fin k => (ν : Measure q.Ω)) := by
    rw [← hacc, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hsumF)
  rw [hint2]
  have hrate := budget_rate q hρ hG hσ hα hε
  have hγ := stepSize_pos q hρ hG hσ hε
  have hc : 0 < q.ρ ^ 2 * stepSize q := mul_pos (pow_pos hρ 2) hγ
  set r := stepSize q * (q.σ ^ q.α / (threshold q / 2) ^ (q.α - 1)) ^ 2 +
    2 * q.ρ * stepSize q ^ 2 * noiseScale q with hr
  have hkk : ((steps q + 1 : ℕ) : ℝ) = (k : ℝ) := by simp [hk]
  rw [hkk] at hrate
  have hfinal : (k : ℝ)⁻¹ * ((2 * q.ρ) ^ 2 * ((q.Δ + k * r) / (q.ρ ^ 2 * stepSize q))) =
      4 * q.Δ / (stepSize q * k) + 4 * r / stepSize q := by
    field_simp
    ring
  calc (k : ℝ)⁻¹ * ((2 * q.ρ) ^ 2 * ∫ η, acc η ∂(Measure.pi fun _ : Fin k => (ν : Measure q.Ω)))
      ≤ (k : ℝ)⁻¹ * ((2 * q.ρ) ^ 2 * ((q.Δ + k * r) / (q.ρ ^ 2 * stepSize q))) := by
        gcongr
        exact hsb.2
    _ = 4 * q.Δ / (stepSize q * k) + 4 * r / stepSize q := hfinal
    _ ≤ q.ε ^ 2 := hrate

end Main

end OracleTemplate.WeaklyConvexHeavyTailed
