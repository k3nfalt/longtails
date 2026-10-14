import LongTails.Proofs.GapStrongGrowthStochastic
import LongTails.Proofs.AdaptiveIID

open MeasureTheory Set ProbabilityTheory
open OracleTemplate.ContinuizedSimilarQuasar

namespace OracleTemplate.GapStrongGrowth

open LongTails.Setups.GapSmoothStrongGrowth

lemma iid_groups_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : Measure (ℕ → Ω)) [IsProbabilityMeasure P]
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → Ω) => ξ k) μ P) (n b : ℕ) :
    MeasurePreserving (fun ξ : ℕ → Ω => fun i : Fin n => fun j : Fin b => ξ (i.val*b+j.val))
      P (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin b => μ) := by
  exact (StochasticGeneralized.prefix_preserving (Measure.pi fun _ : Fin b => μ) n).comp
    (OracleTemplate.FiniteVariance.infinite_block_law μ P h.independent h.marginal b)

lemma iterate_block_time (p : Params) (g : p.E → p.Ω → p.E) (n : ℕ)
    (s : ℕ × (p.E × p.E)) (ξ : Fin n → Fin (batchSize p) → p.Ω) :
    (iterateSamples (blockAdvance p g) n s ξ).1 = s.1 + n := by
  induction n generalizing s with
  | zero => simp [iterateSamples]
  | succ n ih =>
    simp only [iterateSamples, ih, blockAdvance]
    omega

lemma iterate_block_run (p : Params) (g : p.E → p.Ω → p.E)
    (ξ : ℕ → Fin (batchSize p) → p.Ω) (n : ℕ) :
    iterateSamples (blockAdvance p g) n (0, (p.x0, p.x0)) (fun i => ξ i.val) =
      (n, run p g ξ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterateSamples_succ_last]
    change blockAdvance p g
      (iterateSamples (blockAdvance p g) n (0, (p.x0, p.x0)) (fun i => ξ i.val)) (ξ n) = _
    rw [ih]
    rfl

lemma initial_exponential_bound {q R V : ℝ} (hq : 0 < q) (hR : 0 < R)
    (hV : V ≤ 3 * R ^ 2 / 2) :
    Real.exp (-(q / (64 * R ^ 2)) * (8 * R ^ 2)) *
      Real.exp (q / (64 * R ^ 2) * V) ≤ Real.exp (-13 * q / 128) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  field_simp
  nlinarith only [hV]

lemma finite_failure_bound (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1) (hρ : 1 ≤ p.ρ)
    (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    {f : p.E → ℝ} {u : p.E} (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hmin : IsMinOn f univ u) (hmodel : GapUpperModel f u p.H0 p.H1)
    (hr : ‖p.x0 - u‖ ≤ p.R) (hgap : f p.x0 - f u ≤ p.Δ)
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] {g : p.E → p.Ω → p.E}
    (hg : IsStrongGrowthOracle μ f g p.ρ) (n : ℕ)
    (hn : 16 * p.R ^ 2 / p.ε ≤ weight p n) :
    Measurable (fun ξ : Fin n → Fin (batchSize p) → p.Ω =>
      (iterateSamples (blockAdvance p g) n (0, (p.x0, p.x0)) ξ).2.1) ∧
    (∫ ξ : Fin n → Fin (batchSize p) → p.Ω,
      (if p.ε < f ((iterateSamples (blockAdvance p g) n (0, (p.x0, p.x0)) ξ).2.1) - f u
        then (1 : ℝ) else 0)
      ∂Measure.pi (fun _ => Measure.pi (fun _ => μ))) ≤ p.δ := by
  let V := fun s : ℕ × (p.E × p.E) => energy p f u s.1 s.2
  let t := confidence p / (64 * p.R ^ 2)
  let c := 8 * p.R ^ 2
  let s0 : ℕ × (p.E × p.E) := (0, (p.x0, p.x0))
  let advance := blockAdvance p g
  let B : ProbabilityMeasure (Fin (batchSize p) → p.Ω) := ⟨Measure.pi fun _ => μ, inferInstance⟩
  have ht : 0 ≤ t := by dsimp [t]; exact div_nonneg (confidence_pos p).le (by positivity)
  have hf : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hgrad x).differentiableAt.continuousAt)).measurable
  have hVm : Measurable V := measurable_energy p hf u
  have ham : Measurable (fun z : (ℕ × (p.E × p.E)) × (Fin (batchSize p) → p.Ω) => advance z.1 z.2) := measurable_blockAdvance p hg.measurable
  have hstep (s) (hs : V s < c) :
      Integrable (fun ω => Real.exp (t * V (advance s ω))) (B : Measure _) ∧
      (∫ ω, Real.exp (t * V (advance s ω)) ∂(B : Measure _)) ≤ Real.exp (t * V s) :=
    batch_step_exponential p hR hΔ h0 h1 hρ hconv hgrad hmin hmodel μ hg s.1 s.2 hs.le
  have hstop := frozen_exponential_integral hVm ham B hstep n s0
  have hout : Measurable (fun ξ => (iterateSamples advance n s0 ξ).2.1) :=
    ((iterateSamples_measurable ham n).comp (measurable_const.prodMk measurable_id)).snd.fst
  refine ⟨hout, ?_⟩
  have hBad : MeasurableSet {ξ | p.ε < f ((iterateSamples advance n s0 ξ).2.1) - f u} :=
    measurableSet_lt measurable_const ((hf.comp hout).sub_const (f u))
  have hcross (ξ : Fin n → Fin (batchSize p) → p.Ω)
      (hbad : p.ε < f ((iterateSamples advance n s0 ξ).2.1) - f u) :
      c ≤ V (iterateSamples (freeze V c advance) n s0 ξ) := by
    rcases frozen_compare V c advance n s0 ξ with he | he
    · rw [← he]
      have htime : (iterateSamples advance n s0 ξ).1 = n := by
        simpa only [s0, Prod.fst, Nat.zero_add] using iterate_block_time p g n s0 ξ
      have hweight := weight_pos p hR hΔ n
      have hprod := mul_lt_mul_of_pos_left hbad hweight
      have htarget := (div_le_iff₀ hε).mp hn
      dsimp [V, c]
      unfold energy
      rw [htime]
      nlinarith only [hprod, htarget,
        sq_nonneg ‖(iterateSamples advance n s0 ξ).2.2 - u‖, sq_nonneg p.R]
    · exact he
  have htail := indicator_integral_exponential hBad
    (Measure.pi fun _ : Fin n => (B : Measure _)) ht hstop.1 hstop.2 hcross
  have hinit : V s0 ≤ 3 * p.R ^ 2 / 2 := initial_energy_bound p hR hΔ hr hgap
  exact htail.trans ((initial_exponential_bound (confidence_pos p) hR hinit).trans
    (confidence_tail p hδ hδ1))

lemma iid_failure_bound (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1) (hρ : 1 ≤ p.ρ)
    (hε : 0 < p.ε) (hδ : 0 < p.δ) (hδ1 : p.δ < 1)
    {f : p.E → ℝ} {u : p.E} (hconv : ConvexOn ℝ univ f)
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x)
    (hmin : IsMinOn f univ u) (hmodel : GapUpperModel f u p.H0 p.H1)
    (hr : ‖p.x0 - u‖ ≤ p.R) (hgap : f p.x0 - f u ≤ p.Δ)
    (μ : Measure p.Ω) [IsProbabilityMeasure μ] (P : ProbabilityMeasure (ℕ → p.Ω))
    (h_samples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k (ξ : ℕ → p.Ω) => ξ k) μ (P : Measure _))
    {g : p.E → p.Ω → p.E} (hg : IsStrongGrowthOracle μ f g p.ρ) (n : ℕ)
    (hn : 16 * p.R ^ 2 / p.ε ≤ weight p n) :
    Measurable (fun seed : Unit × (ℕ → p.Ω) =>
      (run p g (fun k i => seed.2 (k * batchSize p + i.val)) n).1) ∧
      (∫ seed : Unit × (ℕ → p.Ω),
        (if p.ε < f ((run p g (fun k i => seed.2 (k * batchSize p + i.val)) n).1) - f u
          then (1 : ℝ) else 0)
        ∂(Measure.dirac ()).prod (P : Measure _)) ≤ p.δ := by
  let T := Fin n → Fin (batchSize p) → p.Ω
  let F := fun ξ : T => (iterateSamples (blockAdvance p g) n (0, (p.x0, p.x0)) ξ).2.1
  let φ := fun seed : Unit × (ℕ → p.Ω) => fun i : Fin n => fun j : Fin (batchSize p) =>
    seed.2 (i.val * batchSize p + j.val)
  have hfinite := finite_failure_bound p hR hΔ h0 h1 hρ hε hδ hδ1 hconv hgrad hmin hmodel hr hgap μ hg n hn
  have hp12 := iid_groups_law μ (P : Measure _) h_samples n (batchSize p)
  have hp0 : MeasurePreserving (Prod.snd : Unit × (ℕ → p.Ω) → (ℕ → p.Ω))
      ((Measure.dirac ()).prod (P : Measure _)) (P : Measure _) := measurePreserving_snd
  have hp : MeasurePreserving φ ((Measure.dirac ()).prod (P : Measure _))
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (batchSize p) => μ) :=
    hp12.comp hp0
  have he (seed : Unit × (ℕ → p.Ω)) :
      (run p g (fun k i => seed.2 (k * batchSize p + i.val)) n).1 = F (φ seed) := by
    dsimp [F, φ]
    rw [iterate_block_run p g (fun k i => seed.2 (k * batchSize p + i.val)) n]
  simp_rw [he]
  refine ⟨hfinite.1.comp hp.measurable, ?_⟩
  have hf : Measurable f := (continuous_iff_continuousAt.mpr
    (fun x => (hgrad x).differentiableAt.continuousAt)).measurable
  have hm : Measurable (fun ξ : T => if p.ε < f (F ξ) - f u then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const ((hf.comp hfinite.1).sub_const _))
      measurable_const measurable_const
  have hl : HasLaw φ (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (batchSize p) => μ)
      ((Measure.dirac ()).prod (P : Measure _)) := ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  exact (hl.integral_comp hm.aestronglyMeasurable).trans_le hfinite.2

lemma confidence_formula (p : Params) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) :
    confidence p = 128 * (1 + Real.log (1 / p.δ)) := by
  unfold confidence
  rw [abs_of_nonpos (Real.log_nonpos hδ.le hδ1.le)]
  simp []

lemma explicit_iterations_suffice (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (hε : 0 < p.ε) (hεΔ : p.ε ≤ p.Δ) (h0 : 0 ≤ p.H0)
    (hδ : 0 < p.δ) (hδ1 : p.δ < 1) :
    16 * p.R ^ 2 / p.ε ≤ weight p
      ⌈134217728 * (1 + Real.log (1 / p.δ)) *
        ((1 + p.R * Real.sqrt p.H1) * Real.log (1 + p.Δ / p.ε) +
          p.R * Real.sqrt (p.H0 / p.ε))⌉₊ := by
  apply weight_reaches_accuracy p hR hΔ hε hεΔ h0
  rw [confidence_formula p hδ hδ1]
  convert Nat.le_ceil (134217728 * (1 + Real.log (1 / p.δ)) *
    ((1 + p.R * Real.sqrt p.H1) * Real.log (1 + p.Δ / p.ε) +
      p.R * Real.sqrt (p.H0 / p.ε))) using 1; ring

end OracleTemplate.GapStrongGrowth
