import LongTails.Proofs.CovarianceAcceleratedProcesses
import LongTails.Proofs.CovarianceAcceleratedParameters
import LongTails.Proofs.CovarianceAcceleratedGrid

open MeasureTheory ProbabilityTheory Convexity
open scoped RealInnerProductSpace NNReal
open LongTails.Algorithms.CovarianceAccelerated
open LongTails.Algorithms.CovarianceAcceleratedMixture
open LongTails.Proofs.CovarianceAcceleratedRun
open LongTails.Proofs.CovarianceAcceleratedProcesses

namespace LongTails.Proofs.CovarianceAcceleratedConvergence

noncomputable local instance simplexMeasurableSpace (n : ℕ) : MeasurableSpace (StdSimplex ℝ (Fin n)) := borel _
local instance (n : ℕ) : BorelSpace (StdSimplex ℝ (Fin n)) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (StdSimplex ℝ (Fin n)) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin n)).secondCountableTopology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n : ℕ} (c : Config E n)

omit [BorelSpace E] in
lemma phase_goodState {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω) (v : E → E)
    (B : ℕ → ℝ) (T : ℕ) {t : ℕ} (ht : t < T)
    (hr : ‖v (query c (phase c g ξ t)) - OracleTemplate.MultiplicativeRobustEstimator.medoid
      (phase c g ξ t).2.2.2‖ ≤ B t) : goodState c v B T (phase c g ξ t) := by
  have hc : (phase c g ξ t).1 = c.window + 1 + t := CovarianceAcceleratedExecution.trajectory_clock c g ξ _
  unfold goodState
  rw [hc, Nat.add_sub_cancel_left]
  exact ⟨by omega, by omega, hr⟩

lemma pathwise_energy_bound {Ω : Type*} (g : E → Ω → E) (ξ : ℕ → Ω)
    {f : E → ℝ} {v : E → E} {L : ℝ} (hη : 0 < c.η) (hL : 0 ≤ L)
    (hβ : 2 * c.η * L ≤ c.β) (hγ : 0 ≤ c.γ)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (v x) x)
    (hlip : ∀ x y, ‖v x - v y‖ ≤ L * ‖x - y‖)
    {M : ℝ} (hM : 0 ≤ M) (hz : ∀ i, ‖c.centers i‖ ≤ M)
    (w : StdSimplex ℝ (Fin n)) (B C : ℕ → ℝ) (T : ℕ) (ell : ℝ)
    (hgood : ∀ t < T, goodState c v B T (phase c g ξ t))
    (hlog : (∑ i ∈ Finset.range (c.window + 1 + T),
      logMassIncrement c g v B C T (trajectory c g ξ i) (ξ i)) ≤ ell)
    (hcomp : (∑ i ∈ Finset.range (c.window + 1 + T),
      comparatorIncrement c g v w B C T (trajectory c g ξ i) (ξ i)) ≤ ell) :
    cumulative c.η T * (f (output c g ξ (c.window + 1 + T)) - f (c.x0 + c.a • mean c.centers w)) ≤
      potential c.centers c.a c.β c.γ w (StdSimplex.single c.initialIndex) +
        2 * (∑ t ∈ Finset.range T, C t) + 2 * ell := by
  have ht := telescoping_energy c g ξ hη hL hβ hγ hc hg hlip hM hz w T
  rw [logMass_sum_of_good c g ξ v B C T hgood] at hlog
  rw [comparator_sum_of_good c g ξ v w B C T hgood] at hcomp
  rw [Finset.sum_sub_distrib] at ht
  have hβ0 : 0 ≤ c.β := (show 0 ≤ 2 * c.η * L by positivity).trans hβ
  have hp := CovarianceAcceleratedGeometry.potential_nonneg c.centers w (phase c g ξ T).2.2.1
    (a := c.a) hβ0 hγ hM hz
  linarith

lemma energy_failure_probability {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure Ξ} [IsProbabilityMeasure P]
    {ξ : ℕ → Ξ → Ω}
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ μ P)
    {f : E → ℝ} {g : E → Ω → E} {σ s L : ℝ}
    (ho : LongTails.Setups.CovarianceSmoothConvex.IsCovarianceGradient μ f g σ s)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hη : 0 < c.η) (hβ : 2 * c.η * L ≤ c.β) (hγ : 0 < c.γ)
    {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hz : ∀ i, ‖c.centers i‖ ≤ M) (ha : |c.a| * M ≤ R)
    (w : StdSimplex ℝ (Fin n)) (T : ℕ) (ell : ℝ) {proxy : ℝ≥0}
    (hp0 : 0 < (proxy : ℝ)) (hp1 : (proxy : ℝ) ≤ 1 / 4) :
    let B := fun t : ℕ => 48 * σ + 96 * L * R * (c.window + 1) / ((t : ℝ) + 1)
    (∀ t < T, 2 * R * weight c.η t * B t ≤ 1 / 4) →
    (∀ t < T, (weight c.η t * c.a) ^ 2 * B t ^ 2 ≤ (proxy : ℝ)) →
    P {ω | potential c.centers c.a c.β c.γ w (StdSimplex.single c.initialIndex) +
        2 * (∑ t ∈ Finset.range T, momentCost c R σ s proxy t) + 2 * ell <
      cumulative c.η T * (f (output c g (fun j => ξ j ω) (c.window + 1 + T)) -
        f (c.x0 + c.a • mean c.centers w))} ≤
      ENNReal.ofReal ((T : ℝ) * Real.exp (-7 * (c.window + 1) / 32)) +
        2 * ENNReal.ofReal (Real.exp (-ell)) := by
  intro B hsmall hproxy
  have hLip : LipschitzWith ⟨L, hL⟩ (gradient f) := LipschitzWith.of_dist_le_mul
    (fun x y => by
      change dist (gradient f x) (gradient f y) ≤ L * dist x y
      simpa only [dist_eq_norm] using hlip x y)
  have hv := hLip.continuous.measurable
  have hβ0 : 0 ≤ c.β := (show 0 ≤ 2 * c.η * L by positivity).trans hβ
  let C := momentCost c R σ s proxy
  let E0 : Set Ξ := {ω | ∃ t : Fin T, B t.val <
    ‖gradient f (query c (phase c g (fun j => ξ j ω) t.val)) -
      OracleTemplate.MultiplicativeRobustEstimator.medoid (phase c g (fun j => ξ j ω) t.val).2.2.2‖}
  let E1 : Set Ξ := {ω | ell ≤ ∑ i ∈ Finset.range (c.window + 1 + T),
    logMassIncrement c g (gradient f) B C T (trajectory c g (fun j => ξ j ω) i) (ξ i ω)}
  let E2 : Set Ξ := {ω | ell ≤ ∑ i ∈ Finset.range (c.window + 1 + T),
    comparatorIncrement c g (gradient f) w B C T (trajectory c g (fun j => ξ j ω) i) (ξ i ω)}
  have hE0 : P E0 ≤ ENNReal.ofReal ((T : ℝ) * Real.exp (-7 * (c.window + 1) / 32)) :=
    CovarianceAcceleratedHints.medoid_failure_probability c hsamples ho.measurable hv hη hβ0 hγ
      hM hR hσ hL hz ha hlip ho.variance_integrable ho.variance T
  have ht := increments_tails c hsamples ho hv hη hβ0 hγ hM hR hz ha B T hp0 hp1 hsmall hproxy w ell
  have hE1 : P E1 ≤ ENNReal.ofReal (Real.exp (-ell)) := ht.1
  have hE2 : P E2 ≤ ENNReal.ofReal (Real.exp (-ell)) := ht.2
  have hsub : {ω | potential c.centers c.a c.β c.γ w (StdSimplex.single c.initialIndex) +
        2 * (∑ t ∈ Finset.range T, C t) + 2 * ell <
      cumulative c.η T * (f (output c g (fun j => ξ j ω) (c.window + 1 + T)) -
        f (c.x0 + c.a • mean c.centers w))} ⊆ E0 ∪ (E1 ∪ E2) := by
    intro ω hbad
    by_cases h0 : ω ∈ E0
    · exact Or.inl h0
    by_cases h1 : ω ∈ E1
    · exact Or.inr (Or.inl h1)
    by_cases h2 : ω ∈ E2
    · exact Or.inr (Or.inr h2)
    have hgood : ∀ t < T, goodState c (gradient f) B T (phase c g (fun j => ξ j ω) t) := by
      intro t ht
      apply phase_goodState c g (fun j => ξ j ω) (gradient f) B T ht
      exact le_of_not_gt (fun hh => h0 ⟨⟨t, ht⟩, hh⟩)
    have hlog : (∑ i ∈ Finset.range (c.window + 1 + T),
        logMassIncrement c g (gradient f) B C T (trajectory c g (fun j => ξ j ω) i) (ξ i ω)) ≤ ell :=
      (lt_of_not_ge h1).le
    have hcomp : (∑ i ∈ Finset.range (c.window + 1 + T),
        comparatorIncrement c g (gradient f) w B C T (trajectory c g (fun j => ξ j ω) i) (ξ i ω)) ≤ ell :=
      (lt_of_not_ge h2).le
    have hb := pathwise_energy_bound c g (fun j => ξ j ω) hη hL hβ hγ.le hc hg hlip hM hz
      w B C T ell hgood hlog hcomp
    exact False.elim ((not_lt_of_ge hb) hbad)
  apply (measure_mono hsub).trans
  have hu := (measure_union_le E0 (E1 ∪ E2)).trans
    (add_le_add hE0 ((measure_union_le E1 E2).trans (add_le_add hE1 hE2)))
  simpa only [two_mul] using hu

lemma grid_failure_probability {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {P : Measure Ξ} [IsProbabilityMeasure P]
    {ξ : ℕ → Ξ → Ω}
    (hsamples : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ μ P)
    {f : E → ℝ} {g : E → Ω → E} {σ s L R mesh a η β γ : ℝ}
    (ho : LongTails.Setups.CovarianceSmoothConvex.IsCovarianceGradient μ f g σ s)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hR : 0 ≤ R) (hmesh : 0 < mesh)
    (ha : 0 < a) (hη : 0 < η) (hβ : 2 * η * L ≤ β) (hγ : 0 < γ)
    (x0 xstar : E) (hmin : IsMinOn f Set.univ xstar) (hdist : ‖x0 - xstar‖ ≤ R)
    (window T : ℕ) (hT : 0 < T) (ell : ℝ) {proxy : ℝ≥0}
    (hp0 : 0 < (proxy : ℝ)) (hp1 : (proxy : ℝ) ≤ 1 / 4) :
    let cfg := LongTails.Algorithms.CovarianceAcceleratedGrid.config x0 R mesh a η β γ window
    let B := fun t : ℕ => 48 * σ + 96 * L * R * (window + 1) / ((t : ℝ) + 1)
    (∀ t < T, 2 * R * weight η t * B t ≤ 1 / 4) →
    (∀ t < T, (weight η t * a) ^ 2 * B t ^ 2 ≤ (proxy : ℝ)) →
    P {ω | L * mesh ^ 2 / 2 +
        (R ^ 2 / (2 * a ^ 2) + β * R ^ 2 / 2 + γ +
          2 * (∑ t ∈ Finset.range T, momentCost cfg R σ s proxy t) + 2 * ell) / cumulative η T <
      f (output cfg g (fun j => ξ j ω) (window + 1 + T)) - f xstar} ≤
      ENNReal.ofReal ((T : ℝ) * Real.exp (-7 * (window + 1) / 32)) +
        2 * ENNReal.ofReal (Real.exp (-ell)) := by
  intro cfg B hsmall hproxy
  obtain ⟨i, hi⟩ := CovarianceAcceleratedGrid.comparator_error hR hmesh ha hL hg hlip x0 xstar hmin hdist
  let w := (StdSimplex.single i : StdSimplex ℝ _)
  have hβ0 : 0 ≤ β := (show 0 ≤ 2 * η * L by positivity).trans hβ
  have hpot := CovarianceAcceleratedGrid.initial_potential_le hR hmesh ha hβ0 hγ.le i
  have hrad : |a| * (R / a) ≤ R := by rw [abs_of_pos ha]; field_simp; exact le_rfl
  have hprob := energy_failure_probability cfg hsamples ho hc hg hlip hL hσ hη hβ hγ
    (div_nonneg hR ha.le) hR (CovarianceAcceleratedGrid.centers_norm_le hR hmesh ha)
    hrad w T ell hp0 hp1 hsmall hproxy
  apply le_trans (measure_mono ?_) hprob
  intro ω hbad
  have hA : 0 < cumulative η T := by unfold cumulative; positivity
  have hcmp : f (x0 + a • mean cfg.centers w) - f xstar ≤ L * mesh ^ 2 / 2 := by
    simpa only [cfg, w, LongTails.Algorithms.CovarianceAcceleratedGrid.config,
      CovarianceAcceleratedGeometry.mean_single] using hi
  have hlt :
      (R ^ 2 / (2 * a ^ 2) + β * R ^ 2 / 2 + γ +
          2 * (∑ t ∈ Finset.range T, momentCost cfg R σ s proxy t) + 2 * ell) / cumulative η T <
        f (output cfg g (fun j => ξ j ω) (window + 1 + T)) - f (x0 + a • mean cfg.centers w) := by
    change L * mesh ^ 2 / 2 + _ < _ at hbad
    linarith
  have hmul := (div_lt_iff₀ hA).mp hlt
  change potential cfg.centers a β γ w (StdSimplex.single 0) +
      2 * (∑ t ∈ Finset.range T, momentCost cfg R σ s proxy t) + 2 * ell <
        cumulative η T * (f (output cfg g (fun j => ξ j ω) (window + 1 + T)) -
          f (x0 + a • mean cfg.centers w))
  change potential cfg.centers a β γ w (StdSimplex.single 0) ≤ _ at hpot
  nlinarith

end LongTails.Proofs.CovarianceAcceleratedConvergence
