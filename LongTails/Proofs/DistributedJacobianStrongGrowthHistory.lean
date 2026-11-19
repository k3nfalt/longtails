import LongTails.Proofs.DistributedJacobianStrongGrowthBlock

open MeasureTheory

namespace LongTails.Proofs.DistributedJacobianStrongGrowthHistory

lemma product_event_bound {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (P : Measure Z) (Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (K : Z → Ω → ℝ) (W : Z → ℝ) (E : Set Z) (hE : MeasurableSet E)
    (hK : Measurable (Function.uncurry K)) (hK0 : ∀ z ω, 0 ≤ K z ω)
    (hKi : ∀ z ∈ E, Integrable (K z) Q)
    (hKW : ∀ z ∈ E, (∫ ω, K z ω ∂Q) ≤ W z)
    (hW : Integrable (E.indicator W) P) :
    Integrable (fun z : Z × Ω => E.indicator (fun t => K t z.2) z.1) (P.prod Q) ∧
      (∫ z : Z × Ω, E.indicator (fun t => K t z.2) z.1 ∂P.prod Q) ≤
        ∫ z, E.indicator W z ∂P := by
  classical
  let V : Z × Ω → ℝ := fun z => E.indicator (fun t => K t z.2) z.1
  have hm : Measurable V := by
    exact hK.indicator (hE.preimage measurable_fst)
  have hn (z : Z × Ω) : 0 ≤ V z := by
    exact Set.indicator_nonneg (fun t _ => hK0 t z.2) z.1
  have hf (z : Z) : Integrable (fun ω => V (z, ω)) Q := by
    by_cases hz : z ∈ E
    · simpa [V, Set.indicator_of_mem hz] using hKi z hz
    · simp [V, Set.indicator_of_notMem hz]
  have hb (z : Z) : (∫ ω, V (z, ω) ∂Q) ≤ E.indicator W z := by
    by_cases hz : z ∈ E
    · simpa [V, Set.indicator_of_mem hz] using hKW z hz
    · simp [V, Set.indicator_of_notMem hz]
  have he (z : Z) : (∫ ω, ‖V (z, ω)‖ ∂Q) = ∫ ω, V (z, ω) ∂Q :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => Real.norm_of_nonneg (hn (z, ω)))
  have ho : Integrable (fun z => ∫ ω, ‖V (z, ω)‖ ∂Q) P := by
    apply hW.mono' hm.aestronglyMeasurable.norm.integral_prod_right'
    apply Filter.Eventually.of_forall
    intro z
    rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _), he]
    exact hb z
  have hi : Integrable V (P.prod Q) :=
    (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨Filter.Eventually.of_forall hf, ho⟩
  refine ⟨hi, ?_⟩
  change (∫ z, V z ∂P.prod Q) ≤ _
  rw [integral_prod V hi]
  exact integral_mono hi.integral_prod_left hW hb

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradient

lemma history_block_contraction (p : Params) (hp : valid p) (I : Problem p)
    (hI : problemAssumptions p I)
    (g : Fin p.n → Point p → p.Ω → Point p) (S : Sampling p)
    (hg : oracleAssumptions p I g S) (T N : ℕ) {r : ℝ} (hr : 0 < r)
    (hT : 1 ≤ T) (hTκ : (T : ℝ) ≤ p.L / p.μ)
    (hn : 64 * (p.L / p.μ) * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T ≤ (p.n : ℝ))
    (hguard : p.M * r ≤ p.L /
      (16 * (p.L / p.μ) * p.ρ * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T))
    (center : (Fin N → p.Ω) → Point p) (hc : Measurable center)
    (E : Set (Fin N → p.Ω)) (hE : MeasurableSet E)
    (hlocal : ∀ z ∈ E, ‖center z - I.solution‖ ≤ r) :
    let H := 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T
    let past := fun ω (i : Fin N) => S.sample i.val ω
    Integrable (fun ω => E.indicator
      (fun z => ‖blockOutput p T N H g (center z) (fun k => S.sample k ω) - I.solution‖ ^ 2)
      (past ω)) (S.law : Measure S.Seed) ∧
    (∫ ω, E.indicator
      (fun z => ‖blockOutput p T N H g (center z) (fun k => S.sample k ω) - I.solution‖ ^ 2)
      (past ω) ∂(S.law : Measure S.Seed)) ≤
      (1 - (T : ℝ) / (64 * (p.L / p.μ))) *
        ∫ ω, E.indicator (fun z => ‖center z - I.solution‖ ^ 2) (past ω) ∂(S.law : Measure S.Seed) := by
  classical
  let H := 256 * (p.L / p.μ) * ((2 + p.ρ / 8 + p.ρ ^ 2 / 128) ^ T + 1) * r / T
  let c := 1 - (T : ℝ) / (64 * (p.L / p.μ))
  let P0 : Measure (Fin N → p.Ω) := Measure.pi fun _ : Fin N => (S.marginal : Measure p.Ω)
  let Q0 : Measure (ℕ → p.Ω) := Measure.infinitePi fun _ : ℕ => (S.marginal : Measure p.Ω)
  have hprev : Integrable (E.indicator (fun z => ‖center z - I.solution‖ ^ 2)) P0 := by
    apply (integrable_const (r ^ 2)).mono'
      ((((hc.sub_const I.solution).norm).pow_const 2).indicator hE).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro z
    by_cases hz : z ∈ E
    · rw [Set.indicator_of_mem hz, Real.norm_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) hr.le).mpr (hlocal z hz)
    · rw [Set.indicator_of_notMem hz, norm_zero]
      positivity
  let S0 : Sampling p := {
    Seed := ℕ → p.Ω
    measurableSeed := inferInstance
    law := ⟨Q0, inferInstance⟩
    marginal := S.marginal
    sample := fun k ω => ω k
    iid := by simpa [Q0] using OracleTemplate.StochasticGeneralized.infinitePi_iid (S.marginal : Measure p.Ω) }
  have hg0 : oracleAssumptions p I g S0 := hg
  let K : (Fin N → p.Ω) → (ℕ → p.Ω) → ℝ :=
    fun z ω => ‖blockOutput p T 0 H g (center z) ω - I.solution‖ ^ 2
  let W : (Fin N → p.Ω) → ℝ := fun z => c * ‖center z - I.solution‖ ^ 2
  have hK : Measurable (Function.uncurry K) :=
    (((DistributedJacobianStrongGrowthBlock.measurable_blockOutput p T 0 H g hg.1).comp
      ((hc.comp measurable_fst).prodMk measurable_snd)).sub_const I.solution).norm.pow_const 2
  have hb (z : Fin N → p.Ω) (hz : z ∈ E) :=
    DistributedJacobianStrongGrowthBlock.local_block_contraction p hp I hI g S0 hg0
      T 0 hr hT hTκ hn hguard (center z) (hlocal z hz)
  have hW : Integrable (E.indicator W) P0 := by
    change Integrable (fun z => E.indicator W z) P0
    simp only [W, Set.indicator_const_mul]
    exact hprev.const_mul c
  have hs := product_event_bound P0 Q0 K W E hE hK (fun _ _ => sq_nonneg _)
    (fun z hz => (hb z hz).1) (fun z hz => (hb z hz).2) hW
  have hpair := S.iid.prefix_tail_law N
  have hlaw : ProbabilityTheory.HasLaw
      (fun ω => ((fun i : Fin N => S.sample i.val ω), (fun k => S.sample (N + k) ω)))
      (P0.prod Q0) (S.law : Measure S.Seed) := ⟨hpair.measurable.aemeasurable, hpair.map_eq⟩
  have he (z : Fin N → p.Ω) (ω : S.Seed) :
      K z (fun k => S.sample (N + k) ω) =
        ‖blockOutput p T N H g (center z) (fun k => S.sample k ω) - I.solution‖ ^ 2 := by
    simp only [K, blockOutput, Nat.zero_add]
  have hi := hlaw.integrable_comp hs.1
  have hv := hlaw.integral_comp hs.1.aestronglyMeasurable
  have hpre := measurePreserving_fst.comp hpair
  have hprelaw : ProbabilityTheory.HasLaw (fun ω (i : Fin N) => S.sample i.val ω)
      P0 (S.law : Measure S.Seed) := ⟨hpre.measurable.aemeasurable, hpre.map_eq⟩
  have hpint := hprelaw.integral_comp hprev.aestronglyMeasurable
  simp only [Function.comp_def] at hpint
  dsimp only
  have hident (ω : S.Seed) :
      E.indicator (fun z => K z (fun k => S.sample (N + k) ω)) (fun i : Fin N => S.sample i.val ω) =
      E.indicator
        (fun z => ‖blockOutput p T N H g (center z) (fun k => S.sample k ω) - I.solution‖ ^ 2)
        (fun i : Fin N => S.sample i.val ω) := by
    apply congrArg (fun f => E.indicator f (fun i : Fin N => S.sample i.val ω))
    funext z
    exact he z ω
  change Integrable (fun ω => E.indicator
    (fun z => K z (fun k => S.sample (N + k) ω))
    (fun i : Fin N => S.sample i.val ω)) (S.law : Measure S.Seed) at hi
  change (∫ ω, E.indicator (fun z => K z (fun k => S.sample (N + k) ω))
    (fun i : Fin N => S.sample i.val ω) ∂(S.law : Measure S.Seed)) = _ at hv
  simp_rw [hident] at hi hv
  refine ⟨hi, ?_⟩
  rw [hv, hpint]
  calc
    _ ≤ ∫ z, E.indicator W z ∂P0 := hs.2
    _ = _ := by simp only [W, Set.indicator_const_mul, integral_const_mul, c]

end LongTails.Proofs.DistributedJacobianStrongGrowthHistory
