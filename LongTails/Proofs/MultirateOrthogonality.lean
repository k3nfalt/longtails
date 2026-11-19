import LongTails.Proofs.MultirateNoise

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.MultirateOrthogonality

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector

open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.MultirateAllocation LongTails.Algorithms.MultirateCalendar
open MultirateFiltration MultirateNoise

variable {p : Params} (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hIID : ∀ i, IID (fun j (s : Samples p) => s i j) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (hf : ∀ i, Measurable (gradient (f i))) (k : ℕ)

include μ hw hIID hsg hf

lemma cross_integrable (i j : Fin p.n) :
    Integrable (fun s => ⟪noise g f k i s, noise g f k j s⟫) P := by
  have h (w : Fin p.n) : MemLp (noise g f k w) 2 P :=
    (OracleTemplate.TwoSidedPL.memLp_two_iff_sq
      (noise_measurable g f (fun t => (hsg t).measurable) hf k w).aestronglyMeasurable).mpr
      (second_moment P μ hw hIID g f hsg hf k w).1
  exact OracleTemplate.TwoSidedPL.integrable_inner_of_memLp (h i) (h j)

lemma cross_ordered {i j : Fin p.n} (hij : i ≠ j) (h : release p i k ≤ release p j k) :
    (∫ s, ⟪noise g f k j s, noise g f k i s⟫ ∂P) = 0 := by
  let H := fun s => (query g k j s, noise g f k i s)
  let B := block p j (epoch p j k)
  have hg := fun i => (hsg i).measurable
  have hprior : @Measurable _ _ (priorSpace p j (epoch p j k)) _ H :=
    (prior_query g hg j j k le_rfl).prodMk (prior_noise g f hg hf k hij h)
  have hH : Measurable H := hprior.mono (prior_le _ _) le_rfl
  have hB : Measurable B := block_measurable j _
  let T := fun z : (Point p × Point p) × (Fin (batch p j) → p.Ω) =>
    ⟪kernel g f j z.1.1 z.2, z.1.2⟫
  have hT : Measurable T := ((kernel_measurable g f hg hf j).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).inner (measurable_snd.comp measurable_fst)
  have hI := independent_block P μ hw hIID j (epoch p j k) H hprior
  have hl := block_law P μ hIID j (epoch p j k)
  have hmap : P.map (fun s => (H s, B s)) = (P.map H).prod (batchLaw μ j) := by
    rw [hI.map_prod_eq_prod_map_map hH.aemeasurable hB.aemeasurable, hl.map_eq]
  have hint : Integrable T ((P.map H).prod (batchLaw μ j)) := by
    rw [← hmap]
    exact (integrable_map_measure hT.aestronglyMeasurable (hH.prodMk hB).aemeasurable).mpr
      (cross_integrable P μ hw hIID g f hsg hf k j i)
  have ht := GeneralizedLipschitzWarmStartSampling.independent_pair_integral P (batchLaw μ j)
    hH hB hI hl.map_eq hint
  change (∫ s, T (H s, B s) ∂P) = 0
  rw [ht.2]
  have he := GeneralizedLipschitzWarmStartSampling.fresh_inner_identity (P.map H) (batchLaw μ j)
    (query := Prod.fst) (direction := Prod.snd) (fun x => (kernel_moments μ g f hsg j x).1) hint
  simp only [(fun x => (kernel_moments μ g f hsg j x).2.1), inner_zero_left, integral_zero] at he
  exact he

lemma aggregate_variance (hh : ∀ i, 0 < p.h i) (hσ : ∀ i, 0 ≤ p.σ i) (hε : 0 < p.ε) :
    let Z := fun s => (p.n : ℝ)⁻¹ • ∑ i, noise g f k i s
    Integrable (fun s => ‖Z s‖ ^ 2) P ∧ (∫ s, ‖Z s‖ ^ 2 ∂P) ≤ precision p ^ 2 := by
  classical
  let X := noise g f k
  have hcross (i j : Fin p.n) : Integrable (fun s => ⟪X i s, X j s⟫) P :=
    cross_integrable P μ hw hIID g f hsg hf k i j
  have hc (i j : Fin p.n) : (∫ s, ⟪X i s, X j s⟫ ∂P) ≤ if i = j then p.σ i ^ 2 / batch p i else 0 := by
    split
    next he =>
      subst j
      simp only [real_inner_self_eq_norm_sq]
      exact (second_moment P μ hw hIID g f hsg hf k i).2
    next he =>
      rcases le_total (release p i k) (release p j k) with h | h
      · calc
          _ = ∫ s, ⟪X j s, X i s⟫ ∂P := integral_congr_ae (Filter.Eventually.of_forall fun _ => real_inner_comm _ _)
          _ ≤ 0 := (cross_ordered P μ hw hIID g f hsg hf k he h).le
      · exact (cross_ordered P μ hw hIID g f hsg hf k (Ne.symm he) h).le
  have hsum (s) : ‖∑ i, X i s‖ ^ 2 = ∑ i, ∑ j, ⟪X i s, X j s⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
  have hrows (i : Fin p.n) := integrable_finsetSum Finset.univ (fun j _ => hcross i j)
  have hs : Integrable (fun s => ‖∑ i, X i s‖ ^ 2) P := by
    simp_rw [hsum]
    exact integrable_finsetSum _ (fun i _ => hrows i)
  have hv : (∫ s, ‖∑ i, X i s‖ ^ 2 ∂P) ≤ ((p.n : ℝ) * precision p) ^ 2 := by
    simp_rw [hsum]
    rw [integral_finsetSum _ (fun i _ => hrows i)]
    simp_rw [integral_finsetSum _ (fun j _ => hcross _ j)]
    apply le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hc i j)
    simpa using MultirateAllocation.batch_variance hh hσ hε
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  refine ⟨hs.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ ((p.n : ℝ)⁻¹)^2 * ((p.n : ℝ) * precision p)^2 := mul_le_mul_of_nonneg_left hv (sq_nonneg _)
    _ = _ := by field_simp

end LongTails.Proofs.MultirateOrthogonality
