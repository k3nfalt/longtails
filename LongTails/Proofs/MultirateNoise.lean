import LongTails.Proofs.MultirateFiltration
import LongTails.Proofs.GeneralizedLipschitzWarmStartSampling
import LongTails.Proofs.TwoSidedPLSampling

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.MultirateNoise

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector

open LongTails.Setups.MultirateSmoothNonconvex
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Setups.StochasticSmoothAndConvex (IsStochasticGradient)
open LongTails.Algorithms.MultirateAllocation LongTails.Algorithms.MultirateTrajectory
open LongTails.Algorithms.MultirateCalendar
open MultirateFiltration

variable {p : Params}

noncomputable def kernel (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (i : Fin p.n) (x : Point p) (z : Fin (batch p i) → p.Ω) : Point p :=
  (1 / (batch p i : ℝ)) • ∑ j, g i x (z j) - gradient (f i) x

noncomputable def noise (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (k : ℕ) (i : Fin p.n) (s : Samples p) :=
  kernel g f i (query g k i s) (block p i (epoch p i k) s)

lemma noise_eq (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (k : ℕ) (i : Fin p.n) (s : Samples p) :
    noise g f k i s = batchMean p g s i (epoch p i k) (query g k i s) - gradient (f i) (query g k i s) := by
  simp only [noise, kernel, batchMean, block, one_div]
  rw [Fin.sum_univ_eq_sum_range (fun j => g i (query g k i s) (s i (epoch p i k * batch p i + j)))]

lemma kernel_measurable (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (hf : ∀ i, Measurable (gradient (f i))) (i : Fin p.n) :
    Measurable (Function.uncurry (kernel g f i)) := by
  apply Measurable.sub _ ((hf i).comp measurable_fst)
  apply Measurable.fun_const_smul
  exact Finset.measurable_sum _ fun j _ => (hg i).comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

noncomputable abbrev batchLaw (μ : Fin p.n → ProbabilityMeasure p.Ω) (i : Fin p.n) :=
  Measure.pi (fun _ : Fin (batch p i) => (μ i : Measure p.Ω))

lemma kernel_moments (μ : Fin p.n → ProbabilityMeasure p.Ω)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (i : Fin p.n) (x : Point p) :
    Integrable (kernel g f i x) (batchLaw μ i) ∧ (∫ z, kernel g f i x z ∂batchLaw μ i) = 0 ∧
    Integrable (fun z => ‖kernel g f i x z‖ ^ 2) (batchLaw μ i) ∧
    ∫ z, ‖kernel g f i x z‖ ^ 2 ∂batchLaw μ i ≤ p.σ i ^ 2 / batch p i := by
  obtain ⟨hi, he⟩ := OracleTemplate.LightTail.finite_mean_integral ((hsg i).integrable x)
    (batch p i) (MultirateAllocation.batch_pos i)
  obtain ⟨hi₂, he₂⟩ := OracleTemplate.RobustGradient.finite_mean_variance
    ((hsg i).measurable.comp measurable_prodMk_left) ((hsg i).integrable x) (gradient (f i) x)
    ((hsg i).variance_integrable x) ((hsg i).unbiased x) (batch p i) (MultirateAllocation.batch_pos i)
  refine ⟨hi.sub (integrable_const _), ?_, hi₂, he₂.trans_le (div_le_div_of_nonneg_right
    ((hsg i).variance x) (Nat.cast_nonneg _))⟩
  unfold kernel
  rw [integral_sub hi (integrable_const _), he, (hsg i).unbiased]
  simp

lemma block_measurable (i : Fin p.n) (a : ℕ) : Measurable (block p i a) :=
  Measurable.of_eval fun j => sample_coordinate p i (a * batch p i + j)

lemma kernel_comp {S : Type*} [MeasurableSpace S]
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (hf : ∀ i, Measurable (gradient (f i)))
    (i : Fin p.n) (H : S → Point p) (B : S → Fin (batch p i) → p.Ω)
    (hH : Measurable H) (hB : Measurable B) : Measurable (fun s => kernel g f i (H s) (B s)) := by
  change Measurable (Function.uncurry (kernel g f i) ∘ (fun s => (H s, B s)))
  exact Measurable.comp (g := Function.uncurry (kernel g f i)) (f := fun s => (H s, B s))
    (kernel_measurable g f hg hf i) (hH.prodMk hB)

lemma prior_noise (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (hf : ∀ i, Measurable (gradient (f i)))
    (k : ℕ) {i j : Fin p.n} (hij : i ≠ j) (h : release p i k ≤ release p j k) :
    @Measurable _ _ (priorSpace p j (epoch p j k)) _ (noise g f k i) := by
  let : MeasurableSpace (Samples p) := priorSpace p j (epoch p j k)
  have hB : Measurable (block p i (epoch p i k)) := Measurable.of_eval fun v =>
    prior_coordinate (w := i) (i := j) (a := epoch p j k) (j := epoch p i k * batch p i + v) (Or.inl hij)
  exact kernel_comp g f hg hf i (query g k i) (block p i (epoch p i k)) (prior_query g hg i j k h) hB

lemma noise_measurable (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (hf : ∀ i, Measurable (gradient (f i)))
    (k : ℕ) (i : Fin p.n) : Measurable (noise g f k i) :=
  kernel_comp g f hg hf i (query g k i) (block p i (epoch p i k))
    ((prior_query g hg i i k le_rfl).mono (prior_le i (epoch p i k)) le_rfl) (block_measurable i (epoch p i k))

lemma second_moment (P : Measure (Samples p)) [IsProbabilityMeasure P]
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (hw : iIndepFun (fun i (s : Samples p) => s i) P)
    (hIID : ∀ i, IID (fun j (s : Samples p) => s i j) (μ i : Measure _) P)
    (g : Fin p.n → Point p → p.Ω → Point p) (f : Functions p)
    (hsg : ∀ i, IsStochasticGradient (Point p) p.Ω (μ i) (f i) (g i) (p.σ i))
    (hf : ∀ i, Measurable (gradient (f i))) (k : ℕ) (i : Fin p.n) :
    Integrable (fun s => ‖noise g f k i s‖ ^ 2) P ∧
    (∫ s, ‖noise g f k i s‖ ^ 2 ∂P) ≤ p.σ i ^ 2 / batch p i := by
  let H := query g k i
  let B := block p i (epoch p i k)
  have hH := prior_query g (fun i => (hsg i).measurable) i i k le_rfl
  have hm : Measurable H := hH.mono (prior_le _ _) le_rfl
  have hB : Measurable B := block_measurable i _
  have hind := independent_block P μ hw hIID i (epoch p i k) H hH
  have hl := block_law P μ hIID i (epoch p i k)
  let T := fun z : Point p × (Fin (batch p i) → p.Ω) => ‖kernel g f i z.1 z.2‖ ^ 2
  have hT : Measurable T := (kernel_measurable g f (fun i => (hsg i).measurable) hf i).norm.pow_const _
  let : IsProbabilityMeasure (P.map H) := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have h := GeneralizedLipschitzWarmStartSampling.nonnegative_product_bound (P.map H) (batchLaw μ i)
    hT (fun _ => sq_nonneg _) (fun x => (kernel_moments μ g f hsg i x).2.2.1)
    (fun x => (kernel_moments μ g f hsg i x).2.2.2)
  have h' := GeneralizedLipschitzWarmStartSampling.independent_pair_integral P (batchLaw μ i) hm hB hind hl.map_eq h.1
  exact ⟨h'.1, h'.2.trans_le h.2⟩

end LongTails.Proofs.MultirateNoise
