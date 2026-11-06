import LongTails.Proofs.AffineSoftmaxMoments
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineSoftmaxMeasurability

open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxQueries
open LongTails.Proofs.AffineSoftmaxSampling

variable {Z ι E : Type*} [MeasurableSpace Z] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]

omit [Fintype ι] in
lemma affine_measurable (s : Z → Snapshot ι E) (x : Z → E)
    (ha : Measurable (fun z => (s z).anchor))
    (hv : ∀ i, Measurable (fun z => (s z).value i))
    (hg : ∀ i, Measurable (fun z => (s z).field i)) (hx : Measurable x) (i : ι) :
    Measurable (fun z => affine (s z) i (x z)) :=
  (hv i).add ((hg i).inner (hx.sub ha))

lemma weight_measurable (s : Z → Snapshot ι E) (x : Z → E) (τ : ℝ)
    (ha : Measurable (fun z => (s z).anchor))
    (hv : ∀ i, Measurable (fun z => (s z).value i))
    (hg : ∀ i, Measurable (fun z => (s z).field i)) (hx : Measurable x) (i : ι) :
    Measurable (fun z => weight (s z) τ (x z) i) := by
  have he : ∀ j, Measurable (fun z => Real.exp (affine (s z) j (x z) / τ)) :=
    fun j => ((affine_measurable s x ha hv hg hx j).div_const τ).exp
  exact (he i).div (Finset.measurable_sum _ (fun j _ => he j))

lemma base_measurable (s : Z → Snapshot ι E) (x : Z → E) (τ : ℝ)
    (ha : Measurable (fun z => (s z).anchor))
    (hv : ∀ i, Measurable (fun z => (s z).value i))
    (hg : ∀ i, Measurable (fun z => (s z).field i)) (hx : Measurable x) :
    Measurable (fun z => base (s z) τ (x z)) := by
  exact Finset.measurable_sum _ (fun i _ =>
    (weight_measurable s x τ ha hv hg hx i).smul (hg i))

lemma numerator_measurable (s : Z → Snapshot ι E) (x : Z → E) (τ : ℝ)
    (ha : Measurable (fun z => (s z).anchor))
    (hv : ∀ i, Measurable (fun z => (s z).value i))
    (hg : ∀ i, Measurable (fun z => (s z).field i)) (hx : Measurable x)
    (i : ι) (reply : Z → ℝ × E) (hr : Measurable reply) :
    Measurable (fun z => numerator (s z) τ (x z) i (reply z)) := by
  have hw := ((hr.fst.sub (affine_measurable s x ha hv hg hx i)).div_const τ).exp
  exact (hw.smul (hr.snd.sub (hg i))).add
    ((hw.sub measurable_const).smul ((hg i).sub (base_measurable s x τ ha hv hg hx)))

omit [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma measurable_select {ι F : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace F] (f : Z → ι → F)
    (hf : ∀ i, Measurable (fun z => f z i)) (i : Z → ι) (hi : Measurable i) :
    Measurable (fun z => f z (i z)) :=
  (measurable_from_prod_countable_left (f := fun z : Z × ι => f z.1 z.2) hf).comp (measurable_id.prodMk hi)

lemma sampledEstimatorPlan_measurable [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι]
    (s : Z → Snapshot ι E) (x : Z → E) (τ : ℝ)
    (ha : Measurable (fun z => (s z).anchor))
    (hv : ∀ i, Measurable (fun z => (s z).value i))
    (hg : ∀ i, Measurable (fun z => (s z).field i)) (hx : Measurable x)
    (reply : Z → ι × E → ℝ × E)
    (hr : ∀ i, Measurable (fun z => reply z (i, x z)))
    (k : ℕ) (u : Z → unitInterval) (hu : Measurable u)
    (us : Z → Fin k → unitInterval) (hus : ∀ j, Measurable (fun z => us z j)) :
    Measurable (fun z => OracleTemplate.ComponentEnvelope.Program.eval (reply z)
      (sampledEstimatorPlan (s z) τ (x z) k (u z) (us z))) := by
  let d := fun z v => LongTails.Algorithms.FiniteCategoricalSampler.draw ι
    (gibbsWeights τ (fun i => affine (s z) i (x z))) v
  have hw : Measurable (fun z => gibbsWeights τ (fun i => affine (s z) i (x z))) :=
    (gibbsWeights_measurable ι τ).comp (Measurable.of_eval (fun i => affine_measurable s x ha hv hg hx i))
  have hd : ∀ v : Z → unitInterval, Measurable v → Measurable (fun z => d z (v z)) :=
    fun v hv => (categorical_draw_measurable ι).comp (hw.prodMk hv)
  have hN : Measurable (fun z => numerator (s z) τ (x z) (d z (u z))
      (reply z (d z (u z), x z))) :=
    measurable_select _ (fun i => numerator_measurable s x τ ha hv hg hx i _ (hr i)) _ (hd u hu)
  have hR : Measurable (fun z => reciprocal (List.ofFn (fun j =>
      Real.exp (((reply z (d z (us z j), x z)).1 - affine (s z) (d z (us z j)) (x z)) / τ)))) := by
    simp_rw [reciprocal_ofFn]
    apply Finset.measurable_prod
    intro j _
    apply measurable_const.sub
    apply Measurable.exp
    apply Measurable.div_const
    exact measurable_select _ (fun i => (hr i).fst.sub (affine_measurable s x ha hv hg hx i))
      _ (hd (fun z => us z j) (hus j))
  have hh := (base_measurable s x τ ha hv hg hx).add (hR.smul hN)
  convert hh using 1
  funext z
  simp only [sampledEstimatorPlan, AffineSoftmaxExecution.estimatorPlan_eval, estimate, List.map_ofFn]
  rfl

lemma seededEstimatorPlan_measurable [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Nonempty ι] [StandardBorelSpace ι]
    (s : Z → Snapshot ι E) (x : Z → E) (τ : ℝ)
    (ha : Measurable (fun z => (s z).anchor))
    (hv : ∀ i, Measurable (fun z => (s z).value i))
    (hg : ∀ i, Measurable (fun z => (s z).field i)) (hx : Measurable x)
    (reply : Z → ι × E → ℝ × E)
    (hr : ∀ i, Measurable (fun z => reply z (i, x z)))
    (seed : Z → StepSeed) (hseed : Measurable seed) :
    Measurable (fun z => OracleTemplate.ComponentEnvelope.Program.eval (reply z)
      (seededEstimatorPlan (s z) τ (x z) (seed z))) := by
  apply measurable_select (fun z k => OracleTemplate.ComponentEnvelope.Program.eval (reply z)
    (sampledEstimatorPlan (s z) τ (x z) k (seed z).2.1 ((seed z).2.2 k))) _
    (fun z => (seed z).1) hseed.fst
  intro k
  apply sampledEstimatorPlan_measurable s x τ ha hv hg hx reply hr k _ hseed.snd.fst
  intro j
  exact (measurable_pi_apply j).comp ((measurable_pi_apply k).comp hseed.snd.snd)

omit [InnerProductSpace ℝ E] in
lemma exists_measurable_reply [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {C : Set E} (hC : MeasurableSet C) (f : ι → E → ℝ) (g : ι → E → E)
    (hf : ∀ i, ContinuousOn (f i) C) (hg : ∀ i, ContinuousOn (g i) C) :
    ∃ reply : ι × E → ℝ × E, Measurable reply ∧
      ∀ i x, x ∈ C → reply (i, x) = (f i x, g i x) := by
  classical
  let reply : ι × E → ℝ × E := fun z =>
    C.piecewise (fun x => (f z.1 x, g z.1 x)) (fun _ => 0) z.2
  refine ⟨reply, ?_, ?_⟩
  · apply measurable_from_prod_countable_right
    intro i
    exact ((hf i).prodMk (hg i)).measurable_piecewise continuousOn_const hC
  · intro i x hx
    simp [reply, Set.piecewise, hx]

end LongTails.Proofs.AffineSoftmaxMeasurability
