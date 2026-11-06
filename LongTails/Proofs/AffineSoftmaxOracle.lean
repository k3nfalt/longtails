import LongTails.Proofs.AffineSoftmaxMeasurability
import LongTails.Proofs.AffineSoftmaxRegularization

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AffineSoftmaxOracle

open LongTails.Algorithms.AffineSoftmaxEstimator
open LongTails.Algorithms.AffineSoftmaxQueries
open LongTails.Proofs.AffineSoftmaxResidual
open LongTails.Proofs.AffineSoftmaxMoments
open LongTails.Proofs.SmoothFiniteMaximumGeometry

variable {ι E : Type*} [Fintype ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [StandardBorelSpace ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma local_gradient_moments {C : Set E} (f : ι → E → ℝ) (s : Snapshot ι E)
    {L G r τ : ℝ} (hL : 0 ≤ L) (hG : 0 ≤ G) (hr : 0 ≤ r) (hτ : 0 < τ)
    (hcap : L * r ^ 2 ≤ τ) (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i z, z ∈ C → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ C → x ∈ C →
      ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ C → ‖gradient (f i) z‖ ≤ G)
    (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = gradient (f i) s.anchor)
    (hz : s.anchor ∈ C) {x : E} (hx : x ∈ C) (hd : ‖x - s.anchor‖ ≤ r)
    (reply : ι × E → ℝ × E) (hreply : ∀ i, reply (i, x) = (f i x, gradient (f i) x)) :
    let F := fun z => smoothValue τ (fun i => f i z)
    let H := fun seed => OracleTemplate.ComponentEnvelope.Program.eval reply (seededEstimatorPlan s τ x seed)
    Integrable H (stepLaw : Measure StepSeed) ∧
      (∫ seed, H seed ∂(stepLaw : Measure StepSeed)) = gradient F x ∧
      Integrable (fun seed => ‖gradient F x - H seed‖ ^ 2) (stepLaw : Measure StepSeed) ∧
      (∫ seed, ‖gradient F x - H seed‖ ^ 2 ∂(stepLaw : Measure StepSeed)) ≤
        8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2) := by
  have hw : ∀ i, 1 ≤ Real.exp (((reply (i, x)).1 - affine s i x) / τ) ∧
      Real.exp (((reply (i, x)).1 - affine s i x) / τ) ≤ 2 := by
    intro i
    have hrange := residual_exponent_bounds (hc i) (hg i)
      (fun z hz y hy => hlip i z y hz hy) hL hr hτ hcap hz hx hd
    have hh := exp_small_residual hrange.1 hrange.2
    simpa only [hreply, affine, hvalue, hfield] using And.intro hh.1 hh.2.1
  have hN : ∀ i, ‖numerator s τ x i (reply (i, x))‖ ^ 2 ≤
      8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2) := by
    intro i
    rw [hreply]
    exact truthful_numerator_sq_le f (fun i => gradient (f i)) s hL hG hr hτ hcap hc hg
      hlip hbound hvalue hfield hz hx hd i
  have hm := seeded_estimator_variance s τ x reply hw hN
  have hmean := seeded_estimator_mean s τ x reply hw
  have htarget : (∑ i, gibbsWeight τ (fun j => (reply (j, x)).1) i • (reply (i, x)).2) =
      gradient (fun z => smoothValue τ (fun i => f i z)) x := by
    rw [(smoothValue_gradient f (fun i => gradient (f i) x) hτ.ne' (fun i => hg i x hx)).gradient]
    simp only [hreply, gibbsWeight]
  rw [htarget] at hm hmean
  refine ⟨hm.1, hmean, ?_, ?_⟩
  · simpa only [norm_sub_rev] using hm.2.1
  · simpa only [norm_sub_rev] using hm.2.2

omit [CompleteSpace E] in
lemma regularized_field_measurable (s : Snapshot ι E) (τ μ : ℝ)
    (reply : ι × E → ℝ × E) (hr : Measurable reply) :
    Measurable (fun z : E × StepSeed => OracleTemplate.ComponentEnvelope.Program.eval reply
      (seededEstimatorPlan s τ z.1 z.2) + μ • (z.1 - s.anchor)) := by
  have hh := AffineSoftmaxMeasurability.seededEstimatorPlan_measurable
    (fun _ : E × StepSeed => s) Prod.fst τ measurable_const (fun _ => measurable_const)
    (fun _ => measurable_const) measurable_fst (fun _ => reply)
    (fun i => hr.comp (measurable_const.prodMk measurable_fst)) Prod.snd measurable_snd
  exact hh.add (measurable_const.smul (measurable_fst.sub measurable_const))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma shift_moments {Ω : Type*} [MeasurableSpace Ω] (P : ProbabilityMeasure Ω)
    (H : Ω → E) (target c : E) {V : ℝ}
    (hHi : Integrable H (P : Measure Ω)) (hmean : (∫ ω, H ω ∂(P : Measure Ω)) = target)
    (hEi : Integrable (fun ω => ‖target - H ω‖ ^ 2) (P : Measure Ω))
    (hvar : (∫ ω, ‖target - H ω‖ ^ 2 ∂(P : Measure Ω)) ≤ V) :
    Integrable (fun ω => H ω + c) (P : Measure Ω) ∧
      (∫ ω, H ω + c ∂(P : Measure Ω)) = target + c ∧
      Integrable (fun ω => ‖(target + c) - (H ω + c)‖ ^ 2) (P : Measure Ω) ∧
      (∫ ω, ‖(target + c) - (H ω + c)‖ ^ 2 ∂(P : Measure Ω)) ≤ V := by
  refine ⟨hHi.add (integrable_const c), ?_, ?_, ?_⟩
  · rw [integral_add hHi (integrable_const c), hmean, integral_const]
    simp only [probReal_univ, one_smul]
  · simpa only [add_sub_add_right_eq_sub] using hEi
  · simpa only [add_sub_add_right_eq_sub] using hvar

lemma local_regularized_gradient_moments {C : Set E} (f : ι → E → ℝ) (s : Snapshot ι E) (μ : ℝ)
    {L G r τ : ℝ} (hL : 0 ≤ L) (hG : 0 ≤ G) (hr : 0 ≤ r) (hτ : 0 < τ)
    (hcap : L * r ^ 2 ≤ τ) (hc : ∀ i, ConvexOn ℝ C (f i))
    (hg : ∀ i z, z ∈ C → HasGradientAt (f i) (gradient (f i) z) z)
    (hlip : ∀ i z x, z ∈ C → x ∈ C →
      ‖gradient (f i) z - gradient (f i) x‖ ≤ L * ‖z - x‖)
    (hbound : ∀ i z, z ∈ C → ‖gradient (f i) z‖ ≤ G)
    (hvalue : ∀ i, s.value i = f i s.anchor)
    (hfield : ∀ i, s.field i = gradient (f i) s.anchor)
    (hz : s.anchor ∈ C) {x : E} (hx : x ∈ C) (hd : ‖x - s.anchor‖ ≤ r)
    (reply : ι × E → ℝ × E) (hreply : ∀ i, reply (i, x) = (f i x, gradient (f i) x)) :
    let F := LongTails.Proofs.RecursiveEnvelopeGeometry.regularized
      (fun z => smoothValue τ (fun i => f i z)) μ s.anchor
    let H := fun seed => OracleTemplate.ComponentEnvelope.Program.eval reply
      (seededEstimatorPlan s τ x seed) + μ • (x - s.anchor)
    Integrable H (stepLaw : Measure StepSeed) ∧
      (∫ seed, H seed ∂(stepLaw : Measure StepSeed)) = gradient F x ∧
      Integrable (fun seed => ‖gradient F x - H seed‖ ^ 2) (stepLaw : Measure StepSeed) ∧
      (∫ seed, ‖gradient F x - H seed‖ ^ 2 ∂(stepLaw : Measure StepSeed)) ≤
        8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2) := by
  have hb := local_gradient_moments f s hL hG hr hτ hcap hc hg hlip hbound
    hvalue hfield hz hx hd reply hreply
  have hs := shift_moments stepLaw _ _ (μ • (x - s.anchor)) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2
  have hsoft := smoothValue_gradient f (fun i => gradient (f i) x) hτ.ne' (fun i => hg i x hx)
  have hreg := AffineSoftmaxRegularization.regularized_hasGradientAt hsoft μ s.anchor
  have he : gradient (LongTails.Proofs.RecursiveEnvelopeGeometry.regularized
      (fun z => smoothValue τ (fun i => f i z)) μ s.anchor) x =
      gradient (fun z => smoothValue τ (fun i => f i z)) x + μ • (x - s.anchor) := by
    rw [hreg.gradient, hsoft.gradient]
  dsimp only
  rw [he]
  exact hs

omit [Nonempty ι] [StandardBorelSpace ι] in
lemma exists_measurable_truthful_reply {C : Set E} (hC : MeasurableSet C)
    (f : ι → E → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ i x, x ∈ C → HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ i x y, x ∈ C → y ∈ C →
      ‖gradient (f i) x - gradient (f i) y‖ ≤ L * ‖x - y‖) :
    ∃ reply : ι × E → ℝ × E, Measurable reply ∧
      ∀ i x, x ∈ C → reply (i, x) = (f i x, gradient (f i) x) := by
  apply AffineSoftmaxMeasurability.exists_measurable_reply hC f (fun i => gradient (f i))
  · intro i x hx
    exact (hg i x hx).continuousAt.continuousWithinAt
  · intro i
    have hh : LipschitzOnWith ⟨L, hL⟩ (gradient (f i)) C := by
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      change dist (gradient (f i) x) (gradient (f i) y) ≤ L * dist x y
      simpa only [dist_eq_norm] using hlip i x y hx hy
    exact hh.continuousOn

end LongTails.Proofs.AffineSoftmaxOracle
