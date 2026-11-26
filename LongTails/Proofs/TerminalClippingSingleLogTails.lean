import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import LongTails.Proofs.TerminalClippingStopping

open MeasureTheory
open scoped RealInnerProductSpace
open OracleTemplate.ContinuizedSimilarQuasar

namespace OracleTemplate.TerminalClippingSingleLog

variable {S Ω Ξ : Type*} [MeasurableSpace S] [MeasurableSpace Ω] [MeasurableSpace Ξ]

def walk (adv : S → Ω → S) (s : S) (ξ : ℕ → Ω) : ℕ → S
  | 0 => s
  | i+1 => adv (walk adv s ξ i) (ξ i)

lemma prefix_tail {adv : S → Ω → S} (ha : Measurable (Function.uncurry adv))
    {inc : S → Ω → ℝ} (hi : Measurable (Function.uncurry inc))
    (ν : ProbabilityMeasure Ω) {c : ℝ} (hc : 0 ≤ c)
    (hm : ∀ s, Integrable (fun ω => Real.exp (inc s ω)) (ν : Measure Ω) ∧
      (∫ ω, Real.exp (inc s ω) ∂(ν : Measure Ω)) ≤ Real.exp c)
    {P : Measure Ξ} (ξ : ℕ → Ξ → Ω) (T : ℕ)
    (hlaw : MeasurePreserving (fun a (i : Fin T) => ξ i a) P
      (Measure.pi fun _ : Fin T => (ν : Measure Ω)))
    (s : S) (q : ℝ) :
    P {a | ∃ j ≤ T, q + T*c < ∑ i ∈ Finset.range j, inc
      (walk adv s (fun i => ξ i a) i) (ξ i a)} ≤ ENNReal.ofReal (Real.exp (-q)) := by
  classical
  let step := TerminalClipping.accumulatingTransition adv inc
  let B := q+T*c
  let good := fun p : S × ℝ => p.2 ≤ B
  have hg : MeasurableSet {p | good p} := measurableSet_le measurable_snd measurable_const
  let stop := TerminalClipping.stopUnless good step
  let A : Set (Fin T → Ω) := {v | B < (iterateSamples stop T (s,0) v).2}
  have hcond (v : S × ℝ) (_ : good v) :
      Integrable (fun ω => Real.exp ((step v ω).2)) (ν : Measure Ω) ∧
      (∫ ω, Real.exp ((step v ω).2) ∂(ν : Measure Ω)) ≤ Real.exp (v.2+c) := by
    simp only [step, TerminalClipping.accumulatingTransition, Real.exp_add]
    refine ⟨(hm v.1).1.const_mul _, ?_⟩
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hm v.1).2 (Real.exp_nonneg _)
  have ht := TerminalClipping.stopped_exponential_tail hg
    (TerminalClipping.accumulatingTransition_measurable ha hi) measurable_snd ν hc hcond T (s,0) B
  have ht' : (Measure.pi fun _ : Fin T => (ν : Measure Ω)) A ≤ ENNReal.ofReal (Real.exp (-q)) := by
    convert ht using 2
    congr 1
    dsimp [B]
    ring
  apply (measure_mono ?_).trans ((hlaw.measure_preimage_le A).trans ht')
  rintro a ⟨j,hj,hbad⟩
  change B < (iterateSamples stop T (s,0) (fun i => ξ i a)).2
  by_contra! hn
  have hgood := TerminalClipping.stopped_prefix_good good step T (s,0) (fun i => ξ i a) hn j hj
  have he := (TerminalClipping.stopped_compare good step j (s,0)
      (fun i : Fin j => ξ i a)).resolve_right (fun hh => hh hgood)
  have hg' : (iterateSamples step j (s,0) (fun i => ξ i a)).2 ≤ B := by
    rw [he]
    exact hgood
  have hs := TerminalClipping.accumulated_along adv inc (walk adv s (fun i => ξ i a))
    (fun i => ξ i a) (fun _ => rfl) j 0
  change iterateSamples step j (s,0) _ = _ at hs
  rw [hs] at hg'
  exact (not_lt_of_ge (by simpa using hg' : _ ≤ B)) hbad

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma two_tails {adv : S → Ω → S} (ha : Measurable (Function.uncurry adv))
    {g : S → Ω → E} (hg : Measurable (Function.uncurry g))
    {A : S → E} (hA : Measurable A)
    (ν : ProbabilityMeasure Ω) {M C b τ : ℝ} (hC : 0 < C)
    (hτ : 0 ≤ τ) (hsmall : 2*τ*C*b ≤ 1)
    (hmi : ∀ s, Integrable (fun ω => ‖g s ω‖^2) (ν : Measure Ω))
    (hm : ∀ s, (∫ ω, ‖g s ω‖^2 ∂(ν : Measure Ω)) ≤ M^2)
    (hdir : ∀ s, ‖A s‖ ≤ b)
    {P : Measure Ξ} (ξ : ℕ → Ξ → Ω) (T : ℕ)
    (hlaw : MeasurePreserving (fun a (i : Fin T) => ξ i a) P
      (Measure.pi fun _ : Fin T => (ν : Measure Ω)))
    (s : S) (q : ℝ) :
    let X := fun z ω => clip C (g z ω)
    let state := fun a => walk adv s (fun i => ξ i a)
    P {a | (∃ j ≤ T, q + T*(2*M^2/C^2) <
        ∑ i ∈ Finset.range j, ‖X (state a i) (ξ i a)‖^2/C^2) ∨
      (∃ j ≤ T, q + T*(τ^2*b^2*M^2) <
        ∑ i ∈ Finset.range j, -τ * ⟪X (state a i) (ξ i a) -
          ∫ ω, X (state a i) ω ∂(ν : Measure Ω), A (state a i)⟫)} ≤
      ENNReal.ofReal (Real.exp (-q)) + ENNReal.ofReal (Real.exp (-q)) := by
  let X := fun z ω => clip C (g z ω)
  have hX : Measurable (Function.uncurry X) := (measurable_clip C).comp hg
  have hmean : Measurable (fun s => ∫ ω, X s ω ∂(ν : Measure Ω)) :=
    hX.stronglyMeasurable.integral_prod_right.measurable
  have h2 s := TerminalClipping.full_moment_clip_second (hg.of_uncurry_left (x := s)) (hmi s) hC.le
  let square := fun s ω => ‖X s ω‖^2/C^2
  let mart := fun s ω => -τ * ⟪X s ω - ∫ v, X s v ∂(ν : Measure Ω), A s⟫
  have hs : Measurable (Function.uncurry square) := (hX.norm.pow_const 2).div_const _
  have hd : Measurable (Function.uncurry mart) :=
    by
    change Measurable (fun p : S × Ω => -τ * ⟪Function.uncurry X p - (∫ v, X p.1 v ∂(ν : Measure Ω)), A p.1⟫)
    exact measurable_const.mul ((hX.sub (hmean.comp measurable_fst)).inner (hA.comp measurable_fst))
  have hs' := prefix_tail ha hs ν (show 0 ≤ 2*M^2/C^2 by positivity) (fun z =>
    TerminalClipping.nonnegative_bounded_mgf ((hX.of_uncurry_left (x := z)).norm.pow_const 2)
      (h2 z).1 (sq_pos_of_pos hC) (fun _ => sq_nonneg _)
      (fun ω => pow_le_pow_left₀ (norm_nonneg _) (norm_clip_le hC.le (g z ω)) 2)
      ((h2 z).2.trans (hm z))) ξ T hlaw s q
  have hd' := prefix_tail ha hd ν (show 0 ≤ τ^2*b^2*M^2 by positivity) (fun z => by
    have hh := TerminalClipping.centered_inner_mgf (hX.of_uncurry_left (x := z))
      (integrable_clip (hg.of_uncurry_left (x := z)) hC.le) (h2 z).1 hτ (A z)
      (fun ω => norm_clip_le hC.le (g z ω)) ((h2 z).2.trans (hm z))
      ((mul_le_mul_of_nonneg_left (hdir z) (by positivity : 0 ≤ 2*τ*C)).trans hsmall)
    exact ⟨hh.1, hh.2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hdir z) 2) (sq_nonneg τ))
      (sq_nonneg M)))⟩) ξ T hlaw s q
  exact (measure_union_le _ _).trans (add_le_add hs' hd')

end OracleTemplate.TerminalClippingSingleLog
