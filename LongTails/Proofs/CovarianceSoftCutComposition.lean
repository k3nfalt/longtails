import LongTails.Proofs.CovarianceSoftCutGeneration
import LongTails.Proofs.CovarianceSoftCutMethodProcess

open MeasureTheory

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutComposition

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut
open LongTails.Proofs.CovarianceSoftCutSelectionProcess
open LongTails.Proofs.CovarianceSoftCutTournament

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma selection_with_candidates_probability (q : Params) (hd : 0 < q.d)
    (hL : 0 ≤ q.L) (hR : 0 < q.R)
    (p : Measure q.Ω) [IsProbabilityMeasure p]
    (f : Space q → ℝ) (hf : Measurable f) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (hlip : ∀ x y, |f x-f y| ≤ q.L*‖x-y‖)
    (τ : ℝ) (hτ : 0 < τ) (K n m h : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hbatch : 8*q.σ^2 ≤ (q.d : ℝ)*n*(τ/(12*q.R))^2)
    (hpower : 4*q.L*q.R ≤ τ*(2 : ℝ)^K)
    {U : Type*} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
    (leaves : U → ℕ → Space q) (hl : Measurable leaves)
    (hrad : ∀ u i, i < 2^h → ‖leaves u i‖ ≤ 2*q.R)
    (α fstar : ℝ) (δ : ENNReal)
    (hgen : μ {u | ∀ i, i < 2^h → α < f (leaves u i)-fstar} ≤ δ) :
    (μ.prod (Measure.infinitePi fun _ : ℕ => p))
      {z : U × (ℕ → q.Ω) | α+(h : ℝ)*τ <
        f (selectionOutput q (τ/(12*q.R)) K n m h (leaves z.1)
          (selectionReplies q (τ/(12*q.R)) K n m h (leaves z.1) g z.2))-fstar} ≤
      δ+ENNReal.ofReal (selectionBlocks K h * Real.exp (-(m : ℝ)/8)) := by
  let a := τ/(12*q.R)
  have ha : 0 < a := by dsimp [a]; positivity
  have hmap : Measurable (fun z : U × (ℕ → q.Ω) => (leaves z.1, z.2)) :=
    (hl.comp measurable_fst).prodMk measurable_snd
  have hout := (measurable_selectedOutput q a K n m h g hg.measurable).comp hmap
  have hbad := measurableSet_lt (measurable_const (a := α+(h : ℝ)*τ)) ((hf.comp hout).sub_const fstar)
  have hB : MeasurableSet {u | ∀ i, i < 2^h → α < f (leaves u i)-fstar} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro hi
    exact measurableSet_lt measurable_const
      ((hf.comp ((measurable_pi_apply i).comp hl)).sub_const fstar)
  apply LongTails.Proofs.StochasticEnvelopeFreshness.product_failure_probability
    μ (Measure.infinitePi fun _ : ℕ => p) hbad hB hgen
  intro u hu
  have hex : ∃ i, i < 2^h ∧ f (leaves u i)-fstar ≤ α := by
    obtain ⟨i, hi⟩ := not_forall.mp hu
    have hh := not_imp.mp hi
    exact ⟨i, hh.1, le_of_not_gt hh.2⟩
  obtain ⟨i, hi, hfi⟩ := hex
  have hsel := selection_failure_probability q hd p (Measure.infinitePi fun _ : ℕ => p)
    (OracleTemplate.StochasticGeneralized.infinitePi_iid p) f v g hg a ha K n m h hn hm hbatch (leaves u)
  apply le_trans (measure_mono ?_) hsel.2
  intro ξ hξ hgood
  have hacc := selectionOutput_accuracy q f v hg.support q.L q.R τ hL hR hτ hlip K n m h
    hpower (leaves u) (selectionReplies q a K n m h (leaves u) g ξ) (hrad u) hgood i hi
  change α+(h : ℝ)*τ < f (selectionOutput q a K n m h (leaves u)
    (selectionReplies q a K n m h (leaves u) g ξ))-fstar at hξ
  linarith

open LongTails.Algorithms.CovarianceSoftCutMethod
open LongTails.Proofs.CovarianceSoftCutMethodProcess
open LongTails.Proofs.CovarianceSoftCutProcess

def completePrefix (q : Params) (G : ℕ) (hG : 0 < G) (ζ : Fin G → q.Ω) (i : ℕ) : q.Ω :=
  if hi : i < G then ζ ⟨i, hi⟩ else ζ ⟨0, hG⟩

lemma measurable_completePrefix (q : Params) (G : ℕ) (hG : 0 < G) :
    Measurable (completePrefix q G hG) := by
  apply Measurable.of_eval
  intro i
  unfold completePrefix
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_pi_apply _

lemma generatorCost_pos (c : Config) (hb : 0 < c.b) : 0 < generatorCost c :=
  Nat.mul_pos (pow_pos (by decide) _) hb

lemma generatedLeaves_completePrefix (q : Params) (c : Config) (hb : 0 < c.b)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) :
    generatedLeaves q c g (completePrefix q (generatorCost c) (generatorCost_pos c hb)
      (fun i => ξ i.val)) = generatedLeaves q c g ξ := by
  apply generatedLeaves_prefix q c hb
  intro i hi
  simp [completePrefix, hi]

lemma generatedLeaves_radius (q : Params) (hR : 0 < q.R) (c : Config) (hb : 0 < c.b)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (i : ℕ) (hi : i < 2^c.H) :
    ‖generatedLeaves q c g ξ i‖ ≤ 2*q.R := by
  rw [generatedLeaves_eq q c hb, ite_eq_left hi]
  exact LongTails.Proofs.CovarianceSoftCutDensity.norm_centroid_le q hR _ _ _

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_generation_failure (q : Params) (f : Space q → ℝ) (hf : Measurable f)
    {U : Type*} [MeasurableSpace U] (l : U → ℕ → Space q) (hl : Measurable l)
    (T : ℕ) (α fstar : ℝ) : MeasurableSet {u | ∀ i, i < T → α < f (l u i)-fstar} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro hi
  exact measurableSet_lt measurable_const ((hf.comp ((measurable_pi_apply i).comp hl)).sub_const fstar)

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma prefix_generation_failure_probability (q : Params) (hd : 0 < q.d) (hL : 0 < q.L) (hR : 0 < q.R)
    (c : Config) (hb : 0 < c.b) (hα : 0 < c.α) (hαR : c.α ≤ q.L*q.R)
    (p : Measure q.Ω) [IsProbabilityMeasure p]
    (f : Space q → ℝ) (hf : Measurable f) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (hlip : ∀ x y, |f x-f y| ≤ q.L*‖x-y‖) (xstar : Space q) (hxstar : ‖xstar‖ ≤ q.R)
    (hbatch : 1024*q.σ^2*q.R^2 ≤ (q.d : ℝ)*c.b*c.α^2)
    (horizon : (q.d : ℝ)*Real.log (8*q.L*q.R/c.α) ≤ (2^c.H : ℕ)/24) :
    (Measure.pi fun _ : Fin (generatorCost c) => p)
      {ζ | ∀ i, i < 2^c.H → c.α < f (generatedLeaves q c g
        (completePrefix q (generatorCost c) (generatorCost_pos c hb) ζ) i)-f xstar} ≤
      (1/4 : ENNReal) := by
  have hl := (measurable_generatedLeaves q hR c hb g hg.measurable).comp
    (measurable_completePrefix q (generatorCost c) (generatorCost_pos c hb))
  have hB := measurable_generation_failure q f hf _ hl (2^c.H) c.α (f xstar)
  have hpre := (OracleTemplate.StochasticGeneralized.prefix_preserving p (generatorCost c)).measure_preimage
    hB.nullMeasurableSet
  have hgen := LongTails.Proofs.CovarianceSoftCutGeneration.generator_failure_probability
    q hd hL hR c.α hα hαR p f v hf g hg hlip xstar hxstar c.b hb hbatch
    (Measure.infinitePi fun _ : ℕ => p) (fun i ξ => ξ i)
    (OracleTemplate.StochasticGeneralized.infinitePi_iid p) (2^c.H) (pow_pos (by decide) _) horizon
  simp only [Function.comp_def] at hpre
  rw [← hpre]
  convert hgen using 1
  congr 1
  ext ξ
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, generatedLeaves_completePrefix q c hb]
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro hi
  rw [generatedLeaves_eq q c hb, ite_eq_left hi]

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma method_output_failure_probability (q : Params) (hd : 0 < q.d) (hL : 0 < q.L) (hR : 0 < q.R)
    (c : Config) (hb : 0 < c.b) (hn : 0 < c.n) (hm : 0 < c.m)
    (hα : 0 < c.α) (hαR : c.α ≤ q.L*q.R) (τ : ℝ) (hτ : 0 < τ) (ha : c.a = τ/(12*q.R))
    (p : Measure q.Ω) [IsProbabilityMeasure p]
    (P : Measure (ℕ → q.Ω)) [IsProbabilityMeasure P]
    (hs : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k ξ => ξ k) p P)
    (f : Space q → ℝ) (hf : Measurable f) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsCovarianceSubgradient q p f v g)
    (hlip : ∀ x y, |f x-f y| ≤ q.L*‖x-y‖) (xstar : Space q) (hxstar : ‖xstar‖ ≤ q.R)
    (hbatch : 1024*q.σ^2*q.R^2 ≤ (q.d : ℝ)*c.b*c.α^2)
    (horizon : (q.d : ℝ)*Real.log (8*q.L*q.R/c.α) ≤ (2^c.H : ℕ)/24)
    (hselbatch : 8*q.σ^2 ≤ (q.d : ℝ)*c.n*c.a^2)
    (hpower : 4*q.L*q.R ≤ τ*(2 : ℝ)^c.K) :
    P {ξ | c.α+(c.H : ℝ)*τ <
      f (selectionOutput q c.a c.K c.n c.m c.H (generatedLeaves q c g ξ) (selectedReplies q c g ξ))-f xstar} ≤
      (1/4 : ENNReal)+ENNReal.ofReal (selectionBlocks c.K c.H * Real.exp (-(c.m : ℝ)/8)) := by
  let l : (Fin (generatorCost c) → q.Ω) → ℕ → Space q := fun ζ =>
    generatedLeaves q c g (completePrefix q (generatorCost c) (generatorCost_pos c hb) ζ)
  have hl : Measurable l := (measurable_generatedLeaves q hR c hb g hg.measurable).comp
    (measurable_completePrefix q (generatorCost c) (generatorCost_pos c hb))
  have hgen := prefix_generation_failure_probability q hd hL hR c hb hα hαR p f hf v g hg
    hlip xstar hxstar hbatch horizon
  have hselbatch' : 8*q.σ^2 ≤ (q.d : ℝ)*c.n*(τ/(12*q.R))^2 := by simpa only [ha] using hselbatch
  have hcomp := selection_with_candidates_probability q hd hL.le hR p f hf v g hg hlip τ hτ
    c.K c.n c.m c.H hn hm hselbatch' hpower (Measure.pi fun _ : Fin (generatorCost c) => p)
    l hl (fun ζ i hi => generatedLeaves_radius q hR c hb g _ i hi) c.α (f xstar) (1/4) hgen
  rw [← ha] at hcomp
  have hmap : Measurable (fun z : (Fin (generatorCost c) → q.Ω) × (ℕ → q.Ω) => (l z.1, z.2)) :=
    (hl.comp measurable_fst).prodMk measurable_snd
  have hout := (measurable_selectedOutput q c.a c.K c.n c.m c.H g hg.measurable).comp hmap
  have hbad := measurableSet_lt (measurable_const (a := c.α+(c.H : ℝ)*τ))
    ((hf.comp hout).sub_const (f xstar))
  have hpre := (hs.prefix_tail_law (generatorCost c)).measure_preimage hbad.nullMeasurableSet
  have hbound := hpre.le.trans hcomp
  simpa only [Set.preimage_ofPred_eq, Function.comp_def, l, generatedLeaves_completePrefix q c hb,
    selectedReplies] using hbound

end LongTails.Proofs.CovarianceSoftCutComposition
