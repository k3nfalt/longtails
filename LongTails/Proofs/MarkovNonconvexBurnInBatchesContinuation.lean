import LongTails.Proofs.MarkovBatchCovariance
import LongTails.Proofs.MarkovNormalizedAlignment

open MeasureTheory ProbabilityTheory Function Preorder
open scoped RealInnerProductSpace
namespace LongTails.Proofs.MarkovNonconvexBurnInBatches

open Setups.HeavyTailedMarkovSmoothAndConvex OracleTemplate.HeavyTailedMarkovGradient
open MarkovBatchCovariance MarkovBatchContinuation
variable {Z E : Type} [MeasurableSpace Z] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma future_test (κ : Kernel Z Z) [IsMarkovKernel κ] (π : ProbabilityMeasure Z)
    (s t : ℕ) (W : (ℕ → Z) → Z → ℝ) (hm : Measurable (uncurry W))
    (ha : ∀ z, AdaptedAt s (fun ξ => W ξ z)) {M : ℝ} (hb : ∀ ξ z, |W ξ z| ≤ M) :
    let P : Measure (ℕ → Z) := pathLaw κ π
    (∫ ξ, W ξ (ξ (s+t)) ∂P) = ∫ ξ, ∫ z, W ξ z ∂(κ^t) (ξ s) ∂P := by
  intro P
  let H := fun a z => W (extendHistory s a) z
  have hH : Measurable (uncurry H) := hm.comp
    (((measurable_extendHistory s).comp measurable_fst).prodMk measurable_snd)
  have e := pathLaw_integral_future κ π s t hH (fun a z => hb (extendHistory s a) z)
  let K := (κ^t).comap (fun a : Finset.Iic s → Z => a ⟨s,Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)
  have m := hH.stronglyMeasurable.integral_kernel_prod_right (κ := K)
  have em := integral_map (μ := P) (φ := frestrictLe s) (by fun_prop) m.aestronglyMeasurable
  have eq := e.trans em
  change (∫ ξ, H (frestrictLe s ξ) (ξ (s+t)) ∂P) =
    ∫ ξ, ∫ z, H (frestrictLe s ξ) z ∂(κ^t) (ξ s) ∂P at eq
  simpa only [H, (ha _).prefix] using eq

noncomputable def continuation (κ : Kernel Z Z) (g : E → Z → E) (grad : E → E) :
    ℕ → E → E → Z → ℝ
  | 0, x, v, _ => ⟪grad x, ‖v‖⁻¹ • v⟫
  | r+1, x, v, z => ∫ y, continuation κ g grad r x (v+g x y) y ∂κ z

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma continuation_bound (κ : Kernel Z Z) [IsMarkovKernel κ] (g : E → Z → E)
    (grad : E → E) (r : ℕ) (x v : E) (z : Z) : |continuation κ g grad r x v z| ≤ ‖grad x‖ := by
  induction r generalizing v z with
  | zero => exact bound_normalized _ _
  | succ r ih =>
    simpa only [continuation, probReal_univ, mul_one, Real.norm_eq_abs] using norm_integral_le_of_norm_le_const (μ := κ z)
      (f := fun y => continuation κ g grad r x (v+g x y) y) (.of_forall fun y => ih _ y)

lemma continuation_measurable (κ : Kernel Z Z) [IsMarkovKernel κ] {g : E → Z → E} {grad : E → E}
    (hg : Measurable (uncurry g)) (hm : Measurable grad) (r : ℕ) :
    Measurable (fun p : E × E × Z => continuation κ g grad r p.1 p.2.1 p.2.2) := by
  induction r with
  | zero => dsimp [continuation]; fun_prop
  | succ r ih =>
    let K := κ.comap (fun p : E × E × Z => p.2.2) (by fun_prop)
    let W := fun (p : E × E × Z) y => continuation κ g grad r p.1 (p.2.1+g p.1 y) y
    have hw : Measurable (uncurry W) := ih.comp
      ((by fun_prop : Measurable (fun q : (E × E × Z) × Z => q.1.1)).prodMk
        (((by fun_prop : Measurable (fun q : (E × E × Z) × Z => q.1.2.1)).add
          (hg.comp ((by fun_prop : Measurable (fun q : (E × E × Z) × Z => q.1.1)).prodMk
            measurable_snd))).prodMk measurable_snd))
    exact (hw.stronglyMeasurable.integral_kernel_prod_right (κ := K)).measurable

lemma block_unroll (κ : Kernel Z Z) [IsMarkovKernel κ] (π : ProbabilityMeasure Z)
    {g : E → Z → E} {grad : E → E} (hg : Measurable (uncurry g)) (hm : Measurable grad)
    (r s : ℕ) (X V : (ℕ → Z) → E) (mx : Measurable X) (mv : Measurable V)
    (ax : AdaptedAt s X) (av : AdaptedAt s V) {M : ℝ} (hb : ∀ ξ, ‖grad (X ξ)‖ ≤ M) :
    let P : Measure (ℕ → Z) := pathLaw κ π
    (∫ ξ, continuation κ g grad 0 (X ξ) (V ξ + ∑ i ∈ Finset.range r,
      g (X ξ) (ξ (s+1+i))) (ξ (s+r)) ∂P) =
      ∫ ξ, continuation κ g grad r (X ξ) (V ξ) (ξ s) ∂P := by
  intro P
  induction r generalizing s V with
  | zero => simp
  | succ r ih =>
    let W := fun ξ y => continuation κ g grad r (X ξ) (V ξ+g (X ξ) y) y
    have hw : Measurable (uncurry W) := (continuation_measurable κ hg hm r).comp
      ((mx.comp measurable_fst).prodMk (((mv.comp measurable_fst).add
        (hg.comp ((mx.comp measurable_fst).prodMk measurable_snd))).prodMk measurable_snd))
    have hx (z) : AdaptedAt s (fun ξ => W ξ z) := by
      intro ξ ζ he
      dsimp [W]
      rw [ax ξ ζ he, av ξ ζ he]
    have one := future_test κ π s 1 W hw hx
      (fun ξ y => (continuation_bound κ g grad r _ _ y).trans (hb ξ))
    simp only [pow_one] at one
    let V' := fun ξ : ℕ → Z => V ξ + g (X ξ) (ξ (s+1))
    have ax' : AdaptedAt (s+1) X := fun ξ ζ he => ax ξ ζ (fun i hi => he i (by omega))
    have av' : AdaptedAt (s+1) V' := by
      intro ξ ζ he
      dsimp [V']
      rw [av ξ ζ (fun i hi => he i (by omega)), ax' ξ ζ he, he _ le_rfl]
    have unfoldNext := ih (s+1) V' (mv.add (hg.comp (mx.prodMk (measurable_pi_apply _)))) ax' av'
    refine Eq.trans ?_ (unfoldNext.trans one)
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ξ
    dsimp only
    rw [Finset.sum_range_succ']
    simp only [continuation, V', add_assoc, add_left_comm, add_comm]

end LongTails.Proofs.MarkovNonconvexBurnInBatches
