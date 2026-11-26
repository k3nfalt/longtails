import LongTails.Proofs.MarkovNonconvexBurnInBatchesContinuation
import LongTails.Proofs.MarkovNonconvexBurnInBatchesVariance

open MeasureTheory ProbabilityTheory Function Preorder
open scoped RealInnerProductSpace
namespace LongTails.Proofs.MarkovNonconvexBurnInBatches

open Setups.HeavyTailedMarkovSmoothAndConvex OracleTemplate.HeavyTailedMarkovGradient
open MarkovBatchCovariance
variable {Z E : Type} [MeasurableSpace Z] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
private lemma block_integral (κ : Kernel Z Z) [IsMarkovKernel κ] (π : ProbabilityMeasure Z)
    {g : E → Z → E} {grad : E → E} (hg : Measurable (uncurry g)) (hm : Measurable grad)
    (r s : ℕ) (X : (ℕ → Z) → E) (mx : Measurable X) (ax : AdaptedAt s X)
    {M : ℝ} (hb : ∀ ξ, ‖grad (X ξ)‖ ≤ M) :
    let P : Measure (ℕ → Z) := pathLaw κ π
    (∫ ξ, let v := ∑ i ∈ Finset.range (r+1), g (X ξ) (ξ (s+i))
      ⟪grad (X ξ), ‖v‖⁻¹ • v⟫ ∂P) =
      ∫ ξ, continuation κ g grad r (X ξ) (g (X ξ) (ξ s)) (ξ s) ∂P := by
  intro P
  apply Eq.trans _ (block_unroll κ π hg hm r s X (fun ξ => g (X ξ) (ξ s)) mx
    (hg.comp (mx.prodMk (measurable_pi_apply _))) ax (fun ξ ζ he => by
      dsimp only
      rw [ax ξ ζ he, he s le_rfl]) hb)
  apply integral_congr_ae
  filter_upwards with ξ
  dsimp only [continuation]
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero, add_comm, add_left_comm]

lemma block_alignment (κ : Kernel Z Z) [IsMarkovKernel κ] (π : ProbabilityMeasure Z)
    (hinv : κ ∘ₘ (π : Measure Z) = π) {τ σ ε : ℝ} (hτ : 1 ≤ τ) (hε : 0 < ε)
    (hd : ∀ t z, mixingDistance κ π t z ≤ 2*Real.exp (-(t:ℝ)/τ))
    {g : E → Z → E} {grad : E → E} (hg : Measurable (uncurry g)) (hm : Measurable grad)
    (hi : ∀ x, Integrable (g x) (π : Measure Z)) (hz : ∀ x, (∫ z, g x z ∂(π : Measure Z)) = grad x)
    (hq : ∀ x, Integrable (fun z => ‖g x z-grad x‖^2) (π : Measure Z))
    (hv : ∀ x, (∫ z, ‖g x z-grad x‖^2 ∂(π : Measure Z)) ≤ σ^2)
    (r b s : ℕ) (hsize : 1024*τ*σ^2 ≤ ((r+1:ℕ):ℝ)*ε^2)
    (hburn : 2*Real.exp (-(b:ℝ)/τ) ≤ 1/8)
    (X : (ℕ → Z) → E) (mx : Measurable X) (ax : AdaptedAt s X) {M : ℝ}
    (hb : ∀ ξ, ‖grad (X ξ)‖ ≤ M) :
    let P : Measure (ℕ → Z) := pathLaw κ π
    3/4*(∫ ξ, ‖grad (X ξ)‖ ∂P)-ε/4 ≤
      ∫ ξ, let v := ∑ i ∈ Finset.range (r+1), g (X ξ) (ξ (s+b+i))
        ⟪grad (X ξ), ‖v‖⁻¹ • v⟫ ∂P := by
  intro P
  let H := fun x z => continuation κ g grad r x (g x z) z
  have mh : Measurable (uncurry H) := (continuation_measurable κ hg hm r).comp
    (measurable_fst.prodMk (hg.prodMk measurable_snd))
  have bh x z : |H x z| ≤ ‖grad x‖ := continuation_bound κ g grad r x _ z
  have stat x : ‖grad x‖-ε/4 ≤ ∫ z, H x z ∂(π : Measure Z) := by
    have hh := stationary_alignment κ π hinv hτ hε hd hg.of_uncurry_left (hi x) (grad x)
      (hz x) (hq x) (hv x) 0 (r+1) (Nat.succ_pos _) hsize
    have eq := block_integral κ π hg hm r 0 (fun _ => x) measurable_const (fun _ _ _ => rfl)
      (fun _ => le_refl ‖grad x‖)
    have he := integral_map (μ := P) (measurable_pi_apply 0).aemeasurable
      (f := H x) mh.of_uncurry_left.aestronglyMeasurable
    rw [pathLaw_map_zero] at he
    exact hh.trans_eq (eq.trans he.symm)
  have ax' : AdaptedAt (s+b) X := fun ξ ζ he => ax ξ ζ (fun i hi => he i (by omega))
  rw [block_integral κ π hg hm r (s+b) X mx ax' hb]
  let W := fun ξ z => H (X ξ) z
  have mW : Measurable (uncurry W) := mh.comp ((mx.comp measurable_fst).prodMk measurable_snd)
  have move := future_test κ π s b W mW (fun z ξ ζ he => congrArg (fun x => H x z) (ax ξ ζ he))
    (fun ξ z => (bh _ _).trans (hb ξ))
  change _ ≤ ∫ ξ, W ξ (ξ (s+b)) ∂P
  rw [move]
  let K := (κ^b).comap (fun ξ : ℕ → Z => ξ s) (measurable_pi_apply _)
  have cW := mW.stronglyMeasurable.integral_kernel_prod_right (κ := K)
  have iw : Integrable (fun ξ => ∫ z, W ξ z ∂K ξ) P :=
    Integrable.of_bound cW.aestronglyMeasurable M (.of_forall fun ξ => by
      simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const (μ := K ξ) (f := W ξ) (.of_forall fun z => (bh _ _).trans (hb ξ)))
  have ig : Integrable (fun ξ => ‖grad (X ξ)‖) P := Integrable.of_bound
    (hm.comp mx).norm.aestronglyMeasurable M (.of_forall fun ξ => by simpa using hb ξ)
  have pt ξ : 3/4*‖grad (X ξ)‖-ε/4 ≤ ∫ z, W ξ z ∂K ξ := by
    have h := integral_sub_le_mixingDistance κ π b (ξ s) (norm_nonneg (grad (X ξ)))
      (mh.of_uncurry_left (x := X ξ)) (bh (X ξ))
    have scale := mul_le_mul_of_nonneg_left ((hd b (ξ s)).trans hburn)
      (show 0 ≤ 2*‖grad (X ξ)‖ by positivity)
    simp only [K, Kernel.comap_apply, W]
    linarith [stat (X ξ), (abs_le.mp h).1]
  have e := integral_mono ((ig.const_mul (3/4)).sub (integrable_const (ε/4))) iw pt
  change (∫ ξ, 3/4*‖grad (X ξ)‖-ε/4 ∂P) ≤ _ at e
  rw [integral_sub (ig.const_mul _) (integrable_const _), integral_const_mul, integral_const,
    probReal_univ, one_smul] at e
  exact e

end LongTails.Proofs.MarkovNonconvexBurnInBatches
