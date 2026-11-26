import LongTails.Proofs.MarkovNonconvexBurnInBatchesExecution
import LongTails.Proofs.MarkovNonconvexBurnInBatchesAlignment
import LongTails.Proofs.MarkovNormalizedDescent

open MeasureTheory ProbabilityTheory Function
open scoped RealInnerProductSpace
namespace LongTails.Proofs.MarkovNonconvexBurnInBatches

open Algorithms.MarkovNonconvexBurnInBatches MarkovNormalizedExecution MarkovNormalizedDescent
open Setups.HeavyTailedMarkovSmoothAndConvex MarkovBatchCovariance
variable {Z E : Type} [MeasurableSpace Z] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_retained (b n : ℕ) : Measurable (retained (Z := Z) b n) :=
  Measurable.of_eval fun _ => measurable_pi_apply _

omit [MeasurableSpace Z] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma iterate_adapted (g : E → Z → E) (η : ℝ) (b n : ℕ) (hn : 0 < n) (x0 : E) (j : ℕ) :
    AdaptedAt (j*(b+n)) (fun ξ => iterate g η b n x0 ξ j) := by
  induction j with
  | zero => intro ξ ζ _; rfl
  | succ j ih =>
    intro ξ ζ he
    rw [Nat.succ_mul] at he
    have hx := ih ξ ζ (fun i hi => he i (by omega))
    change iterate g η b n x0 ξ j = iterate g η b n x0 ζ j at hx
    simp only [iterate, Algorithms.MarkovNormalizedBatch.output, Nat.mul_one,
      retained_slot b n j hn] at ⊢
    unfold iterate at hx
    rw [hx]
    congr 3
    funext i
    rw [he _ (by have := i.isLt; omega)]

lemma trajectory_budget (κ : Kernel Z Z) [IsMarkovKernel κ] (π : ProbabilityMeasure Z)
    (hinv : κ ∘ₘ (π : Measure Z) = π) {τ σ ε L Δ η : ℝ} (hτ : 1 ≤ τ)
    (hε : 0 < ε) (hL : 0 ≤ L) (hη : 0 < η) (ηL : L*η = ε/2)
    (hd : ∀ t z, mixingDistance κ π t z ≤ 2*Real.exp (-(t:ℝ)/τ))
    {g : E → Z → E} {f : E → ℝ} (hg : Measurable (uncurry g))
    (hgrad : ∀ x, HasGradientAt f (gradient f x) x) (gm : Measurable (gradient f))
    (hl : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (hi : ∀ x, Integrable (g x) (π : Measure Z)) (hz : ∀ x, (∫ z, g x z ∂(π : Measure Z)) = gradient f x)
    (hq : ∀ x, Integrable (fun z => ‖g x z-gradient f x‖^2) (π : Measure Z))
    (hv : ∀ x, (∫ z, ‖g x z-gradient f x‖^2 ∂(π : Measure Z)) ≤ σ^2)
    (x0 : E) (hlow : ∀ x, f x0 - f x ≤ Δ) (K b r : ℕ)
    (hsize : 1024*τ*σ^2 ≤ ((r+1:ℕ):ℝ)*ε^2) (hburn : 2*Real.exp (-(b:ℝ)/τ) ≤ 1/8)
    (hgap : Δ ≤ K*η*(ε/4)) :
    let P : Measure (ℕ → Z) := pathLaw κ π
    (∑ j ∈ Finset.range K, ∫ ξ, ‖gradient f (iterate g η b (r+1) x0 ξ j)‖ ∂P) ≤ K*ε := by
  intro P
  let n := r+1
  let X := fun j (ξ : ℕ → Z) => iterate g η b n x0 ξ j
  let G := fun j ξ => ‖gradient f (X j ξ)‖
  let A := alignmentValue (gradient f) g η n 1 x0
  have mx j : Measurable (X j) := (measurable_output hg η n 1 x0 j).comp (measurable_retained b n)
  have hb j ξ : ‖gradient f (X j ξ)‖ ≤ ‖gradient f x0‖ + j*(L*η) :=
    norm_bound hL hη.le _ hl g n 1 x0 j (retained b n ξ)
  have point (j : ℕ) : 3/4*(∫ ξ, G j ξ ∂P)-ε/4 ≤ ∫ ξ, A j (retained b n ξ) ∂P := by
    have e := block_alignment κ π hinv hτ hε hd hg gm hi hz hq hv r b (j*(b+n)) hsize hburn
      (X j) (mx j) (iterate_adapted g η b n (Nat.succ_pos r) x0 j) (hb j)
    apply e.trans_eq
    apply integral_congr_ae
    filter_upwards with ξ
    have eq : (∑ i : Fin n, g (X j ξ) (retained b n ξ (j*n+i.val))) =
        ∑ i ∈ Finset.range n, g (X j ξ) (ξ (j*(b+n)+b+i)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => g (X j ξ) (ξ (j*(b+n)+b+i)))]
      apply Finset.sum_congr rfl
      intro i _
      rw [retained_slot b n j (Nat.succ_pos r) i, Nat.add_assoc]
    simp only [A, alignmentValue, Algorithms.MarkovNormalizedBatch.direction, Nat.mul_one]
    exact congrArg (fun v : E => ⟪gradient f (X j ξ), ‖v‖⁻¹ • v⟫) eq.symm
  let Q := P.map (retained b n)
  have mr := measurable_retained (Z := Z) b n
  let : IsProbabilityMeasure Q := (Measure.isProbabilityMeasure_map_iff mr.aemeasurable).2 inferInstance
  have des := integrated_descent Q hL hη.le hgrad hl gm (fstar := f x0 - Δ)
    (fun x => by linarith [hlow x]) hg n 1 x0 (by linarith) K
  have ma (j : ℕ) : Measurable (A j) := by
    let Y := fun ξ : ℕ → Z => Algorithms.MarkovNormalizedBatch.output g η n 1 x0 ξ j
    have my : Measurable Y := measurable_output hg η n 1 x0 j
    have ms (i : Fin n) : Measurable (fun ξ => g (Y ξ) (ξ (j*(n*1)+i.val*1))) :=
      hg.comp (my.prodMk (measurable_pi_apply _))
    change Measurable (fun ξ => ⟪gradient f (Y ξ), Algorithms.MarkovNormalizedBatch.direction
      (fun i : Fin n => g (Y ξ) (ξ (j*(n*1)+i.val*1)))⟫)
    unfold Algorithms.MarkovNormalizedBatch.direction
    fun_prop
  have mapA j : (∫ ξ, A j ξ ∂Q) = ∫ ξ, A j (retained b n ξ) ∂P :=
    integral_map mr.aemeasurable (ma j).aestronglyMeasurable
  change η*(∑ j ∈ Finset.range K, ∫ ξ, A j ξ ∂Q) ≤ _ at des
  simp_rw [mapA] at des
  have summed := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range K) => point j)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at summed
  change (∑ j ∈ Finset.range K, ∫ ξ, G j ξ ∂P) ≤ K*ε
  apply le_of_mul_le_mul_left (a := η) _ hη
  have cost : L/2*η^2 = η*(ε/4) := by nlinarith [congrArg (· * η) ηL]
  rw [cost] at des
  nlinarith [mul_le_mul_of_nonneg_left summed hη.le]

end LongTails.Proofs.MarkovNonconvexBurnInBatches
