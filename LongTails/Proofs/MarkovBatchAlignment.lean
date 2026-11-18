import LongTails.Proofs.MarkovBatchCovariance
import LongTails.Proofs.MarkovNormalizedExecution
import LongTails.Proofs.MarkovNormalizedAlignment

open MeasureTheory Function Preorder
open scoped BigOperators

namespace LongTails.Proofs.MarkovBatchHistory

open Algorithms.MarkovNormalizedBatch MarkovBatchCovariance MarkovNormalizedExecution

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma output_adapted (g : E → Ω → E) (η : ℝ) (B h : ℕ) (x0 : E) (j s : ℕ)
    (hs : (j*B-1)*h ≤ s) : AdaptedAt s (fun ξ => output g η B h x0 ξ j) := by
  induction j generalizing s with
  | zero => intro ξ ζ _; rfl
  | succ j ih =>
    intro ξ ζ he
    have hp : (j*B-1)*h ≤ s := (Nat.mul_le_mul_right h (by
      rw [Nat.succ_mul]
      omega)).trans hs
    simp only [output, ih s hp ξ ζ he]
    congr 3
    funext i
    rw [he]
    rw [← Nat.mul_assoc, ← Nat.add_mul]
    apply le_trans (Nat.mul_le_mul_right h _) hs
    rw [Nat.succ_mul]
    omega

noncomputable def partialSum (g : E → Ω → E) (η : ℝ) (B h : ℕ) (x0 : E)
    (j i : ℕ) (ξ : ℕ → Ω) : E :=
  ∑ k ∈ Finset.range i, g (output g η B h x0 ξ j) (ξ ((j*B+k)*h))

lemma measurable_partial [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (η : ℝ) (B h : ℕ) (x0 : E) (j i : ℕ) : Measurable (partialSum g η B h x0 j i) := by
  exact Finset.measurable_sum _ (fun k _ =>
    hg.comp ((measurable_output hg η B h x0 j).prodMk (measurable_pi_apply _)))

lemma partial_adapted (g : E → Ω → E) (η : ℝ) (B h : ℕ) (x0 : E) (j i : ℕ) :
    AdaptedAt ((j*B+i-1)*h) (partialSum g η B h x0 j i) := by
  intro ξ ζ he
  have hx := output_adapted g η B h x0 j _ (Nat.mul_le_mul_right h (by omega :
    j*B-1 ≤ j*B+i-1)) ξ ζ he
  dsimp only at hx
  apply Finset.sum_congr rfl
  intro k hk
  rw [hx, he _ (Nat.mul_le_mul_right h (by have := Finset.mem_range.mp hk; omega))]

lemma gradient_change (g : E → Ω → E) (η L : ℝ) (hη : 0 ≤ η) (hL : 0 ≤ L)
    (B h : ℕ) (x0 : E) (grad : E → E) (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x-y‖)
    (j : ℕ) (ξ : ℕ → Ω) :
    |‖grad (output g η B h x0 ξ (j+1))‖ - ‖grad (output g η B h x0 ξ j)‖| ≤ L*η :=
  (abs_norm_sub_norm_le _ _).trans ((hlip _ _).trans
    (mul_le_mul_of_nonneg_left (output_step_le g η hη B h x0 ξ j) hL))

end LongTails.Proofs.MarkovBatchHistory

open MeasureTheory ProbabilityTheory Function Preorder
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.MarkovBatchHybrid

open Algorithms.MarkovNormalizedBatch MarkovBatchContinuation MarkovBatchHistory
open MarkovBatchCovariance MarkovWeightedComparison MarkovNormalizedExecution
open OracleTemplate.HeavyTailedMarkovGradient Setups.HeavyTailedMarkovSmoothAndConvex

variable {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

noncomputable def test (π : ProbabilityMeasure Ω) (g : E → Ω → E) (grad : E → E)
    (η : ℝ) (B h : ℕ) (x0 : E) (j i : ℕ) (ξ : ℕ → Ω) : ℝ :=
  value (π : Measure Ω) g grad (B-i) (output g η B h x0 ξ j) (partialSum g η B h x0 j i ξ)

lemma test_step (κ : Kernel Ω Ω) [IsMarkovKernel κ] (π : ProbabilityMeasure Ω)
    (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω)) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) {grad : E → E} (hgrad : Measurable grad)
    (η : ℝ) (B h : ℕ) (hB : 0 < B) (x0 : E) (j i : ℕ) (hi : i < B)
    {u : Ω → ℝ} (hu : Measurable u) (hub : ∀ z, 0 ≤ u z ∧ u z ≤ 1)
    (hue : u =ᵐ[(π : Measure Ω)] mixingDistance κ π h)
    {M : ℝ} (hM : ∀ ξ, ‖grad (output g η B h x0 ξ j)‖ ≤ M) :
    let P : Measure (ℕ → Ω) := pathLaw κ π
    |(∫ ξ, test π g grad η B h x0 j (i+1) ξ ∂P) - ∫ ξ, test π g grad η B h x0 j i ξ ∂P| ≤
      2 * ∫ ξ, ‖grad (output g η B h x0 ξ j)‖ * u (ξ ((j*B+i-1)*h)) ∂P := by
  intro P
  let s := (j*B+i-1)*h
  let X := fun ξ => output g η B h x0 ξ j
  let V := partialSum g η B h x0 j i
  let F := fun (ξ : ℕ → Ω) (z : Ω) => value (π : Measure Ω) g grad (B-(i+1)) (X ξ) (V ξ + g (X ξ) z)
  have hx : Measurable X := measurable_output hg η B h x0 j
  have hv : Measurable V := measurable_partial hg η B h x0 j i
  have hf : Measurable (Function.uncurry F) := (measurable_value _ hg hgrad _).comp
    ((hx.comp measurable_fst).prodMk ((hv.comp measurable_fst).add
      (hg.comp ((hx.comp measurable_fst).prodMk measurable_snd))))
  have hbefore ξ : test π g grad η B h x0 j i ξ = ∫ z, F ξ z ∂(π : Measure Ω) := by
    unfold test
    rw [show B-i = B-(i+1)+1 by omega]
    exact value_succ _ hg grad _ _ _
  have hafter ξ : test π g grad η B h x0 j (i+1) ξ = F ξ (ξ ((j*B+i)*h)) := by
    unfold test F V partialSum
    rw [Finset.sum_range_succ]
  simp_rw [hbefore, hafter]
  by_cases hn : j*B+i = 0
  · have hj : j = 0 := by by_contra hh; have := Nat.mul_pos (Nat.pos_of_ne_zero hh) hB; omega
    have hi0 : i = 0 := by omega
    subst j i
    let f := fun z => value (π : Measure Ω) g grad (B-(0+1)) x0 (0 + g x0 z)
    have he ξ z : F ξ z = f z := by simp [F, X, V, partialSum, output, f]
    simp_rw [he]
    have hf' : Measurable f := (measurable_value _ hg hgrad _).comp
      (measurable_const.prodMk (measurable_const.add (hg.comp (measurable_const.prodMk measurable_id))))
    rw [← integral_map (measurable_pi_apply _).aemeasurable hf'.aestronglyMeasurable,
      pathLaw_stationary_marginal κ π hπ, integral_const, probReal_univ, one_smul, sub_self, abs_zero]
    exact mul_nonneg (by norm_num) (integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (hub _).1)
  · have ht : (j*B+i)*h = s+h := by
      rw [← Nat.succ_mul]; congr 1; omega
    let ex := extendHistory (Ω := Ω) s
    have hx' := output_adapted g η B h x0 j s (Nat.mul_le_mul_right h (by omega))
    have hv' := partial_adapted g η B h x0 j i
    have he ξ z : F (ex (frestrictLe s ξ)) z = F ξ z := by
      dsimp only [F, X, V, ex]
      rw [hx'.prefix, hv'.prefix]
    have hh := weighted_comparison κ π hπ s h u hu hub hue
      (fun a => ‖grad (X (ex a))‖) (fun a z => F (ex a) z)
      ((hgrad.comp (hx.comp (measurable_extendHistory s))).norm)
      (hf.comp (((measurable_extendHistory s).comp measurable_fst).prodMk measurable_snd))
      (fun a => hM (ex a)) (fun a z => value_bound _ _ _ _ _ _)
    dsimp only at hh
    simp_rw [he] at hh
    simpa only [ht, X, ex, hx'.prefix] using hh

end LongTails.Proofs.MarkovBatchHybrid

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.MarkovBatchAlignment

open Algorithms.MarkovNormalizedBatch MarkovBatchContinuation MarkovBatchHistory
open MarkovBatchCovariance MarkovWeightedComparison MarkovNormalizedExecution MarkovBatchHybrid
open MarkovNormalizedAlignment MarkovBatchMoments
open OracleTemplate.HeavyTailedMarkovGradient Setups.HeavyTailedMarkovSmoothAndConvex

variable {Ω E : Type} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

lemma batch_alignment (κ : Kernel Ω Ω) [IsMarkovKernel κ] (π : ProbabilityMeasure Ω)
    (hπ : κ ∘ₘ (π : Measure Ω) = (π : Measure Ω)) {g : E → Ω → E}
    (hg : Measurable (Function.uncurry g)) {grad : E → E} (hgrad : Measurable grad)
    {L η ε σ : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η) (hε : 0 < ε)
    (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x-y‖)
    (hI : ∀ x, Integrable (g x) (π : Measure Ω))
    (hunb : ∀ x, (∫ z, g x z ∂(π : Measure Ω)) = grad x)
    (h2 : ∀ x, Integrable (fun z => ‖g x z - grad x‖^2) (π : Measure Ω))
    (hvar : ∀ x, (∫ z, ‖g x z - grad x‖^2 ∂(π : Measure Ω)) ≤ σ^2)
    (B h : ℕ) (hB : 0 < B) (hsize : 256*σ^2 ≤ (B : ℝ)*ε^2)
    (hd : ∀ t, Integrable (mixingDistance κ π t) (π : Measure Ω))
    (hm : ∀ i : ℕ, (∫ z, mixingDistance κ π (i*h) z ∂(π : Measure Ω)) ≤ (1/2 : ℝ)^i)
    (hsmall : (∫ z, mixingDistance κ π h z ∂(π : Measure Ω)) ≤ 1/(16*B))
    (x0 : E) (j : ℕ) :
    let P : Measure (ℕ → Ω) := pathLaw κ π
    let X := fun ξ => output g η B h x0 ξ j
    (7/8)*(∫ ξ, ‖grad (X ξ)‖ ∂P) - ε/4 - 16*L*η ≤
      ∫ ξ, ⟪grad (X ξ), direction (fun i : Fin B => g (X ξ) (ξ (j*(B*h)+i.val*h)))⟫ ∂P := by
  intro P X
  let G := fun k (ξ : ℕ → Ω) => ‖grad (output g η B h x0 ξ k)‖
  have hG k : Measurable (G k) := (hgrad.comp (measurable_output hg η B h x0 k)).norm
  have hbound k ξ : G k ξ ≤ ‖grad x0‖ + k*(L*η) := by
    exact norm_bound hL hη grad hlip g B h x0 k ξ
  have hGI k : Integrable (G k) P := Integrable.of_bound (hG k).aestronglyMeasurable _
    (.of_forall fun ξ => by simpa [G] using hbound k ξ)
  obtain ⟨u, hu, hub, hue⟩ := mixing_representative κ π h (hd h)
  have hu' z : |u z| ≤ 1 := by rw [abs_of_nonneg (hub z).1]; exact (hub z).2
  have hmean : (∫ z, u z ∂(π : Measure Ω)) ≤ 1/(16*B) := (integral_congr_ae hue).le.trans hsmall
  let A := ∫ ξ, G j ξ ∂P
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  let J := fun i => ∫ ξ, test π g grad η B h x0 j i ξ ∂P
  have hadapt k : AdaptedAt (((k+1)*B-1)*h) (fun ξ => G (k+1) ξ - G k ξ) := by
    intro ξ ζ he
    have hh := output_adapted g η B h x0 (k+1) _ le_rfl ξ ζ he
    have hh' := output_adapted g η B h x0 k _ (Nat.mul_le_mul_right h (by rw [Nat.succ_mul]; omega)) ξ ζ he
    dsimp only at hh hh'
    simp only [G, hh, hh']
  have step (i : ℕ) (hi : i < B) : J i - J (i+1) ≤ 2*(A/(16*B)) + 8*(L*η)*(1/2 : ℝ)^i := by
    have hmom := weighted_moment κ π hπ B h hB hd hm hG (fun k =>
      ⟨_,fun ξ => by simpa only [G, abs_norm] using hbound k ξ⟩) (g0 := ‖grad x0‖)
      (fun _ => rfl) (mul_nonneg hL hη) (gradient_change g η L hη hL B h x0 grad hlip)
      hadapt hu hu' j i
    have hh := test_step κ π hπ hg hgrad η B h hB x0 j i hi hu hub hue (hbound j)
    have ha := (neg_le_abs _).trans hh
    have hb := mul_le_mul_of_nonneg_left hmean hA
    change -(J (i+1)-J i) ≤ _ at ha
    change _ ≤ A*_ + _ at hmom
    rw [div_eq_mul_inv]
    simp only [one_div] at hb
    linarith
  have telescope (k : ℕ) (hk : k ≤ B) :
      J 0 - J k ≤ k*(2*(A/(16*B))) + 16*(L*η)*(1-(1/2 : ℝ)^k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := step k (by omega)
      have hh' := ih (by omega)
      rw [pow_succ, Nat.cast_succ]
      linarith
  have htel := telescope B le_rfl
  have hcancel : (B : ℝ)*(2*(A/(16*B))) = A/8 := by field_simp [show (B : ℝ) ≠ 0 by exact_mod_cast hB.ne']; ring
  rw [hcancel] at htel
  have hiid ξ : G j ξ - ε/4 ≤ test π g grad η B h x0 j 0 ξ := by
    simpa [test, partialSum, value, direction, G, X] using
      iid_alignment (π : Measure Ω) (g (X ξ)) (grad (X ξ))
        (hg.comp (measurable_const.prodMk measurable_id)) (hI _) (hunb _) (h2 _) hε (hvar _) B hB hsize
  have htI : Integrable (test π g grad η B h x0 j 0) P := by
    refine Integrable.of_bound ((measurable_value _ hg hgrad _).comp
      ((measurable_output hg η B h x0 j).prodMk (measurable_partial hg η B h x0 j 0))).aestronglyMeasurable _
      (.of_forall fun ξ => (value_bound _ _ _ _ _ _).trans (hbound j ξ))
  have hj0 := integral_mono ((hGI j).sub (integrable_const _)) htI hiid
  change (∫ ξ, G j ξ - ε/4 ∂P) ≤ J 0 at hj0
  rw [integral_sub (hGI j) (integrable_const _), integral_const, probReal_univ, one_smul] at hj0
  change A - ε/4 ≤ J 0 at hj0
  have hend ξ : test π g grad η B h x0 j B ξ =
      ⟪grad (X ξ), direction (fun i : Fin B => g (X ξ) (ξ (j*(B*h)+i.val*h)))⟫ := by
    simp [test, partialSum, value, direction, X, Nat.add_mul, Nat.mul_assoc]
    rw [Fin.sum_univ_eq_sum_range (fun k => g (output g η B h x0 ξ j) (ξ (j*(B*h)+k*h)))]
  change 7/8*A - _ - _ ≤ _
  simp_rw [← hend]
  change _ ≤ J B
  nlinarith [mul_nonneg (mul_nonneg hL hη) (by positivity : 0 ≤ (1/2 : ℝ)^B)]

end LongTails.Proofs.MarkovBatchAlignment
