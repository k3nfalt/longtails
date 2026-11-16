import LongTails.Proofs.ProximalEf21Step
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw

section MomentCalculus

open MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21MomentCalculus

open LongTails.Proofs.ProximalEf21Geometry

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma integral_square_add_smul (P : @Measure Ω mΩ) (u ζ : Ω → E) (a : ℝ)
    (hu : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hζ : Integrable (fun ω => ‖ζ ω‖ ^ 2) P)
    (hc : Integrable (fun ω => ⟪u ω, ζ ω⟫_ℝ) P) :
    (∫ ω, ‖u ω + a • ζ ω‖ ^ 2 ∂P) =
      (∫ ω, ‖u ω‖ ^ 2 ∂P) + 2 * a * (∫ ω, ⟪u ω, ζ ω⟫_ℝ ∂P) +
        a ^ 2 * (∫ ω, ‖ζ ω‖ ^ 2 ∂P) := by
  have hid : (fun ω => ‖u ω + a • ζ ω‖ ^ 2) =
      (fun ω => ‖u ω‖ ^ 2 + (2 * a) * ⟪u ω, ζ ω⟫_ℝ + a ^ 2 * ‖ζ ω‖ ^ 2) := by
    funext ω
    exact square_add_smul (u ω) (ζ ω) a
  rw [hid]
  rw [integral_add
    (f := fun ω => ‖u ω‖ ^ 2 + (2 * a) * ⟪u ω, ζ ω⟫_ℝ)
    (g := fun ω => a ^ 2 * ‖ζ ω‖ ^ 2)
    (hu.add (hc.const_mul (2 * a))) (hζ.const_mul (a ^ 2))]
  rw [integral_add
    (f := fun ω => ‖u ω‖ ^ 2)
    (g := fun ω => (2 * a) * ⟪u ω, ζ ω⟫_ℝ)
    hu (hc.const_mul (2 * a))]
  rw [integral_const_mul, integral_const_mul]

lemma integral_square_add_smul_centered (P : @Measure Ω mΩ) (u ζ : Ω → E)
    (a variance : ℝ)
    (hu : Integrable (fun ω => ‖u ω‖ ^ 2) P)
    (hζ : Integrable (fun ω => ‖ζ ω‖ ^ 2) P)
    (hc : Integrable (fun ω => ⟪u ω, ζ ω⟫_ℝ) P)
    (hzero : (∫ ω, ⟪u ω, ζ ω⟫_ℝ ∂P) = 0)
    (hvariance : (∫ ω, ‖ζ ω‖ ^ 2 ∂P) ≤ variance) :
    (∫ ω, ‖u ω + a • ζ ω‖ ^ 2 ∂P) ≤
      (∫ ω, ‖u ω‖ ^ 2 ∂P) + a ^ 2 * variance := by
  rw [integral_square_add_smul P u ζ a hu hζ hc, hzero]
  have h := mul_le_mul_of_nonneg_left hvariance (sq_nonneg a)
  linarith

lemma integral_inner_sum {ι : Type*} [Fintype ι]
    (P : @Measure Ω mΩ) (u : ι → Ω → E) (v : Ω → E)
    (hi : ∀ i, Integrable (fun ω => ⟪u i ω, v ω⟫_ℝ) P) :
    (∫ ω, ⟪∑ i, u i ω, v ω⟫_ℝ ∂P) =
      ∑ i, ∫ ω, ⟪u i ω, v ω⟫_ℝ ∂P := by
  simp_rw [sum_inner]
  exact integral_finsetSum _ (fun i _ => hi i)

lemma integral_norm_sq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : @Measure Ω mΩ) (u : ι → Ω → E)
    (hint : ∀ i j, Integrable (fun ω => ⟪u i ω, u j ω⟫_ℝ) P)
    (hortho : ∀ i j, i ≠ j → (∫ ω, ⟪u i ω, u j ω⟫_ℝ ∂P) = 0) :
    (∫ ω, ‖∑ i, u i ω‖ ^ 2 ∂P) =
      ∑ i, ∫ ω, ‖u i ω‖ ^ 2 ∂P := by
  have hexpand : ∀ ω, ‖∑ i, u i ω‖ ^ 2 =
      ∑ i, ∑ j, ⟪u i ω, u j ω⟫_ℝ := by
    intro ω
    rw [← inner_self_eq, sum_inner]
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  calc
    (∑ j, ∫ ω, ⟪u i ω, u j ω⟫_ℝ ∂P) = ∫ ω, ⟪u i ω, u i ω⟫_ℝ ∂P := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        exact hortho i j (Ne.symm hji)
      · intro hnot
        exact (hnot (Finset.mem_univ i)).elim
    _ = ∫ ω, ‖u i ω‖ ^ 2 ∂P := by simp_rw [inner_self_eq]

lemma miniBatch_second_moment {B : ℕ} (hB : 0 < B)
    (P : @Measure Ω mΩ) (ζ : Fin B → Ω → E) (variance : ℝ)
    (hint : ∀ i j, Integrable (fun ω => ⟪ζ i ω, ζ j ω⟫_ℝ) P)
    (hortho : ∀ i j, i ≠ j → (∫ ω, ⟪ζ i ω, ζ j ω⟫_ℝ ∂P) = 0)
    (hvariance : ∀ i, (∫ ω, ‖ζ i ω‖ ^ 2 ∂P) ≤ variance) :
    (∫ ω, ‖(B : ℝ)⁻¹ • ∑ i, ζ i ω‖ ^ 2 ∂P) ≤ variance / B := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  simp_rw [square_smul]
  rw [integral_const_mul, integral_norm_sq_sum P ζ hint hortho]
  have hs : (∑ i, ∫ ω, ‖ζ i ω‖ ^ 2 ∂P) ≤ (B : ℝ) * variance := by
    calc
      (∑ i, ∫ ω, ‖ζ i ω‖ ^ 2 ∂P) ≤ ∑ _ : Fin B, variance :=
        Finset.sum_le_sum (fun i _ => hvariance i)
      _ = (B : ℝ) * variance := by simp
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg ((B : ℝ)⁻¹))
  have hid : (B : ℝ)⁻¹ ^ 2 * ((B : ℝ) * variance) = variance / B := by
    field_simp [ne_of_gt hBR]
  simpa only [hid] using hm

lemma scalar_conditional_zero_integral
    (m : MeasurableSpace Ω) (P : @Measure Ω mΩ)
    (hm : m ≤ mΩ)
    [IsProbabilityMeasure P] (u : Ω → ℝ)
    (hu : Integrable u P)
    (hzero : condExp m P u =ᵐ[P] (fun _ => 0)) :
    (∫ ω, u ω ∂P) = 0 := by
  calc
    (∫ ω, u ω ∂P) = ∫ ω, condExp m P u ω ∂P :=
      (integral_condExp (μ := P) (f := u) hm).symm
    _ = ∫ _ : Ω, (0 : ℝ) ∂P := integral_congr_ae hzero
    _ = 0 := by simp

lemma integrate_pointwise_progress (P : @Measure Ω mΩ)
    (next current decrease noise : Ω → ℝ)
    (hn : Integrable next P) (hc : Integrable current P)
    (hd : Integrable decrease P) (he : Integrable noise P)
    (hstep : ∀ᵐ ω ∂P, next ω ≤ current ω - decrease ω + noise ω) :
    (∫ ω, next ω ∂P) ≤
      (∫ ω, current ω ∂P) - (∫ ω, decrease ω ∂P) + (∫ ω, noise ω ∂P) := by
  have h := integral_mono_ae hn ((hc.sub hd).add he) hstep
  change (∫ ω, next ω ∂P) ≤
    ∫ ω, current ω - decrease ω + noise ω ∂P at h
  rw [integral_add (f := fun ω => current ω - decrease ω) (g := noise)
    (hc.sub hd) he, integral_sub (f := current) (g := decrease) hc hd] at h
  exact h

section SquareIntegrableNoise

variable [CompleteSpace E]

lemma integrable_inner_of_memLp_two (P : @Measure Ω mΩ) (u v : Ω → E)
    (hu : MemLp u 2 P) (hv : MemLp v 2 P) :
    Integrable (fun ω => ⟪u ω, v ω⟫_ℝ) P := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hu.toLp u) (hv.toLp v)
  apply h.congr
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with ω hωu hωv
  simp only [hωu, hωv]

lemma predictable_inner_centered_noise (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (u ζ : Ω → E)
    (hu : MemLp u 2 P) (hζ : MemLp ζ 2 P)
    (hpredictable : AEStronglyMeasurable[m] u P)
    (hcentered : condExp m P ζ =ᵐ[P] (fun _ => 0)) :
    (∫ ω, ⟪u ω, ζ ω⟫_ℝ ∂P) = 0 := by
  have hprojection :
      ((condExpL2 E ℝ (μ := P) hm) (hζ.toLp ζ)).1 = (0 : Lp E 2 P) := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    exact (MeasureTheory.MemLp.condExpL2_ae_eq_condExp
      (𝕜 := ℝ) (μ := P) hm hζ).trans hcentered
  have hpred : AEStronglyMeasurable[m] (hu.toLp u : Ω → E) P :=
    hpredictable.congr hu.coeFn_toLp.symm
  have hinner := MeasureTheory.inner_condExpL2_eq_inner_fun
    (𝕜 := ℝ) (μ := P) hm (hζ.toLp ζ) (hu.toLp u) hpred
  rw [hprojection, inner_zero_left, MeasureTheory.L2.inner_def] at hinner
  calc
    (∫ ω, ⟪u ω, ζ ω⟫_ℝ ∂P) =
        ∫ ω, ⟪(hζ.toLp ζ : Ω → E) ω, (hu.toLp u : Ω → E) ω⟫_ℝ ∂P := by
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp, hζ.coeFn_toLp] with ω hωu hωζ
      rw [hωu, hωζ, real_inner_comm]
    _ = 0 := hinner.symm

lemma conditional_variance_to_integral (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (ζ : Ω → E) (variance : ℝ)
    (hvariance : ∀ᵐ ω ∂P,
      condExp m P (fun ω' => ‖ζ ω'‖ ^ 2) ω ≤ variance) :
    (∫ ω, ‖ζ ω‖ ^ 2 ∂P) ≤ variance := by
  calc
    (∫ ω, ‖ζ ω‖ ^ 2 ∂P) =
        ∫ ω, condExp m P (fun ω' => ‖ζ ω'‖ ^ 2) ω ∂P :=
      (integral_condExp (μ := P) (f := fun ω => ‖ζ ω‖ ^ 2) hm).symm
    _ ≤ ∫ _ : Ω, variance ∂P :=
      integral_mono_ae integrable_condExp (integrable_const variance) hvariance
    _ = variance := by simp

lemma square_integral_add_fresh_noise (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (u ζ : Ω → E) (a variance : ℝ)
    (hu : MemLp u 2 P) (hζ : MemLp ζ 2 P)
    (hpredictable : AEStronglyMeasurable[m] u P)
    (hcentered : condExp m P ζ =ᵐ[P] (fun _ => 0))
    (hvariance : ∀ᵐ ω ∂P,
      condExp m P (fun ω' => ‖ζ ω'‖ ^ 2) ω ≤ variance) :
    (∫ ω, ‖u ω + a • ζ ω‖ ^ 2 ∂P) ≤
      (∫ ω, ‖u ω‖ ^ 2 ∂P) + a ^ 2 * variance := by
  apply integral_square_add_smul_centered (mΩ := mΩ) P u ζ a variance
  · exact (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  · exact (memLp_two_iff_integrable_sq_norm hζ.aestronglyMeasurable).mp hζ
  · exact integrable_inner_of_memLp_two (mΩ := mΩ) P u ζ hu hζ
  · exact predictable_inner_centered_noise (mΩ := mΩ) P m hm u ζ hu hζ hpredictable hcentered
  · exact conditional_variance_to_integral (mΩ := mΩ) P m hm ζ variance hvariance

end SquareIntegrableNoise

end LongTails.Proofs.ProximalEf21MomentCalculus


end MomentCalculus


section AverageMoments

open MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21AverageMoments

open LongTails.Proofs.ProximalEf21Averages
open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21MomentCalculus
open LongTails.Proofs.ProximalEf21WeightedErrors

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] [mΩ : MeasurableSpace Ω]

lemma weightedSquare_integrable {n : ℕ} (P : @Measure Ω mΩ)
    (w : Fin n → ℝ) (u : Fin n → Ω → E)
    (hu : ∀ i, Integrable (fun ω => ‖u i ω‖ ^ 2) P) :
    Integrable (fun ω => weightedSquare w (fun i => u i ω)) P := by
  exact (integrable_finsetSum _ (fun i _ => (hu i).const_mul (w i))).const_mul _

lemma integral_weightedSquare {n : ℕ} (P : @Measure Ω mΩ)
    (w : Fin n → ℝ) (u : Fin n → Ω → E)
    (hu : ∀ i, Integrable (fun ω => ‖u i ω‖ ^ 2) P) :
    (∫ ω, weightedSquare w (fun i => u i ω) ∂P) =
      (n : ℝ)⁻¹ * ∑ i, w i * (∫ ω, ‖u i ω‖ ^ 2 ∂P) := by
  unfold weightedSquare
  rw [integral_const_mul,
    integral_finsetSum _ (fun i _ => (hu i).const_mul (w i))]
  simp only [integral_const_mul]

lemma workerMean_memLp {n : ℕ} (P : @Measure Ω mΩ) (u : Fin n → Ω → E)
    (hu : ∀ i, MemLp (u i) 2 P) :
    MemLp (fun ω => workerMean (fun i => u i ω)) 2 P := by
  exact (memLp_finsetSum _ (fun i _ => hu i)).const_smul _

lemma workerMean_predictable {n : ℕ} (P : @Measure Ω mΩ)
    (m : MeasurableSpace Ω) (u : Fin n → Ω → E)
    (hu : ∀ i, AEStronglyMeasurable[m] (u i) P) :
    AEStronglyMeasurable[m] (fun ω => workerMean (fun i => u i ω)) P := by
  classical
  have hsum (s : Finset (Fin n)) :
      AEStronglyMeasurable[m] (fun ω => ∑ i ∈ s, u i ω) P := by
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (aestronglyMeasurable_const : AEStronglyMeasurable[m] (fun _ : Ω => (0 : E)) P)
    | @insert i s hi ih =>
        simpa only [Finset.sum_insert hi] using (hu i).fun_add ih
  exact (hsum Finset.univ).const_smul ((n : ℝ)⁻¹)

lemma mean_noise_orthogonal {n : ℕ} (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (ζ : Fin n → Ω → E) (hζ : ∀ i, MemLp (ζ i) 2 P)
    (hcentered : ∀ i, condExp m P (ζ i) =ᵐ[P] (fun _ => 0))
    (u : Ω → E) (hu : MemLp u 2 P)
    (hpred : AEStronglyMeasurable[m] u P) :
    (∫ ω, ⟪u ω, workerMean (fun i => ζ i ω)⟫_ℝ ∂P) = 0 := by
  have hint : ∀ i, Integrable (fun ω => ⟪u ω, ζ i ω⟫_ℝ) P :=
    fun i => integrable_inner_of_memLp_two (mΩ := mΩ) P u (ζ i) hu (hζ i)
  have hz : ∀ i, (∫ ω, ⟪u ω, ζ i ω⟫_ℝ ∂P) = 0 :=
    fun i => predictable_inner_centered_noise (mΩ := mΩ) P m hm u (ζ i)
      hu (hζ i) hpred (hcentered i)
  simp only [workerMean, real_inner_smul_right, inner_sum]
  rw [integral_const_mul,
    integral_finsetSum _ (fun i _ => hint i)]
  simp only [hz, Finset.sum_const_zero, mul_zero]

lemma mean_noise_second_moment {n : ℕ} (hn : 0 < n)
    (P : @Measure Ω mΩ) (ζ : Fin n → Ω → E) (variance : ℝ)
    (hζ : ∀ i, MemLp (ζ i) 2 P)
    (hvar : ∀ i, (∫ ω, ‖ζ i ω‖ ^ 2 ∂P) ≤ variance) :
    (∫ ω, ‖workerMean (fun i => ζ i ω)‖ ^ 2 ∂P) ≤ variance := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hsqi : ∀ i, Integrable (fun ω => ‖ζ i ω‖ ^ 2) P := fun i =>
    (memLp_two_iff_integrable_sq_norm (hζ i).aestronglyMeasurable).mp (hζ i)
  have hmean := workerMean_memLp P ζ hζ
  have hmeansq := (memLp_two_iff_integrable_sq_norm hmean.aestronglyMeasurable).mp hmean
  have hpoint : ∀ ω, ‖workerMean (fun i => ζ i ω)‖ ^ 2 ≤
      (n : ℝ)⁻¹ * ∑ i, ‖ζ i ω‖ ^ 2 := by
    intro ω
    have h := weighted_cauchy_schwarz_mean hn (fun _ => 1)
      (fun _ => by norm_num) (fun i => ζ i ω)
    simpa [workerMean, hnR] using h
  have hsumint : Integrable
      (fun ω => (n : ℝ)⁻¹ * ∑ i : Fin n, ‖ζ i ω‖ ^ 2) P :=
    (integrable_finsetSum (Finset.univ : Finset (Fin n))
      (fun i _ => hsqi i)).const_mul ((n : ℝ)⁻¹)
  calc
    (∫ ω, ‖workerMean (fun i => ζ i ω)‖ ^ 2 ∂P) ≤
        ∫ ω, (n : ℝ)⁻¹ * ∑ i, ‖ζ i ω‖ ^ 2 ∂P :=
      integral_mono hmeansq hsumint hpoint
    _ = (n : ℝ)⁻¹ * ∑ i, ∫ ω, ‖ζ i ω‖ ^ 2 ∂P := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ => hsqi i)]
    _ ≤ (n : ℝ)⁻¹ * ∑ _ : Fin n, variance := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
      exact Finset.sum_le_sum (fun i _ => hvar i)
    _ = variance := by simp [hnR]

end LongTails.Proofs.ProximalEf21AverageMoments

end

end AverageMoments


section RawBatch

open MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21RawBatch

open LongTails.Proofs.ProximalEf21AverageMoments

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21MomentCalculus

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma ordered_noise_orthogonality {B : ℕ}
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (filtration : Fin B → MeasurableSpace Ω)
    (hfiltration : ∀ j, filtration j ≤ mΩ)
    (ζ : Fin B → Ω → E)
    (hlp : ∀ j, MemLp (ζ j) 2 P)
    (hpast : ∀ i j, i < j → AEStronglyMeasurable[filtration j] (ζ i) P)
    (hcentered : ∀ j, condExp (filtration j) P (ζ j) =ᵐ[P] (fun _ => 0)) :
    ∀ i j, i ≠ j → (∫ ω, ⟪ζ i ω, ζ j ω⟫_ℝ ∂P) = 0 := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact predictable_inner_centered_noise (mΩ := mΩ) P (filtration j) (hfiltration j)
      (ζ i) (ζ j) (hlp i) (hlp j) (hpast i j hlt) (hcentered j)
  · have h := predictable_inner_centered_noise (mΩ := mΩ) P (filtration i) (hfiltration i)
      (ζ j) (ζ i) (hlp j) (hlp i) (hpast j i hgt) (hcentered i)
    calc
      (∫ ω, ⟪ζ i ω, ζ j ω⟫_ℝ ∂P) = (∫ ω, ⟪ζ j ω, ζ i ω⟫_ℝ ∂P) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun _ => real_inner_comm _ _)
      _ = 0 := h

lemma miniBatch_from_raw_samples {B : ℕ} (hB : 0 < B)
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (filtration : Fin B → MeasurableSpace Ω)
    (hfiltration : ∀ j, filtration j ≤ mΩ)
    (ζ : Fin B → Ω → E) (σ : ℝ)
    (hlp : ∀ j, MemLp (ζ j) 2 P)
    (hpast : ∀ i j, i < j → AEStronglyMeasurable[filtration j] (ζ i) P)
    (hcentered : ∀ j, condExp (filtration j) P (ζ j) =ᵐ[P] (fun _ => 0))
    (hvariance : ∀ j, ∀ᵐ ω ∂P,
      condExp (filtration j) P (fun ω' => ‖ζ j ω'‖ ^ 2) ω ≤ σ ^ 2) :
    MemLp (fun ω => (B : ℝ)⁻¹ • ∑ j, ζ j ω) 2 P ∧
    (∫ ω, ‖(B : ℝ)⁻¹ • ∑ j, ζ j ω‖ ^ 2 ∂P) ≤ σ ^ 2 / B := by
  refine ⟨workerMean_memLp P ζ hlp, ?_⟩
  apply miniBatch_second_moment hB P ζ (σ ^ 2)
  · intro i j
    exact integrable_inner_of_memLp_two (mΩ := mΩ) P _ _ (hlp i) (hlp j)
  · exact ordered_noise_orthogonality P filtration hfiltration ζ hlp hpast hcentered
  · intro j
    exact conditional_variance_to_integral (mΩ := mΩ) P (filtration j) (hfiltration j)
      (ζ j) (σ ^ 2) (hvariance j)

lemma miniBatch_orthogonal_to_initial_state {B : ℕ}
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (filtration : Fin B → MeasurableSpace Ω)
    (hfiltration : ∀ j, filtration j ≤ mΩ)
    (ζ : Fin B → Ω → E) (u : Ω → E)
    (hlp : ∀ j, MemLp (ζ j) 2 P) (hu : MemLp u 2 P)
    (hpredictable : ∀ j, AEStronglyMeasurable[filtration j] u P)
    (hcentered : ∀ j, condExp (filtration j) P (ζ j) =ᵐ[P] (fun _ => 0)) :
    (∫ ω, ⟪u ω, (B : ℝ)⁻¹ • ∑ j, ζ j ω⟫_ℝ ∂P) = 0 := by
  have hz : ∀ j, (∫ ω, ⟪u ω, ζ j ω⟫_ℝ ∂P) = 0 := by
    intro j
    exact predictable_inner_centered_noise (mΩ := mΩ) P (filtration j) (hfiltration j)
      u (ζ j) hu (hlp j) (hpredictable j) (hcentered j)
  simp_rw [real_inner_smul_right, inner_sum]
  rw [integral_const_mul, integral_finsetSum]
  · simp only [hz, Finset.sum_const_zero, mul_zero]
  · intro j hj
    exact integrable_inner_of_memLp_two (mΩ := mΩ) P _ _ hu (hlp j)

lemma raw_sample_number (B K : ℕ) :
    (∑ _ ∈ Finset.range K, B) = B * K := by
  simp [Nat.mul_comm]

end LongTails.Proofs.ProximalEf21RawBatch

end

end RawBatch


section ConditionalBatch

open MeasureTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21ConditionalBatch

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21MomentCalculus

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma conditional_finset_sum {ι : Type*}
    (P : @Measure Ω mΩ) (m : MeasurableSpace Ω)
    (s : Finset ι) (f : ι → Ω → E)
    (hf : ∀ i ∈ s, Integrable (f i) P) :
    condExp m P (fun ω => ∑ i ∈ s, f i ω) =ᵐ[P]
      (fun ω => ∑ i ∈ s, condExp m P (f i) ω) := by
  have hfun : (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, f i := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hfun]
  filter_upwards [condExp_finsetSum (μ := P) (s := s) (f := f) hf m] with ω hω
  simpa only [Finset.sum_apply] using hω

lemma conditional_const_smul (P : @Measure Ω mΩ) (m : MeasurableSpace Ω)
    (c : ℝ) (f : Ω → E) :
    condExp m P (fun ω => c • f ω) =ᵐ[P]
      (fun ω => c • condExp m P f ω) := by
  have hfun : (fun ω => c • f ω) = c • f := rfl
  rw [hfun]
  filter_upwards [condExp_smul (μ := P) c f m] with ω hω
  simpa only [Pi.smul_apply] using hω

lemma conditional_inner_centered
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (u z : Ω → E) (hu : MemLp u 2 P) (hz : MemLp z 2 P)
    (hpred : AEStronglyMeasurable[m] u P)
    (hzero : condExp m P z =ᵐ[P] (fun _ => 0)) :
    condExp m P (fun ω => ⟪u ω, z ω⟫_ℝ) =ᵐ[P] (fun _ => 0) := by
  have hi := integrable_inner_of_memLp_two (mΩ := mΩ) P u z hu hz
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq
    (m := m) (m₀ := mΩ) (μ := P)
    (f := fun ω => ⟪u ω, z ω⟫_ℝ)
    (g := fun _ : Ω => (0 : ℝ)) hm hi
  · intro s hs hfin
    exact integrable_zero Ω ℝ (P.restrict s)
  · intro s hs hfin
    have hsm : MeasurableSet[mΩ] s := hm s hs
    have hpred' : AEStronglyMeasurable[m] (s.indicator u) P := by
      rcases hpred with ⟨u', hu', hueq⟩
      refine ⟨s.indicator u', hu'.indicator hs, ?_⟩
      filter_upwards [hueq] with ω hω
      by_cases hsω : ω ∈ s <;> simp [hsω, hω]
    have hu' : MemLp (s.indicator u) 2 P := hu.indicator hsm
    have h := predictable_inner_centered_noise (mΩ := mΩ) P m hm
      (s.indicator u) z hu' hz hpred' hzero
    have hid : (fun ω => ⟪s.indicator u ω, z ω⟫_ℝ) =
        s.indicator (fun ω => ⟪u ω, z ω⟫_ℝ) := by
      funext ω
      by_cases hω : ω ∈ s <;> simp [hω]
    rw [hid, integral_indicator hsm] at h
    simpa using h.symm
  · exact aestronglyMeasurable_const

lemma conditional_mean_to_smaller
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (m₀ m₁ : MeasurableSpace Ω)
    (h01 : m₀ ≤ m₁) (h1 : m₁ ≤ mΩ)
    (z : Ω → E) (hz : Integrable z P)
    (hzero : condExp m₁ P z =ᵐ[P] (fun _ => 0)) :
    condExp m₀ P z =ᵐ[P] (fun _ => 0) := by
  calc
    condExp m₀ P z =ᵐ[P] condExp m₀ P (condExp m₁ P z) :=
      (condExp_condExp_of_le (μ := P) (f := z) h01 h1).symm
    _ =ᵐ[P] condExp m₀ P (fun _ : Ω => (0 : E)) :=
      condExp_congr_ae (μ := P) (m := m₀) hzero
    _ =ᵐ[P] (fun _ => 0) := by simp

lemma conditional_bound_to_smaller
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (m₀ m₁ : MeasurableSpace Ω)
    (h01 : m₀ ≤ m₁) (h1 : m₁ ≤ mΩ)
    (f : Ω → ℝ) (c : ℝ) (hf : Integrable f P)
    (hc : ∀ᵐ ω ∂P, condExp m₁ P f ω ≤ c) :
    ∀ᵐ ω ∂P, condExp m₀ P f ω ≤ c := by
  have htower := condExp_condExp_of_le (μ := P) (f := f) h01 h1
  have hmono := condExp_mono (m := m₀) (m₀ := mΩ) (μ := P)
    (f := condExp m₁ P f) (g := fun _ : Ω => c)
    (integrable_condExp (m := m₁) (μ := P) (f := f))
    (integrable_const c) hc
  have hconst : condExp m₀ P (fun _ : Ω => c) =ᵐ[P] (fun _ => c) :=
    condExp_of_aestronglyMeasurable' (h01.trans h1)
      aestronglyMeasurable_const (integrable_const c)
  filter_upwards [htower, hmono, hconst] with ω ht hm hc
  rw [ht, hc] at hm
  exact hm

lemma conditional_batch_mean {B : ℕ}
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (m₀ : MeasurableSpace Ω) (filtration : Fin B → MeasurableSpace Ω)
    (hsmall : ∀ j, m₀ ≤ filtration j)
    (hfiltration : ∀ j, filtration j ≤ mΩ)
    (z : Fin B → Ω → E) (hz : ∀ j, MemLp (z j) 2 P)
    (hzero : ∀ j, condExp (filtration j) P (z j) =ᵐ[P] (fun _ => 0)) :
    condExp m₀ P (fun ω => (B : ℝ)⁻¹ • ∑ j, z j ω) =ᵐ[P] (fun _ => 0) := by
  have hi (j : Fin B) : Integrable (z j) P :=
    (hz j).integrable (by norm_num)
  have hsmallzero (j : Fin B) :
      condExp m₀ P (z j) =ᵐ[P] (fun _ => 0) :=
    conditional_mean_to_smaller (mΩ := mΩ) P m₀ (filtration j)
      (hsmall j) (hfiltration j) (z j) (hi j) (hzero j)
  have hsum := conditional_finset_sum (mΩ := mΩ) P m₀ Finset.univ z
    (fun j _ => hi j)
  have hsmul := conditional_const_smul (mΩ := mΩ) P m₀ ((B : ℝ)⁻¹)
    (fun ω => ∑ j : Fin B, z j ω)
  filter_upwards [hsum, hsmul, ae_all_iff.mpr hsmallzero] with ω hs hm hz0
  rw [hm, hs]
  simp only [hz0, Finset.sum_const_zero, smul_zero]

lemma conditional_batch_variance {B : ℕ} (hB : 0 < B)
    (P : @Measure Ω mΩ) [IsProbabilityMeasure P]
    (m₀ : MeasurableSpace Ω) (filtration : Fin B → MeasurableSpace Ω)
    (hsmall : ∀ j, m₀ ≤ filtration j)
    (hfiltration : ∀ j, filtration j ≤ mΩ)
    (z : Fin B → Ω → E) (σ : ℝ)
    (hz : ∀ j, MemLp (z j) 2 P)
    (hpast : ∀ i j, i < j → AEStronglyMeasurable[filtration j] (z i) P)
    (hzero : ∀ j, condExp (filtration j) P (z j) =ᵐ[P] (fun _ => 0))
    (hvar : ∀ j, ∀ᵐ ω ∂P,
      condExp (filtration j) P (fun ω' => ‖z j ω'‖ ^ 2) ω ≤ σ ^ 2) :
    ∀ᵐ ω ∂P,
      condExp m₀ P (fun ω' => ‖(B : ℝ)⁻¹ • ∑ j, z j ω'‖ ^ 2) ω ≤
        σ ^ 2 / B := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have h0 : m₀ ≤ mΩ :=
    (hsmall ⟨0, hB⟩).trans (hfiltration ⟨0, hB⟩)
  have hint (i j : Fin B) : Integrable (fun ω => ⟪z i ω, z j ω⟫_ℝ) P :=
    integrable_inner_of_memLp_two (mΩ := mΩ) P _ _ (hz i) (hz j)
  have hoff (i j : Fin B) (hij : i ≠ j) :
      condExp m₀ P (fun ω => ⟪z i ω, z j ω⟫_ℝ) =ᵐ[P] (fun _ => 0) := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact conditional_mean_to_smaller (mΩ := mΩ) P m₀ (filtration j)
        (hsmall j) (hfiltration j) _ (hint i j)
        (conditional_inner_centered (mΩ := mΩ) P (filtration j) (hfiltration j)
          (z i) (z j) (hz i) (hz j) (hpast i j hlt) (hzero j))
    · have h := conditional_mean_to_smaller (mΩ := mΩ) P m₀ (filtration i)
        (hsmall i) (hfiltration i) _ (hint j i)
        (conditional_inner_centered (mΩ := mΩ) P (filtration i) (hfiltration i)
          (z j) (z i) (hz j) (hz i) (hpast j i hgt) (hzero i))
      have hid : (fun ω => ⟪z i ω, z j ω⟫_ℝ) =
          (fun ω => ⟪z j ω, z i ω⟫_ℝ) := by
        funext ω
        exact real_inner_comm (z j ω) (z i ω)
      rw [hid]
      exact h
  have hdiag (i : Fin B) : ∀ᵐ ω ∂P,
      condExp m₀ P (fun ω' => ‖z i ω'‖ ^ 2) ω ≤ σ ^ 2 := by
    apply conditional_bound_to_smaller (mΩ := mΩ) P m₀ (filtration i)
      (hsmall i) (hfiltration i) _ (σ ^ 2)
      ((memLp_two_iff_integrable_sq_norm (hz i).aestronglyMeasurable).mp (hz i))
    exact hvar i
  have hexpand : (fun ω => ‖(B : ℝ)⁻¹ • ∑ j, z j ω‖ ^ 2) =
      fun ω => ((B : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, ⟪z i ω, z j ω⟫_ℝ := by
    funext ω
    rw [square_smul, ← inner_self_eq, sum_inner]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [inner_sum]
  rw [hexpand]
  have hsum₁ := conditional_finset_sum (mΩ := mΩ) P m₀ (Finset.univ : Finset (Fin B))
    (fun i ω => ∑ j : Fin B, ⟪z i ω, z j ω⟫_ℝ)
    (fun i _ => integrable_finsetSum (Finset.univ : Finset (Fin B))
      (fun j _ => hint i j))
  have hsum₂ (i : Fin B) := conditional_finset_sum (mΩ := mΩ) P m₀ Finset.univ
    (fun j ω => ⟪z i ω, z j ω⟫_ℝ) (fun j _ => hint i j)
  have hmul :
      condExp m₀ P (fun ω => ((B : ℝ)⁻¹) ^ 2 *
        ∑ i : Fin B, ∑ j : Fin B, ⟪z i ω, z j ω⟫_ℝ) =ᵐ[P]
      (fun ω => ((B : ℝ)⁻¹) ^ 2 * condExp m₀ P
        (fun ω' => ∑ i : Fin B, ∑ j : Fin B, ⟪z i ω', z j ω'⟫_ℝ) ω) := by
    simpa only [smul_eq_mul] using
      (conditional_const_smul (mΩ := mΩ) (E := ℝ) P m₀ (((B : ℝ)⁻¹) ^ 2)
        (fun ω => ∑ i : Fin B, ∑ j : Fin B, ⟪z i ω, z j ω⟫_ℝ))
  have hoffall : ∀ᵐ ω ∂P, ∀ i j : Fin B, i ≠ j →
      condExp m₀ P (fun ω' => ⟪z i ω', z j ω'⟫_ℝ) ω = 0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ h => (h hij).elim)
    · exact (hoff i j hij).mono (fun _ h _ => h)
  filter_upwards [hsum₁, ae_all_iff.mpr hsum₂, hmul,
    hoffall, ae_all_iff.mpr hdiag] with ω hs₁ hs₂ hm ho hd
  rw [hm, hs₁]
  simp_rw [hs₂]
  have heq : (∑ i : Fin B, ∑ j : Fin B,
      condExp m₀ P (fun ω' => ⟪z i ω', z j ω'⟫_ℝ) ω) =
      ∑ i : Fin B, condExp m₀ P (fun ω' => ‖z i ω'‖ ^ 2) ω := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp_rw [inner_self_eq]
    · intro j hj hji
      exact ho i j (Ne.symm hji)
    · intro hnot
      exact (hnot (Finset.mem_univ i)).elim
  rw [heq]
  calc
    ((B : ℝ)⁻¹) ^ 2 *
        (∑ i, condExp m₀ P (fun ω' => ‖z i ω'‖ ^ 2) ω) ≤
        ((B : ℝ)⁻¹) ^ 2 * ∑ _ : Fin B, σ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hd i)) (sq_nonneg _)
    _ = σ ^ 2 / B := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [ne_of_gt hBR]

end LongTails.Proofs.ProximalEf21ConditionalBatch

end

end ConditionalBatch


section Regularity

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace ENNReal

noncomputable section

namespace LongTails.Proofs.ProximalEf21Regularity

open LongTails.Proofs.ProximalEf21AverageMoments

open LongTails.Proofs.ProximalEf21Averages

open LongTails.Setups.StochasticProximalEf21
open LongTails.Proofs.ProximalEf21SetupGeometry
open LongTails.Proofs.ProximalEf21MomentCalculus
open LongTails.Proofs.ProximalEf21WeightedErrors
open LongTails.Proofs.ProximalEf21Regularization

variable {p : Params} {I : Instance p}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : @Measure Ω mΩ) [IsProbabilityMeasure P]

lemma extended_regularizer_measurable (h : ProblemAssumptions p I) : Measurable I.ψ := by
  apply measurable_of_Iic
  intro a
  induction a using EReal.rec with
  | bot =>
      have he : I.ψ ⁻¹' Set.Iic ⊥ = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, le_bot_iff, Set.mem_empty_iff_false]
        exact iff_false_intro (h.regularizerNoBottom x)
      rw [he]
      exact MeasurableSet.empty
  | coe a =>
      have hc : Continuous (fun x : Point p => (x, a)) := continuous_id.prodMk continuous_const
      have he : I.ψ ⁻¹' Set.Iic (a : EReal) =
          (fun x : Point p => (x, a)) ⁻¹' {z : Point p × ℝ | I.ψ z.1 ≤ (z.2 : EReal)} := rfl
      rw [he]
      exact (h.regularizerClosed.preimage hc).measurableSet
  | top => simp

lemma regularizer_measurable (h : ProblemAssumptions p I) : Measurable (psiValue I) := by
  exact measurable_ereal_toReal.comp (extended_regularizer_measurable h)

lemma gradient_continuous (h : ProblemAssumptions p I) (i : Fin p.workers) :
    Continuous (gradient (I.f i)) := by
  have hl : LipschitzWith ⟨I.localL i, h.localNonnegative i⟩ (gradient (I.f i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    change ‖gradient (I.f i) x - gradient (I.f i) y‖ ≤
      I.localL i * ‖x - y‖
    exact h.localSmooth i x y
  exact hl.continuous

lemma smooth_objective_continuous (h : ProblemAssumptions p I) :
    Continuous (smoothObjective I) := by
  unfold smoothObjective
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro i hi
  exact continuous_iff_continuousAt.mpr (fun x => (h.localGradient i x).continuousAt)

lemma norm_square_integrable {E : Type*} [NormedAddCommGroup E]
    {x : Ω → E} (hx : MemLp x 2 P) : Integrable (fun ω => ‖x ω‖ ^ 2) P :=
  (memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx

lemma memLp_of_integrable_square {E : Type*} [NormedAddCommGroup E]
    {x : Ω → E} (hx : AEStronglyMeasurable x P)
    (hi : Integrable (fun ω => ‖x ω‖ ^ 2) P) : MemLp x 2 P :=
  (memLp_two_iff_integrable_sq_norm hx).mpr hi

lemma integrable_sandwich {f lo hi : Ω → ℝ}
    (hf : AEStronglyMeasurable f P) (hlo : Integrable lo P) (hhi : Integrable hi P)
    (hl : ∀ᵐ ω ∂P, lo ω ≤ f ω) (hu : ∀ᵐ ω ∂P, f ω ≤ hi ω) :
    Integrable f P := by
  apply (hlo.norm.add hhi.norm).mono' hf
  filter_upwards [hl, hu] with ω hl hu
  change ‖f ω‖ ≤ ‖lo ω‖ + ‖hi ω‖
  simp only [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith only [hl, neg_abs_le (lo ω), abs_nonneg (hi ω)]
  · linarith only [hu, le_abs_self (hi ω), abs_nonneg (lo ω)]

lemma lipschitz_comp_memLp {F G : Type*}
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    {K : NNReal} (g : F → G) (hg : LipschitzWith K g)
    {x : Ω → F} (hx : MemLp x 2 P) :
    MemLp (fun ω => g (x ω)) 2 P := by
  have hshift : LipschitzWith K (fun y => g y - g 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simpa only [dist_sub_right] using hg.dist_le_mul y z
  have hzero : (fun y => g y - g 0) 0 = 0 := sub_self _
  have hmem : MemLp (fun ω => g (x ω) - g 0) 2 P := by
    simpa only [Function.comp_def] using hshift.comp_memLp hzero hx
  have hconst : MemLp (fun _ : Ω => g 0) 2 P := memLp_const _
  have hsum := hmem.add hconst
  have hfun :
      ((fun ω : Ω => g (x ω) - g 0) + (fun _ : Ω => g 0)) =
        (fun ω : Ω => g (x ω)) := by
    funext ω
    exact sub_add_cancel _ _
  rw [hfun] at hsum
  exact hsum

lemma gradient_memLp (h : ProblemAssumptions p I) (i : Fin p.workers)
    {x : Ω → Point p} (hx : MemLp x 2 P) :
    MemLp (fun ω => gradient (I.f i) (x ω)) 2 P := by
  have hl : LipschitzWith ⟨I.localL i, h.localNonnegative i⟩
      (gradient (I.f i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [dist_eq_norm, dist_eq_norm]
    change ‖gradient (I.f i) y - gradient (I.f i) z‖ ≤
      I.localL i * ‖y - z‖
    exact h.localSmooth i y z
  exact lipschitz_comp_memLp P (gradient (I.f i)) hl hx

lemma prox_memLp (hp : spec.valid p) (h : ProblemAssumptions p I)
    {τ : ℝ} (hτ : 0 < τ) {u : Ω → Point p} (hu : MemLp u 2 P) :
    MemLp (fun ω => I.prox τ (u ω)) 2 P := by
  have hl : LipschitzWith 1 (I.prox τ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
      prox_nonexpansive hp h hτ x y
  exact lipschitz_comp_memLp P (I.prox τ) hl hu

lemma regularizer_at_prox_integrable (hp : spec.valid p) (h : ProblemAssumptions p I)
    {τ : ℝ} (hτ : 0 < τ) {u : Ω → Point p} (hu : MemLp u 2 P) :
    Integrable (fun ω => psiValue I (I.prox τ (u ω))) P := by
  have hy := prox_memLp P hp h hτ hu
  have hm : AEMeasurable (fun ω => psiValue I (I.prox τ (u ω))) P := by
    simpa only [Function.comp_def] using
      (regularizer_measurable h).comp_aemeasurable hy.aestronglyMeasurable.aemeasurable
  let a := workerMean (fun i => gradient (I.f i) I.xstar)
  have hlo : Integrable (fun ω => psiValue I I.xstar +
      ⟪-a, I.prox τ (u ω) - I.xstar⟫_ℝ) P :=
    (integrable_const _).add (integrable_inner_of_memLp_two P _ _ (memLp_const _)
      (hy.sub (memLp_const _)))
  have hhi : Integrable (fun ω => psiValue I I.xstar +
      ‖I.xstar - u ω‖ ^ 2 / (2 * τ)) P :=
    (integrable_const _).add
      ((norm_square_integrable P ((memLp_const I.xstar).sub hu)).div_const _)
  apply integrable_sandwich P hm.aestronglyMeasurable hlo hhi
  · filter_upwards [] with ω
    exact composite_optimum_support h hp.1 _ (h.proximalFinite τ hτ _)
  · filter_upwards [] with ω
    have hmin := finite_prox_min h hτ (u ω) I.xstar h.optimumFinite
    have hn : 0 ≤ ‖I.prox τ (u ω) - u ω‖ ^ 2 / (2 * τ) := by positivity
    change psiValue I (I.prox τ (u ω)) ≤
      psiValue I I.xstar + ‖I.xstar - u ω‖ ^ 2 / (2 * τ)
    exact (le_add_of_nonneg_right hn).trans hmin

lemma local_objective_integrable (h : ProblemAssumptions p I)
    (i : Fin p.workers) {x : Ω → Point p} (hx : MemLp x 2 P) :
    Integrable (fun ω => I.f i (x ω)) P := by
  have hc : Continuous (I.f i) :=
    continuous_iff_continuousAt.mpr (fun z => (h.localGradient i z).continuousAt)
  have hm := hc.comp_aestronglyMeasurable hx.aestronglyMeasurable
  have ha : Integrable (fun ω => I.f i 0 + ⟪gradient (I.f i) 0, x ω⟫_ℝ) P :=
    (integrable_const _).add (integrable_inner_of_memLp_two P _ _ (memLp_const _) hx)
  have hq := (norm_square_integrable P hx).const_mul (I.localL i / 2)
  apply integrable_sandwich P hm ha (ha.add hq)
  · filter_upwards [] with ω
    simpa using convex_gradient_lower (I.f i) (gradient (I.f i))
      (h.localConvex i) (h.localGradient i) 0 (x ω)
  · filter_upwards [] with ω
    simpa using smooth_gradient_upper (I.f i) (gradient (I.f i)) (I.localL i)
      (h.localNonnegative i) (h.localGradient i) (h.localSmooth i) 0 (x ω)

lemma smooth_objective_integrable (h : ProblemAssumptions p I)
    {x : Ω → Point p} (hx : MemLp x 2 P) :
    Integrable (fun ω => smoothObjective I (x ω)) P := by
  exact (integrable_finsetSum _ (fun i _ => local_objective_integrable P h i hx)).const_mul _

lemma gap_integrable (hp : spec.valid p) (h : ProblemAssumptions p I)
    {x : Ω → Point p} (hx : MemLp x 2 P)
    (hψ : Integrable (fun ω => psiValue I (x ω)) P) :
    Integrable (fun ω => (geometry hp h).gap (x ω)) P := by
  exact ((smooth_objective_integrable P h hx).add hψ).sub (integrable_const _)

lemma regularized_gap_integrable (hp : spec.valid p) (h : ProblemAssumptions p I)
    {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ 2 * p.L)
    {x : Ω → Point p} (hx : MemLp x 2 P)
    (hψ : Integrable (fun ω => psiValue I (x ω)) P) :
    Integrable (fun ω => ((geometry hp h).regularized μ hμ hμL).gap (x ω)) P := by
  simp_rw [ConvexCompositeGeometry.regularized_gap]
  exact (gap_integrable P hp h hx hψ).add
    ((norm_square_integrable P (hx.sub (memLp_const _))).const_mul _)

lemma regularized_gradient_memLp (hp : spec.valid p) (h : ProblemAssumptions p I)
    {μ : ℝ} (hμ : 0 < μ) (hμL : μ ≤ 2 * p.L) (i : Fin p.workers)
    {x : Ω → Point p} (hx : MemLp x 2 P) :
    MemLp (fun ω => ((geometry hp h).regularized μ hμ hμL).grad i (x ω)) 2 P := by
  exact (gradient_memLp P h i hx).add ((hx.sub (memLp_const _)).const_smul μ)

lemma auxiliary_memLp (hp : spec.valid p) (h : ProblemAssumptions p I)
    {τ : ℝ} (hτ : 0 < τ) {x : Ω → Point p} {m : Fin p.workers → Ω → Point p}
    (hx : MemLp x 2 P) (hm : ∀ i, MemLp (m i) 2 P) :
    MemLp (fun ω => I.prox τ (x ω - τ • workerMean (fun i => m i ω))) 2 P := by
  apply prox_memLp P hp h hτ
  exact hx.sub ((workerMean_memLp P m hm).const_smul τ)

lemma initial_momentum_memLp (h : ProblemAssumptions p I)
    (O : OracleTemplate.Oracle (Query p) (Reply p) 4) (i : Fin p.workers) :
    MemLp (fun ω : Randomness p O => ω.1.1 i) 2 (executionMeasure p O) := by
  letI : IsProbabilityMeasure (executionMeasure p O) := by
    unfold executionMeasure
    infer_instance
  have hm : Measurable (fun z : InitialMemories p => z.1 i - gradient (I.f i) p.x0) := by
    fun_prop
  have he : MemLp (fun z : InitialMemories p => z.1 i - gradient (I.f i) p.x0) 2
      (p.initialLaw : Measure _) :=
    memLp_of_integrable_square (p.initialLaw : Measure _) hm.aestronglyMeasurable
      (h.momentumInitiallyIntegrable i)
  have hi := (h.momentumInitiallyIntegrable i).comp_fst (ν := (O.law : Measure (Tape O)))
  have he' : MemLp (fun ω : Randomness p O => ω.1.1 i - gradient (I.f i) p.x0) 2
      (executionMeasure p O) := by
    apply memLp_of_integrable_square (executionMeasure p O) (by fun_prop)
    exact hi
  have hsum := he'.add (memLp_const (gradient (I.f i) p.x0))
  have hfun :
      ((fun ω : Randomness p O => ω.1.1 i - gradient (I.f i) p.x0) +
        (fun _ : Randomness p O => gradient (I.f i) p.x0)) =
          (fun ω : Randomness p O => ω.1.1 i) := by
    funext ω
    exact sub_add_cancel _ _
  rw [hfun] at hsum
  exact hsum

lemma initial_compressed_memLp (h : ProblemAssumptions p I)
    (O : OracleTemplate.Oracle (Query p) (Reply p) 4) (i : Fin p.workers) :
    MemLp (fun ω : Randomness p O => ω.1.2 i) 2 (executionMeasure p O) := by
  letI : IsProbabilityMeasure (executionMeasure p O) := by
    unfold executionMeasure
    infer_instance
  have hi := (h.compressionInitiallyIntegrable i).comp_fst (ν := (O.law : Measure (Tape O)))
  have he : MemLp (fun ω : Randomness p O => ω.1.2 i - ω.1.1 i) 2
      (executionMeasure p O) := by
    apply memLp_of_integrable_square (executionMeasure p O) (by fun_prop)
    exact hi
  have hsum := he.add (initial_momentum_memLp h O i)
  have hfun :
      ((fun ω : Randomness p O => ω.1.2 i - ω.1.1 i) +
        (fun ω : Randomness p O => ω.1.1 i)) =
          (fun ω : Randomness p O => ω.1.2 i) := by
    funext ω
    exact sub_add_cancel _ _
  rw [hfun] at hsum
  exact hsum

end LongTails.Proofs.ProximalEf21Regularity

end

end Regularity
