import LongTails.Proofs.ProximalEf21Geometry

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.ProximalEf21MomentCalculus

open LongTails.Proofs.ProximalEf21Geometry

variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma integral_square_add_smul (P : Measure Ω) (u ζ : Ω → E) (a : ℝ)
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
  rw [integral_add (hu.add (hc.const_mul (2 * a))) (hζ.const_mul (a ^ 2)),
    integral_add hu (hc.const_mul (2 * a)), integral_const_mul, integral_const_mul]

lemma integral_square_add_smul_centered (P : Measure Ω) (u ζ : Ω → E)
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
    (P : Measure Ω) (u : ι → Ω → E) (v : Ω → E)
    (hi : ∀ i, Integrable (fun ω => ⟪u i ω, v ω⟫_ℝ) P) :
    (∫ ω, ⟪∑ i, u i ω, v ω⟫_ℝ ∂P) =
      ∑ i, ∫ ω, ⟪u i ω, v ω⟫_ℝ ∂P := by
  simp_rw [sum_inner]
  exact integral_finset_sum _ (fun i _ => hi i)

lemma integral_norm_sq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (u : ι → Ω → E)
    (hint : ∀ i j, Integrable (fun ω => ⟪u i ω, u j ω⟫_ℝ) P)
    (hortho : ∀ i j, i ≠ j → (∫ ω, ⟪u i ω, u j ω⟫_ℝ ∂P) = 0) :
    (∫ ω, ‖∑ i, u i ω‖ ^ 2 ∂P) =
      ∑ i, ∫ ω, ‖u i ω‖ ^ 2 ∂P := by
  have hexpand : ∀ ω, ‖∑ i, u i ω‖ ^ 2 =
      ∑ i, ∑ j, ⟪u i ω, u j ω⟫_ℝ := by
    intro ω
    rw [← inner_self_eq]
    simp only [sum_inner, inner_sum]
  simp_rw [hexpand]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finset_sum _ (fun j _ => hint i j)]
  calc
    (∑ j, ∫ ω, ⟪u i ω, u j ω⟫_ℝ ∂P) = ∫ ω, ⟪u i ω, u i ω⟫_ℝ ∂P := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        exact hortho i j (Ne.symm hji)
      · intro hnot
        exact (hnot (Finset.mem_univ i)).elim
    _ = ∫ ω, ‖u i ω‖ ^ 2 ∂P := by simp_rw [inner_self_eq]

lemma miniBatch_second_moment {B : ℕ} (hB : 0 < B)
    (P : Measure Ω) (ζ : Fin B → Ω → E) (variance : ℝ)
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
    <;> ring
  simpa only [hid] using hm

lemma scalar_conditional_zero_integral
    (m : MeasurableSpace Ω) (P : Measure Ω)
    (hm : m ≤ ‹MeasurableSpace Ω›)
    [IsProbabilityMeasure P] (u : Ω → ℝ)
    (hu : Integrable u P)
    (hzero : condExp m P u =ᵐ[P] (fun _ => 0)) :
    (∫ ω, u ω ∂P) = 0 := by
  calc
    (∫ ω, u ω ∂P) = ∫ ω, condExp m P u ω ∂P :=
      (integral_condExp hm).symm
    _ = ∫ _ : Ω, (0 : ℝ) ∂P := integral_congr_ae hzero
    _ = 0 := by simp

lemma integrate_pointwise_progress (P : Measure Ω)
    (next current decrease noise : Ω → ℝ)
    (hn : Integrable next P) (hc : Integrable current P)
    (hd : Integrable decrease P) (he : Integrable noise P)
    (hstep : ∀ᵐ ω ∂P, next ω ≤ current ω - decrease ω + noise ω) :
    (∫ ω, next ω ∂P) ≤
      (∫ ω, current ω ∂P) - (∫ ω, decrease ω ∂P) + (∫ ω, noise ω ∂P) := by
  have h := integral_mono_ae hn ((hc.sub hd).add he) hstep
  rwa [integral_add (hc.sub hd) he, integral_sub hc hd] at h


section SquareIntegrableNoise

variable [CompleteSpace E]

lemma integrable_inner_of_memLp_two (P : Measure Ω) (u v : Ω → E)
    (hu : MemLp u 2 P) (hv : MemLp v 2 P) :
    Integrable (fun ω => ⟪u ω, v ω⟫_ℝ) P := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (hu.toLp u) (hv.toLp v)
  apply h.congr
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with ω hωu hωv
  simp only [hωu, hωv]

lemma predictable_inner_centered_noise (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ ‹MeasurableSpace Ω›) (u ζ : Ω → E)
    (hu : MemLp u 2 P) (hζ : MemLp ζ 2 P)
    (hpredictable : AEStronglyMeasurable[m] u P)
    (hcentered : condExp m P ζ =ᵐ[P] (fun _ => 0)) :
    (∫ ω, ⟪u ω, ζ ω⟫_ℝ ∂P) = 0 := by
  have hprojection :
      ((condExpL2 E ℝ hm) (hζ.toLp ζ) : Lp E 2 P) = 0 := by
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    exact (MeasureTheory.MemLp.condExpL2_ae_eq_condExp
      (𝕜 := ℝ) hm hζ).trans hcentered
  have hpred : AEStronglyMeasurable[m] (hu.toLp u : Ω → E) P :=
    hpredictable.congr hu.coeFn_toLp.symm
  have hinner := MeasureTheory.inner_condExpL2_eq_inner_fun
    (𝕜 := ℝ) hm (hζ.toLp ζ) (hu.toLp u) hpred
  rw [hprojection, inner_zero_left, MeasureTheory.L2.inner_def] at hinner
  calc
    (∫ ω, ⟪u ω, ζ ω⟫_ℝ ∂P) =
        ∫ ω, ⟪(hζ.toLp ζ : Ω → E) ω, (hu.toLp u : Ω → E) ω⟫_ℝ ∂P := by
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp, hζ.coeFn_toLp] with ω hωu hωζ
      rw [hωu, hωζ, real_inner_comm]
    _ = 0 := hinner.symm

lemma conditional_variance_to_integral (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ ‹MeasurableSpace Ω›)
    (ζ : Ω → E) (variance : ℝ)
    (hvariance : ∀ᵐ ω ∂P,
      condExp m P (fun ω' => ‖ζ ω'‖ ^ 2) ω ≤ variance) :
    (∫ ω, ‖ζ ω‖ ^ 2 ∂P) ≤ variance := by
  calc
    (∫ ω, ‖ζ ω‖ ^ 2 ∂P) =
        ∫ ω, condExp m P (fun ω' => ‖ζ ω'‖ ^ 2) ω ∂P :=
      (integral_condExp hm).symm
    _ ≤ ∫ _ : Ω, variance ∂P :=
      integral_mono_ae integrable_condExp (integrable_const variance) hvariance
    _ = variance := by simp

lemma square_integral_add_fresh_noise (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ ‹MeasurableSpace Ω›)
    (u ζ : Ω → E) (a variance : ℝ)
    (hu : MemLp u 2 P) (hζ : MemLp ζ 2 P)
    (hpredictable : AEStronglyMeasurable[m] u P)
    (hcentered : condExp m P ζ =ᵐ[P] (fun _ => 0))
    (hvariance : ∀ᵐ ω ∂P,
      condExp m P (fun ω' => ‖ζ ω'‖ ^ 2) ω ≤ variance) :
    (∫ ω, ‖u ω + a • ζ ω‖ ^ 2 ∂P) ≤
      (∫ ω, ‖u ω‖ ^ 2 ∂P) + a ^ 2 * variance := by
  apply integral_square_add_smul_centered P u ζ a variance
  · exact (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu
  · exact (memLp_two_iff_integrable_sq_norm hζ.aestronglyMeasurable).mp hζ
  · exact integrable_inner_of_memLp_two P u ζ hu hζ
  · exact predictable_inner_centered_noise P m hm u ζ hu hζ hpredictable hcentered
  · exact conditional_variance_to_integral P m hm ζ variance hvariance

end SquareIntegrableNoise

end LongTails.Proofs.ProximalEf21MomentCalculus
