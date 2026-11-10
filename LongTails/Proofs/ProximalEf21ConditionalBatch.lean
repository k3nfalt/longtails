import LongTails.Proofs.ProximalEf21RawBatch

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.ProximalEf21ConditionalBatch

open LongTails.Proofs.ProximalEf21Geometry
open LongTails.Proofs.ProximalEf21MomentCalculus
open LongTails.Proofs.ProximalEf21StochasticContraction

variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma conditional_inner_centered
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ ‹MeasurableSpace Ω›)
    (u z : Ω → E) (hu : MemLp u 2 P) (hz : MemLp z 2 P)
    (hpred : AEStronglyMeasurable[m] u P)
    (hzero : condExp m P z =ᵐ[P] (fun _ => 0)) :
    condExp m P (fun ω => ⟪u ω, z ω⟫_ℝ) =ᵐ[P] (fun _ => 0) := by
  have hi := integrable_inner_of_memLp_two P u z hu hz
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm hi
  · intro s hs hfin
    exact integrable_zero
  · intro s hs hfin
    have hsm : MeasurableSet s := hm s hs
    have hpred' : AEStronglyMeasurable[m] (s.indicator u) P :=
      hpred.indicator hs
    have hu' : MemLp (s.indicator u) 2 P := hu.indicator hsm
    have h := predictable_inner_centered_noise P m hm
      (s.indicator u) z hu' hz hpred' hzero
    have hid : (fun ω => ⟪s.indicator u ω, z ω⟫_ℝ) =
        s.indicator (fun ω => ⟪u ω, z ω⟫_ℝ) := by
      funext ω
      by_cases hω : ω ∈ s <;> simp [hω]
    rw [hid, integral_indicator hsm] at h
    simpa using h.symm
  · exact aestronglyMeasurable_const

lemma conditional_mean_to_smaller
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m₀ m₁ : MeasurableSpace Ω)
    (h01 : m₀ ≤ m₁) (h1 : m₁ ≤ ‹MeasurableSpace Ω›)
    (z : Ω → E) (hz : Integrable z P)
    (hzero : condExp m₁ P z =ᵐ[P] (fun _ => 0)) :
    condExp m₀ P z =ᵐ[P] (fun _ => 0) := by
  calc
    condExp m₀ P z =ᵐ[P] condExp m₀ P (condExp m₁ P z) :=
      (condExp_condExp_of_le h01 h1).symm
    _ =ᵐ[P] condExp m₀ P (fun _ : Ω => (0 : E)) :=
      condExp_congr_ae hzero
    _ =ᵐ[P] (fun _ => 0) := by simp

lemma conditional_bound_to_smaller
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m₀ m₁ : MeasurableSpace Ω)
    (h01 : m₀ ≤ m₁) (h1 : m₁ ≤ ‹MeasurableSpace Ω›)
    (f : Ω → ℝ) (c : ℝ) (hf : Integrable f P)
    (hc : ∀ᵐ ω ∂P, condExp m₁ P f ω ≤ c) :
    ∀ᵐ ω ∂P, condExp m₀ P f ω ≤ c := by
  have htower := condExp_condExp_of_le (f := f) h01 h1
  have hmono := condExp_mono integrable_condExp (integrable_const c) hc m₀
  have hconst : condExp m₀ P (fun _ : Ω => c) =ᵐ[P] (fun _ => c) :=
    condExp_of_aestronglyMeasurable' (h01.trans h1)
      aestronglyMeasurable_const (integrable_const c)
  filter_upwards [htower, hmono, hconst] with ω ht hm hc
  rw [ht, hc] at hm
  exact hm

lemma conditional_batch_mean {B : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m₀ : MeasurableSpace Ω) (filtration : Fin B → MeasurableSpace Ω)
    (hsmall : ∀ j, m₀ ≤ filtration j)
    (hfiltration : ∀ j, filtration j ≤ ‹MeasurableSpace Ω›)
    (z : Fin B → Ω → E) (hz : ∀ j, MemLp (z j) 2 P)
    (hzero : ∀ j, condExp (filtration j) P (z j) =ᵐ[P] (fun _ => 0)) :
    condExp m₀ P (fun ω => (B : ℝ)⁻¹ • ∑ j, z j ω) =ᵐ[P] (fun _ => 0) := by
  have hi (j : Fin B) : Integrable (z j) P :=
    (hz j).integrable (by norm_num)
  have hsmallzero (j : Fin B) :
      condExp m₀ P (z j) =ᵐ[P] (fun _ => 0) :=
    conditional_mean_to_smaller P m₀ (filtration j)
      (hsmall j) (hfiltration j) (z j) (hi j) (hzero j)
  have hsum := condExp_finsetSum (s := Finset.univ)
    (fun j (_ : j ∈ Finset.univ) => hi j) m₀
  have hsmul := condExp_smul ((B : ℝ)⁻¹)
    (integrable_finset_sum _ (fun j _ => hi j)) m₀
  have hall := ae_all_iff.mpr hsmallzero
  filter_upwards [hsum, hsmul, hall] with ω hs hm hz
  simpa [hs, hz] using hm

lemma conditional_batch_variance {B : ℕ} (hB : 0 < B)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m₀ : MeasurableSpace Ω) (filtration : Fin B → MeasurableSpace Ω)
    (hsmall : ∀ j, m₀ ≤ filtration j)
    (hfiltration : ∀ j, filtration j ≤ ‹MeasurableSpace Ω›)
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
  have h0 : m₀ ≤ ‹MeasurableSpace Ω› :=
    (hsmall ⟨0, hB⟩).trans (hfiltration ⟨0, hB⟩)
  have hint (i j : Fin B) : Integrable (fun ω => ⟪z i ω, z j ω⟫_ℝ) P :=
    integrable_inner_of_memLp_two P _ _ (hz i) (hz j)
  have hoff (i j : Fin B) (hij : i ≠ j) :
      condExp m₀ P (fun ω => ⟪z i ω, z j ω⟫_ℝ) =ᵐ[P] (fun _ => 0) := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact conditional_mean_to_smaller P m₀ (filtration j)
        (hsmall j) (hfiltration j) _ (hint i j)
        (conditional_inner_centered P (filtration j) (hfiltration j)
          (z i) (z j) (hz i) (hz j) (hpast i j hlt) (hzero j))
    · have h := conditional_mean_to_smaller P m₀ (filtration i)
        (hsmall i) (hfiltration i) _ (hint j i)
        (conditional_inner_centered P (filtration i) (hfiltration i)
          (z j) (z i) (hz j) (hz i) (hpast j i hgt) (hzero i))
      simpa only [real_inner_comm] using h
  have hdiag (i : Fin B) : ∀ᵐ ω ∂P,
      condExp m₀ P (fun ω' => ‖z i ω'‖ ^ 2) ω ≤ σ ^ 2 := by
    apply conditional_bound_to_smaller P m₀ (filtration i)
      (hsmall i) (hfiltration i) _ (σ ^ 2)
      ((memLp_two_iff_integrable_sq_norm (hz i).aestronglyMeasurable).mp (hz i))
    exact hvar i
  have hexpand : (fun ω => ‖(B : ℝ)⁻¹ • ∑ j, z j ω‖ ^ 2) =
      fun ω => ((B : ℝ)⁻¹) ^ 2 * ∑ i, ∑ j, ⟪z i ω, z j ω⟫_ℝ := by
    funext ω
    rw [square_smul, ← inner_self_eq]
    simp only [sum_inner, inner_sum]
  rw [hexpand]
  have hsum₁ := condExp_finsetSum (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) =>
      integrable_finset_sum _ (fun j _ => hint i j)) m₀
  have hsum₂ (i : Fin B) := condExp_finsetSum (s := Finset.univ)
    (fun j (_ : j ∈ Finset.univ) => hint i j) m₀
  have hmul := condExp_smul (((B : ℝ)⁻¹) ^ 2)
    (integrable_finset_sum _ (fun i _ =>
      integrable_finset_sum _ (fun j _ => hint i j))) m₀
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
  simp only [Pi.smul_apply, smul_eq_mul] at hm
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
      <;> ring

end LongTails.Proofs.ProximalEf21ConditionalBatch
