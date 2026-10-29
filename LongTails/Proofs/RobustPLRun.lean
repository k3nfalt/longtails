import LongTails.Proofs.RobustPLContraction
import LongTails.Proofs.PLHessianConvergence

open Set Metric MeasureTheory
open scoped ENNReal

namespace OracleTemplate.RobustPLProcess

open PLHessian

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E} {u : E}
  {L μ ρ η lam t q C : ℝ}

local notation "Pω" => Measure.infinitePi fun _ : ℕ => p

lemma run_step (H : Hyp p f (fun x (_ : Ω) => gradient f x) u L μ ρ 0 1)
    (hg : Measurable (Function.uncurry g)) (hη : 0 ≤ η) (ht : 0 < t)
    (hlam0 : 0 ≤ lam) (hq : 0 ≤ q)
    (hstep : ∀ y, Integrable (fun ω => pot f u lam t (y - η • g y ω)) p ∧
      (∫ ω, pot f u lam t (y - η • g y ω) ∂p) ≤
        (1 - q) * pot f u lam t y - η / 2 * (f y - f u) + C)
    (x0 : E) (n : ℕ)
    (hI : Integrable (fun ξ => pot f u lam t (sgdSeq g η x0 ξ n)) Pω) :
    Integrable (fun ξ => pot f u lam t (sgdSeq g η x0 ξ (n + 1))) Pω ∧
    Integrable (fun ξ => f (sgdSeq g η x0 ξ n) - f u) Pω ∧
    (∫ ξ, pot f u lam t (sgdSeq g η x0 ξ (n + 1)) ∂Pω) ≤
      (1 - q) * (∫ ξ, pot f u lam t (sgdSeq g η x0 ξ n) ∂Pω) -
        η / 2 * (∫ ξ, f (sgdSeq g η x0 ξ n) - f u ∂Pω) + C := by
  set S := fun ξ : ℕ → Ω => sgdSeq g η x0 ξ n with hSdef
  have hS : Measurable S := measurable_sgdSeq hg η x0 n
  have hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < n → ξ i = ξ' i) → S ξ = S ξ' :=
    fun ξ ξ' h => sgdSeq_congr g η x0 n h
  have hpc := H.pot_continuous (lam := lam) ht
  set Φf : E → Ω → ℝ := fun y ω => pot f u lam t (y - η • g y ω) with hΦfdef
  have hΦm : Measurable (Function.uncurry Φf) :=
    hpc.measurable.comp (measurable_fst.sub (hg.const_smul η))
  have hnext : ∀ ξ, pot f u lam t (sgdSeq g η x0 ξ (n + 1)) = Φf (S ξ) (ξ n) := fun ξ => rfl
  have hgapm : Measurable fun ξ => f (S ξ) - f u := (H.continuous.measurable.comp hS).sub_const _
  have hgap0 : ∀ ξ, 0 ≤ f (S ξ) - f u := fun ξ => sub_nonneg.mpr (H.min (mem_univ _))
  have igap : Integrable (fun ξ => f (S ξ) - f u) Pω := by
    refine Integrable.mono' (hI.const_mul (L / 2)) hgapm.aestronglyMeasurable
      (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hgap0 ξ)]
    exact H.gap_le_pot hlam0 ht (S ξ)
  have hbound : ∀ y, ∫ ω, Φf y ω ∂p ≤ pot f u lam t y + C := by
    intro y
    have hb := (hstep y).2
    have h0 : 0 ≤ f y - f u := sub_nonneg.mpr (H.min (mem_univ _))
    have hp0 := pot_nonneg (f := f) (u := u) hlam0 ht y
    have : (1 - q) * pot f u lam t y ≤ pot f u lam t y := by nlinarith
    have : 0 ≤ η / 2 * (f y - f u) := by positivity
    exact le_trans hb (by linarith)
  have inext : Integrable (fun ξ => pot f u lam t (sgdSeq g η x0 ξ (n + 1))) Pω := by
    refine NormalizedStorm.integrable_of_lintegral_le
      (hpc.measurable.comp (measurable_sgdSeq hg η x0 (n + 1)))
      (fun ξ => pot_nonneg hlam0 ht _) (hI.add (integrable_const (C))) ?_
    simp_rw [hnext]
    have hh : Measurable fun z : E × Ω => ENNReal.ofReal (Φf z.1 z.2) :=
      ENNReal.measurable_ofReal.comp hΦm
    rw [HessianNcsc.fresh_lintegral p n S hS hdep (fun z => ENNReal.ofReal (Φf z.1 z.2)) hh]
    refine lintegral_mono fun ξ => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hstep (S ξ)).1
      (Filter.Eventually.of_forall fun ω => pot_nonneg hlam0 ht _)]
    exact ENNReal.ofReal_le_ofReal (hbound (S ξ))
  refine ⟨inext, igap, ?_⟩
  set Ψ : E → Ω → ℝ := fun y ω => Φf y ω -
    ((1 - q) * pot f u lam t y - η / 2 * (f y - f u) + C) with hΨdef
  have hΨm : Measurable (Function.uncurry Ψ) := by
    refine hΦm.sub ?_
    have hm1 : Measurable fun z : E × Ω => pot f u lam t z.1 := hpc.measurable.comp measurable_fst
    have hm2 : Measurable fun z : E × Ω => f z.1 := H.continuous.measurable.comp measurable_fst
    exact (((hm1.const_mul _).sub ((hm2.sub_const _).const_mul _)).add_const _)
  have ibd : Integrable (fun ξ => (1 - q) * pot f u lam t (S ξ) -
      η / 2 * (f (S ξ) - f u) + C) Pω :=
    ((hI.const_mul _).sub (igap.const_mul _)).add (integrable_const _)
  have iΨ : Integrable (fun ξ => Ψ (S ξ) (ξ n)) Pω := inext.sub ibd
  have hΨeq := TwoSidedPL.integral_prefix_dep p n S hS hdep Ψ hΨm iΨ
  have hΨle : ∫ ξ, Ψ (S ξ) (ξ n) ∂Pω ≤ 0 := by
    rw [hΨeq]
    refine integral_nonpos fun ξ => ?_
    show ∫ ω, Ψ (S ξ) ω ∂p ≤ 0
    simp only [Ψ]
    rw [integral_sub (hstep (S ξ)).1 (integrable_const _), integral_const]
    simp only [probReal_univ, one_smul]
    have h := (hstep (S ξ)).2
    change ∫ ω, Φf (S ξ) ω ∂p ≤ _ at h
    simp only [Φf] at h ⊢
    linarith
  have hsplit : ∫ ξ, Ψ (S ξ) (ξ n) ∂Pω =
      ∫ ξ, pot f u lam t (sgdSeq g η x0 ξ (n + 1)) ∂Pω -
        ((1 - q) * ∫ ξ, pot f u lam t (S ξ) ∂Pω -
          η / 2 * ∫ ξ, (f (S ξ) - f u) ∂Pω + C) := by
    have inext' : Integrable (fun ξ => Φf (S ξ) (ξ n)) Pω := inext
    simp only [Ψ, hnext]
    have i1 : Integrable (fun ξ => (1 - q) * pot f u lam t (S ξ)) Pω := hI.const_mul _
    have i2 : Integrable (fun ξ => η / 2 * (f (S ξ) - f u)) Pω := igap.const_mul _
    have i12 : Integrable (fun ξ => (1 - q) * pot f u lam t (S ξ) -
        η / 2 * (f (S ξ) - f u)) Pω := i1.sub i2
    rw [integral_sub inext' ibd, integral_add i12 (integrable_const _), integral_sub i1 i2,
      integral_const_mul, integral_const_mul, integral_const]
    simp
  rw [hsplit] at hΨle
  linarith

lemma run_bound (H : Hyp p f (fun x (_ : Ω) => gradient f x) u L μ ρ 0 1)
    (hg : Measurable (Function.uncurry g)) (hη : 0 ≤ η) (ht : 0 < t)
    (hlam0 : 0 ≤ lam) (hq : 0 < q) (hq1 : q ≤ 1) (hC : 0 ≤ C)
    (hstep : ∀ y, Integrable (fun ω => pot f u lam t (y - η • g y ω)) p ∧
      (∫ ω, pot f u lam t (y - η • g y ω) ∂p) ≤
        (1 - q) * pot f u lam t y - η / 2 * (f y - f u) + C)
    (x0 : E) : ∀ n,
    Integrable (fun ξ => pot f u lam t (sgdSeq g η x0 ξ n)) Pω ∧
    (∫ ξ, pot f u lam t (sgdSeq g η x0 ξ n) ∂Pω) ≤
      (1 - q) ^ n * pot f u lam t x0 + C / q
  | 0 => by
      refine ⟨(integrable_const (pot f u lam t x0) : Integrable (fun _ : ℕ → Ω => pot f u lam t x0) Pω), ?_⟩
      simp only [sgdSeq, integral_const, probReal_univ, one_smul, pow_zero, one_mul]
      exact le_add_of_nonneg_right (div_nonneg hC hq.le)
  | n + 1 => by
      obtain ⟨hI, hb⟩ := run_bound H hg hη ht hlam0 hq hq1 hC hstep x0 n
      obtain ⟨hI', _, hs⟩ := run_step H hg hη ht hlam0 hq.le hstep x0 n hI
      refine ⟨hI', ?_⟩
      have hgap : 0 ≤ ∫ ξ, f (sgdSeq g η x0 ξ n) - f u ∂Pω :=
        integral_nonneg fun ξ => sub_nonneg.mpr (H.min (mem_univ _))
      have hm := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hq1)
      have he : (1 - q) * ((1 - q) ^ n * pot f u lam t x0 + C / q) + C =
          (1 - q) ^ (n + 1) * pot f u lam t x0 + C / q := by
        field_simp
        ring
      have hnonneg : 0 ≤ η / 2 * ∫ ξ, f (sgdSeq g η x0 ξ n) - f u ∂Pω := by positivity
      linarith

lemma window_sum (H : Hyp p f (fun x (_ : Ω) => gradient f x) u L μ ρ 0 1)
    (hg : Measurable (Function.uncurry g)) (hη : 0 ≤ η) (ht : 0 < t)
    (hlam0 : 0 ≤ lam) (hq : 0 < q) (hq1 : q ≤ 1) (hC : 0 ≤ C)
    (hstep : ∀ y, Integrable (fun ω => pot f u lam t (y - η • g y ω)) p ∧
      (∫ ω, pot f u lam t (y - η • g y ω) ∂p) ≤
        (1 - q) * pot f u lam t y - η / 2 * (f y - f u) + C)
    (x0 : E) (a : ℕ) : ∀ m,
    (∑ i ∈ Finset.range m, η / 2 * ∫ ξ, f (sgdSeq g η x0 ξ (a + i)) - f u ∂Pω) +
      (∫ ξ, pot f u lam t (sgdSeq g η x0 ξ (a + m)) ∂Pω) ≤
    (∫ ξ, pot f u lam t (sgdSeq g η x0 ξ a) ∂Pω) + m * C
  | 0 => by simp
  | m + 1 => by
      have ih := window_sum H hg hη ht hlam0 hq hq1 hC hstep x0 a m
      have hI := (run_bound H hg hη ht hlam0 hq hq1 hC hstep x0 (a + m)).1
      have hs := (run_step H hg hη ht hlam0 hq.le hstep x0 (a + m) hI).2.2
      have hp : 0 ≤ ∫ ξ, pot f u lam t (sgdSeq g η x0 ξ (a + m)) ∂Pω :=
        integral_nonneg fun ξ => pot_nonneg hlam0 ht _
      have hnonneg : 0 ≤ q * ∫ ξ, pot f u lam t (sgdSeq g η x0 ξ (a + m)) ∂Pω := by positivity
      rw [Finset.sum_range_succ, show a + (m + 1) = a + m + 1 by omega]
      push_cast
      nlinarith

lemma window_accuracy (H : Hyp p f (fun x (_ : Ω) => gradient f x) u L μ ρ 0 1)
    (hg : Measurable (Function.uncurry g)) (hη : 0 < η) (ht : 0 < t)
    (hlam0 : 0 ≤ lam) (hq : 0 < q) (hq1 : q ≤ 1) (hC : 0 ≤ C)
    (hstep : ∀ y, Integrable (fun ω => pot f u lam t (y - η • g y ω)) p ∧
      (∫ ω, pot f u lam t (y - η • g y ω) ∂p) ≤
        (1 - q) * pot f u lam t y - η / 2 * (f y - f u) + C)
    (x0 : E) (a m : ℕ) {W ε : ℝ}
    (hwarm : (1 - q) ^ a * pot f u lam t x0 + C / q ≤ W)
    (hacc : 2 * W / η / (m + 1) + 2 * C / η ≤ ε) :
    ∫⁻ ω, ENNReal.ofReal (f (sgdSeq g η x0 ω.2 (a + ω.1.val)) - f u)
      ∂((PMF.uniformOfFintype (Fin (m + 1))).toMeasure.prod Pω) ≤ ENNReal.ofReal ε := by
  have hm : Measurable (fun ω : Fin (m + 1) × (ℕ → Ω) =>
      ENNReal.ofReal (f (sgdSeq g η x0 ω.2 (a + ω.1.val)) - f u)) :=
    ENNReal.measurable_ofReal.comp
      ((H.continuous.measurable.comp (measurable_window_out hg η a m x0)).sub_const _)
  rw [lintegral_prod _ hm.aemeasurable, lintegral_fintype]
  simp only [PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _), Fintype.card_fin]
  have hc : ∀ τ : Fin (m + 1), (Fintype.card ({τ} : Set (Fin (m + 1))) : ℝ≥0∞) = 1 := by
    intro τ; simp
  simp only [hc, one_div]
  have higap : ∀ n, Integrable (fun ξ => f (sgdSeq g η x0 ξ n) - f u) Pω := fun n =>
    (run_step H hg hη.le ht hlam0 hq.le hstep x0 n
      (run_bound H hg hη.le ht hlam0 hq hq1 hC hstep x0 n).1).2.1
  have hj : ∀ τ : Fin (m + 1), ∫⁻ ξ, ENNReal.ofReal (f (sgdSeq g η x0 ξ (a + τ.val)) - f u) ∂Pω =
      ENNReal.ofReal (∫ ξ, (f (sgdSeq g η x0 ξ (a + τ.val)) - f u) ∂Pω) := by
    intro τ
    rw [ofReal_integral_eq_lintegral_ofReal (higap _)
      (Filter.Eventually.of_forall fun _ => sub_nonneg.mpr (H.min (mem_univ _)))]
  simp_rw [hj]
  have hnn : ∀ i, 0 ≤ ∫ ξ, (f (sgdSeq g η x0 ξ i) - f u) ∂Pω :=
    fun i => integral_nonneg fun _ => sub_nonneg.mpr (H.min (mem_univ _))
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun τ _ => hnn _)]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∫ ξ, (f (sgdSeq g η x0 ξ (a + k)) - f u) ∂Pω)]
  set S := ∑ k ∈ Finset.range (m + 1), ∫ ξ, (f (sgdSeq g η x0 ξ (a + k)) - f u) ∂Pω
  have hM : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hinv : (((m + 1 : ℕ) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / ((m : ℝ) + 1)) := by
    rw [ENNReal.ofReal_div_of_pos hM, ENNReal.ofReal_one, one_div]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]
    simp
  have hS : 0 ≤ S := Finset.sum_nonneg fun k _ => hnn _
  rw [hinv, ← ENNReal.ofReal_mul hS]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_one_div]
  have hw := window_sum H hg hη.le ht hlam0 hq hq1 hC hstep x0 a (m + 1)
  have hp : 0 ≤ ∫ ξ, pot f u lam t (sgdSeq g η x0 ξ (a + (m + 1))) ∂Pω :=
    integral_nonneg fun _ => pot_nonneg hlam0 ht _
  rw [← Finset.mul_sum] at hw
  have hb := (run_bound H hg hη.le ht hlam0 hq hq1 hC hstep x0 a).2.trans hwarm
  have hs : η / 2 * S ≤ W + (m + 1) * C := by
    push_cast at hw
    linarith
  have hs' : S ≤ 2 * W / η + (m + 1) * (2 * C / η) := by
    have hscaled : η * S ≤ η * (2 * W / η + (m + 1) * (2 * C / η)) := by
      calc
        η * S ≤ 2 * (W + (m + 1) * C) := by linarith
        _ = η * (2 * W / η + (m + 1) * (2 * C / η)) := by field_simp
    exact le_of_mul_le_mul_left hscaled hη
  have hh := div_le_div_of_nonneg_right hs' hM.le
  have he : (2 * W / η + (m + 1) * (2 * C / η)) / (m + 1) =
      2 * W / η / (m + 1) + 2 * C / η := by field_simp
  exact (hh.trans_eq he).trans hacc

end OracleTemplate.RobustPLProcess
