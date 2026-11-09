import LongTails.Proofs.FullRangeEstimator
import LongTails.Proofs.FullRangeLaw
import LongTails.Proofs.FiniteVarianceBatch

open MeasureTheory
open scoped RealInnerProductSpace BigOperators ENNReal

namespace LongTails.Proofs.FullRangeCertificate

open OracleTemplate.StochasticCohypomonotone
open LongTails.Algorithms.FullRangeMlmc
open LongTails.Setups.StochasticGeneralizedMonotone (IsStochasticOperator)
open LongTails.Proofs.FullRangeInner LongTails.Proofs.FullRangeEstimator

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
variable {F : E → E} {G : E → Set E} {J : ℝ → E → E} {L ρ η : ℝ}

lemma integral_le_sqrt {W : Type*} [MeasurableSpace W] (Q : Measure W) [IsProbabilityMeasure Q]
    {f : W → ℝ} (_hf0 : ∀ w, 0 ≤ f w) (hfi : Integrable f Q) (hf2 : Integrable (fun w => f w ^ 2) Q)
    {M : ℝ} (hM : (∫ w, f w ^ 2 ∂Q) ≤ M) : (∫ w, f w ∂Q) ≤ Real.sqrt M := by
  have hM0 : 0 ≤ M := (integral_nonneg fun w => sq_nonneg (f w)).trans hM
  have key (t : ℝ) (ht : 0 < t) : (∫ w, f w ∂Q) ≤ (M / t + t) / 2 := by
    have hpt (w : W) : f w ≤ (f w ^ 2 / t + t) / 2 := by
      have : 0 ≤ (f w - t) ^ 2 / t := by positivity
      have e : (f w ^ 2 / t + t) / 2 - f w = (f w - t) ^ 2 / (2 * t) := by field_simp; ring
      nlinarith [div_nonneg (sq_nonneg (f w - t)) (by positivity : (0 : ℝ) ≤ 2 * t)]
    have hR : Integrable (fun w => (f w ^ 2 / t + t) / 2) Q :=
      ((hf2.div_const t).add (integrable_const t)).div_const 2
    refine (integral_mono hfi hR hpt).trans ?_
    rw [integral_div, integral_add (hf2.div_const t) (integrable_const t), integral_div]
    simp only [integral_const, probReal_univ, one_smul]
    have := div_le_div_of_nonneg_right hM ht.le
    linarith
  rcases hM0.lt_or_eq with hpos | hzero
  · have hs := Real.sqrt_pos.mpr hpos
    have := key (Real.sqrt M) hs
    have e : (M / Real.sqrt M + Real.sqrt M) / 2 = Real.sqrt M := by
      have hs2 : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM0
      field_simp
      nlinarith
    linarith
  · subst hzero
    rw [Real.sqrt_zero]
    by_contra h
    push Not at h
    have := key ((∫ w, f w ∂Q)) h
    simp at this
    linarith

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
include ρ in
lemma certificate_pathwise (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) (hηL1 : η * L ≤ 1)
    (y zhat Fhat : E) :
    let p := y - η • Fhat
    let xb := J η p
    ‖F xb + η⁻¹ • (p - xb)‖ ≤
      3 * ‖Fhat - F zhat‖ + 3 * L * ‖zhat - resH H hη hηL y‖ + ‖y - resH H hη hηL y‖ / η := by
  intro p xb
  set zs := resH H hη hηL y
  have hzs : J η (y - η • F zs) = zs := H.resH_eq hη hηL y
  have hL := H.L_pos
  have hx : ‖xb - zs‖ ≤ η * ‖Fhat - F zs‖ := by
    have := H.res_nonexp hη p (y - η • F zs)
    rw [hzs] at this
    have e : p - (y - η • F zs) = η • (F zs - Fhat) := by simp only [p]; rw [smul_sub]; abel
    rw [e, norm_smul, Real.norm_of_nonneg hη.le] at this
    rw [show xb = J η p from rfl, norm_sub_rev Fhat]
    exact this
  set e := ‖Fhat - F zs‖ with he
  have he2 : e ≤ ‖Fhat - F zhat‖ + L * ‖zhat - zs‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub Fhat (F zhat) (F zs)
    have hl := H.lip zhat zs
    linarith
  have hid : F xb + η⁻¹ • (p - xb) = (F xb - F zs) + (F zs - Fhat) + η⁻¹ • (y - zs) + η⁻¹ • (zs - xb) := by
    simp only [p, smul_sub, smul_smul, inv_mul_cancel₀ hη.ne', one_smul]
    abel
  rw [hid]
  have h1 : ‖F xb - F zs‖ ≤ L * (η * e) := (H.lip _ _).trans (mul_le_mul_of_nonneg_left hx hL.le)
  have h2 : ‖η⁻¹ • (y - zs)‖ = ‖y - zs‖ / η := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hη.le)]
    field_simp
  have h3 : ‖η⁻¹ • (zs - xb)‖ ≤ e := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hη.le), norm_sub_rev]
    rw [inv_mul_le_iff₀ hη]
    linarith
  have h4 : ‖F zs - Fhat‖ = e := by rw [he, norm_sub_rev]
  have hsum := norm_add_le ((F xb - F zs) + (F zs - Fhat) + η⁻¹ • (y - zs)) (η⁻¹ • (zs - xb))
  have hsum2 := norm_add_le ((F xb - F zs) + (F zs - Fhat)) (η⁻¹ • (y - zs))
  have hsum3 := norm_add_le (F xb - F zs) (F zs - Fhat)
  have he0 : 0 ≤ e := norm_nonneg _
  have hLe : L * (η * e) ≤ e := by nlinarith [mul_le_mul_of_nonneg_right hηL1 he0]
  nlinarith [mul_le_mul_of_nonneg_left he2 (show (0 : ℝ) ≤ 3 by norm_num)]

noncomputable def certFhat (g : E → Ω → E) (zhat : E) (T B : ℕ) (ξ : ℕ → Ω) : E :=
  (1 / (B : ℝ)) • ∑ i : Fin B, g zhat (ξ (T + i))

lemma batch_error (g : E → Ω → E) (p : ProbabilityMeasure Ω) {σ : ℝ} (hσ : 0 ≤ σ)
    (hg : IsStochasticOperator (p : Measure Ω) F g σ) (z : E) (T B : ℕ) (hB : 0 < B) :
    Integrable (fun ξ => ‖certFhat g z T B ξ - F z‖) (Measure.infinitePi fun _ : ℕ => (p : Measure Ω)) ∧
    (∫ ξ, ‖certFhat g z T B ξ - F z‖ ∂Measure.infinitePi fun _ : ℕ => (p : Measure Ω)) ≤
      σ / Real.sqrt B := by
  let μ := Measure.infinitePi fun _ : ℕ => (p : Measure Ω)
  have hgz : Measurable (g z) := hg.measurable.comp measurable_prodMk_left
  have hv := OracleTemplate.RobustGradient.finite_mean_variance (P := (p : Measure Ω)) hgz
    (hg.integrable z) (F z) (hg.variance_integrable z) (hg.unbiased z) B hB
  let h : (Fin B → Ω) → ℝ := fun w => ‖(1 / (B : ℝ)) • ∑ i, g z (w i) - F z‖
  have hm : Measurable h := by
    have : Measurable (fun w : Fin B → Ω => ∑ i, g z (w i)) :=
      Finset.measurable_sum _ fun i _ => hgz.comp (measurable_pi_apply i)
    exact ((this.const_smul _).sub measurable_const).norm
  have hmap : MeasurePreserving (fun ξ : ℕ → Ω => fun i : Fin B => ξ (T + i)) μ
      (Measure.pi fun _ : Fin B => (p : Measure Ω)) := by
    have h1 := LongTails.Proofs.FullRangeLaw.shift_measurable (Ω := Ω) T
    have hs : MeasurePreserving (LongTails.Proofs.FullRangeLaw.shift (Ω := Ω) T) μ μ := by
      have := OracleTemplate.StochasticGeneralized.splitStream_preserving (p : Measure Ω) T
      exact measurePreserving_snd.comp this
    exact (OracleTemplate.StochasticGeneralized.prefix_preserving (p : Measure Ω) B).comp hs
  have hcomp (ξ : ℕ → Ω) : ‖certFhat g z T B ξ - F z‖ = h (fun i : Fin B => ξ (T + i)) := rfl
  have hhi : Integrable h (Measure.pi fun _ : Fin B => (p : Measure Ω)) := by
    have hb : Integrable (fun w : Fin B → Ω => h w ^ 2 + 1) (Measure.pi fun _ : Fin B => (p : Measure Ω)) :=
      hv.1.add (integrable_const 1)
    refine hb.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    nlinarith [sq_nonneg (h w - 1), norm_nonneg ((1 / (B : ℝ)) • ∑ i, g z (w i) - F z)]
  simp_rw [hcomp]
  refine ⟨hmap.integrable_comp_of_integrable hhi, ?_⟩
  have hchg := integral_map (μ := μ) hmap.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hmap.map_eq] at hchg
  rw [← hchg]
  · have hsq : (∫ w, h w ^ 2 ∂Measure.pi fun _ : Fin B => (p : Measure Ω)) ≤ σ ^ 2 / B := by
      have := hv.2
      simp only [h] at this ⊢
      rw [this]
      exact div_le_div_of_nonneg_right (hg.variance z) (Nat.cast_nonneg B)
    have := integral_le_sqrt (Measure.pi fun _ : Fin B => (p : Measure Ω)) (fun w => norm_nonneg _)
      hhi hv.1 hsq
    rwa [Real.sqrt_div' _ (Nat.cast_nonneg B), Real.sqrt_sq hσ] at this

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω] in
lemma innerPath_dep (g : E → Ω → E) (η γ0 : ℝ) (n0 : ℕ) (x : E) (k : ℕ) (ξ ξ' : ℕ → Ω)
    (h : ∀ i < k, ξ i = ξ' i) : innerPath J g η γ0 n0 x k ξ = innerPath J g η γ0 n0 x k ξ' := by
  unfold innerPath
  congr 2
  funext i
  exact h i i.2

noncomputable def certResidual (F : E → E) (J : ℝ → E → E) (g : E → Ω → E) (η γ0 : ℝ) (n0 T B : ℕ)
    (y : E) (ξ : ℕ → Ω) : ℝ :=
  let zhat := innerPath J g η γ0 n0 y T ξ
  let p := y - η • certFhat g zhat T B ξ
  ‖F (J η p) + η⁻¹ • (p - J η p)‖

include ρ in
theorem cert_expectation (H : OpHyp F G J L ρ) (hη : 0 < η) (hηL : η * L < 1) {σ γ0 : ℝ} {n0 : ℕ}
    (p : ProbabilityMeasure Ω) (g : E → Ω → E) (hσ : 0 ≤ σ)
    (hg : IsStochasticOperator (p : Measure Ω) F g σ)
    (hγ0 : 0 < γ0) (hγ0s : γ0 * (1 + η * L) ^ 2 ≤ 1 - η * L) (y : E) (T B : ℕ) (hB : 0 < B) :
    Integrable (certResidual F J g η γ0 n0 T B y) (Measure.infinitePi fun _ : ℕ => (p : Measure Ω)) ∧
    (∫ ξ, certResidual F J g η γ0 n0 T B y ξ ∂Measure.infinitePi fun _ : ℕ => (p : Measure Ω)) ≤
      3 * (σ / Real.sqrt B) + 3 * L * Real.sqrt (mse H hη hηL γ0 n0 p g y T) +
        ‖y - resH H hη hηL y‖ / η := by
  let μ := Measure.infinitePi fun _ : ℕ => (p : Measure Ω)
  set zs := resH H hη hηL y
  have hL := H.L_pos
  have hηL1 : η * L ≤ 1 := hηL.le
  let Z : (ℕ → Ω) → E := innerPath J g η γ0 n0 y T
  have hZm : Measurable Z := innerPath_measurable H hη g y hγ0 hg.measurable T
  have hZ2 := path_integrable H hη hηL (n0 := n0) p g y hγ0 hγ0s hg T
  have hFl : Continuous F := (LipschitzWith.of_dist_le_mul (K := Real.toNNReal L) (by
    intro a b
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL.le]
    exact H.lip a b)).continuous
  have hJc : Continuous (J η) := (LipschitzWith.of_dist_le_mul (K := 1) (by
    intro a b
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using H.res_nonexp hη a b)).continuous
  have hFh : Measurable (fun ξ => certFhat g (Z ξ) T B ξ) := by
    unfold certFhat
    refine (Finset.measurable_sum _ fun i _ => ?_).const_smul _
    exact hg.measurable.comp (hZm.prodMk (measurable_pi_apply _))
  have hRm : Measurable (certResidual F J g η γ0 n0 T B y) := by
    unfold certResidual
    have hp : Measurable (fun ξ => y - η • certFhat g (Z ξ) T B ξ) := measurable_const.sub (hFh.const_smul _)
    exact ((hFl.measurable.comp (hJc.measurable.comp hp)).add
      ((hp.sub (hJc.measurable.comp hp)).const_smul _)).norm
  have hpt (ξ : ℕ → Ω) : certResidual F J g η γ0 n0 T B y ξ ≤
      3 * ‖certFhat g (Z ξ) T B ξ - F (Z ξ)‖ + 3 * L * ‖Z ξ - zs‖ + ‖y - zs‖ / η :=
    certificate_pathwise H hη hηL hηL1 y (Z ξ) (certFhat g (Z ξ) T B ξ)
  have hA : ∫⁻ ξ, ENNReal.ofReal ‖certFhat g (Z ξ) T B ξ - F (Z ξ)‖ ∂μ ≤
      ENNReal.ofReal (σ / Real.sqrt B) := by
    have hsplit := LongTails.Proofs.FullRangeLaw.split_lintegral (p : Measure Ω) T Z hZm
      (fun ξ ξ' h => innerPath_dep g η γ0 n0 y T ξ ξ' h)
      (fun w => ENNReal.ofReal ‖certFhat g w.1 0 B w.2 - F w.1‖) (by
        apply ENNReal.measurable_ofReal.comp
        unfold certFhat
        refine (((Finset.measurable_sum _ fun i _ => ?_).const_smul _).sub
          (hFl.measurable.comp measurable_fst)).norm
        exact hg.measurable.comp (measurable_fst.prodMk
          ((measurable_pi_apply _).comp measurable_snd)))
    have he (ξ : ℕ → Ω) : certFhat g (Z ξ) T B ξ =
        certFhat g (Z ξ) 0 B (LongTails.Proofs.FullRangeLaw.shift T ξ) := by
      simp [certFhat, LongTails.Proofs.FullRangeLaw.shift]
    simp_rw [he]
    rw [hsplit]
    calc _ ≤ ∫⁻ _, ENNReal.ofReal (σ / Real.sqrt B) ∂μ := by
          refine lintegral_mono fun ξ => ?_
          have hb := batch_error g p hσ hg (Z ξ) 0 B hB
          rw [← ofReal_integral_eq_lintegral_ofReal hb.1
            (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal hb.2
      _ = _ := by simp
  have hZ1 : Integrable (fun ξ => ‖Z ξ - zs‖) μ := by
    have hb : Integrable (fun ξ => ‖Z ξ - zs‖ ^ 2 + 1) μ := hZ2.add (integrable_const 1)
    refine hb.mono' (hZm.sub measurable_const).norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    nlinarith [sq_nonneg (‖Z ξ - zs‖ - 1)]
  have hZb : (∫ ξ, ‖Z ξ - zs‖ ∂μ) ≤ Real.sqrt (mse H hη hηL γ0 n0 p g y T) :=
    integral_le_sqrt μ (fun _ => norm_nonneg _) hZ1 hZ2 le_rfl
  have hB1m : Measurable (fun ξ => ‖certFhat g (Z ξ) T B ξ - F (Z ξ)‖) :=
    (hFh.sub (hFl.measurable.comp hZm)).norm
  have hB1 : Integrable (fun ξ => ‖certFhat g (Z ξ) T B ξ - F (Z ξ)‖) μ := by
    refine ⟨hB1m.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => norm_nonneg _)]
    exact hA.trans_lt ENNReal.ofReal_lt_top
  have hB1b : (∫ ξ, ‖certFhat g (Z ξ) T B ξ - F (Z ξ)‖ ∂μ) ≤ σ / Real.sqrt B := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hB1m.aestronglyMeasurable]
    have hσB : 0 ≤ σ / Real.sqrt B := by positivity
    exact (ENNReal.toReal_le_of_le_ofReal hσB hA)
  have hR : Integrable (fun ξ => 3 * ‖certFhat g (Z ξ) T B ξ - F (Z ξ)‖ + 3 * L * ‖Z ξ - zs‖ +
      ‖y - zs‖ / η) μ := ((hB1.const_mul 3).add (hZ1.const_mul _)).add (integrable_const _)
  have hRi : Integrable (certResidual F J g η γ0 n0 T B y) μ :=
    hR.mono' hRm.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (show 0 ≤ certResidual F J g η γ0 n0 T B y ξ from norm_nonneg _)]
      exact hpt ξ)
  refine ⟨hRi, (integral_mono hRi hR hpt).trans ?_⟩
  rw [integral_add (f := fun ξ => 3 * ‖certFhat g (Z ξ) T B ξ - F (Z ξ)‖ + 3 * L * ‖Z ξ - zs‖)
      (g := fun _ => ‖y - zs‖ / η) ((hB1.const_mul 3).add (hZ1.const_mul _)) (integrable_const _),
    integral_add (f := fun ξ => 3 * ‖certFhat g (Z ξ) T B ξ - F (Z ξ)‖)
      (g := fun ξ => 3 * L * ‖Z ξ - zs‖) (hB1.const_mul 3) (hZ1.const_mul _),
    integral_const_mul, integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  have h1 := mul_le_mul_of_nonneg_left hB1b (show (0 : ℝ) ≤ 3 by norm_num)
  have h2 := mul_le_mul_of_nonneg_left hZb (show 0 ≤ 3 * L by positivity)
  linarith

end LongTails.Proofs.FullRangeCertificate
