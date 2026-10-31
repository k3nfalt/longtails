import LongTails.Proofs.MultiplicativeRobustMoments
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory
open LongTails.Proofs.HilbertSmallMoments

namespace OracleTemplate.MultiplicativeRobustEstimator

lemma normalization_coefficient {p B ρ : ℝ} (hB : 0 < B)
    (hb : 4*65536^p*ρ ≤ B^(p-1)) :
    4*B^(1-p)*ρ ≤ (1/65536 : ℝ)^p := by
  have hpB : 0 < B^(p-1) := Real.rpow_pos_of_pos hB _
  have hpc : (0 : ℝ) < 65536^p := Real.rpow_pos_of_pos (by norm_num) _
  rw [show 1-p = -(p-1) by ring, Real.rpow_neg hB.le]
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 65536),
    Real.one_rpow]
  apply (le_div_iff₀ hpc).mpr
  apply (mul_le_mul_iff_right₀ hpB).mp
  convert hb using 1 <;> field_simp

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
lemma split_last_measurePreserving (n : ℕ) :
    MeasurePreserving (fun ξ : Fin (n+1) → Ω => ((fun i : Fin n => ξ i.castSucc),ξ (Fin.last n)))
      (Measure.pi fun _ => P) ((Measure.pi fun _ : Fin n => P).prod P) := by
  have h := (Measure.measurePreserving_swap (μ := P) (ν := Measure.pi fun _ : Fin n => P)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => P) (Fin.last n))
  convert h using 1
  ext ξ <;> simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.init]


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma normalized_batch_moment {X : Ω → E} (hX : Measurable X) (u : E)
    {p ρ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hi : Integrable X P)
    (hmean : ∫ ω, X ω ∂P = u)
    (hpi : Integrable (fun ω => ‖X ω-u‖^p) P)
    (hm : (∫ ω, ‖X ω-u‖^p ∂P) ≤ ρ*‖u‖^p)
    (b : ℕ) (hb : 4*65536^p*ρ ≤ (b+1 : ℝ)^(p-1)) :
    Integrable (fun ξ : Fin (b+1) → Ω => ‖blockMean (fun i => X (ξ i))-u‖^p)
      (Measure.pi fun _ => P) ∧
    (∫ ξ : Fin (b+1) → Ω, ‖blockMean (fun i => X (ξ i))-u‖^p
      ∂Measure.pi fun _ => P) ≤ (‖u‖/65536)^p := by
  have h := iid_centered_mean_power_bound hX hp hp2 hi u hpi hmean (b+1) (by omega)
  have hcoef := normalization_coefficient (by positivity : (0 : ℝ) < b+1) hb
  refine ⟨by simpa only [blockMean, Nat.cast_add, Nat.cast_one] using h.1, ?_⟩
  change (∫ ξ : Fin (b+1) → Ω, ‖((b+1 : ℝ)⁻¹) • ∑ i, X (ξ i)-u‖^p
    ∂Measure.pi fun _ => P) ≤ _
  have hbase : (∫ ξ : Fin (b+1) → Ω, ‖((b+1 : ℝ)⁻¹) • ∑ i, X (ξ i)-u‖^p
      ∂Measure.pi fun _ => P) ≤ 4*(b+1 : ℝ)^(1-p)*(ρ*‖u‖^p) := by
    simpa only [Nat.cast_add, Nat.cast_one] using h.2.trans
      (mul_le_mul_of_nonneg_left hm (by positivity))
  calc
    _ ≤ 4*(b+1 : ℝ)^(1-p)*(ρ*‖u‖^p) := hbase
    _ = (4*(b+1 : ℝ)^(1-p)*ρ)*‖u‖^p := by ring
    _ ≤ (1/65536 : ℝ)^p*‖u‖^p :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (norm_nonneg _) _)
    _ = _ := by rw [← Real.mul_rpow (by norm_num) (norm_nonneg _)]; congr 1; ring

omit [CompleteSpace E] in
lemma measurable_blockMean {b : ℕ} : Measurable (blockMean (E := E) (b := b)) := by
  unfold blockMean
  fun_prop

omit [CompleteSpace E] in
lemma measurable_estimate {k b : ℕ} (Λ : ℝ) :
    Measurable (estimate (E := E) (k := k) (b := b) Λ) := by
  have hd : Measurable (fun v : Fin (k+2) → Fin (b+1) → E =>
      medoid (fun i : Fin (k+1) => blockMean (v i.castSucc))) :=
    measurable_medoid.comp (Measurable.of_eval (fun i =>
      measurable_blockMean.comp (measurable_pi_apply i.castSucc)))
  exact hd.prodMk (measurable_variable_clip.comp
    ((measurable_const.mul hd.norm).prodMk
      (measurable_blockMean.comp (measurable_pi_apply (Fin.last (k+1))))))

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [IsProbabilityMeasure P] in
lemma ae_eq_of_zero_power {X : Ω → E} (u : E) {p : ℝ} (hp : p ≠ 0)
    (hi : Integrable (fun ω => ‖X ω-u‖^p) P)
    (hm : (∫ ω, ‖X ω-u‖^p ∂P) ≤ 0) : X =ᵐ[P] fun _ => u := by
  have hz : (∫ ω, ‖X ω-u‖^p ∂P) = 0 :=
    le_antisymm hm (integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg _) _))
  have h := (integral_eq_zero_iff_of_nonneg
    (fun ω => Real.rpow_nonneg (norm_nonneg (X ω-u)) p) hi).mp hz
  filter_upwards [h] with ω hω
  exact sub_eq_zero.mp (norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg _) hp).mp hω))

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma blockMean_const (b : ℕ) (u : E) : blockMean (fun _ : Fin (b+1) => u) = u := by
  simp only [blockMean, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_add, Nat.cast_one]
  rw [inv_mul_cancel₀ (by positivity : (b+1 : ℝ) ≠ 0), one_smul]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma estimate_const {Λ : ℝ} (hΛ : 1 ≤ Λ) (k b : ℕ) (u : E) :
    estimate Λ (fun (_ : Fin (k+2)) (_ : Fin (b+1)) => u) = (u,u) := by
  have hc : clip (4*Λ*‖u‖) u = u := clip_eq_self (by nlinarith [norm_nonneg u])
  simp only [estimate, blockMean_const, medoid, hc]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma estimate_ae_const {X : Ω → E} (u : E) (hae : X =ᵐ[P] fun _ => u)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (k b : ℕ) :
    (fun ξ : Fin (k+2) → Fin (b+1) → Ω => estimate Λ (fun i j => X (ξ i j))) =ᵐ[
      Measure.pi fun _ => Measure.pi fun _ => P] fun _ => (u,u) := by
  have hrow := Measure.ae_eq_pi (fun _ : Fin (b+1) => hae)
  have hmatrix := Measure.ae_eq_pi (fun _ : Fin (k+2) => hrow)
  filter_upwards [hmatrix] with ξ hξ
  rw [hξ]
  exact estimate_const hΛ k b u

omit [CompleteSpace E] in
lemma row_estimator_moments {X : Ω → E} (hX : Measurable X) (u : E)
    {p Λ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hΛ : 1 ≤ Λ) (hu : 0 < ‖u‖)
    (hi : Integrable X P) (hmean : ∫ ω, X ω ∂P = u)
    (hpi : Integrable (fun ω => ‖X ω-u‖^p) P)
    (hm : (∫ ω, ‖X ω-u‖^p ∂P) ≤ (‖u‖/65536)^p)
    (n : ℕ) (hn : 8 ≤ n+1) (hprob : (1/2 : ℝ)^(n+1) ≤ Λ^(1-p)/64) :
    let Q := Measure.pi (fun _ : Fin (n+2) => P)
    let d := fun ξ : Fin (n+2) → Ω => medoid (fun i : Fin (n+1) => X (ξ i.castSucc))
    let v := fun ξ : Fin (n+2) → Ω => clip (4*Λ*‖d ξ‖) (X (ξ (Fin.last (n+1))))
    Integrable v Q ∧ Integrable (fun ξ => ‖d ξ-u‖^2) Q ∧
    Integrable (fun ξ => ‖v ξ‖^2) Q ∧
    (∫ ξ, ‖d ξ-u‖^2 ∂Q) ≤ ‖u‖^2/64 ∧
    (∫ ξ, ‖v ξ‖^2 ∂Q) ≤ 32*Λ^(2-p)*‖u‖^2 ∧
    ‖(∫ ξ, v ξ ∂Q)-u‖ ≤ Λ^(1-p)/16*‖u‖ := by
  let Q := Measure.pi (fun _ : Fin (n+2) => P)
  let R := Measure.pi (fun _ : Fin (n+1) => P)
  let d' := fun ξ : Fin (n+1) → Ω => medoid (fun i => X (ξ i))
  let v' := fun w : (Fin (n+1) → Ω) × Ω => clip (4*Λ*‖d' w.1‖) (X w.2)
  have ho := normalized_oracle_moments hX u hp hp2 hi hpi hm
  have hbad : R.real {ξ | ‖u‖/2 < ‖d' ξ-u‖} ≤ Λ^(1-p)/64 := by
    have h := normalized_medoid_failure hX u hu (hi.sub (integrable_const u)).norm ho.1 n
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    have hb : R.real {ξ | ‖u‖/2 < ‖d' ξ-u‖} ≤ (1/2 : ℝ)^(n+1) := by
      simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (1/2)^(n+1))] using ht
    exact hb.trans hprob
  have hbi := normalized_mirror_bias hX u hp hp2 hΛ hu hi hmean hpi hm n hbad
  have hvm := normalized_mirror_second_moment hX u hp hp2 hΛ hi hpi hm n hn
  have hdm := normalized_medoid_second_moment hX u (hi.sub (integrable_const u)).norm ho.1 n hn
  have hs := split_last_measurePreserving (P := P) (n+1)
  let split : (Fin (n+2) → Ω) → (Fin (n+1) → Ω) × Ω :=
    fun ξ => ((fun i => ξ i.castSucc),ξ (Fin.last (n+1)))
  have hl : ProbabilityTheory.HasLaw split (R.prod P) Q := ⟨hs.measurable.aemeasurable,hs.map_eq⟩
  have hvi : Integrable v' (R.prod P) := hbi.1
  have hv2i : Integrable (fun w => ‖v' w‖^2) (R.prod P) := hvm.1
  have hdi : Integrable (fun w : (Fin (n+1) → Ω) × Ω => ‖d' w.1-u‖^2) (R.prod P) :=
    hdm.1.comp_fst P
  have heV : (∫ ξ, v' (split ξ) ∂Q) = ∫ w, v' w ∂R.prod P :=
    hl.integral_comp hvi.aestronglyMeasurable
  have heV2 : (∫ ξ, ‖v' (split ξ)‖^2 ∂Q) = ∫ w, ‖v' w‖^2 ∂R.prod P :=
    hl.integral_comp hv2i.aestronglyMeasurable
  have heD : (∫ ξ, ‖d' (split ξ).1-u‖^2 ∂Q) = ∫ ξ, ‖d' ξ-u‖^2 ∂R := by
    calc
      _ = ∫ w : (Fin (n+1) → Ω) × Ω, ‖d' w.1-u‖^2 ∂R.prod P :=
        hl.integral_comp hdi.aestronglyMeasurable
      _ = _ := by
        rw [integral_fun_fst (μ := R) (ν := P) (fun ξ => ‖d' ξ-u‖^2)]
        simp
  refine ⟨hl.integrable_comp hvi, hl.integrable_comp hdi, hl.integrable_comp hv2i, ?_, ?_, ?_⟩
  · change (∫ ξ, ‖d' (split ξ).1-u‖^2 ∂Q) ≤ _
    rw [heD]
    exact hdm.2
  · change (∫ ξ, ‖v' (split ξ)‖^2 ∂Q) ≤ _
    rw [heV2]
    exact hvm.2
  · change ‖(∫ ξ, v' (split ξ) ∂Q)-u‖ ≤ _
    rw [heV]
    exact hbi.2

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma exact_estimate_moments {X : Ω → E} (u : E) (hae : X =ᵐ[P] fun _ => u)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (k b : ℕ) :
    let Q := Measure.pi (fun _ : Fin (k+2) => Measure.pi fun _ : Fin (b+1) => P)
    let e := fun ξ : Fin (k+2) → Fin (b+1) → Ω => estimate Λ (fun i j => X (ξ i j))
    Integrable (fun ξ => (e ξ).2) Q ∧
    Integrable (fun ξ => ‖(e ξ).1-u‖^2) Q ∧
    Integrable (fun ξ => ‖(e ξ).2‖^2) Q ∧
    (∫ ξ, (e ξ).2 ∂Q) = u ∧
    (∫ ξ, ‖(e ξ).1-u‖^2 ∂Q) = 0 ∧
    (∫ ξ, ‖(e ξ).2‖^2 ∂Q) = ‖u‖^2 := by
  let Q := Measure.pi (fun _ : Fin (k+2) => Measure.pi fun _ : Fin (b+1) => P)
  let e := fun ξ : Fin (k+2) → Fin (b+1) → Ω => estimate Λ (fun i j => X (ξ i j))
  have he := estimate_ae_const u hae hΛ k b
  have hv : (fun ξ => (e ξ).2) =ᵐ[Q] fun _ => u := he.fun_comp Prod.snd
  have hd2 : (fun ξ => ‖(e ξ).1-u‖^2) =ᵐ[Q] fun _ => (0 : ℝ) := by
    filter_upwards [he] with ξ hξ
    change ‖(estimate Λ (fun i j => X (ξ i j))).1-u‖^2 = 0
    rw [hξ]
    simp
  have hv2 : (fun ξ => ‖(e ξ).2‖^2) =ᵐ[Q] fun _ => ‖u‖^2 :=
    he.fun_comp (fun v : E × E => ‖v.2‖^2)
  refine ⟨(integrable_const u).congr hv.symm, (integrable_const (0 : ℝ)).congr hd2.symm,
    (integrable_const (‖u‖^2)).congr hv2.symm, ?_, ?_, ?_⟩
  · rw [integral_congr_ae hv]
    simp
  · rw [integral_congr_ae hd2]
    simp
  · rw [integral_congr_ae hv2]
    simp

lemma batched_estimator_moments {X : Ω → E} (hX : Measurable X) (u : E)
    {p ρ Λ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hΛ : 1 ≤ Λ)
    (hi : Integrable X P) (hmean : ∫ ω, X ω ∂P = u)
    (hpi : Integrable (fun ω => ‖X ω-u‖^p) P)
    (hm : (∫ ω, ‖X ω-u‖^p ∂P) ≤ ρ*‖u‖^p)
    (k b : ℕ) (hk : 8 ≤ k+1) (hb : 4*65536^p*ρ ≤ (b+1 : ℝ)^(p-1))
    (hprob : (1/2 : ℝ)^(k+1) ≤ Λ^(1-p)/64) :
    let Q := Measure.pi (fun _ : Fin (k+2) => Measure.pi fun _ : Fin (b+1) => P)
    let e := fun ξ : Fin (k+2) → Fin (b+1) → Ω => estimate Λ (fun i j => X (ξ i j))
    Integrable (fun ξ => (e ξ).2) Q ∧
    Integrable (fun ξ => ‖(e ξ).1-u‖^2) Q ∧
    Integrable (fun ξ => ‖(e ξ).2‖^2) Q ∧
    (∫ ξ, ‖(e ξ).1-u‖^2 ∂Q) ≤ ‖u‖^2/64 ∧
    (∫ ξ, ‖(e ξ).2‖^2 ∂Q) ≤ 32*Λ^(2-p)*‖u‖^2 ∧
    ‖(∫ ξ, (e ξ).2 ∂Q)-u‖ ≤ Λ^(1-p)/16*‖u‖ := by
  by_cases hu : u = 0
  · clear hmean
    subst u
    have hm0 : (∫ ω, ‖X ω-(0 : E)‖^p ∂P) ≤ 0 := by
      simpa only [norm_zero, Real.zero_rpow (by linarith : p ≠ 0), mul_zero] using hm
    have he := exact_estimate_moments (0 : E)
      (ae_eq_of_zero_power (0 : E) (by linarith) hpi hm0) hΛ k b
    refine ⟨he.1, he.2.1, he.2.2.1, ?_, ?_, ?_⟩
    · rw [he.2.2.2.2.1]
      simp
    · rw [he.2.2.2.2.2]
      simp
    · rw [he.2.2.2.1]
      simp
  have hup : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let R := Measure.pi (fun _ : Fin (b+1) => P)
  let Y := fun ξ : Fin (b+1) → Ω => blockMean (fun i => X (ξ i))
  have hY : Measurable Y := measurable_blockMean.comp
    (Measurable.of_eval (fun i => hX.comp (measurable_pi_apply i)))
  have hYint := LightTail.finite_mean_integral hi (b+1) (by omega)
  have hYi : Integrable Y R := by
    simpa only [Y, blockMean, one_div, Nat.cast_add, Nat.cast_one] using hYint.1
  have hYm : (∫ ξ, Y ξ ∂R) = u := by
    have hh : (∫ ξ, Y ξ ∂R) = ∫ ω, X ω ∂P := by
      simpa only [Y, blockMean, one_div, Nat.cast_add, Nat.cast_one] using hYint.2
    exact hh.trans hmean
  have hYmoms := normalized_batch_moment hX u hp hp2 hi hmean hpi hm b hb
  have hrow := row_estimator_moments hY u hp hp2 hΛ hup hYi hYm
    hYmoms.1 hYmoms.2 k hk hprob
  simpa only [estimate] using hrow

end OracleTemplate.MultiplicativeRobustEstimator
