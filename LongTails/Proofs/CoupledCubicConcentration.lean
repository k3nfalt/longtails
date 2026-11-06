import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.RobustPilotConfidence
import LongTails.Proofs.ZerothOrderGridEstimator
import Mathlib.Probability.UniformOn

open MeasureTheory Classical
open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledCubicConcentration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma finite_centered_norm_sq_le {ι : Type*} [Fintype ι]
    (X : ι → E) (u : E) (hmean : ∑ i, X i = (Fintype.card ι : ℝ) • u) :
    ∑ i, ‖X i - u‖ ^ 2 ≤ ∑ i, ‖X i‖ ^ 2 := by
  have hi : ∑ i, ⟪X i, u⟫ = (Fintype.card ι : ℝ) * ‖u‖ ^ 2 := by
    rw [← sum_inner, hmean, real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp_rw [norm_sub_sq_real]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hi]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hh : 0 ≤ (Fintype.card ι : ℝ) * ‖u‖ ^ 2 := by positivity
  linarith

lemma finite_uniform_batch_second_moment {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (X : ι → E) (u : E) (hmean : ∑ i, X i = (Fintype.card ι : ℝ) • u)
    (b : ℕ) (hb : 0 < b) :
    (∫ ξ : Fin b → ι, ‖(1 / (b : ℝ)) • ∑ j, X (ξ j) - u‖ ^ 2
      ∂Measure.pi (fun _ : Fin b => (PMF.uniformOfFintype ι).toMeasure)) ≤
      ((Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖X i‖ ^ 2) / b := by
  let P := (PMF.uniformOfFintype ι).toMeasure
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hm : (∫ i, X i ∂P) = u := by
    rw [OracleTemplate.ZerothOrder.uniform_integral_explicit, hmean, smul_smul,
      inv_mul_cancel₀ hn, one_smul]
  have hh := OracleTemplate.RobustGradient.finite_mean_variance
    (P := P) (X := X) (measurable_of_finite X) (Integrable.of_finite) u
    (Integrable.of_finite) hm b hb
  rw [hh.2, OracleTemplate.ZerothOrder.uniform_integral_explicit]
  change ((Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖X i - u‖ ^ 2) / (b : ℝ) ≤ _
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (finite_centered_norm_sq_le X u hmean) (by positivity))
    (Nat.cast_nonneg b)


lemma finite_uniform_weighted_batch_bound {ι J : Type*} [Fintype ι] [Nonempty ι] [Fintype J]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (X : ι → J → E) (u : J → E) (w V : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hmean : ∀ j, ∑ i, X i j = (Fintype.card ι : ℝ) • u j)
    (hmoment : ∀ j, (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖X i j‖ ^ 2 ≤ V j)
    (b : ℕ) (hb : 0 < b) :
    (∫ ξ : Fin b → ι, ∑ j, w j * ‖(1 / (b : ℝ)) • ∑ k, X (ξ k) j - u j‖ ^ 2
      ∂Measure.pi (fun _ : Fin b => (PMF.uniformOfFintype ι).toMeasure)) ≤
      (∑ j, w j * V j) / b := by
  rw [integral_finsetSum _ (fun j _ => Integrable.of_finite), Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  rw [integral_const_mul]
  have hh := (finite_uniform_batch_second_moment (fun i => X i j) (u j) (hmean j) b hb).trans
    (div_le_div_of_nonneg_right (hmoment j) (Nat.cast_nonneg b))
  calc
    _ ≤ w j * (V j / b) := mul_le_mul_of_nonneg_left hh (hw j)
    _ = w j * V j / b := by ring


lemma finite_uniform_weighted_batch_tail {ι J : Type*} [Fintype ι] [Nonempty ι] [Fintype J]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (X : ι → J → E) (u : J → E) (w V : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hmean : ∀ j, ∑ i, X i j = (Fintype.card ι : ℝ) • u j)
    (hmoment : ∀ j, (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖X i j‖ ^ 2 ≤ V j)
    (b : ℕ) (hb : 0 < b) (τ : ℝ) (hτ : 0 < τ) :
    (Measure.pi (fun _ : Fin b => (PMF.uniformOfFintype ι).toMeasure)).real
      {ξ : Fin b → ι | τ < ∑ j, w j * ‖(1 / (b : ℝ)) • ∑ k, X (ξ k) j - u j‖ ^ 2} ≤
      (∑ j, w j * V j) / ((b : ℝ) * τ) := by
  let P := Measure.pi (fun _ : Fin b => (PMF.uniformOfFintype ι).toMeasure)
  let S : (Fin b → ι) → ℝ := fun ξ =>
    ∑ j, w j * ‖(1 / (b : ℝ)) • ∑ k, X (ξ k) j - u j‖ ^ 2
  have hnonneg (ξ : Fin b → ι) : 0 ≤ S ξ :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (sq_nonneg _)
  have hi : Integrable S P := Integrable.of_finite
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hnonneg) hi τ
  have hbound : (∫ ξ, S ξ ∂P) ≤ (∑ j, w j * V j) / b :=
    finite_uniform_weighted_batch_bound X u w V hw hmean hmoment b hb
  change P.real {ξ | τ < S ξ} ≤ _
  calc
    _ ≤ P.real {ξ | τ ≤ S ξ} := measureReal_mono (show {ξ | τ < S ξ} ⊆ {ξ | τ ≤ S ξ} from
      fun ξ h => (show τ < S ξ from h).le)
    _ ≤ ((∑ j, w j * V j) / b) / τ := by
      apply (le_div_iff₀ hτ).mpr
      linarith [hmarkov, hbound]
    _ = (∑ j, w j * V j) / ((b : ℝ) * τ) := by ring


omit [InnerProductSpace ℝ E] in
lemma finite_zero_of_second_moment {ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → E) (hzero : (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖X i‖ ^ 2 ≤ 0) (i : ι) :
    X i = 0 := by
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : ∑ j, ‖X j‖ ^ 2 ≤ 0 :=
    (mul_le_mul_iff_of_pos_left (inv_pos.mpr hn)).mp (by simpa using hzero)
  have hi : ‖X i‖ ^ 2 ≤ ∑ j, ‖X j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ‖X j‖) (Finset.mem_univ i)
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (X i)]

lemma finite_batch_error_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → E) (u : E) (hmean : ∑ i, X i = (Fintype.card ι : ℝ) • u)
    (hzero : (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖X i‖ ^ 2 ≤ 0)
    (b : ℕ) (ξ : Fin b → ι) : (1 / (b : ℝ)) • ∑ k, X (ξ k) - u = 0 := by
  have hX : ∀ i, X i = 0 := finite_zero_of_second_moment X hzero
  have hu : u = 0 := by
    have hh : (Fintype.card ι : ℝ) • u = 0 := hmean.symm.trans (by simp [hX])
    exact (smul_eq_zero.mp hh).resolve_left (by exact_mod_cast Fintype.card_ne_zero)
  simp [hX, hu]


lemma finite_uniform_relative_batch_tail {ι J : Type*} [Fintype ι] [Nonempty ι] [Fintype J]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (X : ι → J → E) (u : J → E) (c : J → ℝ) (V : ℝ) (hV : 0 ≤ V)
    (hmean : ∀ j, ∑ i, X i j = (Fintype.card ι : ℝ) • u j)
    (hmoment : ∀ j, (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖X i j‖ ^ 2 ≤ V * c j ^ 2)
    (b : ℕ) (hb : 0 < b) (η : ℝ) (hη : 0 < η) :
    (Measure.pi (fun _ : Fin b => (PMF.uniformOfFintype ι).toMeasure)).real
      {ξ : Fin b → ι | η ^ 2 <
        ∑ j, (c j)⁻¹ ^ 2 * ‖(1 / (b : ℝ)) • ∑ k, X (ξ k) j - u j‖ ^ 2} ≤
      (Fintype.card J : ℝ) * V / ((b : ℝ) * η ^ 2) := by
  have ht := finite_uniform_weighted_batch_tail X u (fun j => (c j)⁻¹ ^ 2)
    (fun j => V * c j ^ 2) (fun j => sq_nonneg _) hmean hmoment b hb (η ^ 2)
    (sq_pos_of_pos hη)
  have hs : ∑ j, (c j)⁻¹ ^ 2 * (V * c j ^ 2) ≤ (Fintype.card J : ℝ) * V := by
    calc
      _ ≤ ∑ _j : J, V := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hc : c j = 0
        · simpa only [hc, inv_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul] using hV
        · have he : (c j)⁻¹ ^ 2 * (V * c j ^ 2) = V := by field_simp
          exact he.le
      _ = _ := by simp
  exact ht.trans (div_le_div_of_nonneg_right hs (by positivity))

lemma finite_relative_batch_coordinate {ι J : Type*} [Fintype ι] [Nonempty ι] [Fintype J]
    (X : ι → J → E) (u : J → E) (c : J → ℝ) (V η : ℝ) (hη : 0 ≤ η)
    (hmean : ∀ j, ∑ i, X i j = (Fintype.card ι : ℝ) • u j)
    (hmoment : ∀ j, (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖X i j‖ ^ 2 ≤ V * c j ^ 2)
    (b : ℕ) (ξ : Fin b → ι)
    (hscore : ∑ j, (c j)⁻¹ ^ 2 * ‖(1 / (b : ℝ)) • ∑ k, X (ξ k) j - u j‖ ^ 2 ≤ η ^ 2)
    (j : J) : ‖(1 / (b : ℝ)) • ∑ k, X (ξ k) j - u j‖ ≤ η * |c j| := by
  by_cases hc : c j = 0
  · have hz : (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖X i j‖ ^ 2 ≤ 0 := by
      simpa only [hc, zero_pow (by decide : 2 ≠ 0), mul_zero] using hmoment j
    rw [finite_batch_error_zero (fun i => X i j) (u j) (hmean j) hz b ξ,
      norm_zero, hc, abs_zero, mul_zero]
  · have hi : (c j)⁻¹ ^ 2 * ‖(1 / (b : ℝ)) • ∑ k, X (ξ k) j - u j‖ ^ 2 ≤ η ^ 2 :=
      (Finset.single_le_sum (fun k _ => mul_nonneg (sq_nonneg (c k)⁻¹)
        (sq_nonneg ‖(1 / (b : ℝ)) • ∑ l, X (ξ l) k - u k‖))
        (Finset.mem_univ j)).trans hscore
    have hh := mul_le_mul_of_nonneg_left hi (sq_nonneg (c j))
    have he : c j ^ 2 * ((c j)⁻¹ ^ 2 *
        ‖(1 / (b : ℝ)) • ∑ k, X (ξ k) j - u j‖ ^ 2) =
        ‖(1 / (b : ℝ)) • ∑ k, X (ξ k) j - u j‖ ^ 2 := by field_simp
    rw [he] at hh
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hη (abs_nonneg _))).mp
    rw [mul_pow, sq_abs]
    nlinarith [hh]


omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma finite_uniform_measure_eq_uniformOn {ι : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] :
    (PMF.uniformOfFintype ι).toMeasure = ProbabilityTheory.uniformOn (Set.univ : Set ι) := by
  apply Measure.ext_of_singleton
  intro i
  rw [(PMF.uniformOfFintype ι).toMeasure_apply_singleton i (measurableSet_singleton i),
    PMF.uniformOfFintype_apply, ProbabilityTheory.uniformOn_univ, Measure.count_singleton, one_div]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma finite_uniform_measure_product {ι J : Type*} [Fintype ι] [Nonempty ι] [Fintype J]
    [DecidableEq J]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] :
    (PMF.uniformOfFintype (J → ι)).toMeasure =
      Measure.pi (fun _ : J => (PMF.uniformOfFintype ι).toMeasure) := by
  simp_rw [finite_uniform_measure_eq_uniformOn]
  simpa using (ProbabilityTheory.uniformOn_pi (f := fun _ : J => (Set.univ : Set ι)))


def goodPath {State Ω : Type*} (step : State → Ω → State) (good : State → Ω → Prop) :
    (T : ℕ) → State → (Fin T → Ω) → Prop
  | 0, _, _ => True
  | T + 1, x, ξ => good x (ξ 0) ∧ goodPath step good T (step x (ξ 0)) (fun i => ξ i.succ)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma finite_uniform_adaptive_failure {State Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (step : State → Ω → State) (good : State → Ω → Prop) (δ : ENNReal)
    (hone : ∀ x, (PMF.uniformOfFintype Ω).toMeasure {ω | ¬good x ω} ≤ δ)
    (T : ℕ) (x : State) :
    (PMF.uniformOfFintype (Fin T → Ω)).toMeasure {ξ | ¬goodPath step good T x ξ} ≤
      (T : ENNReal) * δ := by
  induction T generalizing x with
  | zero => simp [goodPath]
  | succ T ih =>
    let P := (PMF.uniformOfFintype Ω).toMeasure
    let Q := (PMF.uniformOfFintype (Fin T → Ω)).toMeasure
    let A : Set (Ω × (Fin T → Ω)) := {z | ¬good x z.1}
    let B : Set (Ω × (Fin T → Ω)) :=
      {z | ¬goodPath step good T (step x z.1) z.2}
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (T + 1) => Ω) 0
    have hm : MeasurePreserving e (PMF.uniformOfFintype (Fin (T + 1) → Ω)).toMeasure
        (P.prod Q) := by
      simpa only [← finite_uniform_measure_product] using
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (T + 1) => (PMF.uniformOfFintype Ω).toMeasure) 0)
    have hevent : e ⁻¹' (A ∪ B) = {ξ | ¬goodPath step good (T + 1) x ξ} := by
      ext ξ
      change (¬good x (ξ 0) ∨
        ¬goodPath step good T (step x (ξ 0)) (fun i => ξ i.succ)) ↔ _
      simp only [goodPath, not_and_or, Set.mem_ofPred_eq]
    have hsplit : (PMF.uniformOfFintype (Fin (T + 1) → Ω)).toMeasure
        {ξ | ¬goodPath step good (T + 1) x ξ} = (P.prod Q) (A ∪ B) := by
      rw [← hevent, ← hm.map_eq, Measure.map_apply e.measurable (Set.toFinite _).measurableSet]
    have hA : (P.prod Q) A ≤ δ := by
      have he : A = {ω | ¬good x ω} ×ˢ (Set.univ : Set (Fin T → Ω)) := by
        ext z
        simp [A]
      rw [he, Measure.prod_prod]
      simpa only [measure_univ, mul_one] using hone x
    have hB : (P.prod Q) B ≤ (T : ENNReal) * δ := by
      rw [Measure.prod_apply (Set.toFinite B).measurableSet]
      calc
        _ ≤ ∫⁻ _ω, (T : ENNReal) * δ ∂P := lintegral_mono fun ω => ih (step x ω)
        _ = (T : ENNReal) * δ := by simp
    rw [hsplit]
    calc
      _ ≤ (P.prod Q) A + (P.prod Q) B := measure_union_le A B
      _ ≤ δ + (T : ENNReal) * δ := add_le_add hA hB
      _ = ((T + 1 : ℕ) : ENNReal) * δ := by push_cast; ring


omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma finite_uniform_majority_failure {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (good : Ω → Prop)
    (hbad : (PMF.uniformOfFintype Ω).toMeasure.real {ω | ¬good ω} ≤ 1 / 16)
    (K : ℕ) :
    (PMF.uniformOfFintype (Fin K → Ω)).toMeasure
      {ξ | ¬K < 2 * (Finset.univ.filter (fun i => good (ξ i))).card} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ K) := by
  rw [finite_uniform_measure_product]
  have hh := OracleTemplate.RobustGradient.majority_failure_probability
    (P := (PMF.uniformOfFintype Ω).toMeasure)
    ((Set.toFinite {ω | ¬good ω}).measurableSet) hbad K
  apply (measure_mono ?_).trans hh
  intro ξ hξ
  change ¬K < 2 * (Finset.univ.filter (fun i => good (ξ i))).card at hξ
  simp only [Set.mem_ofPred_eq]
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin K))) (p := fun i => good (ξ i))
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  omega

end LongTails.Proofs.CoupledCubicConcentration
