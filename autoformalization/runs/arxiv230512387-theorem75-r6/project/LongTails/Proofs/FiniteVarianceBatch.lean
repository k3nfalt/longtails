import LongTails.Proofs.NormSubGaussianBatch
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.RobustGradient

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [IsProbabilityMeasure P] [SecondCountableTopology E] in
lemma independent_sum_second_moment {ι : Type*} [Fintype ι]
    (X : ι → Ω → E)
    (hind : iIndepFun X P) (hXi : ∀ i, Integrable (X i) P)
    (hX2i : ∀ i, Integrable (fun ω => ‖X i ω‖^2) P)
    (hzero : ∀ i, (∫ ω, X i ω ∂P) = 0) :
    Integrable (fun ω => ‖∑ i, X i ω‖^2) P ∧
    (∫ ω, ‖∑ i, X i ω‖^2 ∂P) = ∑ i, ∫ ω, ‖X i ω‖^2 ∂P := by
  classical
  have hi (i j : ι) : Integrable (fun ω => ⟪X i ω, X j ω⟫) P := by
    by_cases hij : i = j
    · subst j
      simpa only [real_inner_self_eq_norm_sq] using hX2i i
    · exact (hind.indepFun hij).integrable_bilin (hXi i) (hXi j) (innerSL ℝ)
  have he (ω : Ω) : ‖∑ i, X i ω‖^2 = ∑ i, ∑ j, ⟪X i ω, X j ω⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
  simp_rw [he]
  refine ⟨integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j)), ?_⟩
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  rw [Finset.sum_eq_single i]
  · simp only [real_inner_self_eq_norm_sq]
  · intro j _ hji
    have h := (hind.indepFun hji.symm).integral_bilin (hXi i) (hXi j) (innerSL ℝ)
    change (∫ ω, ⟪X i ω, X j ω⟫ ∂P) = ⟪∫ ω, X i ω ∂P, ∫ ω, X j ω ∂P⟫ at h
    simpa [hzero] using h
  · simp

omit [SecondCountableTopology E] in
lemma finite_mean_second_moment {X : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (hX2i : Integrable (fun ω => ‖X ω‖^2) P)
    (hzero : (∫ ω, X ω ∂P) = 0) (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → Ω => ‖(1/(n : ℝ)) • ∑ i, X (ξ i)‖^2)
      (Measure.pi fun _ : Fin n => P) ∧
    (∫ ξ : Fin n → Ω, ‖(1/(n : ℝ)) • ∑ i, X (ξ i)‖^2
      ∂Measure.pi (fun _ : Fin n => P)) = (∫ ω, ‖X ω‖^2 ∂P) / n := by
  have hl (i : Fin n) : HasLaw (fun ξ : Fin n → Ω => ξ i) P
      (Measure.pi fun _ : Fin n => P) :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval _ i).map_eq⟩
  have h := independent_sum_second_moment (fun (i : Fin n) (ξ : Fin n → Ω) => X (ξ i))
    (iIndepFun_pi (fun _ => hX.aemeasurable))
    (fun i => (hl i).integrable_comp hXi) (fun i => (hl i).integrable_comp hX2i)
    (fun i => ((hl i).integral_comp hXi.aestronglyMeasurable).trans hzero)
  simp_rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul, h.2]
  have hm (i : Fin n) : (∫ ξ : Fin n → Ω, ‖X (ξ i)‖^2
      ∂Measure.pi (fun _ : Fin n => P)) = ∫ ω, ‖X ω‖^2 ∂P :=
    (hl i).integral_comp hX2i.aestronglyMeasurable
  simp_rw [hm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp

omit [MeasurableSpace Ω] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma finite_mean_centered {X : Ω → E} (u : E) (n : ℕ) (hn : 0 < n)
    (ξ : Fin n → Ω) :
    (1/(n : ℝ)) • ∑ i, X (ξ i)-u = (1/(n : ℝ)) • ∑ i, (X (ξ i)-u) := by
  rw [Finset.sum_sub_distrib, smul_sub]
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp [hn']

lemma finite_mean_variance {X : Ω → E} (hX : Measurable X)
    (hXi : Integrable X P) (u : E)
    (hX2i : Integrable (fun ω => ‖X ω-u‖^2) P)
    (hmean : (∫ ω, X ω ∂P) = u) (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → Ω => ‖(1/(n : ℝ)) • ∑ i, X (ξ i)-u‖^2)
      (Measure.pi fun _ : Fin n => P) ∧
    (∫ ξ : Fin n → Ω, ‖(1/(n : ℝ)) • ∑ i, X (ξ i)-u‖^2
      ∂Measure.pi (fun _ : Fin n => P)) = (∫ ω, ‖X ω-u‖^2 ∂P) / n := by
  simp_rw [finite_mean_centered u n hn]
  exact finite_mean_second_moment (hX.sub measurable_const) (hXi.sub (integrable_const u))
    hX2i (by simp only [Pi.sub_apply]; rw [integral_sub hXi (integrable_const u), hmean]; simp) n hn

omit [IsProbabilityMeasure P] [InnerProductSpace ℝ E]
    [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma norm_tail_le_second_moment {X : Ω → E}
    (hX2i : Integrable (fun ω => ‖X ω‖^2) P) {r v : ℝ} (hr : 0 < r)
    (hv : (∫ ω, ‖X ω‖^2 ∂P) ≤ v) :
    P.real {ω | r < ‖X ω‖} ≤ v/r^2 := by
  have h := (hX2i.div_const (r^2)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => by positivity))
    (s := {ω | r < ‖X ω‖}) (by
      intro ω hω
      apply (one_le_div (sq_pos_of_pos hr)).mpr
      exact pow_le_pow_left₀ hr.le hω.le 2)
  have h' : P {ω | r < ‖X ω‖} ≤ ENNReal.ofReal (v/r^2) := by
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_div]
    exact div_le_div_of_nonneg_right hv (sq_nonneg r)
  have hv' : 0 ≤ v := (integral_nonneg (fun _ => sq_nonneg _)).trans hv
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top h'
  simpa only [measureReal_def, ENNReal.toReal_ofReal (div_nonneg hv' (sq_nonneg r))] using ht

end OracleTemplate.RobustGradient
