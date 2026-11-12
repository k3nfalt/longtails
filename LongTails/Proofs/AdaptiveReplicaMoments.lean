import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.IIDBlocks
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdaptiveReplicaMoments

lemma independent_product_integrable {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (s : Finset ι)
    (X : ι → Ω → ℝ) (hind : iIndepFun X P)
    (hm : ∀ i, Measurable (X i)) (hi : ∀ i, Integrable (X i) P) :
    Integrable (fun ω => ∏ i ∈ s, X i ω) P := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih =>
    have heq : (∏ i ∈ s, X i) = fun ω => ∏ i ∈ s, X i ω := by
      ext ω
      simp
    have ih' : Integrable (∏ i ∈ s, X i) P := by
      rw [heq]
      exact ih
    have h := ((hind.indepFun_finsetProd_of_notMem hm hj).symm).integrable_mul (hi j) ih'
    change Integrable (fun ω => X j ω * (∏ i ∈ s, X i) ω) P at h
    rw [heq] at h
    simpa only [Finset.prod_cons] using h

lemma replica_blocks_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (r b : ℕ) :
    MeasurePreserving (fun ξ : Fin (r * b) → Ω => fun i : Fin r => fun j : Fin b =>
      ξ (finProdFinEquiv (i, j)))
      (Measure.pi fun _ : Fin (r * b) => P)
      (Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin b => P) := by
  have hf := measurePreserving_piCongrLeft (fun _ : Fin r × Fin b => P) finProdFinEquiv.symm
  have hc : MeasurePreserving (MeasurableEquiv.curry (Fin r) (Fin b) Ω)
      (Measure.pi fun _ : Fin r × Fin b => P)
      (Measure.pi fun _ : Fin r => Measure.pi fun _ : Fin b => P) := by
    refine ⟨(MeasurableEquiv.curry (Fin r) (Fin b) Ω).measurable, ?_⟩
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry (fun (_ : Fin r) (_ : Fin b) => P))
  convert hc.comp hf using 1
  funext ξ i j
  simp [MeasurableEquiv.curry, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P]

lemma shifted_second_moment (w : E) {z : Ω → E}
    (hz : Integrable z P) (hz2 : Integrable (fun ω => ‖z ω‖ ^ 2) P)
    (hzero : ∫ ω, z ω ∂P = 0) :
    (∫ ω, ‖w + z ω‖ ^ 2 ∂P) = ‖w‖ ^ 2 + ∫ ω, ‖z ω‖ ^ 2 ∂P := by
  have hi : Integrable (fun ω => 2 * ⟪w, z ω⟫) P := (hz.const_inner w).const_mul 2
  have hc : Integrable (fun _ : Ω => ‖w‖ ^ 2) P := integrable_const _
  have hci : Integrable (fun ω => ‖w‖ ^ 2 + 2 * ⟪w, z ω⟫) P := hc.add hi
  simp_rw [norm_add_sq_real]
  rw [integral_add hci hz2,
    integral_add hc hi, integral_const_mul,
    integral_inner hz, hzero, inner_zero_right]
  simp

omit [CompleteSpace E] in
lemma shifted_second_moment_integrable (w : E) {z : Ω → E}
    (hz : Integrable z P) (hz2 : Integrable (fun ω => ‖z ω‖ ^ 2) P) :
    Integrable (fun ω => ‖w + z ω‖ ^ 2) P := by
  simp_rw [norm_add_sq_real]
  exact ((integrable_const _).add ((hz.const_inner w).const_mul 2)).add hz2

lemma fresh_product_step {ι : Type*} [Fintype ι]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (w : ι → E) (z : ι → Ω → E) (a v : ℝ)
    (ha : 0 ≤ a)
    (hind : iIndepFun z P) (hm : ∀ i, Measurable (z i))
    (hz : ∀ i, Integrable (z i) P)
    (hz2 : ∀ i, Integrable (fun ω => ‖z i ω‖ ^ 2) P)
    (hzero : ∀ i, ∫ ω, z i ω ∂P = 0)
    (hvar : ∀ i, (∫ ω, ‖z i ω‖ ^ 2 ∂P) ≤ v) :
    (∫ ω, ∏ i, (‖w i + z i ω‖ ^ 2 + a) ∂P) ≤
      ∏ i, (‖w i‖ ^ 2 + (v + a)) := by
  have hcomp : iIndepFun (fun i ω => ‖w i + z i ω‖ ^ 2 + a) P :=
    hind.comp (fun i x => ‖w i + x‖ ^ 2 + a) (fun _ => by fun_prop)
  rw [hcomp.integral_fun_prod_eq_prod_integral (fun i => by fun_prop)]
  apply Finset.prod_le_prod₀
  · intro i _
    exact integral_nonneg (fun _ => by positivity)
  · intro i _
    rw [integral_add (shifted_second_moment_integrable (w i) (hz i) (hz2 i))
      (integrable_const a), shifted_second_moment (w i) (hz i) (hz2 i) (hzero i)]
    simp only [integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    linarith [hvar i]

omit [CompleteSpace E] in
lemma fresh_product_integrable {ι : Type*} [Fintype ι]
    [MeasurableSpace E] [BorelSpace E]
    (w : ι → E) (z : ι → Ω → E) (a : ℝ)
    (hind : iIndepFun z P) (hm : ∀ i, Measurable (z i))
    (hz : ∀ i, Integrable (z i) P)
    (hz2 : ∀ i, Integrable (fun ω => ‖z i ω‖ ^ 2) P) :
    Integrable (fun ω => ∏ i, (‖w i + z i ω‖ ^ 2 + a)) P := by
  apply independent_product_integrable Finset.univ
  · exact hind.comp (fun i x => ‖w i + x‖ ^ 2 + a) (fun _ => by fun_prop)
  · intro i
    fun_prop
  · intro i
    exact (shifted_second_moment_integrable (w i) (hz i) (hz2 i)).add (integrable_const a)

lemma batch_error_moments [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (X : Ω → E) (hX : Measurable X) (hXi : Integrable X P) (u : E)
    (hmean : (∫ ω, X ω ∂P) = u)
    (hX2 : Integrable (fun ω => ‖X ω - u‖ ^ 2) P) (v : ℝ)
    (hvar : (∫ ω, ‖X ω - u‖ ^ 2 ∂P) ≤ v) (n : ℕ) (hn : 0 < n) :
    Integrable (fun ξ : Fin n → Ω => (1 / (n : ℝ)) • ∑ i, X (ξ i) - u)
      (Measure.pi fun _ : Fin n => P) ∧
    (∫ ξ : Fin n → Ω, (1 / (n : ℝ)) • ∑ i, X (ξ i) - u
      ∂Measure.pi (fun _ : Fin n => P)) = 0 ∧
    Integrable (fun ξ : Fin n → Ω => ‖(1 / (n : ℝ)) • ∑ i, X (ξ i) - u‖ ^ 2)
      (Measure.pi fun _ : Fin n => P) ∧
    (∫ ξ : Fin n → Ω, ‖(1 / (n : ℝ)) • ∑ i, X (ξ i) - u‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => P)) ≤ v / n := by
  have hi := OracleTemplate.LightTail.finite_mean_integral hXi n hn
  have hv := OracleTemplate.RobustGradient.finite_mean_variance hX hXi u hX2 hmean n hn
  refine ⟨hi.1.sub (integrable_const u), ?_, hv.1, ?_⟩
  · rw [integral_sub hi.1 (integrable_const u), hi.2, hmean]
    simp
  · rw [hv.2]
    exact div_le_div_of_nonneg_right hvar (Nat.cast_nonneg n)

lemma independent_batch_product_step {ι : Type*} [Fintype ι]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (X : Ω → E) (hX : Measurable X) (hXi : Integrable X P) (u : E)
    (hmean : (∫ ω, X ω ∂P) = u)
    (hX2 : Integrable (fun ω => ‖X ω - u‖ ^ 2) P) (v : ℝ)
    (hvar : (∫ ω, ‖X ω - u‖ ^ 2 ∂P) ≤ v) (n : ℕ) (hn : 0 < n)
    (w : ι → E) (a : ℝ) (ha : 0 ≤ a) :
    Integrable (fun ξ : ι → Fin n → Ω =>
      ∏ i, (‖w i + ((1 / (n : ℝ)) • ∑ j, X (ξ i j) - u)‖ ^ 2 + a))
      (Measure.pi fun _ : ι => Measure.pi fun _ : Fin n => P) ∧
    (∫ ξ : ι → Fin n → Ω,
      ∏ i, (‖w i + ((1 / (n : ℝ)) • ∑ j, X (ξ i j) - u)‖ ^ 2 + a)
      ∂Measure.pi (fun _ : ι => Measure.pi fun _ : Fin n => P)) ≤
      ∏ i, (‖w i‖ ^ 2 + (v / n + a)) := by
  let Z : (Fin n → Ω) → E := fun ξ => (1 / (n : ℝ)) • ∑ j, X (ξ j) - u
  have hZ : Measurable Z := by dsimp [Z]; fun_prop
  have h := batch_error_moments X hX hXi u hmean hX2 v hvar n hn
  have hm (i : ι) := measurePreserving_eval (fun _ : ι => Measure.pi fun _ : Fin n => P) i
  have hz (i : ι) : Integrable (fun ξ : ι → Fin n → Ω => Z (ξ i))
      (Measure.pi fun _ : ι => Measure.pi fun _ : Fin n => P) :=
    (hm i).integrable_comp_of_integrable h.1
  have hz2 (i : ι) : Integrable (fun ξ : ι → Fin n → Ω => ‖Z (ξ i)‖ ^ 2)
      (Measure.pi fun _ : ι => Measure.pi fun _ : Fin n => P) :=
    (hm i).integrable_comp_of_integrable h.2.2.1
  have hzero (i : ι) : (∫ ξ : ι → Fin n → Ω, Z (ξ i)
      ∂Measure.pi (fun _ : ι => Measure.pi fun _ : Fin n => P)) = 0 := by
    have he := integral_map (μ := Measure.pi fun _ : ι => Measure.pi fun _ : Fin n => P)
      (hm i).measurable.aemeasurable hZ.aestronglyMeasurable
    rw [(hm i).map_eq] at he
    exact he.symm.trans h.2.1
  have hv (i : ι) : (∫ ξ : ι → Fin n → Ω, ‖Z (ξ i)‖ ^ 2
      ∂Measure.pi (fun _ : ι => Measure.pi fun _ : Fin n => P)) ≤ v / n := by
    have he := integral_map (μ := Measure.pi fun _ : ι => Measure.pi fun _ : Fin n => P)
      (hm i).measurable.aemeasurable (hZ.norm.pow_const 2).aestronglyMeasurable
    rw [(hm i).map_eq] at he
    exact he.symm.trans_le h.2.2.2
  have hind : iIndepFun (fun i (ξ : ι → Fin n → Ω) => Z (ξ i))
      (Measure.pi fun _ : ι => Measure.pi fun _ : Fin n => P) :=
    iIndepFun_pi (μ := fun _ : ι => Measure.pi fun _ : Fin n => P)
    (fun _ : ι => hZ.aemeasurable)
  with_reducible exact ⟨fresh_product_integrable (P := Measure.pi fun _ : ι => Measure.pi fun _ : Fin n => P)
      w (fun i ξ => Z (ξ i)) a hind
      (fun i => hZ.comp (measurable_pi_apply i)) hz hz2,
    fresh_product_step (P := Measure.pi fun _ : ι => Measure.pi fun _ : Fin n => P)
      w (fun i ξ => Z (ξ i)) a (v / n) ha hind
      (fun i => hZ.comp (measurable_pi_apply i)) hz hz2 hzero hv⟩

end LongTails.Proofs.AdaptiveReplicaMoments
