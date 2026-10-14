import LongTails.Proofs.RobustEstimatorMoments
import LongTails.Proofs.RobustPilotConfidence

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.RobustGradient

open Classical

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma majority_failure_probability_le {A : Set Ω} (hA : MeasurableSet A) {θ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hp : P.real A ≤ θ) (k : ℕ) :
    (Measure.pi fun _ : Fin k => P)
      {ξ | k ≤ 2*(Finset.univ.filter (fun i => ξ i ∈ A)).card} ≤
      ENNReal.ofReal ((2*Real.sqrt θ)^k) := by
  classical
  let s : ℝ := 1/Real.sqrt θ
  have hsq : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθ
  have hs1 : 1 ≤ s := by
    apply (one_le_div hsq).mpr
    calc Real.sqrt θ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hθ1
      _ = 1 := Real.sqrt_one
  have hs2 : s^2 = 1/θ := by
    dsimp [s]
    rw [div_pow, Real.sq_sqrt hθ.le, one_pow]
  let F : Ω → ℝ := fun ω => if ω ∈ A then s^2 else 1
  have hF1 : ∀ ω, 1 ≤ F ω := fun ω => by
    dsimp [F]; split_ifs
    · nlinarith
    · exact le_rfl
  have hFb : ∀ ω, F ω ≤ s^2 := fun ω => by
    dsimp [F]; split_ifs
    · exact le_rfl
    · nlinarith
  have hFm : Measurable F := Measurable.ite hA measurable_const measurable_const
  have hFe : (∫ ω, F ω ∂P) = 1+(s^2-1)*P.real A := by
    have he : F = fun ω => 1+(s^2-1)*A.indicator (fun _ => (1 : ℝ)) ω := by
      ext ω
      by_cases h : ω ∈ A <;> simp [F, h]
    rw [he, integral_add (integrable_const 1)
      (((integrable_const 1).indicator hA).const_mul (s^2-1)), integral_const_mul]
    change (∫ a, (1 : ℝ) ∂P) + (s^2-1)*(∫ a, A.indicator 1 a ∂P) = _
    rw [integral_indicator_one hA]
    simp
  have hFnonneg : 0 ≤ ∫ ω, F ω ∂P :=
    integral_nonneg (fun ω => (zero_le_one.trans (hF1 ω)))
  have hFbound : (∫ ω, F ω ∂P) ≤ 2 := by
    rw [hFe]
    have h1 : (s^2-1)*P.real A ≤ (s^2-1)*θ :=
      mul_le_mul_of_nonneg_left hp (by nlinarith)
    have h2 : (s^2-1)*θ ≤ 1 := by
      rw [hs2, sub_mul, div_mul_cancel₀ 1 hθ.ne']
      linarith
    linarith
  let W : (Fin k → Ω) → ℝ := fun ξ => ∏ i, F (ξ i)
  have hWm : Measurable W := by dsimp [W]; fun_prop
  have hWnonneg (ξ : Fin k → Ω) : 0 ≤ W ξ :=
    Finset.prod_nonneg (fun i _ => zero_le_one.trans (hF1 _))
  have hWbound (ξ : Fin k → Ω) : W ξ ≤ (s^2)^k := by
    calc
      _ ≤ ∏ _i : Fin k, s^2 := Finset.prod_le_prod₀
        (fun i _ => zero_le_one.trans (hF1 _)) (fun i _ => hFb _)
      _ = _ := by simp
  have hWi : Integrable W (Measure.pi fun _ : Fin k => P) :=
    Integrable.of_bound hWm.aestronglyMeasurable ((s^2)^k)
      (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg ξ)]
        exact hWbound ξ))
  have hWe (ξ : Fin k → Ω) : W ξ = (s^2)^(Finset.univ.filter (fun i => ξ i ∈ A)).card := by
    simp only [W, F, ← Finset.prod_filter, Finset.prod_const]
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  have h := (hWi.div_const (s^k)).measure_le_integral
    (Filter.Eventually.of_forall (fun ξ => div_nonneg (hWnonneg ξ) (by positivity)))
    (s := {ξ | k ≤ 2*(Finset.univ.filter (fun i => ξ i ∈ A)).card}) (by
      intro ξ hξ
      apply (one_le_div (by positivity : (0 : ℝ) < s^k)).mpr
      rw [hWe, ← pow_mul]
      exact pow_le_pow_right₀ hs1 hξ)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div, show W = fun ξ => ∏ i : Fin k, F (ξ i) from rfl,
    integral_fintype_prod_eq_pow, Fintype.card_fin]
  calc
    _ ≤ 2^k/s^k := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hFnonneg hFbound k) (by positivity)
    _ = _ := by
      rw [← div_pow]
      congr 1
      dsimp [s]
      field_simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
omit [InnerProductSpace ℝ E] in
lemma pilotCenter_failure_probability_le {V : Ω → E} (hV : Measurable V) (u : E) (B : ℝ)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hp : P.real {ω | B/6 < ‖V ω-u‖} ≤ θ) (k : ℕ) :
    (Measure.pi fun _ : Fin k => P)
      {ξ | B/2 < ‖pilotCenter B (fun i => V (ξ i))-u‖} ≤
      ENNReal.ofReal ((2*Real.sqrt θ)^k) := by
  classical
  apply (measure_mono ?_).trans (majority_failure_probability_le
    (measurableSet_lt measurable_const ((hV.sub measurable_const).norm)) hθ hθ1 hp k)
  intro ξ hξ
  have hgood : ¬ k < 2*(Finset.univ.filter (fun i => ‖V (ξ i)-u‖ ≤ B/6)).card := by
    intro hg
    exact (not_le_of_gt hξ) (pilotCenter_accuracy (fun i => V (ξ i)) u hg)
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k))) (p := fun i => ‖V (ξ i)-u‖ ≤ B/6)
  simp only [Finset.card_univ, Fintype.card_fin, not_le] at hc
  change k ≤ 2*(Finset.univ.filter (fun i => B/6 < ‖V (ξ i)-u‖)).card
  omega

lemma pilot_means_failure_probability_le {V : Ω → E} (hV : Measurable V)
    (hVi : Integrable V P) (u : E) (hmean : ∫ ω, V ω ∂P = u)
    (hV2i : Integrable (fun ω => ‖V ω-u‖^2) P) {σ B θ : ℝ}
    (hvar : (∫ ω, ‖V ω-u‖^2 ∂P) ≤ σ^2) (hB : 0 < B) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (k r : ℕ) (hr : 0 < r) (hsize : (σ^2/(r : ℝ))/(B/6)^2 ≤ θ) :
    (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin r => P)
      {ξ | B/2 < ‖pilotCenter B (fun i => (1/(r : ℝ)) • ∑ j, V (ξ i j))-u‖} ≤
      ENNReal.ofReal ((2*Real.sqrt θ)^k) := by
  have h := finite_mean_variance hV hVi u hV2i hmean r hr
  apply pilotCenter_failure_probability_le (P := Measure.pi fun _ : Fin r => P)
    (V := fun ξ : Fin r → Ω => (1/(r : ℝ)) • ∑ j, V (ξ j)) (by fun_prop) u B hθ hθ1 ?_ k
  apply (norm_tail_le_second_moment h.1 (by positivity) ?_).trans hsize
  rw [h.2]
  exact div_le_div_of_nonneg_right hvar (by positivity)

end OracleTemplate.RobustGradient
