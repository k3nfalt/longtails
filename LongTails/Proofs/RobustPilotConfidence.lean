import LongTails.Proofs.RobustPilot
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.RobustGradient

open Classical

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma majority_failure_probability {A : Set Ω} (hA : MeasurableSet A)
    (hp : P.real A ≤ 1/16) (k : ℕ) :
    (Measure.pi fun _ : Fin k => P)
      {ξ | k ≤ 2*(Finset.univ.filter (fun i => ξ i ∈ A)).card} ≤
      ENNReal.ofReal ((1/2 : ℝ)^k) := by
  classical
  let F : Ω → ℝ := fun ω => if ω ∈ A then 16 else 1
  have hFm : Measurable F := Measurable.ite hA measurable_const measurable_const
  have hFi : Integrable F P := Integrable.of_bound hFm.aestronglyMeasurable 16
    (Filter.Eventually.of_forall (fun ω => by dsimp [F]; split_ifs <;> norm_num))
  have hFe : (∫ ω, F ω ∂P) = 1+15*P.real A := by
    have he : F = fun ω => 1+15*A.indicator (fun _ => (1 : ℝ)) ω := by
      ext ω
      by_cases h : ω ∈ A <;> norm_num [F, h]
    rw [he, integral_add (integrable_const 1)
      (((integrable_const 1).indicator hA).const_mul 15), integral_const_mul]
    change (∫ a, (1 : ℝ) ∂P) + 15*(∫ a, A.indicator 1 a ∂P) = _
    rw [integral_indicator_one hA]
    simp
  have hFnonneg : 0 ≤ ∫ ω, F ω ∂P := integral_nonneg (fun ω => by dsimp [F]; split_ifs <;> norm_num)
  have hFbound : (∫ ω, F ω ∂P) ≤ 2 := by rw [hFe]; linarith
  let W : (Fin k → Ω) → ℝ := fun ξ => ∏ i, F (ξ i)
  have hWm : Measurable W := by dsimp [W]; fun_prop
  have hWnonneg (ξ : Fin k → Ω) : 0 ≤ W ξ := by
    apply Finset.prod_nonneg
    intro i _
    dsimp [F]
    split_ifs <;> norm_num
  have hWbound (ξ : Fin k → Ω) : W ξ ≤ 16^k := by
    calc
      _ ≤ ∏ _i : Fin k, (16 : ℝ) := Finset.prod_le_prod₀
        (fun i _ => by dsimp [F]; split_ifs <;> norm_num)
        (fun i _ => by dsimp [F]; split_ifs <;> norm_num)
      _ = _ := by simp
  have hWi : Integrable W (Measure.pi fun _ : Fin k => P) :=
    Integrable.of_bound hWm.aestronglyMeasurable (16^k)
      (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg ξ)]
        exact hWbound ξ))
  have hWe (ξ : Fin k → Ω) : W ξ = 16^(Finset.univ.filter (fun i => ξ i ∈ A)).card := by
    simp only [W, F, ← Finset.prod_filter, Finset.prod_const]
  have h := (hWi.div_const (4^k)).measure_le_integral
    (Filter.Eventually.of_forall (fun ξ => div_nonneg (hWnonneg ξ) (by positivity)))
    (s := {ξ | k ≤ 2*(Finset.univ.filter (fun i => ξ i ∈ A)).card}) (by
      intro ξ hξ
      apply (one_le_div (by positivity : (0 : ℝ) < 4^k)).mpr
      rw [hWe]
      have he : (16 : ℝ) = 4^2 := by norm_num
      rw [he, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) hξ)
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  rw [integral_div, show W = fun ξ => ∏ i : Fin k, F (ξ i) from rfl,
    integral_fintype_prod_eq_pow, Fintype.card_fin]
  calc
    _ ≤ 2^k/4^k := div_le_div_of_nonneg_right
      (pow_le_pow_left₀ hFnonneg hFbound k) (by positivity)
    _ = _ := by rw [← div_pow]; norm_num

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [InnerProductSpace ℝ E] in
lemma pilotCenter_failure_probability {V : Ω → E} (hV : Measurable V) (u : E) (B : ℝ)
    (hp : P.real {ω | B/6 < ‖V ω-u‖} ≤ 1/16) (k : ℕ) :
    (Measure.pi fun _ : Fin k => P)
      {ξ | B/2 < ‖pilotCenter B (fun i => V (ξ i))-u‖} ≤
      ENNReal.ofReal ((1/2 : ℝ)^k) := by
  classical
  apply (measure_mono ?_).trans (majority_failure_probability
    (measurableSet_lt measurable_const ((hV.sub measurable_const).norm)) hp k)
  intro ξ hξ
  have hgood : ¬ k < 2*(Finset.univ.filter (fun i => ‖V (ξ i)-u‖ ≤ B/6)).card := by
    intro hg
    exact (not_le_of_gt hξ) (pilotCenter_accuracy (fun i => V (ξ i)) u hg)
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k))) (p := fun i => ‖V (ξ i)-u‖ ≤ B/6)
  simp only [Finset.card_univ, Fintype.card_fin, not_le] at hc
  change k ≤ 2*(Finset.univ.filter (fun i => B/6 < ‖V (ξ i)-u‖)).card
  omega

end OracleTemplate.RobustGradient
