import LongTails.Proofs.MultiplicativeRobustMedoid
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory
open scoped BigOperators

namespace OracleTemplate.MultiplicativeRobustEstimator

open Classical

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma quarter_failure_probability {A : Set Ω} (hA : MeasurableSet A)
    (hp : P.real A ≤ 1/256) (k : ℕ) :
    (Measure.pi fun _ : Fin k => P)
      {ξ | k ≤ 4*(Finset.univ.filter (fun i => ξ i ∈ A)).card} ≤
      ENNReal.ofReal ((1/2 : ℝ)^k) := by
  classical
  let F : Ω → ℝ := fun ω => if ω ∈ A then 256 else 1
  have hFm : Measurable F := Measurable.ite hA measurable_const measurable_const
  have hFi : Integrable F P := Integrable.of_bound hFm.aestronglyMeasurable 256
    (Filter.Eventually.of_forall (fun ω => by dsimp [F]; split_ifs <;> norm_num))
  have hFe : (∫ ω, F ω ∂P) = 1+255*P.real A := by
    have he : F = fun ω => 1+255*A.indicator (fun _ => (1 : ℝ)) ω := by
      ext ω
      by_cases h : ω ∈ A <;> norm_num [F, h]
    rw [he, integral_add (integrable_const 1)
      (((integrable_const 1).indicator hA).const_mul 255), integral_const_mul]
    change (∫ a, (1 : ℝ) ∂P) + 255*(∫ a, A.indicator 1 a ∂P) = _
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
  have hWbound (ξ : Fin k → Ω) : W ξ ≤ 256^k := by
    calc
      _ ≤ ∏ _i : Fin k, (256 : ℝ) := Finset.prod_le_prod₀
        (fun i _ => by dsimp [F]; split_ifs <;> norm_num)
        (fun i _ => by dsimp [F]; split_ifs <;> norm_num)
      _ = _ := by simp
  have hWi : Integrable W (Measure.pi fun _ : Fin k => P) :=
    Integrable.of_bound hWm.aestronglyMeasurable (256^k)
      (Filter.Eventually.of_forall (fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg ξ)]
        exact hWbound ξ))
  have hWe (ξ : Fin k → Ω) : W ξ = 256^(Finset.univ.filter (fun i => ξ i ∈ A)).card := by
    simp only [W, F, ← Finset.prod_filter, Finset.prod_const]
  have h := (hWi.div_const (4^k)).measure_le_integral
    (Filter.Eventually.of_forall (fun ξ => div_nonneg (hWnonneg ξ) (by positivity)))
    (s := {ξ | k ≤ 4*(Finset.univ.filter (fun i => ξ i ∈ A)).card}) (by
      intro ξ hξ
      apply (one_le_div (by positivity : (0 : ℝ) < 4^k)).mpr
      rw [hWe]
      have he : (256 : ℝ) = 4^4 := by norm_num
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

variable {E : Type*} [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma medoid_failure_probability {X : Ω → E} (hX : Measurable X) (u : E) {r : ℝ}
    (hr : 0 ≤ r) (hp : P.real {ω | r < ‖X ω-u‖} ≤ 1/256) (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => P)
      {ξ | 6*r < ‖medoid (fun i => X (ξ i))-u‖} ≤
      ENNReal.ofReal ((1/2 : ℝ)^(n + 1)) := by
  classical
  apply (measure_mono ?_).trans (quarter_failure_probability
    (measurableSet_lt measurable_const ((hX.sub measurable_const).norm)) hp (n + 1))
  intro ξ hξ
  have hgood : ¬ 3*(n + 1) ≤ 4*(Finset.univ.filter
      (fun i => ‖X (ξ i)-u‖ ≤ r)).card := by
    intro hg
    exact (not_le_of_gt hξ) (medoid_accuracy (fun i => X (ξ i)) u _ hr
      (fun i hi => (Finset.mem_filter.mp hi).2) hg)
  have hc := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n + 1)))) (p := fun i => ‖X (ξ i)-u‖ ≤ r)
  simp only [Finset.card_univ, Fintype.card_fin, not_le] at hc
  change n + 1 ≤ 4*(Finset.univ.filter (fun i => r < ‖X (ξ i)-u‖)).card
  omega

omit [IsProbabilityMeasure P] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma normalized_block_tail {X : Ω → E} (u : E) (hu : 0 < ‖u‖)
    (hi : Integrable (fun ω => ‖X ω-u‖) P)
    (hm : (∫ ω, ‖X ω-u‖ ∂P) ≤ ‖u‖ / 65536) :
    P.real {ω | ‖u‖/12 < ‖X ω-u‖} ≤ 1/256 := by
  have hr : 0 < ‖u‖/12 := by positivity
  have h := (hi.div_const (‖u‖/12)).measure_le_integral
    (Filter.Eventually.of_forall (fun ω => div_nonneg (norm_nonneg _) hr.le))
    (s := {ω | ‖u‖/12 < ‖X ω-u‖}) (fun ω hω => (one_le_div hr).mpr hω.le)
  have hb : P {ω | ‖u‖/12 < ‖X ω-u‖} ≤ ENNReal.ofReal (1/256 : ℝ) := by
    apply h.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_div]
    apply (div_le_iff₀ hr).mpr
    linarith
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/256)] using ht

lemma normalized_medoid_failure {X : Ω → E} (hX : Measurable X) (u : E)
    (hu : 0 < ‖u‖) (hi : Integrable (fun ω => ‖X ω-u‖) P)
    (hm : (∫ ω, ‖X ω-u‖ ∂P) ≤ ‖u‖ / 65536) (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) => P)
      {ξ | ‖u‖/2 < ‖medoid (fun i => X (ξ i))-u‖} ≤
      ENNReal.ofReal ((1/2 : ℝ)^(n + 1)) := by
  have h := medoid_failure_probability hX u (by positivity : 0 ≤ ‖u‖/12)
    (normalized_block_tail u hu hi hm) n
  simpa only [show 6 * (‖u‖/12) = ‖u‖/2 by ring] using h

lemma normalized_medoid_second_moment {X : Ω → E} (hX : Measurable X) (u : E)
    (hi : Integrable (fun ω => ‖X ω-u‖) P)
    (hm : (∫ ω, ‖X ω-u‖ ∂P) ≤ ‖u‖ / 65536) (n : ℕ) (hn : 8 ≤ n + 1) :
    Integrable (fun ξ : Fin (n + 1) → Ω => ‖medoid (fun i => X (ξ i))-u‖ ^ 2)
      (Measure.pi fun _ => P) ∧
    (∫ ξ : Fin (n + 1) → Ω, ‖medoid (fun i => X (ξ i))-u‖ ^ 2
      ∂Measure.pi (fun _ => P)) ≤ ‖u‖ ^ 2 / 64 := by
  have h := medoid_second_moment hX u hi n hn
  refine ⟨h.1, h.2.trans ?_⟩
  have hs := pow_le_pow_left₀ (integral_nonneg (fun ω => norm_nonneg (X ω-u))) hm 2
  nlinarith [sq_nonneg ‖u‖]

end OracleTemplate.MultiplicativeRobustEstimator
