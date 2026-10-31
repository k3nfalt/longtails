import LongTails.Algorithms.MultiplicativeRobustEstimator
import LongTails.Proofs.AdaptiveEntropicExecution
import LongTails.Proofs.AdaptiveEntropicStateMeasurable
import Mathlib.Probability.Independence.Integration

open MeasureTheory

namespace OracleTemplate.MultiplicativeRobustEstimator

variable {E : Type*} [NormedAddCommGroup E]

lemma medoid_score_le {n : ℕ} (v : Fin (n + 1) → E) (j : Fin (n + 1)) :
    (∑ i, ‖medoid v - v i‖) ≤ ∑ i, ‖v j - v i‖ :=
  by simpa only [score, medoid] using
    AdaptiveHeavyTailSimplex.minimumIndex_le (Nat.succ_pos n) (score v) j

lemma score_lower {n : ℕ} (v : Fin n → E) (G : Finset (Fin n)) (c u : E)
    {r : ℝ} (hgood : ∀ i ∈ G, ‖v i - u‖ ≤ r) :
    (∑ i, ‖u - v i‖) + 2 * G.card * (‖c - u‖ - r) - n * ‖c - u‖ ≤
      ∑ i, ‖c - v i‖ := by
  classical
  have h (i : Fin n) : ‖u - v i‖ + (if i ∈ G then 2 * (‖c - u‖ - r) else 0) -
      ‖c - u‖ ≤ ‖c - v i‖ := by
    by_cases hi : i ∈ G
    · simp only [hi, ite_true]
      have ht := norm_sub_le_norm_sub_add_norm_sub c (v i) u
      have hg := hgood i hi
      rw [norm_sub_rev u (v i)]
      linarith
    · simp only [hi, ite_false, add_zero]
      have ht := norm_sub_le_norm_sub_add_norm_sub u c (v i)
      rw [norm_sub_rev u c] at ht
      linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hs

lemma medoid_accuracy {n : ℕ} (v : Fin (n + 1) → E) (u : E)
    (G : Finset (Fin (n + 1))) {r : ℝ} (hr : 0 ≤ r)
    (hgood : ∀ i ∈ G, ‖v i - u‖ ≤ r) (hcard : 3 * (n + 1) ≤ 4 * G.card) :
    ‖medoid v - u‖ ≤ 6 * r := by
  have hG : G.Nonempty := by
    by_contra h
    have he : G.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    omega
  obtain ⟨j, hj⟩ := hG
  have hup : (∑ i, ‖v j - v i‖) ≤ (∑ i, ‖u - v i‖) + (n + 1 : ℝ) * r := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      (norm_sub_le_norm_sub_add_norm_sub (v j) u (v i)).trans
        (add_le_add (hgood j hj) le_rfl))
    simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, add_comm] using hs
  have hlo := score_lower v G (medoid v) u hgood
  have hscore := (medoid_score_le v j).trans hup
  have hc : 3 * (n + 1 : ℝ) ≤ 4 * (G.card : ℝ) := by exact_mod_cast hcard
  have hc' : (G.card : ℝ) ≤ n + 1 := by
    exact_mod_cast (show G.card ≤ n + 1 by simpa using Finset.card_le_univ G)
  have hp := mul_le_mul_of_nonneg_right hc (norm_nonneg (medoid v - u))
  have hp' := mul_le_mul_of_nonneg_right hc' hr
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hb : (n + 1 : ℝ) * ‖medoid v - u‖ ≤ (n + 1 : ℝ) * (6 * r) := by
    push_cast at hlo
    nlinarith only [hlo, hscore, hp, hp']
  exact (mul_le_mul_iff_right₀ hn).mp (by simpa only [mul_comm] using hb)

lemma medoid_square_domination {n : ℕ} (v : Fin (n + 1) → E) (u : E)
    (hn : 8 ≤ n + 1) :
    (n + 1 : ℝ) ^ 2 * ‖medoid v - u‖ ^ 2 ≤
      4608 * ∑ ij ∈ (Finset.univ : Finset (Fin (n + 1))).offDiag,
        ‖v ij.1 - u‖ * ‖v ij.2 - u‖ := by
  classical
  let D := ‖medoid v - u‖
  by_cases hD : D = 0
  · change (n + 1 : ℝ) ^ 2 * D ^ 2 ≤ _
    rw [hD]
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun ij _ =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hDpos : 0 < D := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hD)
  let B := Finset.univ.filter (fun i => D / 12 < ‖v i - u‖)
  let G := Finset.univ.filter (fun i => ‖v i - u‖ ≤ D / 12)
  have hsumcard : G.card + B.card = n + 1 := by
    simpa only [G, B, not_le, Finset.card_univ, Fintype.card_fin] using
      Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun i : Fin (n + 1) => ‖v i - u‖ ≤ D / 12)
  have hm : n + 1 < 4 * B.card := by
    by_contra h
    have hg : 3 * (n + 1) ≤ 4 * G.card := by omega
    have hb := medoid_accuracy v u G (by positivity : 0 ≤ D / 12)
      (fun i hi => (Finset.mem_filter.mp hi).2) hg
    change D ≤ 6 * (D / 12) at hb
    linarith
  have hm2 : 2 ≤ B.card := by omega
  have hbr : (2 : ℝ) ≤ B.card := by exact_mod_cast hm2
  have hnr : (n + 1 : ℝ) ≤ 4 * B.card := by exact_mod_cast hm.le
  have hcard : ((n + 1 : ℝ) ^ 2) ≤ 32 * (B.offDiag.card : ℝ) := by
    rw [Finset.offDiag_card, Nat.cast_sub (by nlinarith : B.card ≤ B.card * B.card), Nat.cast_mul]
    have hs := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ n + 1) hnr
    nlinarith
  have hlower : (B.offDiag.card : ℝ) * (D / 12) ^ 2 ≤
      ∑ ij ∈ B.offDiag, ‖v ij.1 - u‖ * ‖v ij.2 - u‖ := by
    calc
      _ = ∑ _ij ∈ B.offDiag, (D / 12) ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun ij hij => by
        obtain ⟨hi, hj, _⟩ := Finset.mem_offDiag.mp hij
        have hi' := (Finset.mem_filter.mp hi).2.le
        have hj' := (Finset.mem_filter.mp hj).2.le
        simpa only [pow_two] using mul_le_mul hi' hj' (by positivity) (norm_nonneg _))
  have hupper : (∑ ij ∈ B.offDiag, ‖v ij.1 - u‖ * ‖v ij.2 - u‖) ≤
      ∑ ij ∈ (Finset.univ : Finset (Fin (n + 1))).offDiag, ‖v ij.1 - u‖ * ‖v ij.2 - u‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.offDiag_mono (Finset.filter_subset _ _))
      (fun _ _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hc := mul_le_mul_of_nonneg_right hcard (sq_nonneg D)
  change (n + 1 : ℝ) ^ 2 * D ^ 2 ≤ _
  nlinarith only [hc, hlower, hupper]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma measurable_score {n : ℕ} : Measurable (score (E := E) (n := n)) := by
  apply Measurable.of_eval
  intro i
  unfold score
  fun_prop

lemma measurable_medoid {n : ℕ} : Measurable (medoid (E := E) (n := n)) := by
  have he : Measurable (fun w : (Fin (n + 1) → E) × Fin (n + 1) => w.1 w.2) :=
    measurable_from_prod_countable_left (fun i => measurable_pi_apply i)
  exact he.comp (measurable_id.prodMk
    ((AdaptiveHeavyTailSimplex.measurable_minimumIndex _).comp measurable_score))

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma medoid_second_moment {X : Ω → E} (hX : Measurable X) (u : E)
    (hi : Integrable (fun ω => ‖X ω - u‖) P) (n : ℕ) (hn : 8 ≤ n + 1) :
    Integrable (fun ξ : Fin (n + 1) → Ω => ‖medoid (fun i => X (ξ i)) - u‖ ^ 2)
      (Measure.pi fun _ => P) ∧
    (∫ ξ : Fin (n + 1) → Ω, ‖medoid (fun i => X (ξ i)) - u‖ ^ 2
      ∂Measure.pi (fun _ => P)) ≤ 4608 * (∫ ω, ‖X ω - u‖ ∂P) ^ 2 := by
  classical
  let Q := Measure.pi (fun _ : Fin (n + 1) => P)
  let e : Fin (n + 1) → (Fin (n + 1) → Ω) → ℝ := fun i ξ => ‖X (ξ i) - u‖
  let S := (Finset.univ : Finset (Fin (n + 1))).offDiag
  have hem (i : Fin (n + 1)) : Measurable (e i) := by dsimp [e]; fun_prop
  have hei (i : Fin (n + 1)) : Integrable (e i) Q :=
    ((measurePreserving_eval (fun _ : Fin (n + 1) => P) i).integrable_comp
      hi.aestronglyMeasurable).mpr hi
  have heind : ProbabilityTheory.iIndepFun e Q :=
    ProbabilityTheory.iIndepFun_pi (fun _ => ((hX.sub measurable_const).norm).aemeasurable)
  have hpair (ij : Fin (n + 1) × Fin (n + 1)) (hij : ij ∈ S) :
      Integrable (fun ξ => e ij.1 ξ * e ij.2 ξ) Q :=
    (heind.indepFun (Finset.mem_offDiag.mp hij).2.2).integrable_mul (hei _) (hei _)
  let F : (Fin (n + 1) → Ω) → ℝ := fun ξ =>
    4608 / (n + 1 : ℝ)^2 * ∑ ij ∈ S, e ij.1 ξ * e ij.2 ξ
  have hFi : Integrable F Q := (integrable_finsetSum S hpair).const_mul _
  have hdom (ξ : Fin (n + 1) → Ω) :
      ‖medoid (fun i => X (ξ i)) - u‖ ^ 2 ≤ F ξ := by
    have h := medoid_square_domination (fun i => X (ξ i)) u hn
    dsimp [F, S, e]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n + 1)^2)).mpr
    simpa only [mul_comm] using h
  have hmi : Integrable (fun ξ : Fin (n + 1) → Ω =>
      ‖medoid (fun i => X (ξ i)) - u‖ ^ 2) Q := by
    apply hFi.mono' (by
      apply Measurable.aestronglyMeasurable
      exact (((measurable_medoid.comp (Measurable.of_eval (fun i =>
        hX.comp (measurable_pi_apply i)))).sub measurable_const).norm).pow_const 2)
    exact Filter.Eventually.of_forall (fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hdom ξ)
  refine ⟨hmi, (integral_mono hmi hFi hdom).trans ?_⟩
  have heint (i : Fin (n + 1)) : (∫ ξ, e i ξ ∂Q) = ∫ ω, ‖X ω - u‖ ∂P :=
    by
      have hm := measurePreserving_eval (fun _ : Fin (n + 1) => P) i
      exact (show ProbabilityTheory.HasLaw (Function.eval i) P Q from
        ⟨hm.measurable.aemeasurable, hm.map_eq⟩).integral_comp hi.aestronglyMeasurable
  have hpint (ij : Fin (n + 1) × Fin (n + 1)) (hij : ij ∈ S) :
      (∫ ξ, e ij.1 ξ * e ij.2 ξ ∂Q) = (∫ ω, ‖X ω - u‖ ∂P)^2 := by
    rw [(heind.indepFun (Finset.mem_offDiag.mp hij).2.2).integral_fun_mul_eq_mul_integral
      (hem _).aestronglyMeasurable (hem _).aestronglyMeasurable, heint, heint, pow_two]
  change (∫ ξ, 4608 / (n + 1 : ℝ)^2 * ∑ ij ∈ S, e ij.1 ξ * e ij.2 ξ ∂Q) ≤ _
  rw [integral_const_mul, integral_finsetSum S hpair]
  rw [Finset.sum_congr rfl hpint]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : (S.card : ℝ) ≤ (n + 1 : ℝ)^2 := by
    dsimp [S]
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
    have h := Nat.sub_le ((n + 1) * (n + 1)) (n + 1)
    have hc : (((n + 1) * (n + 1) - (n + 1) : ℕ) : ℝ) ≤ (n + 1 : ℝ) * (n + 1) := by exact_mod_cast h
    simpa only [pow_two] using hc
  calc
    _ ≤ 4608 / (n + 1 : ℝ)^2 * ((n + 1 : ℝ)^2 * (∫ ω, ‖X ω-u‖ ∂P)^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) (by positivity)
    _ = _ := by field_simp

end OracleTemplate.MultiplicativeRobustEstimator
