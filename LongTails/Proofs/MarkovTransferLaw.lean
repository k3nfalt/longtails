import LongTails.Proofs.FiniteMarkovOperators
import LongTails.Proofs.FiniteMarkovLaw

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory ProbabilityTheory Function Preorder
open scoped BigOperators

namespace OracleTemplate.MarkovProduct

variable {S : Type} {B : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
variable [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

noncomputable def pathOperator (T : S → B →L[ℂ] B) (ξ : ℕ → S) : ℕ → B →L[ℂ] B
  | 0 => 1
  | n + 1 => pathOperator T ξ n * T (ξ n)

def extendHistory {k : ℕ} (h : Finset.Iic k → S) (i : ℕ) : S :=
  h ⟨min i k, Finset.mem_Iic.mpr (Nat.min_le_right i k)⟩

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] in
lemma extendHistory_eq {k i : ℕ} (h : Finset.Iic k → S) (hi : i ≤ k) :
    extendHistory h i = h ⟨i, Finset.mem_Iic.mpr hi⟩ := by
  simp [extendHistory, Nat.min_eq_left hi]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [CompleteSpace B] in
lemma pathOperator_congr (T : S → B →L[ℂ] B) (ξ ζ : ℕ → S) (n : ℕ)
    (h : ∀ i < n, ξ i = ζ i) : pathOperator T ξ n = pathOperator T ζ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pathOperator, pathOperator, ih (fun i hi => h i (by omega)), h n (by omega)]

omit [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S] [CompleteSpace B] in
lemma pathOperator_prefix (T : S → B →L[ℂ] B) (ξ : ℕ → S) (n k : ℕ) (hn : n ≤ k + 1) :
    pathOperator T (extendHistory (frestrictLe k ξ)) n = pathOperator T ξ n := by
  apply pathOperator_congr
  intro i hi
  rw [extendHistory_eq _ (by omega)]
  rfl

lemma finite_integral_complex (μ : Measure S) [IsFiniteMeasure μ] (g : S → B) :
    (∫ i, g i ∂μ) = ∑ i, (μ.real {i} : ℂ) • g i := by
  rw [finite_integral]
  simp only [Complex.coe_smul]

lemma pathOperator_integral_step (κ : Kernel S S) [IsMarkovKernel κ]
    (μ : ProbabilityMeasure S) (T : S → B →L[ℂ] B) (g : S → B) (n : ℕ) :
    (∫ ξ, pathOperator T ξ (n + 1) (g (ξ (n + 1)))
      ∂(LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ : Measure (ℕ → S))) =
    ∫ ξ, pathOperator T ξ n
      (T (ξ n) (∑ j, ((κ (ξ n)).real {j} : ℂ) • g j))
      ∂(LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ : Measure (ℕ → S)) := by
  let W : (Finset.Iic n → S) → S → B := fun h y =>
    pathOperator T (extendHistory h) n (T (h ⟨n, by simp⟩) (g y))
  have he := finite_pathLaw_integral_future κ μ n 1 W
  have hleft : (fun ξ : ℕ → S => W (frestrictLe n ξ) (ξ (n + 1))) =
      (fun ξ => pathOperator T ξ (n + 1) (g (ξ (n + 1)))) := by
    funext ξ
    simp only [W, pathOperator_prefix T ξ n n (by omega), frestrictLe_apply,
      pathOperator, mul_apply_eq_comp]
  rw [hleft] at he
  rw [he]
  have hi (h : Finset.Iic n → S) :
      (∫ y, W h y ∂(κ ^ 1) (h ⟨n, by simp⟩)) =
      pathOperator T (extendHistory h) n
        (T (h ⟨n, by simp⟩) (∑ j, ((κ (h ⟨n, by simp⟩)).real {j} : ℂ) • g j)) := by
    rw [pow_one, finite_integral_complex]
    simp only [W, map_sum, map_smul]
  simp_rw [hi]
  rw [integral_map (by fun_prop) (StronglyMeasurable.of_discrete.aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [pathOperator_prefix T ξ n n (by omega)]
  rfl

lemma pathOperator_integral_transfer (κ : Kernel S S) [IsMarkovKernel κ]
    (μ : ProbabilityMeasure S) (T : S → B →L[ℂ] B) (g : S → B) (n : ℕ) :
    (∫ ξ, pathOperator T ξ n (g (ξ n))
      ∂(LongTails.Setups.HeavyTailedMarkovSmoothAndConvex.pathLaw κ μ : Measure (ℕ → S))) =
    stateAverage (B := B) (fun i => (μ : Measure S).real {i})
      (((stateAction T * stateMix (B := B) (fun i j => (κ i).real {j})) ^ n) g) := by
  induction n generalizing g with
  | zero =>
    simp only [pathOperator, one_apply_eq_self, pow_zero]
    have hm := HeavyTailedMarkovGradient.pathLaw_map_zero κ μ
    calc
      _ = ∫ i, g i ∂(μ : Measure S) := by
        rw [← hm, integral_map (measurable_pi_apply 0).aemeasurable (StronglyMeasurable.of_discrete.aestronglyMeasurable)]
      _ = _ := by rw [finite_integral_complex, stateAverage_apply]
  | succ n ih =>
    rw [pathOperator_integral_step]
    simpa only [pow_succ, mul_apply_eq_comp, stateAction_apply, stateMix_apply] using
      ih ((stateAction T * stateMix (B := B) (fun i j => (κ i).real {j})) g)


end OracleTemplate.MarkovProduct
