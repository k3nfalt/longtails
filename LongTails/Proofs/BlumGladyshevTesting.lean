import LongTails.Proofs.BlumGladyshevMask
import LongTails.Proofs.CountdownTesting
import LongTails.Proofs.AdaptiveIID
import Mathlib.Probability.Distributions.Bernoulli

open MeasureTheory ProbabilityTheory OracleTemplate OracleTemplate.CountdownMarkov
open scoped ENNReal

namespace LongTails.Proofs.BlumGladyshevTesting

noncomputable def marginal (q : unitInterval) : ProbabilityMeasure Bool :=
  ⟨bernoulliMeasure true false q, inferInstance⟩

noncomputable def stream (q : unitInterval) : ProbabilityMeasure (ℕ → Bool) :=
  ⟨Measure.infinitePi fun _ : ℕ => (marginal q : Measure Bool), inferInstance⟩

lemma prefix_mass (q : unitInterval) (n : ℕ) :
    (stream q : Measure (ℕ → Bool)).real (commonPrefix false n) = (1 - (q : ℝ)) ^ (n + 1) := by
  have he : commonPrefix false n = Set.pi (Finset.range (n + 1) : Set ℕ)
      (fun _ => ({false} : Set Bool)) := by
    ext ξ
    simp only [commonPrefix, Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range,
      Nat.lt_succ_iff, Set.mem_singleton_iff]
  rw [he, measureReal_def]
  change ((Measure.infinitePi fun _ : ℕ => (marginal q : Measure Bool)) _).toReal = _
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton false)]
  simp only [Finset.prod_const, Finset.card_range, ENNReal.toReal_pow]
  congr 1
  exact bernoulliMeasure_real_apply_of_notMem_of_mem q (measurableSet_singleton false)
    (by decide) (by simp)

lemma incompatible_success {Q V E : Type*} (g₁ g₂ : Q → Bool → V) (q : unitInterval)
    (hcommon : ∀ x, g₁ x false = g₂ x false) (A : Algorithm Q V E) (n : ℕ)
    (F₁ F₂ : E → ℝ) {ε δ : ℝ} (hδ : 0 ≤ δ)
    (hsep : ∀ x, ε < F₁ x ∨ ε < F₂ x)
    (hm : 2 * δ < (1 - (q : ℝ)) ^ (n + 1)) :
    let P := (A.law : Measure A.Seed).prod (stream q : Measure (ℕ → Bool))
    let out := fun (g : Q → Bool → V) (w : A.Seed × (ℕ → Bool)) =>
      execute (sampledOracle g (stream q)) A (fun _ => n) w.1 w.2
    ¬ (P {w | ε < F₁ (out g₁ w)} ≤ ENNReal.ofReal δ ∧
       P {w | ε < F₂ (out g₂ w)} ≤ ENNReal.ofReal δ) := by
  dsimp only
  rintro ⟨h₁, h₂⟩
  let P := (A.law : Measure A.Seed).prod (stream q : Measure (ℕ → Bool))
  let S := (Set.univ : Set A.Seed) ×ˢ commonPrefix false n
  let T := fun (g : Q → Bool → V) (F : E → ℝ) =>
    {w : A.Seed × (ℕ → Bool) | ε < F (execute (sampledOracle g (stream q))
      A (fun _ => n) w.1 w.2)}
  have hs : S ⊆ T g₁ F₁ ∪ T g₂ F₂ := by
    intro w hw
    have he := execute_commonPrefix g₁ g₂ (stream q) (stream q) false hcommon A w.1 w.2 n hw.2
    rcases hsep (execute (sampledOracle g₁ (stream q)) A (fun _ => n) w.1 w.2) with h | h
    · exact Or.inl h
    · right
      rw [he] at h
      exact h
  have hmeas : P S ≤ ENNReal.ofReal (δ + δ) := by
    rw [ENNReal.ofReal_add hδ hδ]
    exact (measure_mono hs).trans ((measure_union_le _ _).trans (add_le_add h₁ h₂))
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeas
  change P.real S ≤ _ at hh
  rw [ENNReal.toReal_ofReal (add_nonneg hδ hδ)] at hh
  change ((A.law : Measure A.Seed).prod (stream q : Measure (ℕ → Bool))).real
    (Set.univ ×ˢ commonPrefix false n) ≤ _ at hh
  rw [measureReal_prod_prod, probReal_univ, one_mul, prefix_mass] at hh
  linarith

end LongTails.Proofs.BlumGladyshevTesting
