import LongTails.Proofs.CountdownPath
import LongTails.Proofs.ExecutionHistory

open MeasureTheory

namespace OracleTemplate.CountdownMarkov

def sampledOracle {Query Reply : Type*} {Ω : Type} [MeasurableSpace Ω]
    (g : Query → Ω → Reply) (P : ProbabilityMeasure (ℕ → Ω)) :
    OracleTemplate.Oracle Query Reply where
  Seed := fun _ => Ω
  law := P
  answer := fun _ q z => g q.2 z

lemma execute_commonPrefix {Query Reply Output : Type*} {Ω : Type} [MeasurableSpace Ω]
    (g₁ g₂ : Query → Ω → Reply) (P₁ P₂ : ProbabilityMeasure (ℕ → Ω))
    (b : Ω) (hcommon : ∀ x, g₁ x b = g₂ x b)
    (A : OracleTemplate.Algorithm Query Reply Output) (seed : A.Seed)
    (ξ : ℕ → Ω) (N : ℕ) (hξ : ξ ∈ commonPrefix b N) :
    OracleTemplate.execute (sampledOracle g₁ P₁) A (fun _ => N) seed ξ =
      OracleTemplate.execute (sampledOracle g₂ P₂) A (fun _ => N) seed ξ := by
  have hist : ∀ k, k ≤ N →
      OracleTemplate.executeIndexedState (sampledOracle g₁ P₁) A seed ξ k =
        OracleTemplate.executeIndexedState (sampledOracle g₂ P₂) A seed ξ k := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      simp only [OracleTemplate.executeIndexedState]
      rw [congrArg Prod.fst hp, congrArg Prod.snd hp]
      simp only [sampledOracle, OracleTemplate.executeIndexedState_length]
      rw [hξ k (by omega), hcommon]
  unfold OracleTemplate.execute
  erw [OracleTemplate.executeWithTrace_eq_executeIndexedState,
    OracleTemplate.executeWithTrace_eq_executeIndexedState, hist N le_rfl]


lemma integral_pair_lower {W : Type*} [MeasurableSpace W]
    (P : ProbabilityMeasure W) (S : Set W) (hS : MeasurableSet S)
    (f g : W → ℝ) (hf : Integrable f (P : Measure W))
    (hg : Integrable g (P : Measure W))
    (hf0 : ∀ w, 0 ≤ f w) (hg0 : ∀ w, 0 ≤ g w)
    (c : ℝ) (hpair : ∀ w ∈ S, c ≤ f w + g w) :
    c * (P : Measure W).real S ≤ (∫ w, f w ∂(P : Measure W)) +
      (∫ w, g w ∂(P : Measure W)) := by
  classical
  have hi : Integrable (S.indicator (fun _ : W => c)) (P : Measure W) :=
    (integrable_const c).indicator hS
  have h := integral_mono hi (hf.add hg) (fun w => show
      S.indicator (fun _ : W => c) w ≤ f w + g w from by
    by_cases hw : w ∈ S
    · simpa only [Set.indicator_of_mem hw] using hpair w hw
    · simp only [Set.indicator_of_notMem hw]
      exact add_nonneg (hf0 w) (hg0 w))
  simp only [Pi.add_apply] at h
  rw [integral_add hf hg] at h
  simpa [integral_indicator hS, measureReal_def, mul_comm] using h

lemma execution_pair_lower {Q R O : Type*} {Ω : Type} [MeasurableSpace Ω]
    (g₁ g₂ : Q → Ω → R) (P : ProbabilityMeasure (ℕ → Ω))
    (b : Ω) (hb : MeasurableSet ({b} : Set Ω)) (hcommon : ∀ x, g₁ x b = g₂ x b)
    (A : OracleTemplate.Algorithm Q R O) (N : ℕ)
    (F₁ F₂ : O → ℝ) (hF₁ : ∀ x, 0 ≤ F₁ x) (hF₂ : ∀ x, 0 ≤ F₂ x)
    (c : ℝ) (hsep : ∀ x, c ≤ F₁ x + F₂ x)
    (hi₁ : Integrable (fun w : A.Seed × (ℕ → Ω) =>
      F₁ (OracleTemplate.execute (sampledOracle g₁ P) A (fun _ => N) w.1 w.2))
      ((A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω))))
    (hi₂ : Integrable (fun w : A.Seed × (ℕ → Ω) =>
      F₂ (OracleTemplate.execute (sampledOracle g₂ P) A (fun _ => N) w.1 w.2))
      ((A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω)))) :
    c * (P : Measure (ℕ → Ω)).real (commonPrefix b N) ≤
      (∫ w : A.Seed × (ℕ → Ω),
        F₁ (OracleTemplate.execute (sampledOracle g₁ P) A (fun _ => N) w.1 w.2)
        ∂((A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω)))) +
      (∫ w : A.Seed × (ℕ → Ω),
        F₂ (OracleTemplate.execute (sampledOracle g₂ P) A (fun _ => N) w.1 w.2)
        ∂((A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω)))) := by
  let joint : ProbabilityMeasure (A.Seed × (ℕ → Ω)) :=
    ⟨(A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω)), inferInstance⟩
  have h := integral_pair_lower joint (Set.univ ×ˢ commonPrefix b N)
    (MeasurableSet.univ.prod (measurableSet_commonPrefix b hb N))
    _ _ hi₁ hi₂ (fun w => hF₁ _) (fun w => hF₂ _) c (by
      intro w hw
      erw [execute_commonPrefix g₁ g₂ P P b hcommon A w.1 w.2 N hw.2]
      exact hsep _)
  change c * ((A.law : Measure A.Seed).prod (P : Measure (ℕ → Ω))).real
    (Set.univ ×ˢ commonPrefix b N) ≤ _ at h
  rw [measureReal_prod_prod] at h
  simpa [measureReal_def, joint] using h


end OracleTemplate.CountdownMarkov
