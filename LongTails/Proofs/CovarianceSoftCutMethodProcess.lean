import LongTails.Proofs.CovarianceSoftCutExecution
import LongTails.Proofs.CovarianceSoftCutProcess
import LongTails.Proofs.CovarianceSoftCutSelectionProcess

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutMethodProcess

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut
open LongTails.Algorithms.CovarianceSoftCutMethod
open LongTails.Proofs.CovarianceSoftCutProcess
open LongTails.Proofs.CovarianceSoftCutSelectionProcess
open LongTails.Proofs.CovarianceSoftCutExecution
open LongTails.Proofs.CovarianceSoftCutTrajectory
open LongTails.Proofs.CovarianceSoftCutTournament

def generatedLeaves (q : Params) (c : Config) (g : Space q → q.Ω → Space q)
    (ξ : ℕ → q.Ω) : ℕ → Space q :=
  leaves q c (sampleReplies q c.α (2/c.α) c.b g ξ)

def selectedReplies (q : Params) (c : Config) (g : Space q → q.Ω → Space q)
    (ξ : ℕ → q.Ω) : ℕ → Space q :=
  selectionReplies q c.a c.K c.n c.m c.H (generatedLeaves q c g ξ) g
    (fun i => ξ (generatorCost c+i))

def combinedReplies (q : Params) (c : Config) (g : Space q → q.Ω → Space q)
    (ξ : ℕ → q.Ω) (i : ℕ) : Space q :=
  if i < generatorCost c then sampleReplies q c.α (2/c.α) c.b g ξ i
  else if i < workCost c then selectedReplies q c g ξ (i-generatorCost c)
  else g 0 (ξ i)

lemma combinedReplies_generator (q : Params) (c : Config) (g : Space q → q.Ω → Space q)
    (ξ : ℕ → q.Ω) (i : ℕ) (hi : i < generatorCost c) :
    combinedReplies q c g ξ i = sampleReplies q c.α (2/c.α) c.b g ξ i := by
  simp [combinedReplies, hi]

lemma combinedReplies_selection (q : Params) (c : Config) (g : Space q → q.Ω → Space q)
    (ξ : ℕ → q.Ω) (i : ℕ) (hi : i < selectionCost c) :
    suffix q c (combinedReplies q c g ξ) i = selectedReplies q c g ξ i := by
  have hge : ¬ generatorCost c+i < generatorCost c := by omega
  have hwork : generatorCost c+i < workCost c := by unfold workCost; omega
  simp [suffix, combinedReplies, hge, hwork]

lemma combinedReplies_leaves (q : Params) (c : Config) (g : Space q → q.Ω → Space q)
    (ξ : ℕ → q.Ω) : leaves q c (combinedReplies q c g ξ) = generatedLeaves q c g ξ := by
  exact leaves_prefix q c _ _ (combinedReplies_generator q c g ξ)

lemma combinedReplies_output (q : Params) (c : Config) (g : Space q → q.Ω → Space q)
    (ξ : ℕ → q.Ω) : output q c (combinedReplies q c g ξ) =
      selectionOutput q c.a c.K c.n c.m c.H (generatedLeaves q c g ξ) (selectedReplies q c g ξ) := by
  unfold output
  rw [combinedReplies_leaves]
  exact selectionOutput_prefix q c.a c.K c.n c.m c.H _ _ _ (combinedReplies_selection q c g ξ)

lemma combinedReplies_consistent (q : Params) (c : Config) (hb : 0 < c.b) (hB : 0 < c.n*c.m)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (i : ℕ) :
    g (query q c i (combinedReplies q c g ξ)) (ξ i) = combinedReplies q c g ξ i := by
  by_cases hgen : i < generatorCost c
  · rw [combinedReplies_generator q c g ξ i hgen]
    simp only [query, hgen, ite_true, sampleReplies]
    rw [samplePoint_eq_generatorPoint q c.α (2/c.α) c.b hb]
    congr 1
    apply generatorPoint_eq_of_prefix
    intro j hj
    exact combinedReplies_generator q c g ξ j
      (lt_trans (lt_of_lt_of_le hj (Nat.div_mul_le_self i c.b)) hgen)
  · by_cases hwork : i < workCost c
    · have hpre : i-generatorCost c < selectionCost c := by unfold workCost at hwork; omega
      have hprobe : selectionProbe q c.a c.K c.n c.m c.H (generatedLeaves q c g ξ)
          (suffix q c (combinedReplies q c g ξ)) ((i-generatorCost c)/(c.n*c.m)) =
          selectionProbe q c.a c.K c.n c.m c.H (generatedLeaves q c g ξ)
          (selectedReplies q c g ξ) ((i-generatorCost c)/(c.n*c.m)) := by
        apply selectionProbe_prefix
        intro j hj
        exact combinedReplies_selection q c g ξ j
          (lt_trans (lt_of_lt_of_le hj (Nat.div_mul_le_self _ _)) hpre)
      simp only [query, hgen, hwork, ite_false, ite_true, combinedReplies_leaves, hprobe,
        combinedReplies]
      unfold selectedReplies
      rw [selectionReplies_consistent q c.a c.K c.n c.m c.H hB]
      congr 2
      omega
    · simp [query, combinedReplies, hgen, hwork]

lemma execute_method (q : Params) (c : Config) (hb : 0 < c.b) (hB : 0 < c.n*c.m)
    (g : Space q → q.Ω → Space q) (P : MeasureTheory.ProbabilityMeasure (ℕ → q.Ω))
    (N : ℕ) (hN : workCost c ≤ N) (ξ : ℕ → q.Ω) :
    let O : OracleTemplate.Oracle (Space q) (Space q) :=
      { Seed := fun _ => q.Ω, law := P, answer := fun _ point seed => g point.2 seed }
    OracleTemplate.execute O (method q c) (fun _ => N) () ξ =
      selectionOutput q c.a c.K c.n c.m c.H (generatedLeaves q c g ξ) (selectedReplies q c g ξ) := by
  dsimp only
  rw [← combinedReplies_output q c g ξ]
  apply execute_historyMethod q (query q c) (output q c) (method_query_prefix q c)
    { Seed := fun _ => q.Ω, law := P, answer := fun _ point seed => g point.2 seed }
    N ξ (fun i point => g point.2 (ξ i)) (by intros; rfl) (combinedReplies q c g ξ)
  · intro i hi
    exact combinedReplies_consistent q c hb hB g ξ i
  · exact method_output_prefix q c N hN

lemma generatedLeaves_eq (q : Params) (c : Config) (hb : 0 < c.b)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (i : ℕ) :
    generatedLeaves q c g ξ i = if i < 2^c.H then samplePoint q c.α (2/c.α) c.b g i ξ else 0 := by
  unfold generatedLeaves leaves
  rw [samplePoint_eq_generatorPoint q c.α (2/c.α) c.b hb]

lemma generatedLeaves_prefix (q : Params) (c : Config) (hb : 0 < c.b)
    (g : Space q → q.Ω → Space q) (ξ ζ : ℕ → q.Ω)
    (heq : ∀ i, i < generatorCost c → ξ i = ζ i) :
    generatedLeaves q c g ξ = generatedLeaves q c g ζ := by
  funext i
  rw [generatedLeaves_eq q c hb, generatedLeaves_eq q c hb]
  split_ifs with hi
  · unfold samplePoint
    rw [sampleCuts_eq_of_prefix q c.α (2/c.α) c.b i g ξ ζ]
    intro j hj
    exact heq j (lt_of_lt_of_le hj (Nat.mul_le_mul_right c.b hi.le))
  · rfl

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_generatedLeaves (q : Params) (hR : 0 < q.R) (c : Config) (hb : 0 < c.b)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) :
    Measurable (generatedLeaves q c g) := by
  apply Measurable.of_eval
  intro i
  simp only [generatedLeaves_eq q c hb]
  split_ifs
  · exact measurable_samplePoint q hR c.α (2/c.α) c.b g hg i
  · exact measurable_const

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_method_output (q : Params) (hR : 0 < q.R) (c : Config) (hb : 0 < c.b)
    (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun ξ => selectionOutput q c.a c.K c.n c.m c.H
      (generatedLeaves q c g ξ) (selectedReplies q c g ξ)) := by
  have htail : Measurable (fun ξ : ℕ → q.Ω => fun i => ξ (generatorCost c+i)) := by fun_prop
  exact (measurable_selectedOutput q c.a c.K c.n c.m c.H g hg).comp
    ((measurable_generatedLeaves q hR c hb g hg).prodMk htail)

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
lemma measurable_execute_method (q : Params) (hR : 0 < q.R) (c : Config) (hb : 0 < c.b)
    (hB : 0 < c.n*c.m) (g : Space q → q.Ω → Space q) (hg : Measurable (Function.uncurry g))
    (P : MeasureTheory.ProbabilityMeasure (ℕ → q.Ω)) (N : ℕ) (hN : workCost c ≤ N) :
    let O : OracleTemplate.Oracle (Space q) (Space q) :=
      { Seed := fun _ => q.Ω, law := P, answer := fun _ point seed => g point.2 seed }
    Measurable (fun ξ => OracleTemplate.execute O (method q c) (fun _ => N) () ξ) := by
  dsimp only
  have he : (fun ξ => OracleTemplate.execute
      ({ Seed := fun _ => q.Ω, law := P, answer := fun _ point seed => g point.2 seed } :
        OracleTemplate.Oracle (Space q) (Space q)) (method q c) (fun _ => N) () ξ) =
      (fun ξ => selectionOutput q c.a c.K c.n c.m c.H (generatedLeaves q c g ξ) (selectedReplies q c g ξ)) := by
    funext ξ
    exact execute_method q c hb hB g P N hN ξ
  rw [he]
  exact measurable_method_output q hR c hb g hg

end LongTails.Proofs.CovarianceSoftCutMethodProcess
