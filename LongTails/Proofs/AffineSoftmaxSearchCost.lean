import LongTails.Proofs.AffineSoftmaxSearchOracle
import LongTails.Proofs.AffineSoftmaxMultilevelCost

namespace LongTails.Proofs.AffineSoftmaxSearchCost

open MeasureTheory
open LongTails.Algorithms.AffineSoftmaxProx
open LongTails.Algorithms.AffineSoftmaxEstimator
open OracleTemplate.ComponentEnvelope
open LongTails.Algorithms.AffineSoftmaxSearch

lemma probePlan_cost_domination {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (center otherCenter : E) {τ L G r floor μ : ℝ}
    (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r) (hf : 0 < floor) (hfm : floor ≤ μ)
    (project otherProject : E → E) (reply otherReply : Fin m × E → ℝ × E)
    (seeds : ProbeSeed) (b : ℕ) :
    Program.cost reply (probePlan m center τ L G r μ project seeds b) ≤
      Program.cost otherReply (probePlan m otherCenter τ L G r floor otherProject seeds b) := by
  simp only [AffineSoftmaxSearchOracle.probePlan_cost, AffineSoftmaxSearch.boostedCachedPlan_cost]
  apply Nat.add_le_add_left
  apply Nat.add_le_add_right
  apply Finset.sum_le_sum
  intro j _
  apply AffineSoftmaxMultilevelCost.cachedProxPlan_cost_domination _ _ hτ hL hG hr hf hfm
  · positivity
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfm (sq_nonneg r)) (by norm_num)

lemma bisectPlan_cost_le_tail {Q R : Type*} (probe : ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r : ℝ) {floor cap : ℝ} (B : ℕ → ℕ) (n : ℕ)
    (hcost : ∀ i < n, ∀ μ ∈ Set.Icc floor cap, Program.cost reply (probe i μ) ≤ B i)
    (fuel index : ℕ) (hindex : index + fuel < n) (lower upper : ℝ)
    (hl : lower ∈ Set.Icc floor cap) (hu : upper ∈ Set.Icc floor cap) :
    Program.cost reply (bisectPlan probe r fuel index lower upper) ≤ ∑ i ∈ Finset.Ico index n, B i := by
  induction fuel generalizing index lower upper with
  | zero =>
    have hm : (lower + upper) / 2 ∈ Set.Icc floor cap := by constructor <;> linarith [hl.1, hl.2, hu.1, hu.2]
    simp only [bisectPlan, Program.cost_bind, Program.cost, Nat.add_zero]
    exact (hcost index (by omega) _ hm).trans
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩))
  | succ fuel ih =>
    have hm : (lower + upper) / 2 ∈ Set.Icc floor cap := by constructor <;> linarith [hl.1, hl.2, hu.1, hu.2]
    have hs := Finset.sum_eq_sum_Ico_succ_bot (show index < n by omega) B
    have hb := hcost index (by omega) _ hm
    have hleft := ih (index + 1) (by omega) lower ((lower + upper) / 2) hl hm
    have hright := ih (index + 1) (by omega) ((lower + upper) / 2) upper hm hu
    simp only [bisectPlan, Program.cost_bind]
    split_ifs
    · omega
    · omega
    · simp only [Program.cost]
      omega

lemma gridPlan_cost_le_tail {Q R : Type*} (probe : ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r : ℝ) {floor cap : ℝ} (hc : 0 ≤ cap) (hfc : floor ≤ cap)
    (B : ℕ → ℕ) (n H : ℕ) (hn : 2 * H + 8 < n)
    (hcost : ∀ i < n, ∀ μ ∈ Set.Icc floor cap, Program.cost reply (probe i μ) ≤ B i)
    (fuel index : ℕ) (hindex : index + fuel = H) (previous : ℝ)
    (hp : previous ∈ Set.Icc floor cap) :
    Program.cost reply (gridPlan probe r floor cap H fuel index previous) ≤
      ∑ i ∈ Finset.Ico index n, B i := by
  induction fuel generalizing index previous with
  | zero =>
    have hcurrent : max floor (cap / 2 ^ index) ∈ Set.Icc floor cap :=
      ⟨le_max_left _ _, max_le hfc (div_le_self hc (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))⟩
    have hb := hcost index (by omega) _ hcurrent
    have hbis := bisectPlan_cost_le_tail probe reply r B n hcost (H + 7) (H + 1)
      (by omega) _ previous hcurrent hp
    have hsub : (∑ i ∈ Finset.Ico (H + 1) n, B i) ≤ ∑ i ∈ Finset.Ico (index + 1) n, B i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_Ico] at hi ⊢
        omega
      · intro i _ _
        exact Nat.zero_le _
    have hs := Finset.sum_eq_sum_Ico_succ_bot (show index < n by omega) B
    simp only [gridPlan, Program.cost_bind]
    split_ifs <;> try simp only [Program.cost]
    all_goals omega
  | succ fuel ih =>
    have hcurrent : max floor (cap / 2 ^ index) ∈ Set.Icc floor cap :=
      ⟨le_max_left _ _, max_le hfc (div_le_self hc (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))⟩
    have hb := hcost index (by omega) _ hcurrent
    have hbis := bisectPlan_cost_le_tail probe reply r B n hcost (H + 7) (H + 1)
      (by omega) _ previous hcurrent hp
    have hsub : (∑ i ∈ Finset.Ico (H + 1) n, B i) ≤ ∑ i ∈ Finset.Ico (index + 1) n, B i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp only [Finset.mem_Ico] at hi ⊢
        omega
      · intro i _ _
        exact Nat.zero_le _
    have hrec := ih (index + 1) (by omega) _ hcurrent
    have hs := Finset.sum_eq_sum_Ico_succ_bot (show index < n by omega) B
    simp only [gridPlan, Program.cost_bind]
    split_ifs <;> try simp only [Program.cost]
    all_goals omega

lemma searchPlan_cost_le_sum {Q R : Type*} (probe : ℕ → ℝ → Program Q R ℝ)
    (reply : Q → R) (r : ℝ) {floor cap : ℝ} (hc : 0 ≤ cap) (hfc : floor ≤ cap)
    (B : ℕ → ℕ) (H : ℕ)
    (hcost : ∀ i < 2 * H + 9, ∀ μ ∈ Set.Icc floor cap, Program.cost reply (probe i μ) ≤ B i) :
    Program.cost reply (searchPlan probe r floor cap H) ≤ ∑ i ∈ Finset.range (2 * H + 9), B i := by
  simpa only [searchPlan, Nat.Ico_zero_eq_range] using
    gridPlan_cost_le_tail probe reply r hc hfc B (2 * H + 9) H (by omega) hcost H 0 (by omega) cap ⟨hfc, le_rfl⟩

lemma regularizationSearchPlan_cost_domination {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (m : ℕ) [NeZero m] (X : Set E)
    (state : LongTails.Algorithms.CappedProximal.State E) (otherCenter : E)
    {τ L G r floor cap : ℝ} (hτ : 0 < τ) (hL : 0 ≤ L) (hG : 0 < G) (hr : 0 < r)
    (hf : 0 < floor) (hfc : floor ≤ cap) (H b : ℕ) (seeds : ℕ → ProbeSeed)
    (otherProject : E → E) (reply otherReply : Fin m × E → ℝ × E) :
    Program.cost reply (regularizationSearchPlan m X state τ L G r floor cap H b seeds) ≤
      ∑ i ∈ Finset.range (2 * H + 9),
        Program.cost otherReply (probePlan m otherCenter τ L G r floor otherProject (seeds i) b) := by
  unfold regularizationSearchPlan
  apply searchPlan_cost_le_sum _ reply r (hf.le.trans hfc) hfc _ H
  intro i _ μ _
  exact probePlan_cost_domination m _ otherCenter hτ hL hG hr hf (le_max_left floor μ)
    _ otherProject reply otherReply (seeds i) b

lemma probePlan_cost_moments {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ) [NeZero m] (center : E) (τ L : ℝ) {G r μ : ℝ}
    (hG : 0 < G) (hr : 0 < r) (hμ : 0 < μ) (project : E → E)
    (reply : Fin m × E → ℝ × E) (b : ℕ) :
    let δ := μ * r ^ 2 / 32768
    let S := L + 2 * G ^ 2 / τ + μ
    let V := 8 * (L ^ 2 * r ^ 2 + G ^ 2 * L ^ 2 * r ^ 4 / τ ^ 2)
    Integrable (fun seeds => (Program.cost reply (probePlan m center τ L G r μ project seeds b) : ℝ))
      (probeLaw : Measure ProbeSeed) ∧
    (∫ seeds, (Program.cost reply (probePlan m center τ L G r μ project seeds b) : ℝ)
      ∂(probeLaw : Measure ProbeSeed)) ≤ m + (b : ℝ) * m + b *
        ((16 * Real.sqrt (S / μ) + 4) *
          (LongTails.Algorithms.AffineSoftmaxAcceleration.restartRounds (G * r) δ : ℝ) + 1024 * V / (μ * δ)) := by
  let δ := μ * r ^ 2 / 32768
  let s : Snapshot (Fin m) E := ⟨center, (fun i => (reply (i, center)).1), (fun i => (reply (i, center)).2)⟩
  let c := fun seed : ProxSeed => (Program.cost reply (cachedProxPlan s τ L G r μ δ project seed) : ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlevel := AffineSoftmaxMultilevelCost.levelPlan_cost_bound s τ L hG hr hμ hδ project reply 0
  simp only [levelPlan, pow_zero, div_one, Nat.cast_zero, add_zero, mul_one] at hlevel
  have hi : Integrable c (proxLaw : Measure ProxSeed) := hlevel.1
  have hp j : MeasurePreserving (fun seeds : ProbeSeed => seeds j)
      (probeLaw : Measure ProbeSeed) (proxLaw : Measure ProxSeed) :=
    measurePreserving_eval_infinitePi (fun _ : ℕ => (proxLaw : Measure ProxSeed)) j
  have hji j : Integrable (fun seeds : ProbeSeed => c (seeds j)) (probeLaw : Measure ProbeSeed) :=
    (hp j).integrable_comp_of_integrable hi
  have hmean j : (∫ seeds : ProbeSeed, c (seeds j) ∂(probeLaw : Measure ProbeSeed)) =
      ∫ seed, c seed ∂(proxLaw : Measure ProxSeed) := by
    rw [← integral_map (hp j).measurable.aemeasurable (by rw [(hp j).map_eq]; exact hi.aestronglyMeasurable), (hp j).map_eq]
  have he : (fun seeds : ProbeSeed => (Program.cost reply (probePlan m center τ L G r μ project seeds b) : ℝ)) =
      (fun seeds => (m : ℝ) + (∑ j ∈ Finset.range b, c (seeds j)) + (b : ℝ) * m) := by
    funext seeds
    simp only [AffineSoftmaxSearchOracle.probePlan_cost, AffineSoftmaxSearch.boostedCachedPlan_cost,
      Nat.cast_add, Nat.cast_sum, Nat.cast_mul, c, s, δ]
    ring
  have hsum := integrable_finsetSum (Finset.range b) (fun j _ => hji j)
  have hms : Integrable (fun seeds : ProbeSeed => (m : ℝ) + ∑ j ∈ Finset.range b, c (seeds j))
      (probeLaw : Measure ProbeSeed) := (integrable_const (m : ℝ)).add hsum
  have hbm : Integrable (fun _ : ProbeSeed => (b : ℝ) * m) (probeLaw : Measure ProbeSeed) := integrable_const _
  refine ⟨?_, ?_⟩
  · rw [he]
    exact ((integrable_const (m : ℝ)).add hsum).add (integrable_const _)
  · rw [he, integral_add hms hbm,
      integral_add (integrable_const (m : ℝ)) hsum, integral_finsetSum _ (fun j _ => hji j)]
    simp only [hmean, integral_const, probReal_univ, one_smul,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hh := mul_le_mul_of_nonneg_left hlevel.2 (Nat.cast_nonneg b)
    dsimp only [δ, c] at hh ⊢
    linarith

end LongTails.Proofs.AffineSoftmaxSearchCost
