import LongTails.Algorithms.SpikedSoftCutMethod
import LongTails.Proofs.CovarianceSoftCutTrajectory
import LongTails.Proofs.StratifiedSubGaussianSampling
import LongTails.Proofs.SpikedSoftCutSelection
import LongTails.Proofs.Execution
import LongTails.Proofs.CovarianceSoftCutExecution

namespace LongTails.Proofs.SpikedSoftCutMethodExecution

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCut
open LongTails.Algorithms.SpikedSoftCutMethod
open LongTails.Proofs.CovarianceSoftCutTrajectory

lemma supportPoints_prefix (q : Params) (c : Config) (r s : ℕ → Space q)
    (h : ∀ i, i < c.T*c.b → r i = s i) : supportPoints q c r = supportPoints q c s := by
  funext i
  unfold supportPoints innerPoints
  apply generatorPoint_eq_of_prefix
  intro j hj
  apply congrArg (tail q)
  exact h j (lt_of_lt_of_le hj (Nat.mul_le_mul_right c.b i.isLt.le))

lemma innerEstimates_prefix (q : Params) (c : Config) (r s : ℕ → Space q)
    (h : ∀ i, i < c.T*c.b → r i = s i) :
    innerEstimates q c.α c.T c.b (fun i => tail q (r i)) =
      innerEstimates q c.α c.T c.b (fun i => tail q (s i)) := by
  funext i
  unfold innerEstimates LongTails.Algorithms.CovarianceSoftCut.batchMean
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (tail q)
  apply h
  have hh := Nat.mul_le_mul_right c.b (Nat.succ_le_of_lt i.isLt)
  rw [Nat.succ_mul] at hh
  have hj := j.isLt
  omega

lemma weights_prefix (q : Params) (c : Config) (r s : ℕ → Space q)
    (h : ∀ i, i < c.T*c.b → r i = s i) : weights q c r = weights q c s := by
  have hp := supportPoints_prefix q c r s h
  unfold supportPoints at hp
  unfold weights innerWeights
  rw [hp, innerEstimates_prefix q c r s h]

lemma sampleCount_prefix (q : Params) (c : Config) (k : ℕ) (r s : ℕ → Space q)
    (h : ∀ i, i < c.T*c.b → r i = s i) : sampleCount q c k r = sampleCount q c k s := by
  unfold sampleCount
  rw [weights_prefix q c r s h]

lemma sampleStart_prefix (q : Params) (c : Config) (k : ℕ) (r s : ℕ → Space q)
    (h : ∀ i, i < c.T*c.b → r i = s i) : sampleStart q c k r = sampleStart q c k s := by
  unfold sampleStart
  rw [sampleCount_prefix q c k r s h]

lemma scalarQuery_prefix (q : Params) (c : Config) (k : ℕ) (state : OuterState q)
    (r s : ℕ → Space q) (h : ∀ i, i < c.T*c.b → r i = s i) (t : ℕ) :
    scalarQuery q c k state r t = scalarQuery q c k state s t := by
  unfold scalarQuery
  rw [sampleStart_prefix q c k r s h, supportPoints_prefix q c r s h]

lemma primalOutput_prefix (q : Params) (c : Config) (state : OuterState q)
    (r s : ℕ → Space q) (h : ∀ i, i < c.T*c.b → r i = s i) :
    primalOutput q c state r = primalOutput q c state s := by
  have hw := weights_prefix q c r s h
  have hp := supportPoints_prefix q c r s h
  unfold weights at hw
  unfold supportPoints at hp
  unfold primalOutput innerOutput
  rw [hw, hp]

lemma sampleStart_succ (q : Params) (c : Config) (k : ℕ) (r : ℕ → Space q) (i : ℕ) :
    sampleStart q c k r (i+1) = sampleStart q c k r i + sampleCount q c k r i := by
  exact Finset.sum_range_succ _ _

lemma sampleStart_mono (q : Params) (c : Config) (k : ℕ) (r : ℕ → Space q)
    {i j : ℕ} (hij : i ≤ j) : sampleStart q c k r i ≤ sampleStart q c k r j := by
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hij)

lemma sampleStart_total_le (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (k : ℕ) (r : ℕ → Space q) : sampleStart q c k r c.T ≤ c.N k+c.T := by
  have hw (i : Fin c.T) : 0 ≤ weights q c r i :=
    SpikedSoftCutSelection.certificateWeights_nonneg q c.α c.T c.n hn _ _ i
  have hsum : ∑ i, weights q c r i = 1 :=
    SpikedSoftCutSelection.certificateWeights_sum q c.α c.T c.n hT _ _
  have hh := StratifiedSubGaussianSampling.ceiling_cost (c.N k) (weights q c r) hw hsum
  unfold sampleStart
  rw [← Fin.sum_univ_eq_sum_range]
  simpa only [sampleCount, dite_eq_left (Fin.isLt _)] using hh

lemma sample_reply_before_epoch_end (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (k : ℕ) (r : ℕ → Space q) (i : Fin c.T) (j : ℕ)
    (hj : j < sampleCount q c k r i) :
    c.T*c.b+sampleStart q c k r i+j < epochCost c k := by
  have hs := sampleStart_succ q c k r i
  have hm := sampleStart_mono q c k r (Nat.succ_le_of_lt i.isLt)
  have ht := sampleStart_total_le q c hT hn k r
  simp only [Nat.succ_eq_add_one] at hm
  unfold epochCost
  omega

lemma scalarQuery_at_sample (q : Params) (c : Config) (k : ℕ) (state : OuterState q)
    (r : ℕ → Space q) (i : Fin c.T) (j : ℕ) (hj : j < sampleCount q c k r i) :
    scalarQuery q c k state r (sampleStart q c k r i+j) =
      join q (center q state) (supportPoints q c r i) := by
  have hf : (List.finRange c.T).find? (fun l =>
      sampleStart q c k r i+j < sampleStart q c k r (l.val+1)) = some i := by
    apply List.find?_eq_some_iff_getElem.mpr
    refine ⟨?_, i.val, by simp, ?_, ?_⟩
    · simp only [decide_eq_true_eq]
      rw [sampleStart_succ]
      omega
    · simp
    · intro l hl
      have hm := sampleStart_mono q c k r (Nat.succ_le_of_lt hl)
      simp only [Nat.succ_eq_add_one] at hm
      have hh : ¬ sampleStart q c k r i+j < sampleStart q c k r (l+1) := by omega
      simpa using hh
  unfold scalarQuery
  rw [hf]

noncomputable def scalarSampleIndex (q : Params) (c : Config) (k : ℕ) (r : ℕ → Space q)
    (j : (i : Fin c.T) × Fin (sampleCount q c k r i)) : ℕ :=
  sampleStart q c k r j.1+j.2

lemma scalarSampleIndex_injective (q : Params) (c : Config) (k : ℕ) (r : ℕ → Space q) :
    Function.Injective (scalarSampleIndex q c k r) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  change sampleStart q c k r i+a = sampleStart q c k r j+b at h
  have hi : i = j := by
    apply Fin.ext
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hm := sampleStart_mono q c k r (Nat.succ_le_of_lt hij)
      have hs := sampleStart_succ q c k r i
      simp only [Nat.succ_eq_add_one] at hm
      have ha := a.isLt
      omega
    · have hm := sampleStart_mono q c k r (Nat.succ_le_of_lt hji)
      have hs := sampleStart_succ q c k r j
      simp only [Nat.succ_eq_add_one] at hm
      have hb := b.isLt
      omega
  subst j
  have hab : a = b := Fin.ext (Nat.add_left_cancel h)
  subst b
  rfl

lemma scalarSampleIndex_lt (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (k : ℕ) (r : ℕ → Space q) (j : (i : Fin c.T) × Fin (sampleCount q c k r i)) :
    scalarSampleIndex q c k r j < c.N k+c.T := by
  have hh := sample_reply_before_epoch_end q c hT hn k r j.1 j.2 j.2.isLt
  unfold epochCost at hh
  unfold scalarSampleIndex
  omega

lemma scalarEstimate_prefix (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (k : ℕ) (r s : ℕ → Space q) (h : ∀ i, i < epochCost c k → r i = s i) :
    scalarEstimate q c k r = scalarEstimate q c k s := by
  have hi : ∀ i, i < c.T*c.b → r i = s i := fun i hi => h i (by unfold epochCost; omega)
  unfold scalarEstimate
  rw [weights_prefix q c r s hi, sampleCount_prefix q c k r s hi, sampleStart_prefix q c k r s hi]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h _ (sample_reply_before_epoch_end q c hT hn k s i j (Finset.mem_range.mp hj))]

lemma nextState_prefix (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (k : ℕ) (state : OuterState q) (r s : ℕ → Space q)
    (h : ∀ i, i < epochCost c k → r i = s i) :
    nextState q c k state r = nextState q c k state s := by
  have hi : ∀ i, i < c.T*c.b → r i = s i := fun i hi => h i (by unfold epochCost; omega)
  unfold nextState
  rw [scalarEstimate_prefix q c hT hn k r s h, primalOutput_prefix q c state r s hi]

lemma queryFrom_prefix (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (remaining k : ℕ) (state : OuterState q) (r s : ℕ → Space q) (t : ℕ)
    (h : ∀ i, i < t → r i = s i) :
    queryFrom q c k remaining state r t = queryFrom q c k remaining state s t := by
  induction remaining generalizing k state r s t with
  | zero => rfl
  | succ remaining ih =>
    simp only [queryFrom]
    split_ifs with hg he
    · congr 1
      apply generatorPoint_eq_of_prefix
      intro i hi
      apply congrArg (tail q)
      exact h i (lt_of_lt_of_le hi (Nat.div_mul_le_self t c.b))
    · exact scalarQuery_prefix q c k state r s (fun i hi => h i (by omega)) _
    · have hstate : nextState q c k state r = nextState q c k state s :=
        nextState_prefix q c hT hn k state r s (fun i hi => h i (by omega))
      rw [hstate]
      apply ih
      intro i hi
      apply h
      omega

def remainingCost (c : Config) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | k, remaining+1 => epochCost c k + remainingCost c (k+1) remaining

lemma outputFrom_prefix (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (remaining k : ℕ) (state : OuterState q) (r s : ℕ → Space q)
    (h : ∀ i, i < remainingCost c k remaining → r i = s i) :
    outputFrom q c k remaining state r = outputFrom q c k remaining state s := by
  induction remaining generalizing k state r s with
  | zero => rfl
  | succ remaining ih =>
    have hstate : nextState q c k state r = nextState q c k state s := by
      apply nextState_prefix q c hT hn k state r s
      intro i hi
      apply h
      simp only [remainingCost]
      omega
    simp only [outputFrom, hstate]
    apply ih
    intro i hi
    apply h
    simp only [remainingCost]
    omega

lemma execute_method (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (O : OracleTemplate.Oracle (Space q) (Space q)) (N : ℕ)
    (hN : remainingCost c 0 c.K ≤ N) (ξ : (k : ℕ) → O.Seed k)
    (response : ℕ → (Fin 1 × Space q) → Space q)
    (hanswer : ∀ history point, O.answer history point (ξ history.length) = response history.length point)
    (replies : ℕ → Space q)
    (hresponse : ∀ i, i < N → response i
      (0, queryFrom q c 0 c.K (initialState q) replies i) = replies i) :
    OracleTemplate.execute O (method q c) (fun _ => N) () ξ =
      outputFrom q c 0 c.K (initialState q) replies := by
  let qp : LongTails.Setups.CovarianceBoundedConvex.Params :=
    { d := q.m+1, Ω := q.Ω, L := q.G, R := q.R, σ := 0, ε := q.ε }
  have hquery : ∀ k r s, (∀ i, i < k → r i = s i) →
      queryFrom q c 0 c.K (initialState q) r k = queryFrom q c 0 c.K (initialState q) s k :=
    fun k r s h => queryFrom_prefix q c hT hn c.K 0 (initialState q) r s k h
  have houtput : ∀ r s, (∀ i, i < N → r i = s i) →
      outputFrom q c 0 c.K (initialState q) r = outputFrom q c 0 c.K (initialState q) s := by
    intro r s h
    exact outputFrom_prefix q c hT hn c.K 0 (initialState q) r s
      (fun i hi => h i (lt_of_lt_of_le hi hN))
  exact CovarianceSoftCutExecution.execute_historyMethod qp
    (fun k r => queryFrom q c 0 c.K (initialState q) r k)
    (outputFrom q c 0 c.K (initialState q)) hquery O N ξ response hanswer replies hresponse houtput

end LongTails.Proofs.SpikedSoftCutMethodExecution
