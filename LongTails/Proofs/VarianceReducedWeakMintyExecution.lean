import LongTails.Algorithms.VarianceReducedWeakMinty
import Mathlib.Data.List.GetD
import LongTails.Proofs.ReshufflingExecution

namespace OracleTemplate.VarianceReducedWeakMinty

open LongTails.Setups.FiniteSumWeakMintyInclusion
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

lemma eval_fullPlan (F : Fin n → E → E) (J : ℝ → E → E) (x : E) :
    QueryPlan.eval (answer F J) (fullPlan x) = operator F x := by
  simp [fullPlan, fullSumPlan, RandomReshuffling.eval_cast, QueryPlan.eval_map, QueryPlan.eval_traverse,
    QueryPlan.eval, answer, operator, List.sum_ofFn]

lemma eval_batchPlan (F : Fin n → E → E) (J : ℝ → E → E) (w y : E)
    {b : ℕ} (ξ : Fin b → Fin n) :
    QueryPlan.eval (answer F J) (batchPlan w (operator F w) y ξ) = batchValue F w y ξ := by
  simp [batchPlan, QueryPlan.eval_map, QueryPlan.eval_traverse, differencePlan,
    QueryPlan.eval, answer, batchValue, List.sum_ofFn]

lemma eval_estimatorPlan (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (w y : E) {b : ℕ} (ξ : Fin b → Fin n) :
    QueryPlan.eval (answer F J) (estimatorPlan exact w (operator F w) y ξ) =
      estimatorValue exact F w y ξ := by
  cases exact with
  | false => exact eval_batchPlan F J w y ξ
  | true => exact eval_fullPlan F J y

lemma eval_picardStepPlan (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (η : ℝ) (z w y : E) {b : ℕ} (ξ : Fin b → Fin n) :
    QueryPlan.eval (answer F J) (picardStepPlan exact η z w (operator F w) y ξ) =
      let g := estimatorValue exact F w y ξ
      let ynext := J η (z - η • g)
      (ynext, η⁻¹ • (z - ynext) - g) := by
  simp [picardStepPlan, QueryPlan.eval_bind, eval_estimatorPlan, QueryPlan.eval, answer]

lemma eval_picardStepPlan_member (exact : Bool) (F : Fin n → E → E)
    (J : ℝ → E → E) (A : E → Set E) {η : ℝ} (hη : 0 < η)
    (hJ : ∀ z, η⁻¹ • (z - J η z) ∈ A (J η z))
    (z w y : E) {b : ℕ} (ξ : Fin b → Fin n) :
    let yv := QueryPlan.eval (answer F J) (picardStepPlan exact η z w (operator F w) y ξ)
    yv.2 ∈ A yv.1 := by
  rw [eval_picardStepPlan]
  dsimp only
  have h := hJ (z - η • estimatorValue exact F w y ξ)
  convert h using 1
  simp only [smul_sub, smul_smul, inv_mul_cancel₀ hη.ne', one_smul]
  abel

lemma eval_picardPlan_member (exact : Bool) (F : Fin n → E → E)
    (J : ℝ → E → E) (A : E → Set E) {η : ℝ} (hη : 0 < η)
    (hJ : ∀ z, η⁻¹ • (z - J η z) ∈ A (J η z))
    (z w : E) {b : ℕ} (k : ℕ) (hk : 0 < k)
    (ξ : Fin k → Fin b → Fin n) (state : E × E) :
    let yv := QueryPlan.eval (answer F J) (picardPlan exact η z w (operator F w) k ξ state)
    yv.2 ∈ A yv.1 := by
  induction k generalizing state with
  | zero => omega
  | succ k ih =>
    simp only [picardPlan, QueryPlan.eval_bind]
    cases k with
    | zero =>
      exact eval_picardStepPlan_member exact F J A hη hJ z w state.1 (ξ 0)
    | succ k => exact ih (by omega) _ _

lemma eval_stepsPlan_length (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (η s p : ℝ) (w : E) {b j : ℕ} (q : ℕ) (ξ : Fin q → StepSeed n b j) (x : E) :
    (QueryPlan.eval (answer F J) (stepsPlan exact η s p w (operator F w) q ξ x)).2.length = q := by
  induction q generalizing x with
  | zero => rfl
  | succ q ih =>
    rw [stepsPlan]
    erw [QueryPlan.eval_bind, QueryPlan.eval_map]
    simp only [List.length_cons, ih]

lemma eval_epochPlan_length (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (η s p : ℝ) (x w : E) {b j q : ℕ} (ξ : EpochSeed n b j q) :
    (QueryPlan.eval (answer F J) (epochPlan exact η s p x w ξ)).2.length = q := by
  simp only [epochPlan, QueryPlan.eval_bind, QueryPlan.eval_map, eval_fullPlan,
    List.length_map, eval_stepsPlan_length]

lemma eval_epochsPlan_length (exact : Bool) (F : Fin n → E → E) (J : ℝ → E → E)
    (η s p : ℝ) {b j q : ℕ} (M : ℕ) (ξ : Fin M → EpochSeed n b j q) (state : E × E) :
    (QueryPlan.eval (answer F J) (epochsPlan exact η s p M ξ state)).2.length = q * M := by
  induction M generalizing state with
  | zero => simp [epochsPlan, QueryPlan.eval]
  | succ M ih =>
    simp only [epochsPlan, QueryPlan.eval_bind, QueryPlan.eval_map, List.length_append,
      eval_epochPlan_length, ih]
    simp [Nat.mul_succ, Nat.add_comm]

lemma eval_stepPlan_member (exact : Bool) (F : Fin n → E → E)
    (J : ℝ → E → E) (A : E → Set E) {η : ℝ} (hη : 0 < η)
    (hJ : ∀ z, η⁻¹ • (z - J η z) ∈ A (J η z))
    (s p : ℝ) (x w : E) {b j : ℕ} (hj : 0 < j) (ξ : StepSeed n b j) :
    let state := QueryPlan.eval (answer F J) (stepPlan exact η s p x w (operator F w) ξ)
    state.2.2 ∈ A state.2.1 := by
  simp only [stepPlan, QueryPlan.eval_bind, QueryPlan.eval_map]
  exact eval_picardPlan_member exact F J A hη hJ ((1 - p) • x + p • w) w j hj ξ.1 _

lemma eval_stepsPlan_members (exact : Bool) (F : Fin n → E → E)
    (J : ℝ → E → E) (A : E → Set E) {η : ℝ} (hη : 0 < η)
    (hJ : ∀ z, η⁻¹ • (z - J η z) ∈ A (J η z))
    (s p : ℝ) (w : E) {b j : ℕ} (hj : 0 < j) (q : ℕ)
    (ξ : Fin q → StepSeed n b j) (x : E) :
    ∀ st ∈ (QueryPlan.eval (answer F J) (stepsPlan exact η s p w (operator F w) q ξ x)).2,
      st.2.2 ∈ A st.2.1 := by
  induction q generalizing x with
  | zero => simp [stepsPlan, QueryPlan.eval]
  | succ q ih =>
    rw [stepsPlan]
    erw [QueryPlan.eval_bind, QueryPlan.eval_map]
    intro st hst
    rcases List.mem_cons.mp hst with hst | hst
    · subst st
      exact eval_stepPlan_member exact F J A hη hJ s p x w hj (ξ 0)
    · exact ih _ _ st hst

lemma eval_epochPlan_members (exact : Bool) (F : Fin n → E → E)
    (J : ℝ → E → E) (A : E → Set E) {η : ℝ} (hη : 0 < η)
    (hJ : ∀ z, η⁻¹ • (z - J η z) ∈ A (J η z))
    (s p : ℝ) (x w : E) {b j q : ℕ} (hj : 0 < j) (ξ : EpochSeed n b j q) :
    ∀ yv ∈ (QueryPlan.eval (answer F J) (epochPlan exact η s p x w ξ)).2,
      yv.2 ∈ A yv.1 := by
  simp only [epochPlan, QueryPlan.eval_bind, QueryPlan.eval_map, eval_fullPlan]
  intro yv hyv
  obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hyv
  exact eval_stepsPlan_members exact F J A hη hJ s p w hj q ξ.1 x st hst

lemma eval_epochsPlan_members (exact : Bool) (F : Fin n → E → E)
    (J : ℝ → E → E) (A : E → Set E) {η : ℝ} (hη : 0 < η)
    (hJ : ∀ z, η⁻¹ • (z - J η z) ∈ A (J η z))
    (s p : ℝ) {b j q : ℕ} (hj : 0 < j) (M : ℕ)
    (ξ : Fin M → EpochSeed n b j q) (state : E × E) :
    ∀ yv ∈ (QueryPlan.eval (answer F J) (epochsPlan exact η s p M ξ state)).2,
      yv.2 ∈ A yv.1 := by
  induction M generalizing state with
  | zero => simp [epochsPlan, QueryPlan.eval]
  | succ M ih =>
    rw [epochsPlan, QueryPlan.eval_bind, QueryPlan.eval_map]
    intro yv hyv
    rcases List.mem_append.mp hyv with hyv | hyv
    · exact eval_epochPlan_members exact F J A hη hJ s p state.1 state.2 hj (ξ 0) yv hyv
    · exact ih _ _ yv hyv

lemma eval_outputPlan_member (exact : Bool) (F : Fin n → E → E)
    (J : ℝ → E → E) (A : E → Set E) {η : ℝ} (hη : 0 < η)
    (hJ : ∀ z, η⁻¹ • (z - J η z) ∈ A (J η z))
    (s p : ℝ) (x0 : E) {b j q M : ℕ} (hj : 0 < j)
    (ξ : (Fin M → EpochSeed n b j q) × Fin (q * M)) :
    let yv := QueryPlan.eval (answer F J) (outputPlan exact η s p x0 ξ)
    yv.2 ∈ A yv.1 := by
  simp only [outputPlan, QueryPlan.eval_map]
  have hlen := eval_epochsPlan_length exact F J η s p M ξ.1 (x0, x0)
  have hidx : ξ.2.val <
      (QueryPlan.eval (answer F J) (epochsPlan exact η s p M ξ.1 (x0, x0))).2.length := by
    rw [hlen]
    exact ξ.2.isLt
  rw [List.getD_eq_getElem _ _ hidx]
  exact eval_epochsPlan_members exact F J A hη hJ s p hj M ξ.1 (x0, x0) _
    (List.getElem_mem hidx)

lemma execute_algorithm {n b J q M : ℕ} [NeZero n] [NeZero q] [NeZero M]
    (exact : Bool) (η s p : ℝ) (x0 : E) (F : Fin n → E → E) (prox : ℝ → E → E)
    (ξ : Seeds n b J q M) {K : ℕ} (hK : (stepCost exact n b J * q + n) * M ≤ K) :
    execute { answer := fun _ (_, query) _ => answer F prox query }
      (algorithm exact η s p x0 b J q M) (fun _ => K) ξ =
      QueryPlan.eval (answer F prox) (outputPlan exact η s p x0 (ξ.epochs, ξ.selection)) := by
  exact QueryPlan.execute_plan_of_le _ _ _ _ _ _ _ _ hK

end OracleTemplate.VarianceReducedWeakMinty
