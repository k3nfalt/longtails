import LongTails.Algorithms.NoisyDampedNewton
import LongTails.Proofs.AdaptiveRobustGeneralizedExecution
import LongTails.Proofs.Execution

namespace LongTails.Proofs.NoisyNewtonExecution

open LongTails.Setups.StochasticLocalHessianConvex
open LongTails.Algorithms.NoisyDampedNewton
open OracleTemplate.GeneralizedAccelerated (Iterate tentativeWeight coupling)
open OracleTemplate.StochasticGradient (advance)
open OracleTemplate.HeavyTailedMarkovGradient (advance_add)
open OracleTemplate.AdaptiveRobustGeneralized (replyPrefix replyPrefix_update meanBlock_congr)

noncomputable def rawAdvance (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (n call : ℕ) (s : State (Point p.d)) : State (Point p.d) := by
  classical
  exact advance (fun k state =>
    let q := (algorithm p).query state
    (algorithm p).update state (if q.1 = 0 then .inl (g q.2 (ξ k)) else .inr (H q.2))) n call s

lemma rawAdvance_add (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (n m call : ℕ) (s : State (Point p.d)) :
    rawAdvance p g H ξ (n + m) call s = rawAdvance p g H ξ m (call + n) (rawAdvance p g H ξ n call s) :=
  advance_add _ _ _ _ _

lemma modelEstimate_congr (p : Params) (a : ℝ) {v w : ℕ → Point p.d}
    (h : ∀ i < modelCost p a, v i = w i) : modelEstimate p a v = modelEstimate p a w := by
  unfold modelEstimate
  congr 1
  funext i
  apply meanBlock_congr
  intro j hj
  apply h
  have hi := Nat.mul_le_mul_right (modelSize p a) (Nat.succ_le_of_lt i.isLt)
  simp only [Nat.succ_mul] at hi
  unfold modelCost
  omega

lemma modelEstimate_replyPrefix (p : Params) (a : ℝ) (v : ℕ → Point p.d) :
    modelEstimate p a (replyPrefix (modelCost p a) v) = modelEstimate p a v :=
  modelEstimate_congr p a (fun i hi => by simp [replyPrefix, hi])

lemma updateEstimate_replyPrefix (p : Params) (t : Trial (Point p.d)) (v : ℕ → Point p.d) :
    updateEstimate p t (replyPrefix (updateSize p (actualWeight t)) v) = updateEstimate p t v := by
  unfold updateEstimate
  congr 1
  apply meanBlock_congr
  intro i hi
  simp [replyPrefix, hi]

lemma rawAdvance_model_prefix (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (s : Iterate (Point p.d)) (call j : ℕ) (hj : j < modelCost p (tentativeWeight s)) :
    rawAdvance p g H ξ j call (.model s 0 (fun _ => 0)) =
      .model s j (replyPrefix j (fun i => g (coupling s) (ξ (call + i)))) := by
  induction j with
  | zero => simp only [rawAdvance, advance]; congr 1
  | succ j ih =>
    rw [rawAdvance_add, ih (by omega)]
    simp only [rawAdvance, advance, algorithm, hj, ↓reduceIte]
    rw [replyPrefix_update]

lemma rawAdvance_correction_prefix (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (t : Trial (Point p.d)) (call j : ℕ) (hj : j < updateSize p (actualWeight t)) :
    rawAdvance p g H ξ j call (.correction t 0 (fun _ => 0)) =
      .correction t j (replyPrefix j (fun i => g (trialPoint t) (ξ (call + i)))) := by
  induction j with
  | zero => simp only [rawAdvance, advance]; congr 1
  | succ j ih =>
    rw [rawAdvance_add, ih (by omega)]
    simp only [rawAdvance, advance, algorithm, hj, ↓reduceIte]
    rw [replyPrefix_update]

lemma rawAdvance_model_block (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (s : Iterate (Point p.d)) (call : ℕ) :
    rawAdvance p g H ξ (modelCost p (tentativeWeight s)) call (.model s 0 (fun _ => 0)) =
      .hessian s (modelEstimate p (tentativeWeight s) (fun i => g (coupling s) (ξ (call + i)))) := by
  have hm : 0 < modelCost p (tentativeWeight s) := Nat.mul_pos
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
  obtain ⟨j, he⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [he, Nat.succ_eq_add_one, rawAdvance_add,
    rawAdvance_model_prefix p g H ξ s call j (by omega)]
  simp only [rawAdvance, advance, algorithm, he, Nat.succ_eq_add_one,
    lt_self_iff_false, ↓reduceIte, replyPrefix_update]
  rw [← Nat.succ_eq_add_one, ← he, modelEstimate_replyPrefix]

lemma rawAdvance_correction_block (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (t : Trial (Point p.d)) (call : ℕ) :
    rawAdvance p g H ξ (updateSize p (actualWeight t)) call (.correction t 0 (fun _ => 0)) =
      resume p (finish (curvatureFloor p) t
        (updateEstimate p t (fun i => g (trialPoint t) (ξ (call + i))))) := by
  have hm : 0 < updateSize p (actualWeight t) :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  obtain ⟨j, he⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [he, Nat.succ_eq_add_one, rawAdvance_add,
    rawAdvance_correction_prefix p g H ξ t call j (by omega)]
  simp only [rawAdvance, advance, algorithm, he, Nat.succ_eq_add_one,
    lt_self_iff_false, ↓reduceIte, replyPrefix_update]
  rw [← Nat.succ_eq_add_one, ← he, updateEstimate_replyPrefix]

lemma rawAdvance_hessian (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (s : Iterate (Point p.d)) (v : Point p.d) (call : ℕ) :
    rawAdvance p g H ξ 1 call (.hessian s v) =
      .correction (prepare p.M₀ p.M₁ p.ρ p.δ (tolerance p) s (H (coupling s)) v) 0 (fun _ => 0) := by
  simp [rawAdvance, advance, algorithm]

lemma rawAdvance_iteration (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (s : Iterate (Point p.d)) (call : ℕ) :
    let m := modelCost p (tentativeWeight s)
    let v := modelEstimate p (tentativeWeight s) (fun i => g (coupling s) (ξ (call + i)))
    let t := prepare p.M₀ p.M₁ p.ρ p.δ (tolerance p) s (H (coupling s)) v
    rawAdvance p g H ξ (m + 1 + updateSize p (actualWeight t)) call (.model s 0 (fun _ => 0)) =
      resume p (finish (curvatureFloor p) t
        (updateEstimate p t (fun i => g (trialPoint t) (ξ (call + m + 1 + i))))) := by
  dsimp only
  rw [rawAdvance_add, rawAdvance_add, rawAdvance_model_block, rawAdvance_hessian,
    rawAdvance_correction_block]
  simp only [Nat.add_assoc]

lemma rawAdvance_done (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d) (ξ : ℕ → p.Ω)
    (s : Iterate (Point p.d)) (n call : ℕ) : rawAdvance p g H ξ n call (.done s) = .done s := by
  induction n generalizing call with
  | zero => rfl
  | succ n ih => exact ih (call + 1)

noncomputable def oracleCount (p : Params) (state : ℕ → State (Point p.d)) (ch : Fin 2) (n : ℕ) : ℕ := by
  classical
  exact ∑ i ∈ Finset.range n, if ((algorithm p).query (state i)).1 = ch then 1 else 0

lemma oracleCount_succ (p : Params) (state : ℕ → State (Point p.d)) (ch : Fin 2) (n : ℕ) :
    oracleCount p state ch (n + 1) = oracleCount p state ch n +
      (if ((algorithm p).query (state n)).1 = ch then 1 else 0) := by
  classical
  exact Finset.sum_range_succ _ _

lemma oracleCount_mono (p : Params) (state : ℕ → State (Point p.d)) (ch : Fin 2)
    {n m : ℕ} (hnm : n ≤ m) : oracleCount p state ch n ≤ oracleCount p state ch m := by
  unfold oracleCount
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hnm) (by intros; omega)

lemma oracleCount_sum (p : Params) (state : ℕ → State (Point p.d)) (n : ℕ) :
    ∑ ch, oracleCount p state ch n = n := by
  classical
  unfold oracleCount
  rw [Finset.sum_comm]
  simp

lemma execute_of_done (p : Params) (g : Point p.d → p.Ω → Point p.d)
    (H : Point p.d → Point p.d →L[ℝ] Point p.d)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → p.Ω)) (ξ : ℕ → p.Ω)
    (budget : Fin 2 → ℕ) (T : ℕ) (s : Iterate (Point p.d))
    (hdone : rawAdvance p g H ξ T 0 ((algorithm p).initial ()) = .done s)
    (hb : ∀ ch, oracleCount p (fun n => rawAdvance p g H ξ n 0 ((algorithm p).initial ())) ch T ≤ budget ch) :
    let O : OracleTemplate.Oracle (Point p.d) (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)) 2 :=
      { Seed := fun _ => p.Ω, law := P,
        answer := fun _ q ω => if q.1 = 0 then .inl (g q.2 ω) else .inr (H q.2) }
    OracleTemplate.execute O (algorithm p) budget () ξ = s.x := by
  classical
  let O : OracleTemplate.Oracle (Point p.d) (Point p.d ⊕ (Point p.d →L[ℝ] Point p.d)) 2 :=
      { Seed := fun _ => p.Ω, law := P,
        answer := fun _ q ω => if q.1 = 0 then .inl (g q.2 ω) else .inr (H q.2) }
  let s0 : State (Point p.d) := (algorithm p).initial ()
  let state := fun n => rawAdvance p g H ξ n 0 s0
  let remaining := fun n ch => budget ch - oracleCount p state ch n
  apply OracleTemplate.execute_eq_of_safe_prefix O (algorithm p) budget () ξ state remaining T s.x
  · rfl
  · intro history
    change rawAdvance p g H ξ (history.length + 1) 0 s0 = _
    rw [rawAdvance_add, Nat.zero_add]
    rfl
  · funext ch
    simp [remaining, oracleCount]
  · intro n
    funext ch
    dsimp only [remaining]
    rw [oracleCount_succ]
    by_cases hc : ((algorithm p).query (state n)).1 = ch
    · subst ch
      simp only [ite_true, Function.update_self]
      omega
    · simp only [hc, ite_false, Nat.add_zero, Function.update_of_ne (Ne.symm hc)]
  · intro n hn
    have hs := oracleCount_succ p state ((algorithm p).query (state n)).1 n
    simp only [↓reduceIte] at hs
    have hm := oracleCount_mono p state ((algorithm p).query (state n)).1 (Nat.succ_le_of_lt hn)
    have hbudget := hb ((algorithm p).query (state n)).1
    change 0 < budget ((algorithm p).query (state n)).1 - oracleCount p state ((algorithm p).query (state n)).1 n
    change oracleCount p state ((algorithm p).query (state n)).1 T ≤ _ at hbudget
    have hstrict : oracleCount p state ((algorithm p).query (state n)).1 n < budget ((algorithm p).query (state n)).1 := by
      calc
        _ < oracleCount p state ((algorithm p).query (state n)).1 (n + 1) := by omega
        _ ≤ oracleCount p state ((algorithm p).query (state n)).1 T := hm
        _ ≤ _ := hbudget
    exact Nat.sub_pos_iff_lt.mpr hstrict
  · intro n hn
    have he : n = T + (n - T) := by omega
    have hstate : state n = .done s := by
      dsimp only [state]
      rw [he, rawAdvance_add, hdone, rawAdvance_done]
    rw [hstate]
    rfl
  · rw [← oracleCount_sum p state T]
    exact Finset.sum_le_sum (fun ch _ => hb ch)

end LongTails.Proofs.NoisyNewtonExecution
