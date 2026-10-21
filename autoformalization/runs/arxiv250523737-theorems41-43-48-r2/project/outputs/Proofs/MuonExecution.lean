import outputs.Algorithms.SimplifiedMuon
import outputs.Proofs.MuonMatrix
import LongTails.Proofs.Execution

open MeasureTheory

namespace OracleTemplate.Muon

variable {Ω : Type}

theorem trajectory_succ (p : Public) (g : Mat p.m p.n → Ω → Mat p.m p.n) (s : ℕ → Ω) (t : ℕ) :
    trajectory p g s (t + 1) = iterationStep p g s (trajectory p g s t) := by
  exact Function.iterate_succ_apply' _ _ _

theorem trajectory_zero (p : Public) (g : Mat p.m p.n → Ω → Mat p.m p.n) (s : ℕ → Ω) :
    trajectory p g s 0 = (0, p.W0, 0) := by
  exact Function.iterate_zero_apply _ _

theorem trajectory_fst (p : Public) (g : Mat p.m p.n → Ω → Mat p.m p.n) (s : ℕ → Ω) (t : ℕ) :
    (trajectory p g s t).1 = t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [trajectory_succ]; change (trajectory p g s t).1 + 1 = t + 1; rw [ih]

theorem trajectory_succ_eq (p : Public) (g : Mat p.m p.n → Ω → Mat p.m p.n) (s : ℕ → Ω) (t : ℕ) :
    trajectory p g s (t + 1) =
      (t + 1, (trajectory p g s t).2.1 - p.η • orthogonalize
        (if t = 0 then batchGradient p g s t (trajectory p g s t).2.1 else
          p.β • (trajectory p g s t).2.2 + (1 - p.β) • batchGradient p g s t (trajectory p g s t).2.1),
        if t = 0 then batchGradient p g s t (trajectory p g s t).2.1 else
          p.β • (trajectory p g s t).2.2 + (1 - p.β) • batchGradient p g s t (trajectory p g s t).2.1) := by
  rw [trajectory_succ]
  change ((trajectory p g s t).1 + 1, _, _) = _
  rw [trajectory_fst]

noncomputable def stateAt (p : Public) (g : Mat p.m p.n → Ω → Mat p.m p.n) (s : ℕ → Ω) (t : ℕ) : State p :=
  ⟨t, 0, (trajectory p g s t).2.1, (trajectory p g s t).2.2, 0,
    fun j => if j ≤ t then (trajectory p g s j).2.1 else p.W0⟩

attribute [local simp] stateAt

theorem batch_partial (p : Public) (g : Mat p.m p.n → Ω → Mat p.m p.n) (s : ℕ → Ω) (t : ℕ) (j : ℕ)
    (hj : j + 1 ≤ p.B) :
    (fun sc : State p × ℕ => (step p sc.1 (g sc.1.point (s sc.2)), sc.2 + 1))^[j] (stateAt p g s t, t * p.B) =
      (⟨t, j, (trajectory p g s t).2.1, (trajectory p g s t).2.2,
        ∑ i ∈ Finset.range j, g (trajectory p g s t).2.1 (s (t * p.B + i)),
        fun i => if i ≤ t then (trajectory p g s i).2.1 else p.W0⟩, t * p.B + j) := by
  induction j with
  | zero => simp [stateAt]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hlt : j + 1 < p.B := by omega
    simp only [step, hlt, ite_true, Finset.sum_range_succ]
    rfl

theorem batch_full (p : Public) (hB : 1 ≤ p.B) (g : Mat p.m p.n → Ω → Mat p.m p.n) (s : ℕ → Ω) (t : ℕ) :
    (fun sc : State p × ℕ => (step p sc.1 (g sc.1.point (s sc.2)), sc.2 + 1))^[p.B] (stateAt p g s t, t * p.B) =
      (stateAt p g s (t + 1), (t + 1) * p.B) := by
  obtain ⟨b, hb⟩ : ∃ b, p.B = b + 1 := ⟨p.B - 1, by omega⟩
  have hpart := batch_partial p g s t b (by omega)
  rw [hb, Function.iterate_succ_apply', ← hb, hpart]
  have hnot : ¬ (b + 1 < p.B) := by omega
  simp only [step, hnot, ite_false]
  have hsum : ∑ i ∈ Finset.range b, g (trajectory p g s t).2.1 (s (t * p.B + i)) +
      g (trajectory p g s t).2.1 (s (t * p.B + b)) =
      ∑ i ∈ Finset.range p.B, g (trajectory p g s t).2.1 (s (t * p.B + i)) := by
    rw [hb, Finset.sum_range_succ]
  rw [hsum]
  have hG : (1 / (p.B : ℝ)) • ∑ i ∈ Finset.range p.B, g (trajectory p g s t).2.1 (s (t * p.B + i)) =
      batchGradient p g s t (trajectory p g s t).2.1 := rfl
  rw [hG]
  refine Prod.ext ?_ ?_
  · simp only [stateAt]
    rw [trajectory_succ_eq]
    congr 1
    funext j
    rw [Function.update_apply]
    by_cases hj : j = t + 1
    · subst hj
      simp only [ite_true, le_refl, trajectory_succ_eq]
    · by_cases hjt : j ≤ t
      · simp only [hj, ite_false, hjt, ite_true, show j ≤ t + 1 by omega]
      · simp only [hj, ite_false, hjt, show ¬ j ≤ t + 1 by omega]
  · simp only
    rw [hb]
    ring

theorem execute_muon [MeasurableSpace Ω] (p : Public) (hB : 1 ≤ p.B) (P : ProbabilityMeasure (ℕ → Ω))
    (g : Mat p.m p.n → Ω → Mat p.m p.n) (seed : (muon p).Seed) (s : ℕ → Ω) :
    execute (sampleOracle P g) (muon p) (fun _ => p.T * p.B) seed s =
      fun j : Fin (p.T + 1) => (trajectory p g s j).2.1 := by
  erw [execute_indexed]
  set F := fun sc : State p × ℕ => (step p sc.1 (g sc.1.point (s sc.2)), sc.2 + 1)
  have hinit : (muon p).initial seed = stateAt p g s 0 := by
    change (⟨0, 0, p.W0, 0, 0, fun _ => p.W0⟩ : State p) = _
    simp only [stateAt]
    congr 1
    funext j
    by_cases hj : j ≤ 0
    · have : j = 0 := by omega
      subst this
      simp only [le_refl, ite_true]
      rfl
    · simp only [hj, ite_false]
  have hit : ∀ t, F^[t * p.B] (stateAt p g s 0, 0) = (stateAt p g s t, t * p.B) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hb := batch_full p hB g s t
      rw [show (t + 1) * p.B = p.B + t * p.B by ring] at hb ⊢
      rw [Function.iterate_add_apply, ih]
      exact hb
  change (muon p).output (F^[p.T * p.B] ((muon p).initial seed, 0)).1 = _
  rw [hinit, hit]
  funext j
  change (if (j : ℕ) ≤ p.T then (trajectory p g s j).2.1 else p.W0) = _
  simp only [Nat.lt_succ_iff.mp j.isLt, ite_true]

theorem trajectory_measurable [MeasurableSpace Ω] (p : Public) (g : Mat p.m p.n → Ω → Mat p.m p.n)
    (hg : Measurable (Function.uncurry g)) (t : ℕ) : Measurable (fun s => (trajectory p g s t).2) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hW : Measurable (fun s => (trajectory p g s t).2.1) := measurable_fst.comp ih
    have hM : Measurable (fun s => (trajectory p g s t).2.2) := measurable_snd.comp ih
    have hG : Measurable (fun s => batchGradient p g s t (trajectory p g s t).2.1) := by
      change Measurable (fun s => (1 / (p.B : ℝ)) • ∑ j ∈ Finset.range p.B,
        g (trajectory p g s t).2.1 (s (t * p.B + j)))
      exact (Finset.measurable_sum _ (fun j _ => hg.comp (hW.prodMk (measurable_pi_apply _)))).const_smul
        (1 / (p.B : ℝ))
    have hMn : Measurable (fun s => if t = 0 then batchGradient p g s t (trajectory p g s t).2.1 else
        p.β • (trajectory p g s t).2.2 + (1 - p.β) • batchGradient p g s t (trajectory p g s t).2.1) := by
      split_ifs
      · exact hG
      · fun_prop
    have heq : (fun s => (trajectory p g s (t + 1)).2) = fun s =>
        ((trajectory p g s t).2.1 - p.η • orthogonalize
          (if t = 0 then batchGradient p g s t (trajectory p g s t).2.1 else
            p.β • (trajectory p g s t).2.2 + (1 - p.β) • batchGradient p g s t (trajectory p g s t).2.1),
        if t = 0 then batchGradient p g s t (trajectory p g s t).2.1 else
          p.β • (trajectory p g s t).2.2 + (1 - p.β) • batchGradient p g s t (trajectory p g s t).2.1) :=
      funext fun s => by rw [trajectory_succ_eq]
    rw [heq]
    exact (hW.sub ((measurable_orthogonalize.comp hMn).const_smul p.η)).prodMk hMn

theorem iterationStep_congr (p : Public) (g : Mat p.m p.n → Ω → Mat p.m p.n) (s s' : ℕ → Ω)
    (x : ℕ × Mat p.m p.n × Mat p.m p.n) (h : ∀ j < (x.1 + 1) * p.B, s j = s' j) :
    iterationStep p g s x = iterationStep p g s' x := by
  have hG : batchGradient p g s x.1 x.2.1 = batchGradient p g s' x.1 x.2.1 := by
    change (1 / (p.B : ℝ)) • ∑ j ∈ Finset.range p.B, g x.2.1 (s (x.1 * p.B + j)) =
      (1 / (p.B : ℝ)) • ∑ j ∈ Finset.range p.B, g x.2.1 (s' (x.1 * p.B + j))
    congr 1
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [h (x.1 * p.B + j) (by rw [Finset.mem_range] at hj; nlinarith)]
  simp only [iterationStep, hG]

theorem trajectory_prefix (p : Public) (g : Mat p.m p.n → Ω → Mat p.m p.n) (t : ℕ) (s s' : ℕ → Ω)
    (h : ∀ j < t * p.B, s j = s' j) : trajectory p g s t = trajectory p g s' t := by
  induction t with
  | zero => rw [trajectory_zero, trajectory_zero]
  | succ t ih =>
    have h' : ∀ j < t * p.B, s j = s' j := fun j hj => h j (by nlinarith)
    rw [trajectory_succ, trajectory_succ, ih h']
    refine iterationStep_congr p g s s' _ (fun j hj => h j ?_)
    rw [trajectory_fst] at hj
    exact hj

end OracleTemplate.Muon

namespace OracleTemplate.SimplifiedMuon

open Muon

theorem execute_simplified (p : Public) (O : Oracle (Mat p.m p.n) (Mat p.m p.n))
    (G : Mat p.m p.n → Mat p.m p.n) (hO : ∀ k W seed, O.answer k (0, W) seed = G W)
    (seed : (simplifiedMuon p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (simplifiedMuon p) (fun _ => p.T) seed ξ = fun j : Fin (p.T + 1) => trajectory p G j := by
  rw [execute_eq_of_answer_eq O G hO, execute_iterate]
  have hit : ∀ t, (fun st => (simplifiedMuon p).update st (G ((simplifiedMuon p).query st).2))^[t]
      ((simplifiedMuon p).initial seed) =
        (⟨t, trajectory p G t, fun j => if j ≤ t then trajectory p G j else p.W0⟩ : State p) := by
    intro t
    induction t with
    | zero =>
      change (⟨0, p.W0, fun _ => p.W0⟩ : State p) = _
      congr 1
      funext j
      by_cases hj : j ≤ 0
      · have : j = 0 := by omega
        subst this
        simp only [le_refl, ite_true]
        rfl
      · simp only [hj, ite_false]
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      change (⟨t + 1, trajectory p G t - p.η • orthogonalize (G (trajectory p G t)),
        Function.update (fun j => if j ≤ t then trajectory p G j else p.W0) (t + 1)
          (trajectory p G t - p.η • orthogonalize (G (trajectory p G t)))⟩ : State p) = _
      have htr : trajectory p G (t + 1) = trajectory p G t - p.η • orthogonalize (G (trajectory p G t)) :=
        Function.iterate_succ_apply' _ _ _
      rw [← htr]
      congr 1
      funext j
      rw [Function.update_apply]
      by_cases hj : j = t + 1
      · subst hj; simp
      · by_cases hjt : j ≤ t
        · simp only [hj, ite_false, hjt, ite_true, show j ≤ t + 1 by omega]
        · simp only [hj, ite_false, hjt, show ¬ j ≤ t + 1 by omega]
  rw [hit]
  funext j
  change (if (j : ℕ) ≤ p.T then trajectory p G j else p.W0) = _
  simp only [Nat.lt_succ_iff.mp j.isLt, ite_true]

end OracleTemplate.SimplifiedMuon
