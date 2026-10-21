import LongTails.Proofs.MuonBatchSimulation

set_option maxHeartbeats 5000000

namespace LongTails.Proofs.MuonValidationSimulation

open OracleTemplate
open LongTails.Algorithms.MatrixPolar LongTails.Algorithms.ValidatedMuon
open LongTails.Proofs.MuonSimulation LongTails.Proofs.MuonBatchSimulation
open LongTails.Proofs.ValidatedMuonExecution
open LongTails.Setups.FiniteVarianceSpectralSmooth (ValidatedMuonState validatedMuonDirect)

lemma sampledEval_resumeMuonPlan_validation {Ω : Type*} {m n T : ℕ}
    (α η ρ : ℝ) (b k q extra : ℕ) (x0 : Space m n)
    (g : Space m n → Ω → Space m n) (ξ : ℕ → Ω)
    (sources : Fin (q + 1) → Space m n) (call : ℕ) :
    QueryPlan.sampledEval g ξ
      (resumeMuonPlan (T := T) (b := b) (k := k) (q := q) α η ρ x0
        ((b * (k + 1)) * (q + 1) + extra)
        (validationStart (T := T) (b := b) (k := k) (q := q) ρ sources)) call =
    QueryPlan.sampledEval g ξ (validationPlan ρ b k q sources) call := by
  by_cases hb : 0 < b
  · let batchMean (i j : ℕ) (hi : i ≤ q) (hj : j ≤ k) : Space m n :=
      QueryPlan.sampledEval g ξ
        (batchMeanPlan (sources ⟨i, by omega⟩) b)
        (call + b * (k + 1) * i + b * j)
    let targetReps : Fin (q + 1) → Space m n :=
      fun i => representative ρ (fun j =>
        batchMean i.val j.val (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt))
    let targetOutput := sources (bestIndex targetReps)
    let meansPrefix (i j : ℕ) (hi : i ≤ q) (hj : j ≤ k) : Fin (k + 1) → Space m n :=
      fun t => if t.val < j then batchMean i t.val hi (by omega) else 0
    let repsPrefix (i : ℕ) (hi : i ≤ q) : Fin (q + 1) → Space m n :=
      fun t => if t.val < i then targetReps t else 0
    let boundaryState (i j : ℕ) (hi : i ≤ q) (hj : j ≤ k) :
        ValidatedMuonState m n T b k q :=
      .validating sources ⟨i, by omega⟩ ⟨j, by omega⟩ ⟨0, hb⟩ 0
        (meansPrefix i j hi hj) (repsPrefix i hi)
    have hmeans (i j : ℕ) (hi : i ≤ q) (hj : j < k) :
        Function.update (meansPrefix i j hi (by omega)) ⟨j, by omega⟩
          (batchMean i j hi (by omega)) = meansPrefix i (j + 1) hi (by omega) := by
      funext t
      by_cases h : t.val = j
      · have he : t = ⟨j, by omega⟩ := Fin.ext h
        rw [he]
        simp [meansPrefix]
      · rw [Function.update_of_ne (fun he => h (congrArg Fin.val he))]
        simp only [meansPrefix]
        by_cases ht : t.val < j
        · have ht' : t.val < j + 1 := by omega
          simp [ht, ht']
        · have ht' : ¬ t.val < j + 1 := by omega
          simp [ht, ht']
    have hreps (i : ℕ) (hi : i < q) :
        Function.update (repsPrefix i (by omega)) ⟨i, by omega⟩
          (targetReps ⟨i, by omega⟩) = repsPrefix (i + 1) (by omega) := by
      funext t
      by_cases h : t.val = i
      · have he : t = ⟨i, by omega⟩ := Fin.ext h
        rw [he]
        simp [repsPrefix]
      · rw [Function.update_of_ne (fun he => h (congrArg Fin.val he))]
        simp only [repsPrefix, targetReps]
        by_cases ht : t.val < i
        · have ht' : t.val < i + 1 := by omega
          simp [ht, ht']
        · have ht' : ¬ t.val < i + 1 := by omega
          simp [ht, ht']
    have hfinish : Function.update (repsPrefix q (by omega)) ⟨q, by omega⟩
        (targetReps ⟨q, by omega⟩) = targetReps := by
      funext t
      by_cases h : t.val = q
      · have he : t = ⟨q, by omega⟩ := Fin.ext h
        rw [he]
        simp [repsPrefix]
      · rw [Function.update_of_ne (fun he => h (congrArg Fin.val he))]
        simp only [repsPrefix]
        have ht : t.val < q := by omega
        simp [ht]
    have hmeansLast (i : ℕ) (hi : i ≤ q) :
        Function.update (meansPrefix i k hi (by omega)) ⟨k, by omega⟩
          (batchMean i k hi (by omega)) = fun t => batchMean i t.val hi (by omega) := by
      funext t
      by_cases h : t.val = k
      · have he : t = ⟨k, by omega⟩ := Fin.ext h
        rw [he]
        simp [meansPrefix]
      · rw [Function.update_of_ne (fun he => h (congrArg Fin.val he))]
        simp only [meansPrefix]
        have ht : t.val < k := by omega
        simp [ht]
    have hrun : ∀ N i j (hi : i ≤ q) (hj : j ≤ k),
        N = (k + 1 - j) + (k + 1) * (q - i) →
        ∀ call' : ℕ, call' = call + b * (k + 1) * i + b * j →
        QueryPlan.sampledEval g ξ
          (resumeMuonPlan α η ρ x0 (b * N + extra) (boundaryState i j hi hj)) call' =
          targetOutput := by
      intro N
      induction N using Nat.strong_induction_on with
      | h N ih =>
          intro i j hi hj hN call' hcall
          have hNpos : 0 < N := by omega
          have hphase := sampledEval_resumeMuonPlan_validating_samples
            (T := T) (α := α) (η := η) (ρ := ρ) (x0 := x0) (g := g) (ξ := ξ)
            (sources := sources) (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩)
            (sample := ⟨0, hb⟩) (acc := (0 : Space m n))
            (means := meansPrefix i j hi hj) (reps := repsPrefix i hi)
            (hb := hb) (r := b) (fuel := b * (N - 1) + extra)
            (call := call') (hr := by simp)
          have hfuel : b * N + extra = b + (b * (N - 1) + extra) := by
            have hmul := congrArg (b * ·) (show N = (N - 1) + 1 by omega)
            simp only [Nat.mul_add, Nat.mul_one] at hmul
            omega
          rw [hfuel, hphase]
          by_cases hjk : j < k
          · have hnext : N - 1 = (k + 1 - (j + 1)) + (k + 1) * (q - i) := by
              have hjdec : k + 1 - j = (k + 1 - (j + 1)) + 1 := by omega
              rw [hjdec] at hN
              omega
            have hcallnext : call' + b = call + b * (k + 1) * i + b * (j + 1) := by
              rw [hcall]
              ring
            have hmean : (1 / (b : ℝ)) •
                (0 + ∑ t ∈ Finset.range b, g (sources ⟨i, by omega⟩) (ξ (call' + t))) =
                batchMean i j hi (by omega) := by
              dsimp [batchMean]
              rw [show call' = call + b * (k + 1) * i + b * j by exact hcall]
              rw [sampledEval_batchMeanPlan]
              simp only [zero_add]
            have hstate : (validatedMuon α η ρ T b k q x0).update
                (show (validatedMuon α η ρ T b k q x0).State from
                  .validating sources ⟨i, by omega⟩ ⟨j, by omega⟩ ⟨b - 1, by omega⟩
                  0 (meansPrefix i j hi hj) (repsPrefix i hi))
                (∑ t ∈ Finset.range b, g (sources ⟨i, by omega⟩) (ξ (call' + t))) =
                boundaryState i (j + 1) hi (by omega) := by
              have hs : ¬ (b - 1 + 1 < b) := by omega
              have hjcond : j + 1 < k + 1 := by omega
              simp only [validatedMuon, validatedMuonDirect, boundaryState]
              simp only [hs, dite_false, hjcond, dite_true]
              rw [hmean, hmeans i j hi hjk]
            have hstate' : (validatedMuon α η ρ T b k q x0).update
                (have h : (validatedMuon α η ρ T b k q x0).State :=
                  .validating sources ⟨i, by omega⟩ ⟨j, by omega⟩ ⟨b - 1, by omega⟩
                    0 (meansPrefix i j hi hj) (repsPrefix i hi); h)
                (0 + ∑ t ∈ Finset.range b, g (sources ⟨i, by omega⟩) (ξ (call' + t))) =
                boundaryState i (j + 1) hi (by omega) := by
              simpa only [zero_add] using hstate
            rw [hstate']
            exact ih (N - 1) (by omega) i (j + 1) hi (by omega) hnext
              (call' + b) hcallnext
          · have hjlast : j = k := by omega
            rw [hjlast] at hN hcall
            subst j
            by_cases hiq : i < q
            · have hnext : N - 1 = (k + 1) + (k + 1) * (q - (i + 1)) := by
                have hqdec : q - i = (q - (i + 1)) + 1 := by omega
                rw [hqdec, Nat.mul_succ] at hN
                omega
              have hcallnext : call' + b = call + b * (k + 1) * (i + 1) := by
                rw [hcall]
                ring
              have hcallk : call' = call + b * (k + 1) * i + b * k := by
                exact hcall
              have hmean : (1 / (b : ℝ)) •
                  (0 + ∑ t ∈ Finset.range b, g (sources ⟨i, by omega⟩) (ξ (call' + t))) =
                  batchMean i k hi (by omega) := by
                dsimp [batchMean]
                rw [hcallk]
                rw [sampledEval_batchMeanPlan]
                simp only [zero_add]
              have hmeanLast : representative ρ
                  (Function.update (meansPrefix i k hi (by omega)) ⟨k, by omega⟩
                    (batchMean i k hi (by omega))) = targetReps ⟨i, by omega⟩ := by
                rw [hmeansLast i hi]
              have hstate : (validatedMuon α η ρ T b k q x0).update
                  (.validating sources ⟨i, by omega⟩ ⟨k, by omega⟩ ⟨b - 1, by omega⟩
                    0 (meansPrefix i k hi (by omega)) (repsPrefix i hi))
                  (∑ t ∈ Finset.range b, g (sources ⟨i, by omega⟩) (ξ (call' + t))) =
                  boundaryState (i + 1) 0 (by omega) (by omega) := by
                have hs : ¬ (b - 1 + 1 < b) := by omega
                have hjcond : ¬ (k + 1 < k + 1) := by omega
                have hicond : i + 1 < q + 1 := by omega
                simp only [validatedMuon, validatedMuonDirect]
                simp only [hs, dite_false, hjcond, dite_false, hicond, dite_true]
                rw [hmean, hmeansLast i hi, hreps i hiq]
                simp [boundaryState, meansPrefix]
              have hstate' : (validatedMuon α η ρ T b k q x0).update
                  (show (validatedMuon α η ρ T b k q x0).State from
                    .validating sources ⟨i, by omega⟩ ⟨k, by omega⟩ ⟨b - 1, by omega⟩
                      0 (meansPrefix i k hi (by omega)) (repsPrefix i hi))
                  (0 + ∑ t ∈ Finset.range b, g (sources ⟨i, by omega⟩) (ξ (call' + t))) =
                  boundaryState (i + 1) 0 (by omega) (by omega) := by
                simpa only [zero_add] using hstate
              dsimp [meansPrefix] at hstate'
              rw [hstate']
              exact ih (N - 1) (by omega) (i + 1) 0 (by omega) (by omega) hnext
                (call' + b) hcallnext
            · have hieq : i = q := by omega
              subst i
              have hmean : (1 / (b : ℝ)) •
                  (0 + ∑ t ∈ Finset.range b, g (sources ⟨q, by omega⟩) (ξ (call' + t))) =
                  batchMean q k (by omega) (by omega) := by
                dsimp [batchMean]
                rw [hcall]
                rw [sampledEval_batchMeanPlan]
                simp only [zero_add]
              have hstate : (validatedMuon α η ρ T b k q x0).update
                  (.validating sources ⟨q, by omega⟩ ⟨k, by omega⟩ ⟨b - 1, by omega⟩
                    0 (meansPrefix q k (by omega) (by omega)) (repsPrefix q (by omega)))
                  (∑ t ∈ Finset.range b, g (sources ⟨q, by omega⟩) (ξ (call' + t))) =
                  .done targetOutput := by
                have hs : ¬ (b - 1 + 1 < b) := by omega
                have hjcond : ¬ (k + 1 < k + 1) := by omega
                have hicond : ¬ (q + 1 < q + 1) := by omega
                simp only [validatedMuon, validatedMuonDirect]
                simp only [hs, dite_false, hjcond, dite_false, hicond, dite_false]
                rw [hmean, hmeansLast q (by omega), hfinish]
              have hstate' : (validatedMuon α η ρ T b k q x0).update
                  (show (validatedMuon α η ρ T b k q x0).State from
                    .validating sources ⟨q, by omega⟩ ⟨k, by omega⟩ ⟨b - 1, by omega⟩
                      0 (meansPrefix q k (by omega) (by omega)) (repsPrefix q (by omega)))
                  (0 + ∑ t ∈ Finset.range b, g (sources ⟨q, by omega⟩) (ξ (call' + t))) =
                  .done targetOutput := by
                simpa only [zero_add] using hstate
              dsimp [meansPrefix] at hstate'
              rw [hstate', sampledEval_resumeMuonPlan_done]
    have hstart : boundaryState 0 0 (by omega) (by omega) =
        validationStart (T := T) (b := b) (k := k) (q := q) ρ sources := by
      simp [boundaryState, validationStart, hb, meansPrefix, repsPrefix]
    have hN : (k + 1) * (q + 1) = (k + 1 - 0) + (k + 1) * (q - 0) := by
      simp only [Nat.sub_zero, Nat.mul_add, Nat.mul_one]
      omega
    have hcall : call = call + b * (k + 1) * 0 + b * 0 := by simp
    have hrun0 := hrun ((k + 1) * (q + 1)) 0 0 (by omega) (by omega) hN call hcall
    calc
      QueryPlan.sampledEval g ξ
          (resumeMuonPlan (T := T) (b := b) (k := k) (q := q) α η ρ x0
            ((b * (k + 1)) * (q + 1) + extra)
            (validationStart (T := T) (b := b) (k := k) (q := q) ρ sources)) call =
          targetOutput := by
            have hstartRun : QueryPlan.sampledEval g ξ
                (resumeMuonPlan (T := T) (b := b) (k := k) (q := q) α η ρ x0
                  (b * ((k + 1) * (q + 1)) + extra)
                  (validationStart (T := T) (b := b) (k := k) (q := q) ρ sources)) call =
                targetOutput := by simpa [hstart] using hrun0
            have hfuelEq : (b * (k + 1)) * (q + 1) + extra =
                b * ((k + 1) * (q + 1)) + extra := by ring
            rw [hfuelEq]
            exact hstartRun
      _ = QueryPlan.sampledEval g ξ (validationPlan ρ b k q sources) call := by
        rw [ValidatedMuonExecution.sampledEval_validationPlan]
  · have hb0 : b = 0 := by omega
    subst b
    have hstart : validationStart (T := T) (b := 0) (k := k) (q := q) ρ sources =
        .done (sources (bestIndex (fun _ : Fin (q + 1) =>
          representative ρ (fun _ : Fin (k + 1) => (0 : Space m n))))) := by
      simp [validationStart]
    rw [hstart]
    simp only [sampledEval_resumeMuonPlan_done]
    rw [ValidatedMuonExecution.sampledEval_validationPlan]
    simp only [Nat.zero_mul, Nat.add_zero]
    have hfun : (fun i : Fin (q + 1) => representative ρ (fun j : Fin (k + 1) =>
        QueryPlan.sampledEval g ξ (batchMeanPlan (sources i) 0) call)) =
        (fun _ : Fin (q + 1) =>
          representative ρ (fun _ : Fin (k + 1) => (0 : Space m n))) := by
      funext i
      congr 1
      funext j
      simp [sampledEval_batchMeanPlan]
    rw [hfun]

end LongTails.Proofs.MuonValidationSimulation
