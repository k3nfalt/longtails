import LongTails.Proofs.Execution

namespace OracleTemplate

lemma execute_eq_trajectory {Query Reply Output : Type*} {n : ℕ}
    (O : Oracle Query Reply n) (A : Algorithm Query Reply Output n)
    (budget : Fin n → ℕ) (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k)
    (R : Fin n × Query → Reply)
    (hR : ∀ history : List ((Fin n × Query) × Reply), history.length < ∑ i, budget i →
      O.answer history (A.query ((fun s => A.update s (R (A.query s)))^[history.length]
        (A.initial seed))) (ξ history.length) =
        R (A.query ((fun s => A.update s (R (A.query s)))^[history.length] (A.initial seed)))) :
    ∃ t ≤ ∑ i, budget i, execute O A budget seed ξ =
      A.output ((fun s => A.update s (R (A.query s)))^[t] (A.initial seed)) := by
  set step := fun s => A.update s (R (A.query s)) with hstep
  unfold execute executeWithTrace
  generalize A.initial seed = σ0 at hR ⊢
  generalize hF : (∑ i, budget i) = F at hR ⊢
  obtain ⟨fuel, hfuel⟩ : ∃ fuel, F = fuel := ⟨F, rfl⟩
  nth_rewrite 2 [hfuel]
  have hb : ([] : List ((Fin n × Query) × Reply)).length + fuel ≤ F := by simp [hfuel]
  conv => enter [1, t, 2, 1]; rw [show σ0 = step^[([] : List ((Fin n × Query) × Reply)).length] σ0 from rfl]
  generalize ([] : List ((Fin n × Query) × Reply)) = history at hb ⊢
  generalize budget = remaining
  clear hfuel hF
  induction fuel generalizing history remaining with
  | zero => exact ⟨history.length, by omega, rfl⟩
  | succ fuel ih =>
      change ∃ t ≤ F,
        (if remaining (A.query (step^[history.length] σ0)).1 = 0 then
          (A.output (step^[history.length] σ0), history) else _).1 = _
      split_ifs with hz
      · exact ⟨history.length, by omega, rfl⟩
      · dsimp only
        rw [hR history (by omega)]
        have hnext : A.update (step^[history.length] σ0) (R (A.query (step^[history.length] σ0))) =
            step^[(history ++ [(A.query (step^[history.length] σ0),
              R (A.query (step^[history.length] σ0)))]).length] σ0 := by
          simp only [List.length_append, List.length_singleton]
          rw [Function.iterate_succ_apply']
        rw [hnext]
        exact ih _ (by simp only [List.length_append, List.length_singleton]; omega) _

end OracleTemplate
