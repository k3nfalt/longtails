import LongTails.Proofs.Execution
import LongTails.Setups.RegretMatchingPotential
import LongTails.Proofs.RegretMatchingRun

namespace OracleTemplate.RegretMatchingPotential

open LongTails.Setups.RegretMatchingPotential

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈20000 * q.B ^ 2 * ((q.m : ℝ) + q.n) ^ 4 / q.ε ^ 2⌉₊ + 1

theorem result : Convergence LongTails.Setups.RegretMatchingPotential.spec budget := by
  apply convergence_of_call_budget (S := spec) (fun p => budget p 0)
  refine ⟨fun p => rmPlusPotential p.m p.n p.ε, ?_, fun _ _ => rfl⟩
  rintro q ⟨hm, hn, hB, hε⟩
  intro K hK
  rintro G oracle ⟨⟨P, hP, hA, hC⟩, hans⟩
  have game : Game G.1 G.2 P q.B := ⟨hm, hn, hB, hP, hA, hC⟩
  have hexec : ∀ seed : (rmPlusPotential q.m q.n q.ε).Seed × ((k : ℕ) → oracle.Seed k),
      execute oracle (rmPlusPotential q.m q.n q.ε) (fun _ => (K)) seed.1 seed.2 =
        (rmPlusPotential q.m q.n q.ε).output ((upd G.1 G.2 q.ε)^[K]
          ((rmPlusPotential q.m q.n q.ε).initial ())) := by
    rintro ⟨⟨⟩, ξ⟩
    rw [execute_eq_of_answer_eq oracle (fun z => (payoffX G.1 z.2, payoffY G.2 z.1))
      (fun k z s => hans k z.1 z.2 s)]
    erw [execute_iterate (oracle := fun z : (Fin q.m → ℝ) × (Fin q.n → ℝ) => (payoffX G.1 z.2, payoffY G.2 z.1))]
    rfl
  have hT : 20000 * q.B ^ 2 * ((q.m : ℝ) + q.n) ^ 4 / q.ε ^ 2 < (K : ℝ) := by
    have hk : (budget q 0 : ℝ) ≤ K := Nat.cast_le.mpr hK
    dsimp [budget] at hk
    push_cast at hk
    linarith [Nat.le_ceil (20000 * q.B ^ 2 * ((q.m : ℝ) + q.n) ^ 4 / q.ε ^ 2)]
  dsimp only
  intro seed
  have key : ∀ o : (Fin q.m → ℝ) × (Fin q.n → ℝ), o = (rmPlusPotential q.m q.n q.ε).output
      ((upd G.1 G.2 q.ε)^[K] ((rmPlusPotential q.m q.n q.ε).initial ())) →
      (∀ i, 0 ≤ o.1 i) ∧ ∑ i, o.1 i = 1 ∧ (∀ j, 0 ≤ o.2 j) ∧ ∑ j, o.2 j = 1 ∧
      (∀ i, ∑ j, G.1 i j * o.2 j ≤ ∑ i', ∑ j, o.1 i' * G.1 i' j * o.2 j + q.ε) ∧
      ∀ j, ∑ i, o.1 i * G.2 i j ≤ ∑ i, ∑ j', o.1 i * G.2 i j' * o.2 j' + q.ε := by
    rintro o rfl
    exact output_nash game hε hT
  exact key (execute oracle (rmPlusPotential q.m q.n q.ε) (fun _ => (K)) seed.1 seed.2)
    ((hexec seed))

end OracleTemplate.RegretMatchingPotential
