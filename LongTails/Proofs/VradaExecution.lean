import LongTails.Algorithms.Vrada
import LongTails.Proofs.Execution
import Mathlib.Tactic

namespace OracleTemplate.FiniteSum

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def vradaStep (oracle : Fin n × E → E) (L : ℝ) (state : VradaState n E) :
    VradaState n E := vradaUpdate L state (oracle (vradaQuery L state))

def vradaEpochStart (seed : List (Fin n)) (m k : ℕ) (x z : E) : VradaState n E :=
  ⟨⟨seed, 0, 0, m, m, x, z, 0, 0, 0⟩, k⟩

noncomputable def vradaInnerState (oracle : Fin n × E → E) (seed : List (Fin n))
    (m k r : ℕ) (x z accumulated : E) : VradaState n E :=
  ⟨⟨seed, 1, 0, m, r, x, z, accumulated, fullGradient oracle z, 0⟩, k⟩

lemma vrada_full_gradient_queries (oracle : Fin n × E → E) (L : ℝ)
    (seed : List (Fin n)) (m k : ℕ) (x z : E) (hne : seed ≠ []) :
    (vradaStep oracle L)^[n] (vradaEpochStart seed m k x z) = vradaInnerState oracle seed m k m x z 0 := by
  let g := fun j : ℕ => oracle (⟨j % n, Nat.mod_lt _ (NeZero.pos n)⟩, z)
  have hi : ∀ j, j ≤ n →
      (vradaStep oracle L)^[j] (vradaEpochStart seed m k x z) =
        if j < n then
          ⟨⟨seed, 0, j, m, m, x, z, 0, ∑ q ∈ Finset.range j, g q, 0⟩, k⟩
        else
          ⟨⟨seed, 1, 0, m, m, x, z, 0, (n : ℝ)⁻¹ • ∑ q ∈ Finset.range j, g q, 0⟩, k⟩ := by
    intro j hk
    induction j with
    | zero => simp [vradaEpochStart, NeZero.pos n]
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih (by omega), ite_eq_left (by omega : j < n)]
      by_cases h : j + 1 < n <;>
        simp [vradaStep, vradaQuery, vradaUpdate, h, Finset.sum_range_succ, g, hne]
  rw [hi n le_rfl, ite_eq_right (Nat.lt_irrefl n)]
  have hs : (∑ j ∈ Finset.range n, g j) = ∑ i : Fin n, oracle (i, z) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [g, Nat.mod_eq_of_lt i.isLt]
  simp only [hs, vradaInnerState, fullGradient]

lemma vrada_inner_two_queries (oracle : Fin n × E → E) (L : ℝ)
    (i : Fin n) (seed : List (Fin n)) (m k r : ℕ) (x z accumulated : E) :
    (vradaStep oracle L)^[2] (vradaInnerState oracle (i :: seed) m k r x z accumulated) =
      if r = 1 then
        vradaEpochStart seed m (k + 1) (x - (vradaIncrement m L k / m) • estimator oracle z (vradaMix (vradaWeight m L k) (vradaIncrement m L k) z x) i)
          ((m : ℝ)⁻¹ • (accumulated + vradaMix (vradaWeight m L k) (vradaIncrement m L k) z (x - (vradaIncrement m L k / m) • estimator oracle z (vradaMix (vradaWeight m L k) (vradaIncrement m L k) z x) i)))
      else
        vradaInnerState oracle seed m k (r - 1) (x - (vradaIncrement m L k / m) • estimator oracle z (vradaMix (vradaWeight m L k) (vradaIncrement m L k) z x) i)
          z (accumulated + vradaMix (vradaWeight m L k) (vradaIncrement m L k) z (x - (vradaIncrement m L k / m) • estimator oracle z (vradaMix (vradaWeight m L k) (vradaIncrement m L k) z x) i)) := by
  by_cases h : r = 1 <;>
    simp [Function.iterate_succ_apply', vradaStep, vradaInnerState, vradaQuery, vradaUpdate,
      vradaEpochStart, estimator, h]

lemma vrada_inner_queries (oracle : Fin n × E → E) (L : ℝ)
    (seed tail : List (Fin n)) (m k : ℕ) (x z accumulated : E) (hne : seed ≠ []) :
    (vradaStep oracle L)^[2 * seed.length]
        (vradaInnerState oracle (seed ++ tail) m k seed.length x z accumulated) =
      vradaEpochStart tail m (k + 1) (vradaInner oracle (vradaWeight m L k) (vradaIncrement m L k) m z x seed).1
        ((m : ℝ)⁻¹ • (accumulated + (vradaInner oracle (vradaWeight m L k) (vradaIncrement m L k) m z x seed).2.sum)) := by
  induction seed generalizing x accumulated with
  | nil => contradiction
  | cons i seed ih =>
    cases seed with
    | nil => simpa [vradaInner] using vrada_inner_two_queries oracle L i tail m k 1 x z accumulated
    | cons j seed =>
      have hr : (j :: seed).length + 1 ≠ 1 := by simp
      rw [List.length_cons, show 2 * ((j :: seed).length + 1) = 2 * (j :: seed).length + 2 by omega,
        Function.iterate_add_apply]
      simp only [List.cons_append]
      rw [vrada_inner_two_queries, ite_eq_right hr]
      simp only [Nat.add_sub_cancel]
      have ih' := ih (x - (vradaIncrement m L k / m) • estimator oracle z (vradaMix (vradaWeight m L k) (vradaIncrement m L k) z x) i)
        (accumulated + vradaMix (vradaWeight m L k) (vradaIncrement m L k) z (x - (vradaIncrement m L k / m) • estimator oracle z (vradaMix (vradaWeight m L k) (vradaIncrement m L k) z x) i)) (by simp)
      simp only [List.cons_append] at ih'
      rw [ih']
      simp [vradaInner, add_assoc]

lemma vrada_epoch_queries (oracle : Fin n × E → E) (L : ℝ)
    {m : ℕ} (hm : 0 < m) (seed : Fin m → Fin n) (tail : List (Fin n)) (k : ℕ) (x z : E) :
    (vradaStep oracle L)^[n + 2 * m] (vradaEpochStart (List.ofFn seed ++ tail) m k x z) =
      vradaEpochStart tail m (k + 1) (vradaInner oracle (vradaWeight m L k) (vradaIncrement m L k) m z x (List.ofFn seed)).1
        ((m : ℝ)⁻¹ • (vradaInner oracle (vradaWeight m L k) (vradaIncrement m L k) m z x (List.ofFn seed)).2.sum) := by
  have hne : List.ofFn seed ++ tail ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  rw [Nat.add_comm, Function.iterate_add_apply, vrada_full_gradient_queries oracle L _ _ _ _ _ hne]
  simpa using vrada_inner_queries oracle L (List.ofFn seed) tail m k x z 0 (by
    intro h
    have := congrArg List.length h
    simp at this
    omega)


lemma vrada_epochs_queries (oracle : Fin n × E → E) (L : ℝ)
    (S m : ℕ) (hm : 0 < m) (seed : VradaSeeds n m S) (tail : List (Fin n)) (k : ℕ) (x z : E) :
    (vradaStep oracle L)^[(n + 2 * m) * S]
        (vradaEpochStart (vradaFlatten S seed ++ tail) m k x z) =
      vradaEpochStart tail m (k + S) (vradaRun oracle L m S k x z seed).1
        (vradaRun oracle L m S k x z seed).2 := by
  induction S generalizing k x z with
  | zero => simp [vradaFlatten, vradaRun]
  | succ S ih =>
    rcases seed with ⟨seed, rest⟩
    simp only [vradaFlatten, List.append_assoc, Nat.mul_succ]
    rw [Function.iterate_add_apply, vrada_epoch_queries oracle L hm]
    rw [ih rest (k + 1)]
    simp [vradaRun, Nat.add_comm, Nat.add_left_comm]

lemma execute_vrada (oracle : Fin n × E → E) (L : ℝ) (x0 : E) (m S : ℕ) (hm : 0 < m)
    (seed : VradaSeeds n m S) :
    execute { answer := fun _ (_, query) _ => oracle query } (vrada L x0 m S) (fun _ => ((n + 2 * m) * S)) seed =
      (vradaRun oracle L m S 0 x0 x0 seed).2 := by
  erw [execute_iterate]
  change ((vradaStep oracle L)^[(n + 2 * m) * S]
    (vradaEpochStart (vradaFlatten S seed) m 0 x0 x0)).snapshot = _
  have h := vrada_epochs_queries oracle L S m hm seed [] 0 x0 x0
  simpa [vradaEpochStart] using congrArg (fun state : VradaState n E => state.snapshot) h

end OracleTemplate.FiniteSum
