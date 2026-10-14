import LongTails.Algorithms.Svrg
import LongTails.Proofs.Execution
import Mathlib.Tactic

namespace OracleTemplate.FiniteSum

lemma queryCount_eq (n m S : ℕ) : queryCount n m S = n * S + 2 * m * (2 ^ S - 1) := by
  induction S generalizing m with
  | zero => simp [queryCount]
  | succ S ih =>
    have hp : 0 < 2 ^ S := by positivity
    have hd : 2 ^ S * 2 - 1 = 2 * (2 ^ S - 1) + 1 := by omega
    simp only [queryCount, ih, pow_succ]
    rw [hd]
    ring

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def svrgStep (oracle : Fin n × E → E) (L : ℝ) (state : SvrgState n E) :
    SvrgState n E := svrgUpdate L state (oracle (svrgQuery state))

def epochStart (seed : List (Fin n)) (m : ℕ) (x z : E) : SvrgState n E :=
  ⟨seed, 0, 0, m, m, x, z, 0, 0, 0⟩

noncomputable def innerState (oracle : Fin n × E → E) (seed : List (Fin n))
    (m r : ℕ) (x z accumulated : E) : SvrgState n E :=
  ⟨seed, 1, 0, m, r, x, z, accumulated, fullGradient oracle z, 0⟩

lemma full_gradient_queries (oracle : Fin n × E → E) (L : ℝ)
    (seed : List (Fin n)) (m : ℕ) (x z : E) (hne : seed ≠ []) :
    (svrgStep oracle L)^[n] (epochStart seed m x z) = innerState oracle seed m m x z 0 := by
  let g := fun k : ℕ => oracle (⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩, z)
  have hi : ∀ k, k ≤ n →
      (svrgStep oracle L)^[k] (epochStart seed m x z) =
        if k < n then
          ⟨seed, 0, k, m, m, x, z, 0, ∑ j ∈ Finset.range k, g j, 0⟩
        else
          ⟨seed, 1, 0, m, m, x, z, 0, (n : ℝ)⁻¹ • ∑ j ∈ Finset.range k, g j, 0⟩ := by
    intro k hk
    induction k with
    | zero => simp [epochStart, NeZero.pos n]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega), ite_eq_left (by omega : k < n)]
      by_cases h : k + 1 < n <;>
        simp [svrgStep, svrgQuery, svrgUpdate, h, Finset.sum_range_succ, g, hne]
  rw [hi n le_rfl, ite_eq_right (Nat.lt_irrefl n)]
  have hs : (∑ j ∈ Finset.range n, g j) = ∑ i : Fin n, oracle (i, z) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [g, Nat.mod_eq_of_lt i.isLt]
  simp only [hs, innerState, fullGradient]

lemma inner_two_queries (oracle : Fin n × E → E) (L : ℝ)
    (i : Fin n) (seed : List (Fin n)) (m r : ℕ) (x z accumulated : E) :
    (svrgStep oracle L)^[2] (innerState oracle (i :: seed) m r x z accumulated) =
      if r = 1 then
        epochStart seed (2 * m) (x - (1 / (8 * L)) • estimator oracle z x i)
          ((m : ℝ)⁻¹ • (accumulated + x))
      else
        innerState oracle seed m (r - 1) (x - (1 / (8 * L)) • estimator oracle z x i)
          z (accumulated + x) := by
  by_cases h : r = 1 <;>
    simp [Function.iterate_succ_apply', svrgStep, innerState, svrgQuery, svrgUpdate,
      epochStart, estimator, h]

lemma inner_queries (oracle : Fin n × E → E) (L : ℝ)
    (seed tail : List (Fin n)) (m : ℕ) (x z accumulated : E) (hne : seed ≠ []) :
    (svrgStep oracle L)^[2 * seed.length]
        (innerState oracle (seed ++ tail) m seed.length x z accumulated) =
      epochStart tail (2 * m) (innerRun oracle L z x seed).1
        ((m : ℝ)⁻¹ • (accumulated + (innerRun oracle L z x seed).2.sum)) := by
  induction seed generalizing x accumulated with
  | nil => contradiction
  | cons i seed ih =>
    cases seed with
    | nil => simpa [innerRun] using inner_two_queries oracle L i tail m 1 x z accumulated
    | cons j seed =>
      have hr : (j :: seed).length + 1 ≠ 1 := by simp
      rw [List.length_cons, show 2 * ((j :: seed).length + 1) = 2 * (j :: seed).length + 2 by omega,
        Function.iterate_add_apply]
      simp only [List.cons_append]
      rw [inner_two_queries, ite_eq_right hr]
      simp only [Nat.add_sub_cancel]
      have ih' := ih (x - (1 / (8 * L)) • estimator oracle z x i)
        (accumulated + x) (by simp)
      simp only [List.cons_append] at ih'
      rw [ih']
      simp [innerRun, add_assoc]

lemma epoch_queries (oracle : Fin n × E → E) (L : ℝ)
    {m : ℕ} (hm : 0 < m) (seed : Fin m → Fin n) (tail : List (Fin n)) (x z : E) :
    (svrgStep oracle L)^[n + 2 * m] (epochStart (List.ofFn seed ++ tail) m x z) =
      epochStart tail (2 * m) (innerRun oracle L z x (List.ofFn seed)).1
        ((m : ℝ)⁻¹ • (innerRun oracle L z x (List.ofFn seed)).2.sum) := by
  have hne : List.ofFn seed ++ tail ≠ [] := by
    intro h
    have := congrArg List.length h
    simp at this
    omega
  rw [Nat.add_comm, Function.iterate_add_apply, full_gradient_queries oracle L _ _ _ _ hne]
  simpa using inner_queries oracle L (List.ofFn seed) tail m x z 0 (by
    intro h
    have := congrArg List.length h
    simp at this
    omega)

lemma epochs_queries (oracle : Fin n × E → E) (L : ℝ)
    (S m : ℕ) (hm : 0 < m) (seed : EpochSeeds n m S) (tail : List (Fin n)) (x z : E) :
    (svrgStep oracle L)^[queryCount n m S] (epochStart (flattenSeeds S seed ++ tail) m x z) =
      epochStart tail (m * 2 ^ S) (epochRun oracle L m S x z seed).1
        (epochRun oracle L m S x z seed).2 := by
  induction S generalizing m x z with
  | zero => simp [queryCount, flattenSeeds, epochRun]
  | succ S ih =>
    rcases seed with ⟨seed, rest⟩
    simp only [queryCount, flattenSeeds, List.append_assoc]
    rw [Nat.add_comm (n + 2 * m), Function.iterate_add_apply, epoch_queries oracle L hm]
    rw [ih (2 * m) (by omega)]
    simp [epochRun, pow_succ, Nat.mul_assoc, Nat.mul_comm]

lemma execute_svrg (oracle : Fin n × E → E) (L : ℝ) (x0 : E) (S : ℕ)
    (seed : EpochSeeds n 2 S) :
    execute { answer := fun _ (_, query) _ => oracle query } (svrg L x0 S) (fun _ => (queryCount n 2 S)) seed =
      (epochRun oracle L 2 S x0 x0 seed).2 := by
  erw [execute_iterate]
  change ((svrgStep oracle L)^[queryCount n 2 S]
    (epochStart (flattenSeeds S seed) 2 x0 x0)).snapshot = _
  have h := epochs_queries oracle L S 2 (by decide) seed [] x0 x0
  simpa [epochStart] using congrArg SvrgState.snapshot h

lemma execute_svrg_of_le (oracle : Fin n × E → E) (L : ℝ) (x0 : E) (S K : ℕ)
    (hK : queryCount n 2 S ≤ K) (seed : EpochSeeds n 2 S) :
    execute { answer := fun _ (_, query) _ => oracle query } (svrg L x0 S) (fun _ => K) seed =
      (epochRun oracle L 2 S x0 x0 seed).2 := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hK
  erw [execute_iterate]
  change ((svrgStep oracle L)^[queryCount n 2 S + extra]
    (epochStart (flattenSeeds S seed) 2 x0 x0)).snapshot = _
  rw [Nat.add_comm, Function.iterate_add_apply]
  have h := epochs_queries oracle L S 2 (by decide) seed [] x0 x0
  simp only [List.append_nil] at h
  rw [h]
  have hfix : ∀ k m x z, (svrgStep oracle L)^[k] (epochStart [] m x z) =
      epochStart [] m x z := by
    intro k m x z
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [svrgStep, svrgUpdate, epochStart]
  rw [hfix]
  rfl

end OracleTemplate.FiniteSum
