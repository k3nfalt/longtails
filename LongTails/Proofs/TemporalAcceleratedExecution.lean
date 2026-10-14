import LongTails.Algorithms.TemporalAccelerated
import LongTails.Proofs.SgdExecution

namespace OracleTemplate.TemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma tailAverage_sub_const (v : ℕ → E) (u : E) (start count : ℕ) (hc : 0 < count) :
    tailAverage (fun k => v k - u) start count = tailAverage v start count - u := by
  have hn : (count : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  simp [tailAverage, Finset.sum_sub_distrib, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_sub, smul_smul, hn]

lemma query_sub_const (θ : ℝ) (hθ : 1 + θ ≠ 0) (s : E × E) (u : E) :
    acceleratedQuery θ (s - (u, u)) = acceleratedQuery θ s - u := by
  dsimp [acceleratedQuery]
  match_scalars
  all_goals field_simp
  all_goals ring

lemma update_sub_const (θ μ : ℝ) (hθ : 1 + θ ≠ 0) (s : E × E) (u g : E) :
    acceleratedUpdate θ μ (s - (u, u)) g = acceleratedUpdate θ μ s g - (u, u) := by
  unfold acceleratedUpdate
  rw [query_sub_const θ hθ]
  ext <;> simp only [Prod.snd_sub, Prod.fst_sub] <;> module

lemma execute_tailAccelerated (O : Oracle E E) (g : ℕ → E → E)
    (hO : ∀ k x seed, O.answer k (0, x) seed = g k x) (θ μ : ℝ) (x0 : E)
    (K : ℕ) (seed : (tailAccelerated θ μ x0).Seed) (ξ : (k : ℕ) → O.Seed k) :
    execute O (tailAccelerated θ μ x0) (fun _ => K) seed ξ =
      tailAverage (fun k => (acceleratedRun g θ μ x0 k).1) (K / 2) (K - K / 2) := by
  let A := tailAccelerated θ μ x0
  let step : ℕ → (ℕ × (ℕ → E × E)) → (ℕ × (ℕ → E × E)) :=
    fun k s => A.update s (g k ((A.query s).2))
  have go (N start : ℕ) (history : ℕ → E × E)
      (hh : ∀ j ≤ start, history j = acceleratedRun g θ μ x0 j) :
      (StochasticGradient.advance step N start (start, history)).1 = start + N ∧
      ∀ j ≤ start + N, (StochasticGradient.advance step N start (start, history)).2 j =
        acceleratedRun g θ μ x0 j := by
    induction N generalizing start history with
    | zero => simpa [StochasticGradient.advance] using hh
    | succ N ih =>
      let next := Function.update history (start + 1)
        (acceleratedUpdate θ μ (history start) (g start (acceleratedQuery θ (history start))))
      have hn : ∀ j ≤ start + 1, next j = acceleratedRun g θ μ x0 j := by
        intro j hj
        by_cases he : j = start + 1
        · subst j
          simp [next, acceleratedRun, hh start le_rfl]
        · dsimp only [next]
          rw [Function.update_of_ne he]
          exact hh j (by omega)
      have hi := ih (start + 1) next hn
      simpa only [StochasticGradient.advance, step, A, tailAccelerated,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.succ_eq_add_one, next] using hi
  have hh : ∀ j ≤ 0, (fun _ => (x0, x0)) j = acceleratedRun g θ μ x0 j := by
    intro j hj
    have : j = 0 := by omega
    subst j
    rfl
  have hr := go K 0 (fun _ => (x0, x0)) hh
  simp only [Nat.zero_add] at hr
  rw [StochasticGradient.execute_advance]
  simp only [tailAccelerated]
  simp_rw [hO]
  change A.output (StochasticGradient.advance step K 0 (0, fun _ => (x0, x0))) = _
  dsimp only [A, tailAccelerated]
  rw [hr.1]
  unfold tailAverage
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only
  rw [hr.2 (K / 2 + k + 1) (by have := Finset.mem_range.mp hk; omega)]

end OracleTemplate.TemporalDiscrepancy
