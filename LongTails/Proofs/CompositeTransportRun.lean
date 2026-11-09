import LongTails.Algorithms.CompositeTransport
import LongTails.Proofs.Execution

open MeasureTheory

namespace OracleTemplate.CompositeTransport

open LongTails.Setups.StochasticCompositeHessianLipschitz

section Traj

variable {E Ω : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def mInit (cfg : Config) (x0 : E) (g : E → Ω → E) (ξ : ℕ → Ω) : E :=
  (1 / (cfg.n0 : ℝ)) • ∑ i ∈ Finset.range cfg.n0, g x0 (ξ i)

noncomputable def traj (cfg : Config) (x0 : E) (g : E → Ω → E) (prox : ℝ → E → E → E)
    (ξ : ℕ → Ω) : ℕ → E × E × E
  | 0 => (x0, x0, mInit cfg x0 g ξ)
  | t + 1 =>
      let s := traj cfg x0 g prox ξ t
      let x' := capStep cfg s.1 (prox cfg.γ s.1 s.2.2)
      (x', s.1, (1 - cfg.α) • s.2.2 + cfg.α • g (lead cfg x' s.1) (ξ (cfg.n0 + 2 * t + 1)))

end Traj

section Exec

variable (p : Params) (cfg : Config) (g : p.E → p.Ω → p.E) (prox : ℝ → p.E → p.E → p.E)
  (ξ : ℕ → p.Ω) (τ : ℕ)

noncomputable def response (k : ℕ) (q : Fin 1 × Query p) : p.E :=
  match q.2 with
  | .gradient x => g x (ξ k)
  | .prox a z v => prox a z v

noncomputable def runStep (sc : State p.E × ℕ) : State p.E × ℕ :=
  (transportUpdate cfg sc.1 (response p g prox ξ sc.2 (0, transportQuery p cfg sc.1)), sc.2 + 1)

noncomputable def init : State p.E × ℕ :=
  ({ c := 0, tau := τ, x := p.x0, xp := p.x0, m := 0, acc := 0 }, 0)

noncomputable def accAll : p.E := ∑ i ∈ Finset.range cfg.n0, g p.x0 (ξ i)

noncomputable def stB (t : ℕ) : State p.E × ℕ :=
  ({ c := cfg.n0 + 2 * t, tau := τ, x := (traj cfg p.x0 g prox ξ t).1,
     xp := (traj cfg p.x0 g prox ξ t).2.1, m := (traj cfg p.x0 g prox ξ t).2.2,
     acc := accAll p cfg g ξ }, cfg.n0 + 2 * t)

lemma phaseA (hn : 1 ≤ cfg.n0) : ∀ k, k ≤ cfg.n0 →
    (runStep p cfg g prox ξ)^[k] (init p τ) =
      ({ c := k, tau := τ, x := p.x0, xp := p.x0,
         m := if k = cfg.n0 then mInit cfg p.x0 g ξ else 0,
         acc := ∑ i ∈ Finset.range k, g p.x0 (ξ i) }, k) := by
  intro k
  induction k with
  | zero =>
      intro _
      have : (0 : ℕ) ≠ cfg.n0 := by omega
      simp [init, this]
  | succ k ih =>
      intro hk
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hlt : k < cfg.n0 := by omega
      have hk0 : k ≠ cfg.n0 := by omega
      simp only [runStep, transportQuery, transportUpdate, hlt, ite_true, response, hk0, ite_false]
      by_cases he : k + 1 = cfg.n0
      · simp only [he, ite_true, mInit]
        rw [← he, Finset.sum_range_succ]
      · simp only [he, ite_false, Finset.sum_range_succ]

lemma phaseB (hn : 1 ≤ cfg.n0) : ∀ t, t ≤ τ →
    (runStep p cfg g prox ξ)^[cfg.n0 + 2 * t] (init p τ) = stB p cfg g prox ξ τ t := by
  intro t
  induction t with
  | zero =>
      intro _
      rw [Nat.mul_zero, Nat.add_zero, phaseA p cfg g prox ξ τ hn cfg.n0 le_rfl]
      simp [stB, traj, accAll]
  | succ t ih =>
      intro ht
      have e : cfg.n0 + 2 * (t + 1) = (cfg.n0 + 2 * t) + 1 + 1 := by ring
      rw [e, Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
      have h1 : ¬ (cfg.n0 + 2 * t < cfg.n0) := by omega
      have h2 : (cfg.n0 + 2 * t - cfg.n0) / 2 < τ := by omega
      have h3 : (cfg.n0 + 2 * t - cfg.n0) % 2 = 0 := by omega
      have h4 : ¬ (cfg.n0 + 2 * t + 1 < cfg.n0) := by omega
      have h5 : (cfg.n0 + 2 * t + 1 - cfg.n0) / 2 < τ := by omega
      have h6 : ¬ ((cfg.n0 + 2 * t + 1 - cfg.n0) % 2 = 0) := by omega
      simp only [stB, runStep, transportQuery, transportUpdate, h1, h2, h3, h4, h5, h6, ite_true,
        ite_false, response]
      simp only [traj]
      congr 1

lemma phaseC (hn : 1 ≤ cfg.n0) : ∀ j,
    ((runStep p cfg g prox ξ)^[cfg.n0 + 2 * τ + j] (init p τ)).1.x = (traj cfg p.x0 g prox ξ τ).1 ∧
    ((runStep p cfg g prox ξ)^[cfg.n0 + 2 * τ + j] (init p τ)).1.c = cfg.n0 + 2 * τ + j ∧
    ((runStep p cfg g prox ξ)^[cfg.n0 + 2 * τ + j] (init p τ)).1.tau = τ := by
  intro j
  induction j with
  | zero =>
      rw [Nat.add_zero, phaseB p cfg g prox ξ τ hn τ le_rfl]
      exact ⟨rfl, rfl, rfl⟩
  | succ j ih =>
      obtain ⟨hx, hc, ht⟩ := ih
      rw [show cfg.n0 + 2 * τ + (j + 1) = (cfg.n0 + 2 * τ + j) + 1 by ring,
        Function.iterate_succ_apply']
      set s := (runStep p cfg g prox ξ)^[cfg.n0 + 2 * τ + j] (init p τ)
      have h1 : ¬ (s.1.c < cfg.n0) := by rw [hc]; omega
      have h2 : ¬ ((s.1.c - cfg.n0) / 2 < s.1.tau) := by rw [hc, ht]; omega
      simp only [runStep, transportUpdate, h1, h2, ite_false]
      exact ⟨hx, by rw [hc], ht⟩

lemma run_output (hn : 1 ≤ cfg.n0) (K : ℕ) (hK : cfg.n0 + 2 * τ ≤ K) :
    ((runStep p cfg g prox ξ)^[K] (init p τ)).1.x = (traj cfg p.x0 g prox ξ τ).1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK
  exact (phaseC p cfg g prox ξ τ hn j).1

noncomputable def oracleOf (P : ProbabilityMeasure (ℕ → p.Ω)) : Oracle (Query p) p.E where
  Seed := fun _ => p.Ω
  law := P
  answer := fun _ (_, query) ω => match query with
    | .gradient x => g x ω
    | .prox a z v => prox a z v

lemma execute_eq (hn : 1 ≤ cfg.n0) (P : ProbabilityMeasure (ℕ → p.Ω)) (K : ℕ)
    (τ' : Fin (cfg.T + 1)) (hK : cfg.n0 + 2 * cfg.T ≤ K) :
    execute (oracleOf p g prox P)
      (transport p cfg) (fun _ => K) τ' ξ =
      (traj cfg p.x0 g prox ξ τ'.val).1 := by
  refine (execute_indexed_of_answer (oracleOf p g prox P) (transport p cfg) K τ' ξ (response p g prox ξ) ?_).trans ?_
  · intro history query
    obtain ⟨i, q⟩ := query
    cases q <;> rfl
  · change ((runStep p cfg g prox ξ)^[K] (init p τ'.val)).1.x = _
    exact run_output p cfg g prox ξ τ'.val hn K (by have := τ'.isLt; omega)

end Exec

end OracleTemplate.CompositeTransport
