import LongTails.Algorithms.RecursiveMomentum
import LongTails.Proofs.NormalizedStormTrajectory

open MeasureTheory

namespace OracleTemplate.RecursiveMomentum

open OracleTemplate.NormalizedStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}

noncomputable def momentumPair (g : E → Ω → E) (γ a : ℝ) (b0 : ℕ) (x0 : E) (ξ : ℕ → Ω) :
    ℕ → E × E
  | 0 => (x0, batchMean g x0 ξ b0)
  | j + 1 =>
      (momentumStep γ (momentumPair g γ a b0 x0 ξ j).1 (momentumPair g γ a b0 x0 ξ j).2,
        g (momentumStep γ (momentumPair g γ a b0 x0 ξ j).1 (momentumPair g γ a b0 x0 ξ j).2)
            (ξ (b0 + j)) +
          (1 - a) • ((momentumPair g γ a b0 x0 ξ j).2 -
            g (momentumPair g γ a b0 x0 ξ j).1 (ξ (b0 + j))))

lemma momentumPair_succ (g : E → Ω → E) (γ a : ℝ) (b0 : ℕ) (x0 : E) (ξ : ℕ → Ω) (j : ℕ) :
    momentumPair g γ a b0 x0 ξ (j + 1) =
      (momentumStep γ (momentumPair g γ a b0 x0 ξ j).1 (momentumPair g γ a b0 x0 ξ j).2,
        g (momentumStep γ (momentumPair g γ a b0 x0 ξ j).1 (momentumPair g γ a b0 x0 ξ j).2)
            (ξ (b0 + j)) +
          (1 - a) • ((momentumPair g γ a b0 x0 ξ j).2 -
            g (momentumPair g γ a b0 x0 ξ j).1 (ξ (b0 + j)))) :=
  rfl

lemma momentumPair_congr (g : E → Ω → E) (γ a : ℝ) (b0 : ℕ) (x0 : E) {ξ ξ' : ℕ → Ω} :
    ∀ j, (∀ i, i < b0 + j → ξ i = ξ' i) →
      momentumPair g γ a b0 x0 ξ j = momentumPair g γ a b0 x0 ξ' j
  | 0, h => by
      simp only [momentumPair]
      rw [batchMean_congr g x0 b0 (fun i hi => h i (by omega))]
  | j + 1, h => by
      rw [momentumPair_succ, momentumPair_succ,
        momentumPair_congr g γ a b0 x0 j (fun i hi => h i (by omega)), h (b0 + j) (by omega)]

section Measurability

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma measurable_momentumStep (γ : ℝ) :
    Measurable (fun z : E × E => momentumStep γ z.1 z.2) := by
  unfold momentumStep
  exact measurable_fst.sub (measurable_snd.const_smul γ)

lemma measurable_momentumPair {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (γ a : ℝ)
    (b0 : ℕ) (x0 : E) : ∀ j, Measurable (fun ξ : ℕ → Ω => momentumPair g γ a b0 x0 ξ j)
  | 0 => by
      simp only [momentumPair]
      exact measurable_const.prodMk (measurable_batchMean hg x0 b0)
  | j + 1 => by
      have hj := measurable_momentumPair hg γ a b0 x0 j
      have hs : Measurable (fun ξ : ℕ → Ω =>
          momentumStep γ (momentumPair g γ a b0 x0 ξ j).1 (momentumPair g γ a b0 x0 ξ j).2) :=
        (measurable_momentumStep γ).comp hj
      have hξ : Measurable (fun ξ : ℕ → Ω => ξ (b0 + j)) := measurable_pi_apply _
      simp_rw [momentumPair_succ]
      refine hs.prodMk ((hg.comp (hs.prodMk hξ)).add ?_)
      exact (hj.snd.sub (hg.comp (hj.fst.prodMk hξ))).const_smul _

end Measurability

section Execution

lemma run_momentumBatch (g : E → Ω → E) (γ a : ℝ) (b0 : ℕ) (x0 : E) (ξ : ℕ → Ω) (τ : ℕ) :
    ∀ n, n ≤ b0 →
      (fun sc : (ℕ × ℕ × E × E) × ℕ =>
          (momentumUpdate γ a b0 sc.1 ((fun z : E × E => (g z.1 (ξ sc.2), g z.2 (ξ sc.2)))
            (momentumQuery γ b0 sc.1)), sc.2 + 1))^[n] ((τ, 0, x0, 0), 0) =
        ((τ, n, x0, batchMean g x0 ξ n), n)
  | 0, _ => rfl
  | n + 1, h => by
      rw [Function.iterate_succ_apply', run_momentumBatch g γ a b0 x0 ξ τ n (by omega)]
      have hn : n < b0 := by omega
      simp [momentumUpdate, momentumQuery, hn, batchMean]

lemma run_momentum (g : E → Ω → E) (γ a : ℝ) (b0 : ℕ) (x0 : E) (ξ : ℕ → Ω) (τ : ℕ) :
    ∀ j, j ≤ τ →
      (fun sc : (ℕ × ℕ × E × E) × ℕ =>
          (momentumUpdate γ a b0 sc.1 ((fun z : E × E => (g z.1 (ξ sc.2), g z.2 (ξ sc.2)))
            (momentumQuery γ b0 sc.1)), sc.2 + 1))^[b0 + j] ((τ, 0, x0, 0), 0) =
        ((τ, b0 + j, momentumPair g γ a b0 x0 ξ j), b0 + j)
  | 0, _ => by
      rw [Nat.add_zero, run_momentumBatch g γ a b0 x0 ξ τ b0 le_rfl]
      rfl
  | j + 1, h => by
      rw [show b0 + (j + 1) = (b0 + j) + 1 by omega, Function.iterate_succ_apply',
        run_momentum g γ a b0 x0 ξ τ j (by omega)]
      have h1 : ¬ b0 + j < b0 := by omega
      have h2 : b0 + j < b0 + τ := by omega
      simp only [momentumUpdate, momentumQuery, h1, h2, ite_false, ite_true]
      rw [momentumPair_succ]

lemma run_momentumFrozen (g : E → Ω → E) (γ a : ℝ) (b0 : ℕ) (x0 : E) (ξ : ℕ → Ω) (τ : ℕ) :
    ∀ m, ((fun sc : (ℕ × ℕ × E × E) × ℕ =>
          (momentumUpdate γ a b0 sc.1 ((fun z : E × E => (g z.1 (ξ sc.2), g z.2 (ξ sc.2)))
            (momentumQuery γ b0 sc.1)), sc.2 + 1))^[b0 + τ + m] ((τ, 0, x0, 0), 0)).1 =
        (τ, b0 + τ, momentumPair g γ a b0 x0 ξ τ)
  | 0 => by rw [Nat.add_zero, run_momentum g γ a b0 x0 ξ τ τ le_rfl]
  | m + 1 => by
      rw [show b0 + τ + (m + 1) = (b0 + τ + m) + 1 by omega, Function.iterate_succ_apply']
      have ih := run_momentumFrozen g γ a b0 x0 ξ τ m
      set sc := (fun sc : (ℕ × ℕ × E × E) × ℕ =>
          (momentumUpdate γ a b0 sc.1 ((fun z : E × E => (g z.1 (ξ sc.2), g z.2 (ξ sc.2)))
            (momentumQuery γ b0 sc.1)), sc.2 + 1))^[b0 + τ + m] ((τ, 0, x0, 0), 0)
      obtain ⟨s, c⟩ := sc
      simp only at ih
      subst ih
      by_cases h0 : b0 + τ < b0
      · omega
      · simp [momentumUpdate, h0]

lemma execute_recursiveMomentum [MeasurableSpace Ω] (g : E → Ω → E)
    (P : ProbabilityMeasure (ℕ → Ω)) (γ a : ℝ) (b0 T : ℕ) (x0 : E) (K : ℕ)
    (τ : (recursiveMomentum (E := E) γ a b0 T x0).Seed) (ξ : ℕ → Ω) (hK : b0 + T ≤ K) :
    execute (pairOracle g P) (recursiveMomentum γ a b0 T x0) (fun _ => K) τ ξ =
      (momentumPair g γ a b0 x0 ξ (τ : Fin (T + 1)).val).1 := by
  refine (execute_indexed_of_answer (pairOracle g P) (recursiveMomentum γ a b0 T x0) K τ ξ (fun k q => (g q.2.1 (ξ k), g q.2.2 (ξ k))) (fun _ _ => rfl)).trans ?_
  change Fin (T + 1) at τ
  obtain ⟨m, hm⟩ : ∃ m, K = b0 + τ.val + m := ⟨K - (b0 + τ.val), by have := τ.isLt; omega⟩
  subst hm
  have h := run_momentumFrozen g γ a b0 x0 ξ τ.val m
  change (((fun sc : (ℕ × ℕ × E × E) × ℕ =>
          (momentumUpdate γ a b0 sc.1 ((fun z : E × E => (g z.1 (ξ sc.2), g z.2 (ξ sc.2)))
            (momentumQuery γ b0 sc.1)), sc.2 + 1))^[b0 + τ.val + m] ((τ.val, 0, x0, 0), 0)).1).2.2.1 = _
  rw [h]

end Execution

end OracleTemplate.RecursiveMomentum
