import LongTails.Algorithms.NormalizedStorm
import LongTails.Proofs.Execution
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Normed.Module.Basic

open MeasureTheory

namespace OracleTemplate.NormalizedStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}

noncomputable def batchMean (g : E → Ω → E) (x0 : E) (ξ : ℕ → Ω) : ℕ → E
  | 0 => 0
  | j + 1 => batchMean g x0 ξ j + (1 / ((j : ℝ) + 1)) • (g x0 (ξ j) - batchMean g x0 ξ j)

noncomputable def stormPair (g : E → Ω → E) (η a : ℝ) (b0 : ℕ) (x0 : E) (ξ : ℕ → Ω) :
    ℕ → E × E
  | 0 => (x0, batchMean g x0 ξ b0)
  | j + 1 =>
      (stormStep η (stormPair g η a b0 x0 ξ j).1 (stormPair g η a b0 x0 ξ j).2,
        g (stormStep η (stormPair g η a b0 x0 ξ j).1 (stormPair g η a b0 x0 ξ j).2) (ξ (b0 + j)) +
          (1 - a) • ((stormPair g η a b0 x0 ξ j).2 - g (stormPair g η a b0 x0 ξ j).1 (ξ (b0 + j))))

lemma stormPair_succ (g : E → Ω → E) (η a : ℝ) (b0 : ℕ) (x0 : E) (ξ : ℕ → Ω) (j : ℕ) :
    stormPair g η a b0 x0 ξ (j + 1) =
      (stormStep η (stormPair g η a b0 x0 ξ j).1 (stormPair g η a b0 x0 ξ j).2,
        g (stormStep η (stormPair g η a b0 x0 ξ j).1 (stormPair g η a b0 x0 ξ j).2) (ξ (b0 + j)) +
          (1 - a) • ((stormPair g η a b0 x0 ξ j).2 - g (stormPair g η a b0 x0 ξ j).1 (ξ (b0 + j)))) :=
  rfl

lemma batchMean_congr (g : E → Ω → E) (x0 : E) {ξ ξ' : ℕ → Ω} :
    ∀ j, (∀ i, i < j → ξ i = ξ' i) → batchMean g x0 ξ j = batchMean g x0 ξ' j
  | 0, _ => rfl
  | j + 1, h => by
      simp only [batchMean]
      rw [batchMean_congr g x0 j (fun i hi => h i (by omega)), h j (by omega)]

lemma stormPair_congr (g : E → Ω → E) (η a : ℝ) (b0 : ℕ) (x0 : E) {ξ ξ' : ℕ → Ω} :
    ∀ j, (∀ i, i < b0 + j → ξ i = ξ' i) → stormPair g η a b0 x0 ξ j = stormPair g η a b0 x0 ξ' j
  | 0, h => by
      simp only [stormPair]
      rw [batchMean_congr g x0 b0 (fun i hi => h i (by omega))]
  | j + 1, h => by
      rw [stormPair_succ, stormPair_succ, stormPair_congr g η a b0 x0 j (fun i hi => h i (by omega)),
        h (b0 + j) (by omega)]

section Measurability

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

lemma measurable_stormStep (η : ℝ) : Measurable (fun z : E × E => stormStep η z.1 z.2) := by
  unfold stormStep
  exact measurable_fst.sub ((measurable_const.div measurable_snd.norm).smul measurable_snd)

lemma measurable_batchMean {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (x0 : E) :
    ∀ j, Measurable (fun ξ : ℕ → Ω => batchMean g x0 ξ j)
  | 0 => measurable_const
  | j + 1 => by
      have hj := measurable_batchMean hg x0 j
      have hgj : Measurable (fun ξ : ℕ → Ω => g x0 (ξ j)) :=
        hg.comp (measurable_const.prodMk (measurable_pi_apply j))
      simp only [batchMean]
      exact hj.add ((hgj.sub hj).const_smul _)

lemma measurable_stormPair {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (η a : ℝ)
    (b0 : ℕ) (x0 : E) : ∀ j, Measurable (fun ξ : ℕ → Ω => stormPair g η a b0 x0 ξ j)
  | 0 => by
      simp only [stormPair]
      exact measurable_const.prodMk (measurable_batchMean hg x0 b0)
  | j + 1 => by
      have hj := measurable_stormPair hg η a b0 x0 j
      have hs : Measurable (fun ξ : ℕ → Ω =>
          stormStep η (stormPair g η a b0 x0 ξ j).1 (stormPair g η a b0 x0 ξ j).2) :=
        (measurable_stormStep η).comp hj
      have hξ : Measurable (fun ξ : ℕ → Ω => ξ (b0 + j)) := measurable_pi_apply _
      simp_rw [stormPair_succ]
      refine hs.prodMk ((hg.comp (hs.prodMk hξ)).add ?_)
      exact (hj.snd.sub (hg.comp (hj.fst.prodMk hξ))).const_smul _

end Measurability

section Execution

noncomputable def pairOracle (g : E → Ω → E) [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω)) :
    Oracle (E × E) (E × E) where
  Seed := fun _ => Ω
  law := P
  answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω)

lemma run_batch (g : E → Ω → E) (η a : ℝ) (b0 : ℕ) (x0 : E) (ξ : ℕ → Ω) (τ : ℕ) :
    ∀ n, n ≤ b0 →
      (fun sc : (ℕ × ℕ × E × E) × ℕ =>
          (stormUpdate η a b0 sc.1 ((fun z : E × E => (g z.1 (ξ sc.2), g z.2 (ξ sc.2)))
            (stormQuery η b0 sc.1)), sc.2 + 1))^[n] ((τ, 0, x0, 0), 0) =
        ((τ, n, x0, batchMean g x0 ξ n), n)
  | 0, _ => rfl
  | n + 1, h => by
      rw [Function.iterate_succ_apply', run_batch g η a b0 x0 ξ τ n (by omega)]
      have hn : n < b0 := by omega
      simp [stormUpdate, stormQuery, hn, batchMean]

lemma run_storm (g : E → Ω → E) (η a : ℝ) (b0 : ℕ) (x0 : E) (ξ : ℕ → Ω) (τ : ℕ) :
    ∀ j, j ≤ τ →
      (fun sc : (ℕ × ℕ × E × E) × ℕ =>
          (stormUpdate η a b0 sc.1 ((fun z : E × E => (g z.1 (ξ sc.2), g z.2 (ξ sc.2)))
            (stormQuery η b0 sc.1)), sc.2 + 1))^[b0 + j] ((τ, 0, x0, 0), 0) =
        ((τ, b0 + j, stormPair g η a b0 x0 ξ j), b0 + j)
  | 0, _ => by
      rw [Nat.add_zero, run_batch g η a b0 x0 ξ τ b0 le_rfl]
      rfl
  | j + 1, h => by
      rw [show b0 + (j + 1) = (b0 + j) + 1 by omega, Function.iterate_succ_apply',
        run_storm g η a b0 x0 ξ τ j (by omega)]
      have h1 : ¬ b0 + j < b0 := by omega
      have h2 : b0 + j < b0 + τ := by omega
      simp only [stormUpdate, stormQuery, h1, h2, ite_false, ite_true]
      rw [stormPair_succ]

lemma run_frozen (g : E → Ω → E) (η a : ℝ) (b0 : ℕ) (x0 : E) (ξ : ℕ → Ω) (τ : ℕ) :
    ∀ m, ((fun sc : (ℕ × ℕ × E × E) × ℕ =>
          (stormUpdate η a b0 sc.1 ((fun z : E × E => (g z.1 (ξ sc.2), g z.2 (ξ sc.2)))
            (stormQuery η b0 sc.1)), sc.2 + 1))^[b0 + τ + m] ((τ, 0, x0, 0), 0)).1 =
        (τ, b0 + τ, stormPair g η a b0 x0 ξ τ)
  | 0 => by rw [Nat.add_zero, run_storm g η a b0 x0 ξ τ τ le_rfl]
  | m + 1 => by
      rw [show b0 + τ + (m + 1) = (b0 + τ + m) + 1 by omega, Function.iterate_succ_apply']
      have ih := run_frozen g η a b0 x0 ξ τ m
      set sc := (fun sc : (ℕ × ℕ × E × E) × ℕ =>
          (stormUpdate η a b0 sc.1 ((fun z : E × E => (g z.1 (ξ sc.2), g z.2 (ξ sc.2)))
            (stormQuery η b0 sc.1)), sc.2 + 1))^[b0 + τ + m] ((τ, 0, x0, 0), 0)
      obtain ⟨s, c⟩ := sc
      simp only at ih
      subst ih
      by_cases h0 : b0 + τ < b0
      · omega
      · simp [stormUpdate, h0]

lemma execute_normalizedStorm [MeasurableSpace Ω] (g : E → Ω → E) (P : ProbabilityMeasure (ℕ → Ω))
    (η a : ℝ) (b0 T : ℕ) (x0 : E) (K : ℕ) (τ : (normalizedStorm (E := E) η a b0 T x0).Seed)
    (ξ : ℕ → Ω) (hK : b0 + T ≤ K) :
    execute (pairOracle g P) (normalizedStorm η a b0 T x0) (fun _ => K) τ ξ =
      (stormPair g η a b0 x0 ξ (τ : Fin (T + 1)).val).1 := by
  refine (execute_indexed_of_answer (pairOracle g P) (normalizedStorm η a b0 T x0) K τ ξ (fun k q => (g q.2.1 (ξ k), g q.2.2 (ξ k))) (fun _ _ => rfl)).trans ?_
  change Fin (T + 1) at τ
  obtain ⟨m, hm⟩ : ∃ m, K = b0 + τ.val + m := ⟨K - (b0 + τ.val), by have := τ.isLt; omega⟩
  subst hm
  have h := run_frozen g η a b0 x0 ξ τ.val m
  change (((fun sc : (ℕ × ℕ × E × E) × ℕ =>
          (stormUpdate η a b0 sc.1 ((fun z : E × E => (g z.1 (ξ sc.2), g z.2 (ξ sc.2)))
            (stormQuery η b0 sc.1)), sc.2 + 1))^[b0 + τ.val + m] ((τ.val, 0, x0, 0), 0)).1).2.2.1 = _
  rw [h]

end Execution

end OracleTemplate.NormalizedStorm
