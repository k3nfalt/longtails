import LongTails.Algorithms.FixedBatchSgd
import LongTails.Proofs.BatchedExecution
import LongTails.Proofs.MarkovQuadraticExecution

open MeasureTheory

namespace OracleTemplate.FixedBatchConfidence

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace Ω]

lemma execute_batched_partial {Q V W U : Type} {b : ℕ} (hb : 0 < b)
    (A : Algorithm Q V U) (queries : A.State → Fin b → Q)
    (decode : A.State → (Fin b → W) → V) (zero : W)
    (P : ProbabilityMeasure (ℕ → Ω)) (g : Q → Ω → W)
    (ξ : ℕ → Ω) (K j : ℕ) (hj : j < b) (seed : A.Seed) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) z => g x z }
      (batched hb A queries decode zero) (fun _ => (K * b + j)) seed ξ =
      (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) z => g x z }
        (batched hb A queries decode zero) (fun _ => (K * b)) seed ξ) := by
  erw [execute_batched, StochasticGradient.execute_advance]
  change (batched hb A queries decode zero).output
    (StochasticGradient.advance _ (K * b + j) 0
      (0, A.initial seed, fun _ => zero)) = _
  erw [HeavyTailedMarkovGradient.advance_add]
  have h := advance_batched hb A queries decode zero g ξ K 0 (A.initial seed)
  simp only [Nat.zero_mul] at h
  erw [h, Nat.zero_add, advance_batched_prefix hb A queries decode zero g ξ _ _ j hj]
  rfl

lemma execute_fixedBatchSgd {b : ℕ} (hb : 0 < b)
    (P : ProbabilityMeasure (ℕ → Ω)) (g : E → Ω → E) (η : ℝ) (x0 : E)
    (K : ℕ) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) z => g x z }
      (fixedBatchSgd hb η x0) (fun _ => (K * b)) () ξ =
      MarkovQuadratic.iterate (fun x (block : Fin b → Ω) =>
        (b : ℝ)⁻¹ • ∑ i : Fin b, g x (block i)) η x0
          (fun k i => ξ (k * b + i.val)) K := by
  unfold fixedBatchSgd
  erw [execute_batched]
  let G := fun x (block : Fin b → Ω) => (b : ℝ)⁻¹ • ∑ i : Fin b, g x (block i)
  let blocks := fun k (i : Fin b) => ξ (k * b + i.val)
  have h : ∀ n call, StochasticGradient.advance
      (fun k x => x - η • G x (blocks k)) n call
        (MarkovQuadratic.iterate G η x0 blocks call) =
          MarkovQuadratic.iterate G η x0 blocks (call + n) := by
    intro n
    induction n with
    | zero => intro call; rfl
    | succ n ih =>
      intro call
      rw [StochasticGradient.advance]
      change StochasticGradient.advance _ n (call + 1)
        (MarkovQuadratic.iterate G η x0 blocks (call + 1)) = _
      rw [ih]
      congr 1
      omega
  simpa only [MarkovQuadratic.lastSgd, MarkovQuadratic.iterate, Nat.zero_add] using
    (h K 0)

lemma execute_fixedBatchSgd_calls {b : ℕ} (hb : 0 < b)
    (P : ProbabilityMeasure (ℕ → Ω)) (g : E → Ω → E) (η : ℝ) (x0 : E)
    (N : ℕ) (ξ : ℕ → Ω) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) z => g x z }
      (fixedBatchSgd hb η x0) (fun _ => N) () ξ =
      MarkovQuadratic.iterate (fun x (block : Fin b → Ω) =>
        (b : ℝ)⁻¹ • ∑ i : Fin b, g x (block i)) η x0
          (fun k i => ξ (k * b + i.val)) (N / b) := by
  have hN : N = N / b * b + N % b := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod N b).symm
  conv_lhs => rw [hN]
  unfold fixedBatchSgd
  erw [execute_batched_partial hb (MarkovQuadratic.lastSgd η x0)
      (fun x _ => x) (fun _ replies => (b : ℝ)⁻¹ • ∑ i : Fin b, replies i)
      0 P g ξ (N / b) (N % b) (Nat.mod_lt N hb) ()]
  change (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) z => g x z } (fixedBatchSgd hb η x0) (fun _ => (N / b * b)) () ξ) = _
  erw [execute_fixedBatchSgd]

lemma measurable_fixedBatchSgd [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {b : ℕ} (hb : 0 < b) (P : ProbabilityMeasure (ℕ → Ω))
    (g : E → Ω → E) (hg : Measurable (Function.uncurry g)) (η : ℝ) (x0 : E) (N : ℕ) :
    Measurable (fun ξ =>
      (execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) z => g x z }
        (fixedBatchSgd hb η x0) (fun _ => N) () ξ)) := by
  let G := fun (x : E) (v : Fin b → Ω) => (b : ℝ)⁻¹ • ∑ i : Fin b, g x (v i)
  have hG : Measurable (Function.uncurry G) := by
    have hs : Measurable (fun z : E × (Fin b → Ω) => ∑ i : Fin b, g z.1 (z.2 i)) := by
      apply Finset.measurable_sum
      intro i _
      exact hg.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
    exact hs.const_smul _
  have hblock : Measurable (fun ξ : ℕ → Ω => fun k (i : Fin b) => ξ (k * b + i.val)) := by
    fun_prop
  have hm := (MarkovQuadratic.measurable_iterate G hG η x0 (N / b)).comp hblock
  simpa only [execute_fixedBatchSgd_calls, G, Function.comp_def] using hm

end OracleTemplate.FixedBatchConfidence
