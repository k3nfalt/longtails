import LongTails.Algorithms.Batched
import LongTails.Proofs.AcceleratedMarkovExecution

namespace OracleTemplate

open StochasticGradient HeavyTailedMarkovGradient
open LongTails.Setups.StochasticSmoothAndConvex

lemma advance_batched_prefix {Q V W U Ω : Type} {n : ℕ} (hn : 0 < n)
    (A : Algorithm Q V U) (queries : A.State → Fin n → Q)
    (decode : A.State → (Fin n → W) → V) (zero : W)
    (g : Q → Ω → W) (ξ : ℕ → Ω) (s : A.State) (call j : ℕ) (hj : j < n) :
    advance (fun k state => (batched hn A queries decode zero).update state
      (g (((batched hn A queries decode zero).query state).2) (ξ k))) j call
      (0, s, fun _ => zero) =
      (j, s, fun i => if i.val < j then g (queries s i) (ξ (call + i.val)) else zero) := by
  induction j with
  | zero => simp [advance, batched]
  | succ j ih =>
    have hj' : j < n := by omega
    erw [show j + 1 = j + 1 by rfl, advance_add, ih hj']
    simp only [advance, batched, Nat.mod_eq_of_lt hj', hj, ite_true]
    congr 2
    funext i
    by_cases hi : i = (⟨j, hj'⟩ : Fin n)
    · subst i
      simp
    · have hne : i.val ≠ j := fun h => hi (Fin.ext h)
      simp only [Function.update_of_ne hi]
      split_ifs <;> simp_all only [not_lt] <;> omega

lemma advance_batched_block {Q V W U Ω : Type} {n : ℕ} (hn : 0 < n)
    (A : Algorithm Q V U) (queries : A.State → Fin n → Q)
    (decode : A.State → (Fin n → W) → V) (zero : W)
    (g : Q → Ω → W) (ξ : ℕ → Ω) (s : A.State) (call : ℕ) :
    advance (fun k state => (batched hn A queries decode zero).update state
      (g (((batched hn A queries decode zero).query state).2) (ξ k))) n call
      (0, s, fun _ => zero) =
      (0, A.update s (decode s (fun i => g (queries s i) (ξ (call + i.val)))), fun _ => zero) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  erw [advance_add (K := j) (J := 1), advance_batched_prefix (by omega) A queries decode zero g ξ s call j (by omega)]
  simp only [advance, batched, Nat.mod_eq_of_lt (show j < j + 1 by omega),
    lt_self_iff_false, ite_false]
  congr 4
  funext i
  by_cases hi : i = (⟨j, by omega⟩ : Fin (j + 1))
  · subst i
    simp
  · have hil : i.val < j := by
      have hv := i.isLt
      have hne : i.val ≠ j := fun h => hi (Fin.ext h)
      omega
    simp [Function.update_of_ne hi, hil]

lemma advance_batched {Q V W U Ω : Type} {n : ℕ} (hn : 0 < n)
    (A : Algorithm Q V U) (queries : A.State → Fin n → Q)
    (decode : A.State → (Fin n → W) → V) (zero : W)
    (g : Q → Ω → W) (ξ : ℕ → Ω) (K k : ℕ) (s : A.State) :
    advance (fun call state => (batched hn A queries decode zero).update state
      (g (((batched hn A queries decode zero).query state).2) (ξ call))) (K * n) (k * n)
      (0, s, fun _ => zero) =
      (0, advance (fun call state => A.update state
        (decode state (fun i => g (queries state i) (ξ (call * n + i.val))))) K k s,
        fun _ => zero) := by
  induction K generalizing k s with
  | zero => simp [advance, batched]
  | succ K ih =>
    erw [show (K + 1) * n = n + K * n by ring, advance_add,
      advance_batched_block]
    erw [show k * n + n = (k + 1) * n by ring, ih]
    rfl

lemma execute_batched {Q V W U Ω : Type} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (A : Algorithm Q V U) (queries : A.State → Fin n → Q)
    (decode : A.State → (Fin n → W) → V) (zero : W)
    (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : Q → Ω → W) (ξ : ℕ → Ω) (K : ℕ) (seed : A.Seed) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) ω => g x ω }
      (batched hn A queries decode zero) (fun _ => (K * n)) seed ξ =
      A.output (advance (fun call state => A.update state
        (decode state (fun i => g (queries state i) (ξ (call * n + i.val))))) K 0
        (A.initial seed)) := by
  erw [execute_advance]
  have h := advance_batched hn A queries decode zero g ξ K 0 (A.initial seed)
  simp only [Nat.zero_mul] at h
  change (batched hn A queries decode zero).output
    (advance (fun k state => (batched hn A queries decode zero).update state
      (g (((batched hn A queries decode zero).query state).2) (ξ k)))
      (K * n) 0 (0, A.initial seed, fun _ => zero)) = _
  erw [h]
  rfl

end OracleTemplate
