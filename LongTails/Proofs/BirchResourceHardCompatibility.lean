import LongTails.Proofs.BirchResourceHardRun
import LongTails.Proofs.BirchResourceHardInstance

namespace LongTails.Proofs.BirchResourceHardCompatibility

open OracleTemplate.Rennala (Point)
open LongTails.Proofs.BirchResourceAdaptiveLower (past)
open LongTails.Proofs.BirchResourceHardRun
open LongTails.Proofs.BirchResourceHardInstance
open LongTails.Proofs.BirchResourceChain
open LongTails.Setups.BirchNonEuclidean (Params)

abbrev Query (d : ℕ) := (n : ℕ) → (Fin n → Bool) → Point d

noncomputable def observedLevel {Packet : Type*} (p : Params) (run : Scheduler Packet)
    (query : Query p.d) (ξ : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    match observed run ξ n with
    | none => observedLevel p run query ξ n
    | some _ =>
      max (observedLevel p run query ξ n)
        (progress (scaledOracle (width p) (amplitude p) (chance p) (query n (past n ξ)) (ξ n)))

def Captured {Packet : Type*} (p : Params) (run : Scheduler Packet) (query : Query p.d) (N : ℕ) : Prop :=
  ∀ ξ n s, n < N → observed run ξ n = some s →
    s.source = progress ((width p)⁻¹ • query n (past n ξ))

lemma scaled_support {D : ℕ} (a s q : ℝ) (x : Point D) (bit : Bool) :
    Supported (scaledOracle a s q x bit) (progress (a⁻¹ • x) + if bit then 1 else 0) := by
  intro i hi
  have hz : noisyGradient q (a⁻¹ • x) bit i = 0 := by
    cases bit
    · exact noisy_false_support q _ i (by simpa using hi)
    · exact noisy_support q _ true i hi
  change s * noisyGradient q (a⁻¹ • x) bit i = 0
  rw [hz, mul_zero]

lemma level_dominates {Packet : Type*} (p : Params) (run : Scheduler Packet)
    (query : Query p.d) {N : ℕ} (hc : Captured p run query N) (ξ : ℕ → Bool) (n : ℕ)
    (hn : n ≤ N) : observedLevel p run query ξ n ≤ level run ξ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases he : observed run ξ n with
    | none =>
      rw [observedLevel, level, he]
      exact ih (by omega)
    | some s =>
      rw [observedLevel, level, he]
      have hsrc := hc ξ n s (by omega) he
      apply max_le_max (ih (by omega))
      rw [hsrc]
      exact progress_le _ (scaled_support _ _ _ _ _)

lemma source_causal {Packet : Type*} (p : Params) (run : Scheduler Packet) (query : Query p.d) {N : ℕ}
    (hc : Captured p run query N) (ξ : ℕ → Bool) (n : ℕ) (s : Slot Packet)
    (hn : n < N) (hs : observed run ξ n = some s)
    (hprefix : s.launchPrefix ≤ n)
    (hquery : Supported (query n (past n ξ)) (observedLevel p run query ξ s.launchPrefix)) :
    s.launchPrefix ≤ n ∧ s.source ≤ level run ξ s.launchPrefix := by
  refine ⟨hprefix, ?_⟩
  rw [hc ξ n s hn hs]
  refine (progress_le _ ?_).trans
    (level_dominates p run query hc ξ s.launchPrefix (hprefix.trans hn.le))
  intro i hi
  change (width p)⁻¹ * query n (past n ξ) i = 0
  rw [hquery i hi, mul_zero]

lemma output_support {Packet : Type*} (p : Params) (run : Scheduler Packet) (query : Query p.d) {N : ℕ}
    (hc : Captured p run query N) (ξ : ℕ → Bool) (x : Point p.d)
    (hx : Supported x (observedLevel p run query ξ N)) :
    Supported x (level run ξ N) := by
  intro i hi
  exact hx i ((level_dominates p run query hc ξ N le_rfl).trans hi)

end LongTails.Proofs.BirchResourceHardCompatibility
