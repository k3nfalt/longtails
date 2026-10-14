import LongTails.Proofs.AcceleratedMarkovRun
import LongTails.Proofs.SgdExecution

namespace OracleTemplate.HeavyTailedMarkovGradient

open StochasticGradient
open LongTails.Setups.StochasticSmoothAndConvex

lemma advance_add {S : Type*} (step : ℕ → S → S) (K J call : ℕ) (s : S) :
    advance step (K + J) call s = advance step J (call + K) (advance step K call s) := by
  induction K generalizing call s with
  | zero => simp [advance]
  | succ K ih =>
    simp only [Nat.succ_add, advance]
    convert ih (call + 1) (step call s) using 1; congr 1; omega

lemma advance_spaced_idle {Q V U Ω : Type*} (A : Algorithm Q V U) (g : Q → Ω → V)
    (ξ : ℕ → Ω) {m : ℕ} (_hm : 0 < m) (k n j : ℕ) (hj : 0 < j) (hjn : j + n ≤ m)
    (s : A.State) :
    advance (fun call state => (spaced m A).update state (g (((spaced m A).query state).2) (ξ call)))
      n (k * m + j) (k * m + j, s) = (k * m + j + n, s) := by
  dsimp only [spaced]
  induction n generalizing j with
  | zero => simp [advance]
  | succ n ih =>
    have hjm : j < m := by omega
    have hmod : (k * m + j) % m ≠ 0 := by simp [Nat.add_mod, Nat.mod_eq_of_lt hjm, Nat.ne_of_gt hj]
    rw [advance]
    simp only [hmod, ite_false]
    convert ih (j + 1) (by omega) (by omega) using 1; congr 1; omega

lemma advance_spaced_block {Q V U Ω : Type*} (A : Algorithm Q V U) (g : Q → Ω → V)
    (ξ : ℕ → Ω) {m : ℕ} (hm : 0 < m) (k : ℕ) (s : A.State) :
    advance (fun call state => (spaced m A).update state (g (((spaced m A).query state).2) (ξ call)))
      m (k * m) (k * m, s) = ((k + 1) * m, A.update s (g ((A.query s).2) (ξ (k * m)))) := by
  dsimp only [spaced]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [advance]
  simp only [Nat.mul_mod, Nat.mod_self, mul_zero, Nat.zero_mod, ite_true]
  have hh := advance_spaced_idle A g ξ (by omega : 0 < n + 1) k n 1 (by omega) (by omega)
    (A.update s (g ((A.query s).2) (ξ (k * (n + 1)))))
  simpa only [spaced, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_mul, Nat.one_mul] using hh

variable {E : Type*} {Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma advance_acceleratedMarkov (g : E → Ω → E) (D R C : ℝ) {m : ℕ} (hm : 0 < m)
    (x0 : E) (ξ : ℕ → Ω) (K : ℕ) :
    advance (fun call state => (acceleratedMarkov D R C m x0).update state
      (g (((acceleratedMarkov D R C m x0).query state).2) (ξ call)))
      (K * m) 0 (0, 0, x0, x0) = (K * m, clippedRun g D R C m x0 ξ K) := by
  dsimp only [acceleratedMarkov, spaced]
  induction K with
  | zero => rw [Nat.zero_mul]; rfl
  | succ K ih =>
    rw [Nat.succ_mul, advance_add, ih, Nat.zero_add]
    simpa only [Nat.succ_mul, clippedRun, acceleratedClipped, acceleratedMarkov, spaced] using
      advance_spaced_block (acceleratedClipped D R C x0) g ξ hm K (clippedRun g D R C m x0 ξ K)

lemma execute_acceleratedMarkov [MeasurableSpace Ω] (P : MeasureTheory.ProbabilityMeasure (ℕ → Ω))
    (g : E → Ω → E) (D R C : ℝ) {m : ℕ} (hm : 0 < m)
    (x0 : E) (ξ : ℕ → Ω) (K : ℕ) :
    execute { Seed := fun _ => Ω, law := P, answer := fun _ (_, x) y => g x y }
      (acceleratedMarkov D R C m x0) (fun _ => (K * m)) () ξ =
      (clippedRun g D R C m x0 ξ K).2.1 := by
  erw [execute_advance]
  change (acceleratedMarkov D R C m x0).output (advance _ (K * m) 0 (0, 0, x0, x0)) = _
  erw [advance_acceleratedMarkov g D R C hm x0 ξ K]
  rfl

end OracleTemplate.HeavyTailedMarkovGradient
