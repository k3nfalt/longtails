import LongTails.Setups.UscgHighProbability
import LongTails.Proofs.LmoTrajectory
import LongTails.Proofs.AdaptiveIID

open MeasureTheory

namespace LongTails.Proofs.UscgSharpExecution

open OracleTemplate
open private _run from LongTails.Template

lemma execute_exact_prefix {Q R U : Type*} {n : ℕ}
    (O : Oracle Q R n) (A : Algorithm Q R U n) (B : Fin n → ℕ)
    (seed : A.Seed) (ξ : (k : ℕ) → O.Seed k)
    (state : ℕ → A.State) (remaining : ℕ → Fin n → ℕ) (T : ℕ)
    (hstate : state 0 = A.initial seed) (hremaining : remaining 0 = B)
    (hstep : ∀ history, history.length < T → state (history.length + 1) =
      A.update (state history.length) (O.answer history (A.query (state history.length)) (ξ history.length)))
    (hconsume : ∀ k < T, remaining (k + 1) = Function.update (remaining k)
      (A.query (state k)).1 (remaining k (A.query (state k)).1 - 1))
    (hsafe : ∀ k < T, 0 < remaining k (A.query (state k)).1)
    (hT : (∑ i, B i) = T) : execute O A B seed ξ = A.output (state T) := by
  have hrun : ∀ fuel history, history.length + fuel = T →
      (_run (fun history query => O.answer history query (ξ history.length)) A fuel
        history (remaining history.length) (state history.length)).1 = A.output (state T) := by
    intro fuel
    induction fuel with
    | zero => intro history hh; simpa [_run] using congrArg (fun k => A.output (state k)) hh
    | succ fuel ih =>
      intro history hh
      have hk : history.length < T := by omega
      change (if remaining history.length (A.query (state history.length)).1 = 0 then
        (A.output (state history.length), history) else _).1 = _
      rw [ite_eq_right (Nat.ne_of_gt (hsafe _ hk))]
      dsimp only
      rw [← hstep history hk, ← hconsume history.length hk]
      simpa only [List.length_append, List.length_singleton] using
        ih (history ++ [(A.query (state history.length),
          O.answer history (A.query (state history.length)) (ξ history.length))]) (by simp; omega)
  unfold execute executeWithTrace
  rw [hT, ← hstate, ← hremaining]
  exact hrun T [] (by simp)

lemma even_iid {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {p : Measure Ω} {P : Measure Ξ} {ξ : ℕ → Ξ → Ω}
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) :
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k ω => ξ (2 * k) ω) p P := by
  exact ⟨fun k => h.measurable (2 * k), h.independent.precomp (by
    intro i j hh
    omega), fun k => h.marginal (2 * k)⟩

lemma even_stream_law {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {p : Measure Ω} {P : Measure Ξ} {ξ : ℕ → Ξ → Ω}
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ p P) :
    MeasurePreserving (fun ω k => ξ (2 * k) ω) P (Measure.infinitePi fun _ : ℕ => p) :=
  (even_iid h).stream_law

open LongTails.Setups.UscgHighProbability (Public State method)
open LongTails.Setups.UscgConstant (Space)
open OracleTemplate.NormBallLMO (path path_succ)

noncomputable def machine {Ω : Type} (p : Public) (α : ℕ → ℝ) (γ : ℝ)
    (g : Space p.d → Ω → Space p.d) (lmo : Space p.d → Space p.d) (ξ : ℕ → Ω) :
    ℕ → State p.d
  | 0 => (method p α (fun _ => γ)).initial ()
  | k + 1 =>
      let s := machine p α γ g lmo ξ k
      (method p α (fun _ => γ)).update s
        (if s.waitingForLmo then lmo s.momentum else g s.point (ξ k))

noncomputable def storedTrajectory {Ω : Type} (p : Public) (α : ℕ → ℝ) (γ : ℝ)
    (g : Space p.d → Ω → Space p.d) (lmo : Space p.d → Space p.d) (ξ : ℕ → Ω)
    (n : ℕ) : ℕ → Space p.d := fun k => if k < n then
      (path (fun x m => x + γ • lmo m) α p.x₁ g (fun i => ξ (2 * i)) k).1 else p.x₁

lemma storedTrajectory_succ {Ω : Type} (p : Public) (α : ℕ → ℝ) (γ : ℝ)
    (g : Space p.d → Ω → Space p.d) (lmo : Space p.d → Space p.d) (ξ : ℕ → Ω)
    (n : ℕ) : storedTrajectory p α γ g lmo ξ (n + 1) =
      Function.update (storedTrajectory p α γ g lmo ξ n) n
        (path (fun x m => x + γ • lmo m) α p.x₁ g (fun i => ξ (2 * i)) n).1 := by
  funext k
  by_cases hkn : k = n
  · subst k
    simp [storedTrajectory]
  · by_cases hk : k < n
    · simp [storedTrajectory, hkn, hk, show k < n + 1 by omega]
    · simp [storedTrajectory, hkn, hk, show ¬k < n + 1 by omega]

lemma machine_even {Ω : Type} (p : Public) (α : ℕ → ℝ) (γ : ℝ)
    (g : Space p.d → Ω → Space p.d) (lmo : Space p.d → Space p.d) (ξ : ℕ → Ω)
    (n : ℕ) : machine p α γ g lmo ξ (2 * n) =
      ⟨n, (path (fun x m => x + γ • lmo m) α p.x₁ g (fun i => ξ (2 * i)) n).1,
        (path (fun x m => x + γ • lmo m) α p.x₁ g (fun i => ξ (2 * i)) n).2,
        false, storedTrajectory p α γ g lmo ξ n⟩ := by
  induction n with
  | zero =>
    simp only [machine, method, path, State.mk.injEq, true_and]
    funext k
    simp [storedTrajectory]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, machine, machine, ih]
    simp only [method, Bool.false_eq_true, ↓reduceIte]
    rw [storedTrajectory_succ, path_succ]

lemma machine_query_even {Ω : Type} (p : Public) (α : ℕ → ℝ) (γ : ℝ)
    (g : Space p.d → Ω → Space p.d) (lmo : Space p.d → Space p.d) (ξ : ℕ → Ω)
    (n : ℕ) : ((method p α (fun _ => γ)).query (machine p α γ g lmo ξ (2 * n))).1 = 0 := by
  simp [machine_even, method]

lemma machine_query_odd {Ω : Type} (p : Public) (α : ℕ → ℝ) (γ : ℝ)
    (g : Space p.d → Ω → Space p.d) (lmo : Space p.d → Space p.d) (ξ : ℕ → Ω)
    (n : ℕ) : ((method p α (fun _ => γ)).query (machine p α γ g lmo ξ (2 * n + 1))).1 = 1 := by
  simp [machine, machine_even, method]

lemma machine_query {Ω : Type} (p : Public) (α : ℕ → ℝ) (γ : ℝ)
    (g : Space p.d → Ω → Space p.d) (lmo : Space p.d → Space p.d) (ξ : ℕ → Ω)
    (k : ℕ) : ((method p α (fun _ => γ)).query (machine p α γ g lmo ξ k)).1 =
      if k % 2 = 0 then 0 else 1 := by
  split_ifs with hk
  · have he : k = 2 * (k / 2) := by omega
    conv_lhs => rw [he]
    exact machine_query_even p α γ g lmo ξ _
  · have he : k = 2 * (k / 2) + 1 := by omega
    conv_lhs => rw [he]
    exact machine_query_odd p α γ g lmo ξ _

def remainingCalls (T k : ℕ) (i : Fin 2) : ℕ :=
  if i = 0 then T - (k + 1) / 2 else T - k / 2

lemma remainingCalls_step (T k : ℕ) :
    remainingCalls T (k + 1) = Function.update (remainingCalls T k)
      (if k % 2 = 0 then 0 else 1) (remainingCalls T k (if k % 2 = 0 then 0 else 1) - 1) := by
  funext i
  fin_cases i <;> by_cases hk : k % 2 = 0 <;> simp [remainingCalls, hk] <;> omega

lemma remainingCalls_safe (T k : ℕ) (hk : k < 2 * T) :
    0 < remainingCalls T k (if k % 2 = 0 then 0 else 1) := by
  by_cases hh : k % 2 = 0 <;> simp [remainingCalls, hh] <;> omega

noncomputable def canonicalOracle {Ω : Type} [MeasurableSpace Ω] (p : Public)
    (g : Space p.d → Ω → Space p.d) (lmo : Space p.d → Space p.d)
    (P : ProbabilityMeasure (ℕ → Ω)) : Oracle (Space p.d) (Space p.d) 2 where
  Seed := fun _ => Ω
  law := P
  answer := fun _ (i, x) ω => if i = 0 then g x ω else lmo x

lemma execute_machine {Ω : Type} [MeasurableSpace Ω] (p : Public) (α : ℕ → ℝ) (γ : ℝ)
    (g : Space p.d → Ω → Space p.d) (lmo : Space p.d → Space p.d)
    (P : ProbabilityMeasure (ℕ → Ω)) (T : ℕ) (ξ : ℕ → Ω) :
    execute (canonicalOracle p g lmo P) (method p α (fun _ => γ)) (fun _ => T) () ξ =
      (T, storedTrajectory p α γ g lmo ξ T) := by
  let A := method p α (fun _ => γ)
  let O := canonicalOracle p g lmo P
  have hstep : ∀ history, history.length < 2 * T → machine p α γ g lmo ξ (history.length + 1) =
      A.update (machine p α γ g lmo ξ history.length)
        (O.answer history (A.query (machine p α γ g lmo ξ history.length)) (ξ history.length)) := by
    intro history _
    rw [machine]
    cases hh : (machine p α γ g lmo ξ history.length).waitingForLmo <;>
      simp [A, O, method, canonicalOracle, hh]
  have hr : remainingCalls T 0 = fun _ => T := by
    funext i
    simp [remainingCalls]
  have hc : ∀ k < 2 * T, remainingCalls T (k + 1) = Function.update (remainingCalls T k)
      (A.query (machine p α γ g lmo ξ k)).1
      (remainingCalls T k (A.query (machine p α γ g lmo ξ k)).1 - 1) := by
    intro k _
    rw [machine_query]
    exact remainingCalls_step T k
  have hs : ∀ k < 2 * T, 0 < remainingCalls T k (A.query (machine p α γ g lmo ξ k)).1 := by
    intro k hk
    rw [machine_query]
    exact remainingCalls_safe T k hk
  have he := execute_exact_prefix O A (fun _ => T) () ξ (machine p α γ g lmo ξ)
    (remainingCalls T) (2 * T) rfl hr hstep hc hs (by simp)
  rw [he, machine_even]
  rfl

end LongTails.Proofs.UscgSharpExecution
