import LongTails.Template
import LongTails.Proofs.Execution
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory

namespace LongTails.Proofs.EscapeChainRun

open OracleTemplate

variable {Q R O : Type*}

def run (A : Algorithm Q R O) (ans : Q → ℝ → R) (seed : A.Seed) (ω : ℕ → ℝ) : ℕ → A.State
  | 0 => A.initial seed
  | t + 1 => A.update (run A ans seed ω t) (ans (A.query (run A ans seed ω t)).2 (ω t))

lemma run_prefix (A : Algorithm Q R O) (ans : Q → ℝ → R) (seed : A.Seed) {ω ω' : ℕ → ℝ} (t : ℕ)
    (h : ∀ s < t, ω s = ω' s) : run A ans seed ω t = run A ans seed ω' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [run]
    rw [ih (fun s hs => h s (by omega)), h t (by omega)]

lemma run_couple (A : Algorithm Q R O) (ans ans' : Q → ℝ → R) (seed : A.Seed) (ω : ℕ → ℝ) (T : ℕ)
    (h : ∀ t < T, ans (A.query (run A ans' seed ω t)).2 (ω t) =
      ans' (A.query (run A ans' seed ω t)).2 (ω t)) :
    ∀ t ≤ T, run A ans seed ω t = run A ans' seed ω t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [run]
    rw [ih (by omega), h t (by omega)]

lemma execute_run (A : Algorithm Q R O) (g : Q → ℝ → R) (P : ProbabilityMeasure (ℕ → ℝ)) (N : ℕ)
    (seed : A.Seed) (ω : ℕ → ℝ) :
    execute ({ Seed := fun _ => ℝ, law := P, answer := fun _ (_, x) s => g x s } : Oracle Q R) A
      (fun _ => N) seed ω = A.output (run A g seed ω N) := by
  have h := execute_indexed_of_answer
    ({ Seed := fun _ => ℝ, law := P, answer := fun _ (_, x) s => g x s } : Oracle Q R) A N seed ω
    (fun t query => g query.2 (ω t)) (fun _ query => by cases query; rfl)
  refine h.trans ?_
  have : ∀ M, ((fun sc : A.State × ℕ => (A.update sc.1 (g (A.query sc.1).2 (ω sc.2)), sc.2 + 1))^[M]
      (A.initial seed, 0)) = (run A g seed ω M, M) := by
    intro M
    induction M with
    | zero => rfl
    | succ M ih => rw [Function.iterate_succ_apply', ih]; rfl
  rw [this]

lemma run_measurable [MeasurableSpace Q] [MeasurableSpace R] (A : Algorithm Q R O)
    [MeasurableSpace A.State] (hinit : Measurable A.initial) (hq : Measurable A.query)
    (hu : Measurable A.update.uncurry) (g : Q → ℝ → R) (hg : Measurable (Function.uncurry g))
    (t : ℕ) : Measurable (fun z : A.Seed × (ℕ → ℝ) => run A g z.1 z.2 t) := by
  induction t with
  | zero => exact hinit.comp measurable_fst
  | succ t ih =>
    have hquery : Measurable (fun z : A.Seed × (ℕ → ℝ) => (A.query (run A g z.1 z.2 t)).2) :=
      measurable_snd.comp (hq.comp ih)
    have hans : Measurable (fun z : A.Seed × (ℕ → ℝ) => g (A.query (run A g z.1 z.2 t)).2 (z.2 t)) :=
      hg.comp (hquery.prodMk ((measurable_pi_apply t).comp measurable_snd))
    exact hu.comp (ih.prodMk hans)

end LongTails.Proofs.EscapeChainRun
