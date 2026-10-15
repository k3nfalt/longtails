import LongTails.Algorithms.TerminalClipping
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.GapStrongGrowthIteration

set_option backward.isDefEq.respectTransparency false

open MeasureTheory

namespace OracleTemplate.TerminalClipping

open LongTails.Setups.TerminalClippingConvex

lemma algorithm_allowed (q : Public) : spec.allowedAlgorithm q (algorithm q) := by
  refine ⟨(fun s => stepSize q.B q.δ q.T s.t),
    (fun s => threshold q.B q.G q.T (s.x - q.x0)
      (influenceScale q.B q.δ q.T s.t • (s.x - q.x0 - s.auxiliary))), ?_, ?_⟩
  · intro seed
    exact ⟨rfl, rfl⟩
  · intro s
    cases h : s.pending <;> simp [algorithm, h, nextPoint]
    intro g
    abel

lemma even_samples_iid {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {ξ : ℕ → Ξ → Ω} {ν : Measure Ω} {P : Measure Ξ}
    (h : LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID ξ ν P) :
    LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID (fun k => ξ (2 * k)) ν P where
  measurable k := h.measurable (2 * k)
  independent := h.independent.precomp (g := fun k : ℕ => 2 * k) (by
    intro a b hab
    dsimp only at hab
    omega)
  marginal k := h.marginal (2 * k)

noncomputable def sampleOracle {Ω : Type} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (P : ProbabilityMeasure (ℕ → Ω)) : Oracle (Query q) (Vector q.d) where
  Seed := fun _ => Ω
  law := P
  answer := fun _ (_, query) seed => match query with
    | .subgradient x => g x seed
    | .projection x => projection x

lemma advance_run {Ω : Type} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (P : ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω) (n call t : ℕ)
    (x p proposal : Vector q.d) :
    (algorithm q).output (StochasticGradient.advance
      (fun k state => (algorithm q).update state
        ((sampleOracle q g projection P).answer k ((algorithm q).query state) (ξ k)))
      (2 * n) call ⟨t, x, p, false, proposal⟩) =
      run q g projection n t x p (fun k => ξ (call + k)) := by
  induction n generalizing call t x p proposal with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    rw [StochasticGradient.advance, StochasticGradient.advance]
    simp only [algorithm, sampleOracle, Bool.false_eq_true, ↓reduceIte]
    simp only [algorithm, sampleOracle] at ih
    rw [ih]
    simp only [run, Nat.add_zero]
    congr 1
    funext k
    congr 1
    omega

lemma execute_terminal {Ω : Type} [MeasurableSpace Ω] (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (P : ProbabilityMeasure (ℕ → Ω)) (ξ : ℕ → Ω) :
    execute (sampleOracle q g projection P) (algorithm q) (fun _ => (2 * q.T)) () ξ =
      terminal q g projection ξ := by
  rw [StochasticGradient.execute_advance]
  have h := advance_run q g projection P ξ q.T 0 0 q.x0 0 q.x0
  simpa only [algorithm, terminal, Nat.zero_add] using
    h

lemma run_eq_iterateSamples {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (n t : ℕ) (x p : Vector q.d) (ξ : ℕ → Ω) :
    run q g projection n t x p ξ =
      (ContinuizedSimilarQuasar.iterateSamples (transition q g projection) n (t, x, p)
        (fun i => ξ (2 * i.val))).2.1 := by
  induction n generalizing t x p ξ with
  | zero => rfl
  | succ n ih =>
    rw [run, ContinuizedSimilarQuasar.iterateSamples]
    dsimp only [transition, Fin.val_zero, mul_zero]
    rw [ih]
    congr 2

lemma iterate_eq_trajectory {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (ξ : ℕ → Ω) (n : ℕ) :
    ContinuizedSimilarQuasar.iterateSamples (transition q g projection) n (0, q.x0, 0)
      (fun i => ξ i.val) = trajectory q g projection ξ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [GapStrongGrowth.iterateSamples_succ_last]
    change transition q g projection
      (ContinuizedSimilarQuasar.iterateSamples (transition q g projection) n (0, q.x0, 0)
        (fun i => ξ i.val)) (ξ n) = _
    rw [ih]
    rfl

lemma terminal_eq_trajectory {Ω : Type*} (q : Public)
    (g : Vector q.d → Ω → Vector q.d) (projection : Vector q.d → Vector q.d)
    (ξ : ℕ → Ω) :
    terminal q g projection ξ = (trajectory q g projection (fun k => ξ (2 * k)) q.T).2.1 := by
  unfold terminal
  rw [run_eq_iterateSamples]
  rw [iterate_eq_trajectory q g projection (fun k => ξ (2 * k)) q.T]

end OracleTemplate.TerminalClipping
