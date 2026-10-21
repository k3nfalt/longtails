import LongTails.Algorithms.RennalaUniform

open MeasureTheory

namespace OracleTemplate.RingmasterAsgd

open Rennala

structure Public where
  d : ℕ
  n : ℕ
  gamma : ℝ
  R : ℕ
  x0 : Point d
  K : ℕ

def EpsStationary {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (f : Point d → ℝ) (x : Ω → Point d)
    (P : Measure Ω) (eps : ℝ) : Prop :=
  Integrable (fun ω => ‖gradient f (x ω)‖ ^ 2) P ∧ (∫ ω, ‖gradient f (x ω)‖ ^ 2 ∂P) ≤ eps

abbrev Query (p : Public) := Option ((Fin p.n → Point p.d) × (Fin p.n → ℝ))

abbrev Reply (p : Public) := Option (Fin p.n × ℝ × Point p.d)

structure State (p : Public) where
  count : ℕ
  point : Point p.d
  points : Fin p.n → Point p.d
  starts : Fin p.n → ℝ
  iters : Fin p.n → ℕ
  clock : ℝ
  chosen : ℕ
  selected : Point p.d

noncomputable def step (p : Public) (s : State p) (reply : Reply p) : State p :=
  Option.elim reply s (fun r =>
    let x := s.point - p.gamma • r.2.2
    ⟨s.count + 1, x,
      fun j => if j = r.1 ∨ p.R ≤ s.count + 1 - s.iters j then x else s.points j,
      fun j => if j = r.1 ∨ p.R ≤ s.count + 1 - s.iters j then r.2.1 else s.starts j,
      fun j => if j = r.1 ∨ p.R ≤ s.count + 1 - s.iters j then s.count + 1 else s.iters j,
      r.2.1, s.chosen, if s.chosen = s.count + 1 then x else s.selected⟩)

noncomputable def ringmaster (p : Public) : Algorithm (Query p) (Reply p) (Point p.d × ℝ) where
  Seed := Fin (p.K + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (p.K + 1))).toMeasure, inferInstance⟩
  State := State p
  initial j := ⟨0, p.x0, fun _ => p.x0, fun _ => 0, fun _ => 0, 0, j.val, p.x0⟩
  query s := (0, if p.K ≤ s.count then none else some (s.points, s.starts))
  update s reply := if p.K ≤ s.count then s else step p s reply
  output s := (s.selected, s.clock)

noncomputable def eventAnswer (p : Public) (V : Fin p.n → ℝ → ℝ) {Ω : Type}
    (g : Point p.d → Ω → Point p.d) (query : Query p) (seed : Ω) : Reply p :=
  Option.elim query none (fun q =>
    Option.elim (RennalaUniform.earliest (fun i => RennalaUniform.completion (V i) (q.2 i))
        (List.finRange p.n)) none
      (fun e => some (e.1, e.2, g (q.1 e.1) seed)))

noncomputable def eventOracle (p : Public) (V : Fin p.n → ℝ → ℝ) {Ω : Type}
    [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d) : Oracle (Query p) (Reply p) where
  Seed := fun _ => Ω
  law := P
  answer := fun _ q seed => eventAnswer p V g q.2 seed

noncomputable def arrivalOracle (p : Public) (arrive : ℕ → Fin p.n) {Ω : Type}
    [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d) : Oracle (Query p) (Reply p) where
  Seed := fun _ => Ω
  law := P
  answer := fun k q seed => Option.elim q.2 none (fun r => some (arrive k, 0, g (r.1 (arrive k)) seed))

noncomputable def history {d : ℕ} {Ω : Type} (g : Point d → Ω → Point d) (gamma : ℝ)
    (a : ℕ → ℕ) (x0 : Point d) (ξ : ℕ → Ω) : ℕ → ℕ → Point d
  | 0 => fun _ => x0
  | k + 1 => fun j =>
      if j ≤ k then history g gamma a x0 ξ k j
      else history g gamma a x0 ξ k k - gamma • g (history g gamma a x0 ξ k (a k)) (ξ k)

noncomputable def delayedIterate {d : ℕ} {Ω : Type} (g : Point d → Ω → Point d) (gamma : ℝ)
    (a : ℕ → ℕ) (x0 : Point d) (ξ : ℕ → Ω) (k : ℕ) : Point d :=
  history g gamma a x0 ξ k k

structure Timing (n : ℕ) where
  count : ℕ
  starts : Fin n → ℝ
  iters : Fin n → ℕ
  clock : ℝ

def timingStep {n : ℕ} (R : ℕ) (s : Timing n) (r : Fin n × ℝ) : Timing n :=
  ⟨s.count + 1,
    fun j => if j = r.1 ∨ R ≤ s.count + 1 - s.iters j then r.2 else s.starts j,
    fun j => if j = r.1 ∨ R ≤ s.count + 1 - s.iters j then s.count + 1 else s.iters j, r.2⟩

def timing {n : ℕ} (R : ℕ) (event : ℕ → (Fin n → ℝ) → Option (Fin n × ℝ)) : ℕ → Timing n
  | 0 => ⟨0, fun _ => 0, fun _ => 0, 0⟩
  | k + 1 => Option.elim (event k (timing R event k).starts) (timing R event k)
      (timingStep R (timing R event k))

def delays {n : ℕ} (R : ℕ) (event : ℕ → (Fin n → ℝ) → Option (Fin n × ℝ)) (k : ℕ) : ℕ :=
  Option.elim (event k (timing R event k).starts) k (fun r => (timing R event k).iters r.1)

noncomputable def completionEvent {n : ℕ} (V : Fin n → ℝ → ℝ) (_ : ℕ) (starts : Fin n → ℝ) :
    Option (Fin n × ℝ) :=
  RennalaUniform.earliest (fun i => RennalaUniform.completion (V i) (starts i)) (List.finRange n)

end OracleTemplate.RingmasterAsgd
