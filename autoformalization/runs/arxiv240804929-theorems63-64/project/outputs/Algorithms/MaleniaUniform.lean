import outputs.Algorithms.RennalaUniform
import outputs.Algorithms.BatchIterations
import Mathlib.Probability.ProductMeasure

open MeasureTheory

namespace OracleTemplate.MaleniaUniform

open Rennala

def code (n : ℕ) (i : Fin n) (j : ℕ) : ℕ := j * n + i.val

noncomputable def estimator {d n : ℕ} {Ω : Type} (B : Fin n → ℕ)
    (g : Fin n → Point d → Ω → Point d) (x : Point d) (ω : ℕ → Ω) : Point d :=
  (1 / (n : ℝ)) • ∑ i, (1 / (B i : ℝ)) • ∑ j ∈ Finset.range (B i), g i x (ω (code n i j))

def harmonicReady (n S : ℕ) (B : Fin n → ℕ) : Prop :=
  (∀ i, 1 ≤ B i) ∧ (S : ℝ) / n ≤ ((1 / (n : ℝ)) * ∑ i, 1 / (B i : ℝ))⁻¹

noncomputable def sgdIterate {d : ℕ} {Ω : Type} (G : ℕ → Point d → Ω → Point d)
    (gamma : ℝ) (x0 : Point d) (seeds : ℕ → Ω) : ℕ → Point d
  | 0 => x0
  | r + 1 =>
      let x := sgdIterate G gamma x0 seeds r
      x - gamma • G r x (seeds r)

noncomputable def iterate {d n : ℕ} {Ω : Type} (g : Fin n → Point d → Ω → Point d)
    (gamma : ℝ) (B : ℕ → Fin n → ℕ) (x0 : Point d) (seeds : ℕ → ℕ → Ω) : ℕ → Point d :=
  sgdIterate (fun r => estimator (B r) g) gamma x0 seeds

def arrays {Ω : Type} (ξ : ℕ → Ω) : ℕ → ℕ → Ω := fun r c => ξ (Nat.pair r c)

noncomputable def iterOracle (p : BatchIterations.Public) (n : ℕ) (B : ℕ → Fin n → ℕ)
    {Ω : Type} [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (g : Fin n → Point p.d → Ω → Point p.d) : Oracle (Point p.d) (Point p.d) where
  Seed := fun _ => ℕ → Ω
  law := ⟨Measure.map arrays (P : Measure (ℕ → Ω)), inferInstance⟩
  answer := fun r (_, x) seed => estimator (B r) g x seed

noncomputable def roundTime {n : ℕ} (V : Fin n → ℝ → ℝ) (eta : ℝ) (s : ℝ) : ENNReal :=
  open Classical in
  if ∃ t, 0 ≤ t ∧ (∀ i, (1 : ℤ) ≤ ⌊V i t - V i s⌋) ∧
      eta ≤ ((1 / (n : ℝ)) * ∑ i, 1 / (⌊V i t - V i s⌋ : ℝ))⁻¹ then
    ENNReal.ofReal (sInf {t | 0 ≤ t ∧ (∀ i, (1 : ℤ) ≤ ⌊V i t - V i s⌋) ∧
      eta ≤ ((1 / (n : ℝ)) * ∑ i, 1 / (⌊V i t - V i s⌋ : ℝ))⁻¹})
  else ⊤

noncomputable def deadline {n : ℕ} (V : Fin n → ℝ → ℝ) (eta : ℝ) : ℕ → ENNReal
  | 0 => 0
  | k + 1 => if deadline V eta k = ⊤ then ⊤ else roundTime V eta (deadline V eta k).toReal

structure Public where
  d : ℕ
  n : ℕ
  gamma : ℝ
  S : ℕ
  x0 : Point d
  K : ℕ

abbrev Query (p : Public) := Option (Point p.d × (Fin p.n → ℝ) × ℕ × (Fin p.n → ℕ))

abbrev Reply (p : Public) := Option (Fin p.n × ℝ × Point p.d)

noncomputable def eventAnswer (p : Public) (V : Fin p.n → ℝ → ℝ) {Ω : Type}
    (g : Fin p.n → Point p.d → Ω → Point p.d) (query : Query p) (seed : ℕ → ℕ → Ω) : Reply p :=
  Option.elim query none (fun q =>
    Option.elim (RennalaUniform.earliest (fun i => RennalaUniform.completion (V i) (q.2.1 i))
        (List.finRange p.n)) none
      (fun e => some (e.1, e.2, g e.1 q.1 (seed q.2.2.1 (code p.n e.1 (q.2.2.2 e.1))))))

noncomputable def eventOracle (p : Public) (V : Fin p.n → ℝ → ℝ) {Ω : Type}
    [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (g : Fin p.n → Point p.d → Ω → Point p.d) : Oracle (Query p) (Reply p) where
  Seed := fun _ => ℕ → ℕ → Ω
  law := ⟨Measure.map (fun ξ (_ : ℕ) => arrays ξ) (P : Measure (ℕ → Ω)), inferInstance⟩
  answer := fun _ (_, query) seed => eventAnswer p V g query seed

structure State (p : Public) where
  round : ℕ
  counts : Fin p.n → ℕ
  sums : Fin p.n → Point p.d
  point : Point p.d
  starts : Fin p.n → ℝ
  clock : ℝ
  chosen : ℕ
  selected : Point p.d

noncomputable def step (p : Public) (s : State p) (reply : Reply p) : State p :=
  open Classical in
  match reply with
  | none => s
  | some (i, t, g) =>
      let B := Function.update s.counts i (s.counts i + 1)
      let G := Function.update s.sums i (s.sums i + g)
      if harmonicReady p.n p.S B then
        let x := s.point - p.gamma • ((1 / (p.n : ℝ)) • ∑ j, (1 / (B j : ℝ)) • G j)
        ⟨s.round + 1, fun _ => 0, fun _ => 0, x, fun _ => t, t, s.chosen,
          if s.chosen = s.round + 1 then x else s.selected⟩
      else
        ⟨s.round, B, G, s.point, Function.update s.starts i t, t, s.chosen, s.selected⟩

noncomputable def malenia (p : Public) : Algorithm (Query p) (Reply p) (Point p.d × ℝ) where
  Seed := Fin (p.K + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (p.K + 1))).toMeasure, inferInstance⟩
  State := State p
  initial j := ⟨0, fun _ => 0, fun _ => 0, p.x0, fun _ => 0, 0, j.val, p.x0⟩
  query s := (0, if p.K ≤ s.round then none else some (s.point, s.starts, s.round, s.counts))
  update s reply := if p.K ≤ s.round then s else step p s reply
  output s := (s.selected, s.clock)

end OracleTemplate.MaleniaUniform
