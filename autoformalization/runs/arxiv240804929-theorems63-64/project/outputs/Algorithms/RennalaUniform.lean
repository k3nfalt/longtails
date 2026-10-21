import outputs.Algorithms.RennalaSgd
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Basic.ENNReal.Real

open MeasureTheory

namespace OracleTemplate.RennalaUniform

open Rennala

noncomputable def work (v : ℝ → ℝ) (t : ℝ) : ℝ := ∫ τ in (0 : ℝ)..t, v τ

noncomputable def completion (V : ℝ → ℝ) (s : ℝ) : Option ℝ :=
  open Classical in
  if ∃ t, s ≤ t ∧ V s + 1 ≤ V t then some (sInf {t | s ≤ t ∧ V s + 1 ≤ V t}) else none

noncomputable def earliestStep {n : ℕ} (c : Fin n → Option ℝ) (i : Fin n)
    (r : Option (Fin n × ℝ)) : Option (Fin n × ℝ) :=
  Option.elim (c i) r (fun a =>
    Option.elim r (some (i, a)) (fun b => if a ≤ b.2 then some (i, a) else some b))

noncomputable def earliest {n : ℕ} (c : Fin n → Option ℝ) (l : List (Fin n)) : Option (Fin n × ℝ) :=
  l.foldr (earliestStep c) none

noncomputable def roundTime {n : ℕ} (V : Fin n → ℝ → ℝ) (S : ℕ) (s : ℝ) : ENNReal :=
  open Classical in
  if ∃ t, 0 ≤ t ∧ (S : ℝ) ≤ ∑ i, (⌊V i t - V i s⌋ : ℝ) then
    ENNReal.ofReal (sInf {t | 0 ≤ t ∧ (S : ℝ) ≤ ∑ i, (⌊V i t - V i s⌋ : ℝ)})
  else ⊤

noncomputable def deadline {n : ℕ} (V : Fin n → ℝ → ℝ) (S : ℕ) : ℕ → ENNReal
  | 0 => 0
  | k + 1 => if deadline V S k = ⊤ then ⊤ else roundTime V S (deadline V S k).toReal

structure Public where
  d : ℕ
  n : ℕ
  gamma : ℝ
  S : ℕ
  x0 : Point d
  K : ℕ

abbrev Query (p : Public) := Option (Point p.d × (Fin p.n → ℝ))

abbrev Reply (p : Public) := Option (Fin p.n × ℝ × Point p.d)

noncomputable def eventAnswer (p : Public) (V : Fin p.n → ℝ → ℝ) {Ω : Type}
    (g : Point p.d → Ω → Point p.d) (query : Query p) (seed : Ω) : Reply p :=
  Option.elim query none (fun q =>
    Option.elim (earliest (fun i => completion (V i) (q.2 i)) (List.finRange p.n)) none
      (fun e => some (e.1, e.2, g q.1 seed)))

noncomputable def eventOracle (p : Public) (V : Fin p.n → ℝ → ℝ) {Ω : Type}
    [MeasurableSpace Ω] (P : ProbabilityMeasure (ℕ → Ω))
    (g : Point p.d → Ω → Point p.d) : Oracle (Query p) (Reply p) where
  Seed := fun _ => Ω
  law := P
  answer := fun _ (_, query) seed => eventAnswer p V g query seed

structure State (p : Public) where
  round : ℕ
  count : ℕ
  acc : Point p.d
  point : Point p.d
  starts : Fin p.n → ℝ
  clock : ℝ
  chosen : ℕ
  selected : Point p.d

noncomputable def step (p : Public) (s : State p) (reply : Reply p) : State p :=
  match reply with
  | none => s
  | some (i, t, g) =>
      let acc := s.acc + (1 / (p.S : ℝ)) • g
      if s.count + 1 = p.S then
        let x := s.point - p.gamma • acc
        ⟨s.round + 1, 0, 0, x, fun _ => t, t, s.chosen,
          if s.chosen = s.round + 1 then x else s.selected⟩
      else
        ⟨s.round, s.count + 1, acc, s.point, Function.update s.starts i t, t, s.chosen, s.selected⟩

noncomputable def rennala (p : Public) : Algorithm (Query p) (Reply p) (Point p.d × ℝ) where
  Seed := Fin (p.K + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (p.K + 1))).toMeasure, inferInstance⟩
  State := State p
  initial j := ⟨0, 0, 0, p.x0, fun _ => 0, 0, j.val, p.x0⟩
  query s := (0, if p.K ≤ s.round then none else some (s.point, s.starts))
  update s reply := if p.K ≤ s.round then s else step p s reply
  output s := (s.selected, s.clock)

end OracleTemplate.RennalaUniform
