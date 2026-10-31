import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped RealInnerProductSpace

namespace OracleTemplate.CoarseGeneralized

structure Tuning where
  L : ℝ
  L1 : ℝ
  ζ : ℝ
  rounds : ℕ
  depth : ℕ

structure Iterate (E : Type*) where
  x : E
  v : E
  A : ℝ
  index : ℕ

inductive Search (E : Type*) where
  | left (s : Iterate E)
  | right (s : Iterate E)
  | bracket (s : Iterate E) (lo hi : ℝ) (upperReply : E) (remaining : ℕ)
  | done (x : E)

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def decrement (t : Tuning) (h : E) : ℝ := ‖h‖ ^ 2 / (t.L + t.L1 * ‖h‖)

def surplus (t : Tuning) (h : E) : ℝ :=
  ‖h‖ * Real.log (t.L1 * ‖h‖ / (2 * t.L)) / (64 * t.L1)

def weight (t : Tuning) (A : ℝ) (h : E) : ℝ :=
  let c := decrement t h / 128 + surplus t h / 2
  (c + Real.sqrt (c ^ 2 + A * decrement t h * ‖h‖ ^ 2 / 32)) / (2 * ‖h‖ ^ 2)

def advance (t : Tuning) (s : Iterate E) (y h : E) : Iterate E :=
  let a := weight t s.A h
  { x := y - (1 / (16 * (t.L + t.L1 * ‖h‖))) • h
    v := s.v - a • h
    A := s.A + a
    index := s.index + 1 }

def resume (t : Tuning) (s : Iterate E) : Search E :=
  if t.rounds ≤ s.index then .done s.x else .left s

def finish (t : Tuning) (s : Iterate E) (y h : E) : Search E := resume t (advance t s y h)

def searchPoint : Search E → E
  | .left s => s.v
  | .right s => s.x
  | .bracket s lo hi _ _ => s.v + ((lo + hi) / 2) • (s.x - s.v)
  | .done x => x

open Classical in
def assess (t : Tuning) (s : Iterate E) (y h : E) (next : Search E) : Search E :=
  if ‖h‖ ≤ 4096 * t.L / t.L1 then .done y
  else if |⟪h, s.x - s.v⟫| ≤ t.ζ * ‖s.x - s.v‖ then finish t s y h
  else next

open Classical in
def searchUpdate (t : Tuning) : Search E → E → Search E
  | .done x, _ => .done x
  | .left s, h => assess t s s.v h
      (if 0 ≤ ⟪h, s.x - s.v⟫ then finish t s s.v h else .right s)
  | .right s, h => assess t s s.x h
      (if ⟪h, s.x - s.v⟫ ≤ 0 then finish t s s.x h
       else if t.depth = 0 then finish t s s.x h else .bracket s 0 1 h t.depth)
  | .bracket s lo hi upper r, h =>
      let mid := (lo + hi) / 2
      let y := s.v + mid • (s.x - s.v)
      assess t s y h
        (if ⟪h, s.x - s.v⟫ < 0 then
          if r ≤ 1 then finish t s (s.v + hi • (s.x - s.v)) upper
          else .bracket s mid hi upper (r - 1)
         else if r ≤ 1 then finish t s y h
         else .bracket s lo mid h (r - 1))

def warmOutput : Search E → E
  | .left s => s.x
  | .right s => s.x
  | .bracket s _ _ _ _ => s.x
  | .done x => x

def warmAlgorithm (t : Tuning) (x0 : E) : Algorithm E E E where
  State := Search E
  initial _ := resume t ⟨x0, x0, 0, 0⟩
  query s := (0, searchPoint s)
  update := searchUpdate t
  output := warmOutput

end

end OracleTemplate.CoarseGeneralized
