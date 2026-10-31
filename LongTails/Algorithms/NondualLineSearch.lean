import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section

open scoped RealInnerProductSpace

namespace LongTails.Algorithms.NondualLineSearch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Reply (E : Type*) := ℝ × E

inductive State (E : Type*) where
  | first
  | second (left : Reply E)
  | bracket (a b : ℝ) (left right : Reply E)
  | done (point : E) (reply : Reply E) (small : Bool)

def point (z y : E) (t : ℝ) : E := z + t • (y - z)

def query (z y : E) : State E → E
  | .first => z
  | .second _ => y
  | .bracket a b _ _ => point z y ((a + b) / 2)
  | .done p _ _ => p

def update (r δ : ℝ) (z y : E) (s : State E) (reply : Reply E) : State E :=
  match s with
  | .first => .second reply
  | .second left =>
    if r * ‖left.2‖ ≤ δ then .done z left true
    else if r * ‖reply.2‖ ≤ δ then .done y reply true
    else if 0 ≤ ⟪left.2, y - z⟫ then .done z left false
    else if ⟪reply.2, y - z⟫ ≤ 0 then .done y reply false
    else .bracket 0 1 left reply
  | .bracket a b left right =>
    let t := (a + b) / 2
    if r * ‖reply.2‖ ≤ δ then .done (point z y t) reply true
    else if ⟪reply.2, y - z⟫ = 0 then .done (point z y t) reply false
    else if ⟪reply.2, y - z⟫ < 0 then .bracket t b reply right
    else .bracket a t left reply
  | .done _ _ _ => s

def output (z y : E) : State E → E × Reply E × Bool
  | .first => (z, (0, 0), false)
  | .second left => (z, left, false)
  | .bracket _ b _ right => (point z y b, right, false)
  | .done p reply small => (p, reply, small)

def algorithm (r δ : ℝ) (z y : E) : OracleTemplate.Algorithm E (Reply E) (E × Reply E × Bool) where
  State := State E
  initial _ := .first
  query s := (0, query z y s)
  update := update r δ z y
  output := output z y

end LongTails.Algorithms.NondualLineSearch
