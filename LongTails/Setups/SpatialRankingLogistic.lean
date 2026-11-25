import LongTails.Setups.TwoSampleQuadraticPerceptron
import Mathlib.Analysis.SpecialFunctions.Sigmoid

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.SpatialRankingLogistic

open TwoSampleQuadraticPerceptron

structure Params where
  n : ℕ
  d : ℕ

structure Population where
  scale : ℝ
  anchorLag : ℝ
  itemLag : ℝ
  slope : ℝ
  left : ℝ
  right : ℝ

def first : Population := ⟨1, -0.5, 0.75, -0.0625, 0.125, 0.0625⟩

def second : Population := ⟨0.5, 0.5, 0.25, 0.0625, 0.0625, 0.125⟩

def population : Bool → Population
  | false => first
  | true => second

abbrev Items (p : Params) := Bool → Fin (p.n+1) → Features p.d
abbrev Point (p : Params) := Space .conv p.d
abbrev Query (p : Params) := (Bool × ℕ) × Point p

noncomputable def traceValue (n : ℕ) (g : Bool) (i : ℕ) : ℝ :=
  let h := population g
  (h.left + h.slope * (i-1 : ℕ) / (n-2 : ℕ)) / Real.sqrt n

noncomputable def lagEntry (n : ℕ) (g : Bool) (i j : ℕ) : ℝ :=
  if i = j then
    if i = 0 ∨ i = n then (population g).anchorLag else (population g).itemLag
  else if j = 0 ∧ i < n then traceValue n g i
  else if i = n ∧ 0 < j then -traceValue n g j
  else 0

def Geometry (p : Params) (U : Items p) : Prop :=
  (∀ g h i j, ⟪U g i, U h j⟫ = if g = h ∧ i = j then 1 else 0) ∧
  ∀ g h i j, ⟪U g i, shift (U h j)⟫ = if g = h then lagEntry p.n g i j else 0

noncomputable def signedRow (p : Params) (U : Items p) (g : Bool) (i : ℕ) : Features p.d :=
  if hi : i < p.n then
    (population g).scale • (U g ⟨i, by omega⟩ - U g ⟨i+1, by omega⟩)
  else 0

noncomputable def answer (p : Params) (U : Items p) (q : Query p) : Point p :=
  let row := signedRow p U q.1.1 q.1.2
  Real.sigmoid (-(margin .conv p.d row q.2)) • direction .conv p.d row q.2

def Separates (p : Params) (U : Items p) (θ : Point p) : Prop :=
  ∀ g i, i < p.n → 0 < margin .conv p.d (signedRow p U g i) θ

inductive Training where
  | joint | frozen
  deriving DecidableEq

structure Scan (p : Params) where
  point : Point p
  cursor : ℕ
  sum : Point p

def scanQuery (p : Params) (s : Scan p) : Query p :=
  ((decide (p.n ≤ s.cursor), s.cursor % p.n), s.point)

noncomputable def scanUpdate (p : Params) (m : Training) (η : ℝ)
    (s : Scan p) (r : Point p) : Scan p :=
  let total := s.sum + r
  if s.cursor + 1 = 2*p.n then
    let grad := ((2*p.n : ℕ) : ℝ)⁻¹ • total
    let step := match m with
      | .joint => grad
      | .frozen => ((0,0),grad.2)
    ⟨s.point + η • step, 0, 0⟩
  else ⟨s.point, s.cursor+1, total⟩

def family (p : Params) (m : Training) (A : Algorithm (Query p) (Point p) (Point p)) : Prop :=
  ∃ (view : A.State → Scan p) (initialTaps : A.Seed → ℝ × ℝ)
    (rate : A.State → Point p → ℝ),
    (∀ s r, 0 < rate s r) ∧
    (m = .joint → (∀ ω, initialTaps ω = (1,0)) ∧ ∃ η, ∀ s r, rate s r = η) ∧
    (∀ ω, view (A.initial ω) = ⟨(initialTaps ω, 0), 0, 0⟩) ∧
    (∀ s, A.query s = (0, scanQuery p (view s))) ∧
    (∀ s r, view (A.update s r) = scanUpdate p m (rate s r) (view s) r) ∧
    ∀ s, A.output s = (view s).point

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  publicInput := id
  Instance := Items
  Query := Query
  Reply := Point
  Output := Point
  valid p := 8 ≤ p.n
  admissible p U O := Geometry p U ∧ ∀ hist q ω, O.answer hist q ω = answer p U q.2
  successful p U output _ := ∀ ω, Separates p U (output ω)
  allowedAlgorithm p := family p .joint

end LongTails.Setups.SpatialRankingLogistic
