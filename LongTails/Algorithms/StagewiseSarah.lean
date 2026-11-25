import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace OracleTemplate.StagewiseSarah

structure Epoch where
  B : ℕ
  m : ℕ
  η : ℝ

structure Ctl where
  todo : List Epoch
  i : ℕ

def ctlNext (c : Ctl) : Ctl :=
  match c.todo with
  | [] => c
  | e :: rest => if c.i + 1 < e.B + e.m then ⟨e :: rest, c.i + 1⟩ else ⟨rest, 0⟩

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def pairQuery (c : Ctl) (z : E × E) : E × E :=
  match c.todo with
  | [] => (z.1, z.1)
  | e :: _ => if c.i < e.B then (z.1, z.1) else (z.1 - e.η • z.2, z.1)

noncomputable def zNext (c : Ctl) (z : E × E) (r : E × E) : E × E :=
  match c.todo with
  | [] => z
  | e :: _ =>
    if c.i < e.B then
      if c.i + 1 < e.B then (z.1, z.2 + r.1)
      else if c.i + 1 < e.B + e.m then (z.1, (1 / (e.B : ℝ)) • (z.2 + r.1))
      else (z.1 - e.η • ((1 / (e.B : ℝ)) • (z.2 + r.1)), 0)
    else if c.i + 1 < e.B + e.m then (z.1 - e.η • z.2, z.2 + (r.1 - r.2))
    else (z.1 - e.η • z.2 - e.η • (z.2 + (r.1 - r.2)), 0)

noncomputable def sarah (schedule : List Epoch) (x0 : E) : Algorithm (E × E) (E × E) E where
  State := Ctl × (E × E)
  initial _ := (⟨schedule, 0⟩, (x0, 0))
  query s := (0, pairQuery s.1 s.2)
  update s r := (ctlNext s.1, zNext s.1 s.2 r)
  output s := s.2.1

noncomputable def stageBatch (μ σ Δ : ℝ) (j : ℕ) : ℝ := 8 * σ ^ 2 * 2 ^ j / (μ * Δ)

noncomputable def stageEpoch (L Lbar μ σ Δ : ℝ) (j : ℕ) : Epoch :=
  let b := stageBatch μ σ Δ j
  let B := max 1 ⌈b⌉₊
  if Lbar * √b < L * b then
    let s := min B ⌊(Lbar / μ) ^ 2⌋₊
    ⟨B, s - 1, 1 / (2 * Lbar * √(s : ℝ))⟩
  else ⟨B, 0, 1 / (2 * L)⟩

noncomputable def stageRepeats (L Lbar μ σ Δ : ℝ) (j : ℕ) : ℕ :=
  let e := stageEpoch L Lbar μ σ Δ j
  ⌈3 / (((e.m : ℝ) + 1) * (e.η * μ))⌉₊

noncomputable def stage (L Lbar μ σ Δ : ℝ) (j : ℕ) : List Epoch :=
  List.replicate (stageRepeats L Lbar μ σ Δ j) (stageEpoch L Lbar μ σ Δ j)

noncomputable def schedule (L Lbar μ σ Δ ε : ℝ) : List Epoch :=
  (List.range ⌈Real.logb 2 (Δ / ε)⌉₊).flatMap (stage L Lbar μ σ Δ)

def cost : List Epoch → ℕ
  | [] => 0
  | e :: rest => e.B + e.m + cost rest

end OracleTemplate.StagewiseSarah
