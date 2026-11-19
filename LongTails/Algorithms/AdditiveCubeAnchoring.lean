import LongTails.Setups.AdditiveCubeFixedPoint
import Mathlib.Data.Nat.Log

open OracleTemplate

namespace LongTails.Algorithms.AdditiveCubeAnchoring

open LongTails.Setups.AdditiveCubeFixedPoint

noncomputable def project (p : Params) (x : Point p) : Cube p :=
  ⟨fun i => (Set.projIcc (-(p.R : ℝ)) p.R (by linarith [p.R.coe_nonneg]) (x i)).val,
    (pi_norm_le_iff_of_nonneg p.R.coe_nonneg).mpr (fun i => abs_le.mpr
      (Set.projIcc (-(p.R : ℝ)) p.R (by linarith [p.R.coe_nonneg]) (x i)).property)⟩

abbrev Command := Option (ℕ × ℕ × Bool)

abbrev Data (p : Params) := Point p × Point p × Point p

def batch (M n : ℕ) (last : Bool) : List Command :=
  List.replicate (n-1) none ++ [some (M,n,last)]

def stage (M n : ℕ) : List Command :=
  (List.replicate (6 * M - 1) (batch M n false)).flatten ++ batch M n true

def program : ℕ → ℕ → List Command
  | 0, n => stage 1 n
  | m+1, n => stage (8^(m+1)) n ++ program m (4*n)

noncomputable def depth (p : Params) : ℕ := Nat.clog 8 ⌈32 * p.R / p.ε⌉₊

noncomputable def replicas (p : Params) : ℕ := max 1 ⌈2097152 * Real.log (2 * p.d) * (p.σ / p.ε)^2⌉₊

noncomputable def applyReply {p : Params} (cmd : Command) (s : Data p) (r : Point p) : Data p :=
  match cmd with
  | none => (s.1, s.2.1, s.2.2 + r)
  | some (M,n,last) =>
    let a := (M : ℝ)⁻¹
    let x := (1+a)⁻¹ • (s.2.1 + (n : ℝ)⁻¹ • (s.2.2 + r))
    (x, if last then s.2.1 + (7*a) • x else s.2.1, 0)

noncomputable def update {p : Params} (state : List Command × Data p) (r : Point p) :
    List Command × Data p :=
  match state.1 with
  | [] => state
  | cmd :: tail => (tail, applyReply cmd state.2 r)

noncomputable def algorithm (p : Params) : Algorithm (Cube p) (Point p) (Cube p) where
  State := List Command × Data p
  initial _ := (program (depth p) (replicas p), 0, 0, 0)
  query s := (0, project p s.2.1)
  update := update
  output s := project p s.2.1

noncomputable def output (p : Params) (O : Oracle (Cube p) (Point p)) (B : Fin 1 → ℕ)
    (ξ : (i : ℕ) → O.Seed i) := execute O (algorithm p) B () ξ

end LongTails.Algorithms.AdditiveCubeAnchoring
