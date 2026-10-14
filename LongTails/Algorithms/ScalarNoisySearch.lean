import Mathlib.Basic.Real.Basic
import Mathlib.Data.List.Basic

namespace OracleTemplate.ScalarNoisySearch

inductive Node where
  | interval (lo hi : ℝ) (level : ℕ)
  | candidate (point : ℝ) (base checks : ℕ)

def Node.level : Node → ℕ
  | .interval _ _ d => d
  | .candidate _ d k => d + k + 1

noncomputable def queries : Node → Fin 3 → ℝ
  | .interval lo hi _, i => if i = 0 then lo else if i = 1 then hi else (lo + hi) / 2
  | .candidate x _ _, _ => x

def retreat : List Node → List Node
  | [] => []
  | [n] => [n]
  | _ :: n :: rest => n :: rest

noncomputable def advance (ε : ℝ) (D ℓ : ℕ)
    (reply : Fin 3 → ℝ) (path : List Node) : List Node := by
  classical
  exact match path with
    | [] => []
    | .interval lo hi d :: _rest =>
      if |reply 0| ≤ ε / 4 then .candidate lo d 0 :: path
      else if |reply 1| ≤ ε / 4 then .candidate hi d 0 :: path
      else if |reply 2| ≤ ε / 4 then .candidate ((lo + hi) / 2) d 0 :: path
      else if reply 0 < 0 ∧ 0 < reply 1 ∧ d < D then
        if reply 2 < 0 then .interval ((lo + hi) / 2) hi (d + 1) :: path
        else .interval lo ((lo + hi) / 2) (d + 1) :: path
      else retreat path
    | .candidate x d k :: _rest =>
      if ℓ ≤ k then path
      else if |reply 0| ≤ ε / 2 then .candidate x d (k + 1) :: path
      else retreat path

def recordedPoint (fallback : ℝ) : List Node → ℝ
  | .candidate x _ _ :: _ => x
  | _ => fallback

noncomputable def trace (ε : ℝ) (D ℓ : ℕ)
    (replies : ℕ → List Node → Fin 3 → ℝ) (initial : List Node) : ℕ → List Node
  | 0 => initial
  | n + 1 => advance ε D ℓ (replies n (trace ε D ℓ replies initial n))
      (trace ε D ℓ replies initial n)

noncomputable def output (ε : ℝ) (D ℓ : ℕ)
    (replies : ℕ → List Node → Fin 3 → ℝ) (initial : List Node)
    (fallback : ℝ) (time : ℕ) : ℝ :=
  recordedPoint fallback (trace ε D ℓ replies initial time)

end OracleTemplate.ScalarNoisySearch
