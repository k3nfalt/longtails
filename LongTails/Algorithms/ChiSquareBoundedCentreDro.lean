import LongTails.Algorithms.ChiSquareBracket
import LongTails.Algorithms.ComponentEnvelope

namespace OracleTemplate.ChiSquareBoundedCentreDro

open LongTails.Setups.ChiSquareConstrainedDro
open ComponentEnvelope (Program)
universe u

noncomputable section

def bracketCount (q : Params) := 1 + Nat.log 2 ⌊8 * q.B / q.ε⌋₊

def rounds (q : Params) := Nat.clog 2 (bracketCount q)

def trainingCount (q : Params) :=
  ⌈256 * (1 + 2 * q.ρ) * (q.G ^ 2 * q.R ^ 2 + 3 * q.B ^ 2) / q.ε ^ 2⌉₊

def batchSize (q : Params) (r : ℕ) :=
  ⌈1024 * (1 + 2 * q.ρ) * q.B ^ 2 * (3 / 2 : ℝ) ^ r / q.ε ^ 2⌉₊

def leftEndpoint (q : Params) (j : ℕ) : ℝ := 2 ^ j * (q.ε / (8 * q.ρ))

def weight (z a l : ℝ) := max (z - (a - l)) 0 / l

abbrev Plan (q : Params) (α : Type*) := Program q.E (q.E × ℝ × q.E) α
abbrev Triple (E : Type*) := E × ℝ × ℝ
abbrev Candidate (E : Type*) := E × ℝ

def nextPoint (q : Params) (d : ℝ) (z : Triple q.E) (reply : q.E × ℝ × q.E) : Triple q.E :=
  let v := weight reply.2.1 z.2.1 z.2.2
  let c₂ := 1 + 2 * q.ρ
  let γx := q.ε / (64 * c₂ * q.G ^ 2)
  let γa := q.ε / (64 * c₂)
  let γl := q.ε / (64 * (q.ρ ^ 2 + c₂ * q.B ^ 2 / d ^ 2))
  (reply.1 - γx • (v • reply.2.2),
   max 0 (min q.B (z.2.1 - γa * (1 - v))),
   max d (min (2*d) (z.2.2 - γl * (q.ρ - (v - 1) ^ 2 / 2))))

def training (q : Params) (d : ℝ) : ℕ → Triple q.E → Candidate q.E → Plan q (Candidate q.E)
  | 0, _, total => .done ((trainingCount q : ℝ)⁻¹ • total.1, total.2 / trainingCount q)
  | n+1, z, total => .ask z.1 fun reply =>
    training q d n (nextPoint q d z reply) (total.1 + reply.1, total.2 + (z.2.1 - z.2.2))

def trainBracket (q : Params) (j : ℕ) :=
  let d := leftEndpoint q j
  training q d (trainingCount q) (q.x0, 0, d) (0, 0)

def collect {q : Params} {α : Type*} (jobs : ℕ → Plan q α) : (n : ℕ) → Plan q (Fin n → α)
  | 0 => .done Fin.elim0
  | n+1 => (collect jobs n).bind fun prev =>
    (jobs n).map fun last => Fin.lastCases last prev

def score (q : Params) (w : Candidate q.E) (m : ℕ) : ℕ → ℝ → Plan q ℝ
  | 0, acc => .done (w.2 + ChiSquareDro.radius q * Real.sqrt (acc / m))
  | n+1, acc => .ask w.1 fun reply => score q w m n (acc + max (reply.2.1 - w.2) 0 ^ 2)

def matchPair (q : Params) (r : ℕ) (x y : Candidate q.E) : Plan q (Candidate q.E) :=
  let m := batchSize q r
  (score q x m m 0).bind fun sx =>
    (score q y m m 0).map fun sy => if sx ≤ sy then x else y

def tournament (q : Params) (r : ℕ) : ℕ → (ℕ → Candidate q.E) → Plan q q.E
  | 0, xs => .done (xs 0).1
  | h+1, xs =>
    (collect (fun i => matchPair q r (xs (2*i)) (xs (2*i+1))) (2^h)).bind fun winners =>
      tournament q (r+1) h fun i => winners ⟨i % (2^h), Nat.mod_lt _ (by positivity)⟩

def plan (q : Params) : Plan q q.E :=
  if min q.B (q.G * q.R) ≤ q.ε then .done q.x0 else
    (collect (trainBracket q) (bracketCount q)).bind fun xs =>
      tournament q 0 (rounds q) fun i =>
        xs (if hi : i < bracketCount q then ⟨i, hi⟩ else ⟨0, by unfold bracketCount; omega⟩)

def algorithm (q : Params.{u}) : Algorithm q.E (q.E × ℝ × q.E) q.E where
  State := Plan q q.E
  initial := fun _ => plan q
  query s := (0, s.query q.x0)
  update := Program.update
  output := Program.output q.x0

end

end OracleTemplate.ChiSquareBoundedCentreDro
