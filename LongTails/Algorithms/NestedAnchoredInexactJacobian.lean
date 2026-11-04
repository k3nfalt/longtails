import LongTails.Setups.InexactJacobianMonotone
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Algorithms.NestedAnchoredInexactJacobian

open OracleTemplate LongTails.Setups.InexactJacobianMonotone

noncomputable section

variable (p : Params)

def outerCount : ℕ := ⌈(p.M * p.R ^ 2 / p.ε) ^ (2 / 5 : ℝ)⌉₊ + 1

def scale : ℝ := 4 * p.R / (p.ε * outerCount p * (outerCount p + 1))

def outerStep (k : ℕ) : ℝ := scale p * (k + 1)

def cumulative (k : ℕ) : ℝ := scale p * k * (k + 1) / 2

def anchor (k : ℕ) (z : p.E) : p.E :=
  (outerStep p k / cumulative p (k + 1)) • p.x0 +
    (cumulative p k / cumulative p (k + 1)) • z

def center (k : ℕ) (z Fz : p.E) : p.E :=
  anchor p k z - (outerStep p k * cumulative p k / cumulative p (k + 1)) • Fz

def guess (k j : ℕ) : ℝ := (1 / outerStep p k + p.δ) / p.M * 2 ^ j

def innerStep (k j : ℕ) : ℝ := 1 / (128 * p.δ + 512 * p.M * guess p k j)

def innerCount (k j : ℕ) : ℕ := ⌈8 * outerStep p k / innerStep p k j⌉₊ + 1

def solve (J : p.E →L[ℝ] p.E) (β τ : ℝ) (v : p.E) : p.E :=
  Function.invFun (β • ContinuousLinearMap.id ℝ p.E + τ • J) v

inductive Phase where
  | model
  | certificate
  | finished

structure State where
  phase : Phase
  k : ℕ
  z : p.E
  Fz : p.E
  j : ℕ
  i : ℕ
  u : p.E
  Gu : p.E
  pending : p.E

variable {p}

def State.outerAnchor (s : State p) : p.E := anchor p s.k s.z

def State.outerCenter (s : State p) : p.E := center p s.k s.z s.Fz

def State.innerAnchor (s : State p) : p.E :=
  (1 / ((s.i : ℝ) + 1)) • s.outerCenter +
    ((s.i : ℝ) / ((s.i : ℝ) + 1)) • s.u

def State.innerCenter (s : State p) : p.E :=
  s.innerAnchor -
    (innerStep p s.k s.j * (s.i : ℝ) / ((s.i : ℝ) + 1)) • s.Gu

def State.regularizedValue (s : State p) (x Fx : p.E) : p.E :=
  Fx + (1 / outerStep p s.k) • (x - s.outerAnchor)

def State.trial (s : State p) (Fc : p.E) (J : p.E →L[ℝ] p.E) : p.E :=
  let t := innerStep p s.k s.j
  let μ := 1 / outerStep p s.k
  solve p J (1 + t * (μ + p.δ)) t
    (s.innerAnchor - t • s.regularizedValue s.innerCenter Fc +
      t • (J s.innerCenter + (μ + p.δ) • s.innerCenter))

def State.accepted (s : State p) (Fy : p.E) : Prop :=
  ‖outerStep p s.k • s.regularizedValue s.pending Fy‖ ≤
    ‖s.pending - s.outerCenter‖ / 2

def outerStart (k : ℕ) (z Fz : p.E) : State p :=
  ⟨if k = outerCount p then .finished else .model,
    k, z, Fz, 0, 0, center p k z Fz, 0, center p k z Fz⟩

def initial : State p := outerStart 0 p.x0 0

def query (s : State p) : Fin 1 × p.E :=
  (0, match s.phase with
    | .model => s.innerCenter
    | .certificate => s.pending
    | .finished => p.x0)

def afterCertificate (s : State p) (Fy : p.E) : State p := by
  classical
  exact if s.accepted Fy then outerStart (s.k + 1) s.pending Fy
    else if s.i + 1 = innerCount p s.k s.j then
      { s with phase := .model, j := s.j + 1, i := 0, u := s.outerCenter, Gu := 0, pending := s.outerCenter }
    else
      { s with phase := .model, i := s.i + 1, u := s.pending, Gu := s.regularizedValue s.pending Fy }

def update (s : State p) (reply : p.E × (p.E →L[ℝ] p.E)) : State p :=
  match s.phase with
  | .model => { s with phase := .certificate, pending := s.trial reply.1 reply.2 }
  | .certificate => afterCertificate s reply.1
  | .finished => s

def algorithm (p : Params) : Algorithm p.E (p.E × (p.E →L[ℝ] p.E)) p.E where
  State := State p
  initial := fun _ => initial
  query := query
  update := update
  output := fun s => s.z

def output (O : Oracle p.E (p.E × (p.E →L[ℝ] p.E))) (N : ℕ)
    (ξ : (k : ℕ) → O.Seed k) : p.E :=
  execute O (algorithm p) (fun _ => N) () ξ

end

end LongTails.Algorithms.NestedAnchoredInexactJacobian
