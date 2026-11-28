import LongTails.Setups.BrightnessLogisticRaw
import LongTails.Setups.ManySampleConvolutionalPerceptron

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.BrightnessLogisticJoint

open TwoSampleQuadraticPerceptron (Features shift Space margin direction)
open ManySampleConvolutionalPerceptron (axis)
open BrightnessLogisticRaw (vote mean)

structure Input where
  d : ℕ+
  n : ℕ+
  start : Space .conv d
  step : ℝ

abbrev Rows (u : Input) := Fin u.n → Features u.d

def fits {u : Input} (X : Rows u) (s : Space .conv u.d) : Prop :=
  ∀ i, 0 < margin .conv u.d (X i) s

noncomputable def answer {u : Input} (X : Rows u) (s : Space .conv u.d) : Space .conv u.d × Bool := by
  classical
  exact ((u.n : ℝ)⁻¹ • ∑ i, vote (margin .conv u.d (X i) s) • direction .conv u.d (X i) s,
    decide (fits X s))

def family (u : Input) (A : Algorithm (Space .conv u.d) (Space .conv u.d × Bool) (Space .conv u.d)) : Prop :=
  ∃ (η : ℝ) (point : A.State → Space .conv u.d), 0 < η ∧
    (∀ seed, point (A.initial seed) = u.start) ∧ (∀ s, A.query s = (0,point s)) ∧
    (∀ s z, point (A.update s z) = if z.2 then point s else point s + η • z.1) ∧
    ∀ s, A.output s = point s

structure Params where
  d : ℕ+
  n : ℕ+
  R : ℝ
  taps : ℝ × ℝ
  t : ℝ
  w : Features d
  dc : Fin n → ℝ
  z : Fin n → Features d
  a : Features d
  u : Features d
  γ : ℝ
  g : ℝ
  m : ℝ
  D : ℝ
  μ : ℝ
  J : ℝ

noncomputable def Params.plus (p : Params) (i : Fin p.n) :=
  (Real.sqrt 2)⁻¹ • (p.z i+shift (p.z i))

noncomputable def Params.minus (p : Params) (i : Fin p.n) :=
  (Real.sqrt 2)⁻¹ • (p.z i-shift (p.z i))

noncomputable def Params.p₀ (p : Params) := (p.taps.1+p.taps.2)/Real.sqrt 2
noncomputable def Params.q₀ (p : Params) := (p.taps.1-p.taps.2)/Real.sqrt 2
noncomputable def Params.L (p : Params) := 1+Real.log (2*(p.n : ℝ))

noncomputable def Params.M (p : Params) :=
  let K := 3*p.L+1
  let I := ‖p.a‖+Real.sqrt (p.p₀^2+p.q₀^2+2*p.t^2+3+K)
  1+2*I/(p.γ*p.g)+4*K/(p.γ*p.g)^2

noncomputable def Params.B (p : Params) :=
  let F := 1+3*(p.p₀^2+p.t^2)+p.q₀^2+‖p.w‖^2
  F*Real.exp ((6*p.L+22*p.J+5*p.J^2)*(p.M+1))

noncomputable def Params.κ (p : Params) := 1/(4*(1+p.D)*(1+p.J*p.B))

noncomputable def Params.δ (p : Params) := 1/(64*p.J*Real.sqrt p.B*(p.M+1))

@[reducible] noncomputable def Params.input (p : Params) : Input :=
  ⟨p.d,p.n,(p.taps,p.w+(p.t/p.R) • axis p.d),p.κ/p.R⟩

noncomputable def Params.rows (p : Params) : Rows p.input :=
  fun i => (p.R*p.dc i) • axis p.d+p.z i

structure Valid (p : Params) : Prop where
  scale : 1 ≤ p.R
  marginPos : 0 < p.γ
  floorPos : 0 < p.g
  dcPos : 0 < p.m
  massPos : 0 < p.μ
  forcePos : 1 ≤ p.J
  minDC : ∀ i, p.dc i ≠ 0 → p.m ≤ |p.dc i|
  maxDC : ∀ i, |p.dc i| ≤ p.D
  positiveMass : p.μ ≤ mean (fun i => if 0 < p.dc i then p.dc i else 0)
  negativeMass : p.μ ≤ mean (fun i => if p.dc i < 0 then -p.dc i else 0)
  centered : ∀ i, ⟪axis p.d,p.z i⟫ = 0
  startCentered : ⟪axis p.d,p.w⟫ = 0
  radius : ∀ i, ‖p.plus i‖+‖p.minus i‖ ≤ p.J
  separator : ‖p.u‖ ≤ 1 ∧ ∀ i, p.γ ≤ ⟪p.u,p.minus i⟫
  tap : 0 < p.q₀
  gap : 4*p.g^2 ≤ p.q₀^2-‖p.a‖^2
  initialCross : ∀ i, 0 ≤ ⟪p.w-p.a,p.minus i⟫
  cross : ∀ i j, 2*p.B*(p.M+1)^2*|⟪p.plus i,p.minus j⟫| ≤ p.g^2
  saturation : 2*(p.J*p.B+Real.log (2*p.D/p.μ)) ≤ p.R*p.m*p.δ^2
  occupation : (p.κ/p.R)*Real.sqrt p.B*p.B ≤ (p.κ*p.μ/2)^2*p.δ^3
  imbalance : (p.κ/p.R)*(8*p.J*p.B) ≤ p.δ^2
  kinetic : (p.κ/p.R)*(3*p.J^2*p.B*(p.M+1)) ≤ min 1 (p.g^2)
  sign : (p.κ/p.R)*p.J*Real.sqrt p.B ≤ p.g

noncomputable def spec : Setup where
  Params := Params
  Public := Input
  publicInput := Params.input
  valid := Valid
  Instance := Rows
  Query u := Space .conv u.d
  Reply u := Space .conv u.d × Bool
  Output u := Space .conv u.d
  admissible p X o := X=p.rows ∧ ∀ k q seed, o.answer k q seed = answer X q.2
  successful _ X out _ := ∀ seed, fits X (out seed)
  allowedAlgorithm := family

end LongTails.Setups.BrightnessLogisticJoint
