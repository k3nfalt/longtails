import LongTails.Setups.ManySampleConvolutionalPerceptron
import Mathlib.Analysis.SpecialFunctions.Sigmoid

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.BrightnessScaledTwoTap

open TwoSampleQuadraticPerceptron (Features shift margin direction)
open ManySampleConvolutionalPerceptron (Space axis)

structure Params where
  d : ℕ+
  n : ℕ+
  R : ℝ
  D : ℝ
  μ : ℝ
  J : ℝ
  γ : ℝ
  P : ℝ
  Q : ℝ
  readout : Features d

abbrev Images (p : Params) := Fin p.n → Features p.d

noncomputable def centered {d : ℕ} (x : Features d) : Features d :=
  x - ⟪axis d,x⟫ • axis d

noncomputable def brightness {d : ℕ} (x : Features d) : ℝ :=
  Real.sqrt 2 * ⟪axis d,x⟫

noncomputable def contrast {d : ℕ} (x : Features d) : Features d :=
  (Real.sqrt 2)⁻¹ • (centered x - shift (centered x))

noncomputable def smooth {d : ℕ} (x : Features d) : Features d :=
  (Real.sqrt 2)⁻¹ • (centered x + shift (centered x))

noncomputable def amplify {d : ℕ} (R : ℝ) (x : Features d) : Features d :=
  centered x + (R * ⟪axis d,x⟫) • axis d

noncomputable def start (p : Params) : Space p.d :=
  let B := Real.sqrt p.R
  ((B * (p.P+p.Q)/Real.sqrt 2, B * (p.P-p.Q)/Real.sqrt 2),
    B⁻¹ • (centered p.readout + (⟪axis p.d,p.readout⟫/p.R) • axis p.d))

def Geometry (p : Params) (x : Images p) : Prop :=
  (∀ i, |brightness (x i)| ≤ p.D ∧ ‖contrast (x i)‖ + ‖smooth (x i)‖ ≤ p.J) ∧
  (p.n : ℝ)*p.μ ≤ ∑ i, max (brightness (x i)) 0 ∧
  (p.n : ℝ)*p.μ ≤ ∑ i, max (-brightness (x i)) 0 ∧
  ∃ u : Features p.d, ‖u‖ = 1 ∧ ∀ i, p.γ ≤ ⟪u,contrast (x i)⟫

structure Reply (d : ℕ) where
  descent : Space d
  fitted : Bool

def Fitted (p : Params) (x : Images p) (θ : Space p.d) : Prop :=
  ∀ i, 0 < margin .conv p.d (amplify p.R (x i)) θ

noncomputable def answer (p : Params) (x : Images p) (θ : Space p.d) : Reply p.d := by
  classical
  exact ⟨(p.n : ℝ)⁻¹ • ∑ i, (Real.sigmoid (-margin .conv p.d (amplify p.R (x i)) θ)) •
    direction .conv p.d (amplify p.R (x i)) θ,decide (Fitted p x θ)⟩

def family (p : Params) (alg : Algorithm (Space p.d) (Reply p.d) (Space p.d)) : Prop :=
  ∃ (point : alg.State → Space p.d) (η : ℝ), 0 < η ∧
    (∀ seed, point (alg.initial seed) = start p) ∧
    (∀ s, alg.query s = (0,point s)) ∧
    (∀ s r, point (alg.update s r) = if r.fitted then point s else point s + η • r.descent) ∧
    (∀ s, alg.output s = point s)

structure Scales where
  U : ℝ
  Γ : ℝ
  κ : ℝ
  δ : ℝ
  V : ℝ
  f : ℝ
  B : ℝ
  M : ℝ
  H : ℕ

noncomputable def scales (p : Params) : Scales :=
  let U := p.J * (4+|p.P|+|p.Q|)
  let Γ := min 1 (|p.Q| * p.γ)/4
  let κ := Γ/(32*(1+p.D)*(1+U))
  let δ := Γ/(128*(1+p.J))
  let V := 6+Real.sqrt (Real.log (1+|p.P|/δ))
  let f := p.μ*Γ/(32*p.n*V*(1+U))
  let B := 1+(1+Real.log (4*(1+|p.P|)^2*p.R^2))/(κ*f)^2
  let M := 8*(1+‖p.readout‖+(1+U)/p.μ+(1+Real.log (2*p.n)+κ*U^2)/Γ)+κ*U*B
  ⟨U,Γ,κ,δ,V,f,B,M,⌈32*p.n*V^2*M/(κ*Γ)⌉₊⟩

noncomputable def largeScale (p : Params) : Prop :=
  let c := scales p
  let W := ‖p.readout‖+c.κ*c.U*c.H
  let ε := c.κ*p.J*W/p.R^2
  let cost := 3*c.κ*(1+c.U*W)/p.R^2+(4*(2+|p.P|)+1)*ε
  c.H*ε ≤ c.δ/4 ∧ 16*c.H*ε*p.R ≤ c.V*c.M ∧
    (‖p.readout‖/p.R^2)^2 + c.H*cost + 2*(1+c.U*W)/(p.μ*p.R^2) +
      (c.V*c.M/p.R)^2 ≤ c.δ^2

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  Instance := Images
  Query p := Space p.d
  Reply p := Reply p.d
  Output p := Space p.d
  publicInput := id
  valid p := 0 < p.μ ∧ 0 < p.γ ∧ 0 < p.D ∧ 0 < p.J ∧ p.Q ≠ 0 ∧ 1 ≤ p.R ∧ largeScale p
  admissible p x oracle := Geometry p x ∧
    ∀ history query seed, oracle.answer history query seed = answer p x query.2
  successful p x output _ := ∀ seed, Fitted p x (output seed)
  allowedAlgorithm := family

end LongTails.Setups.BrightnessScaledTwoTap
