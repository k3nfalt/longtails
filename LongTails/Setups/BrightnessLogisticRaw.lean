import LongTails.Setups.TwoSampleQuadraticPerceptron
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.BrightnessLogisticRaw

open TwoSampleQuadraticPerceptron (Features)

structure Input where
  d : ℕ
  n : ℕ+
  start : ℝ × Features d

structure Rows (u : Input) where
  dc : Fin u.n → ℝ
  detail : Fin u.n → Features u.d

noncomputable def score {u : Input} (X : Rows u) (w : ℝ × Features u.d) (i : Fin u.n) : ℝ :=
  X.dc i * w.1 + ⟪w.2,X.detail i⟫

noncomputable def vote (m : ℝ) : ℝ := 1 / (1 + Real.exp m)

noncomputable def mean {n : ℕ+} (x : Fin n → ℝ) : ℝ := (n : ℝ)⁻¹ * ∑ i, x i

def fits {u : Input} (X : Rows u) (w : ℝ × Features u.d) : Prop := ∀ i, 0 < score X w i

noncomputable def answer {u : Input} (X : Rows u) (w : ℝ × Features u.d) :
    (ℝ × Features u.d) × Bool := by
  classical
  let g := fun i => vote (score X w i)
  exact ((mean (fun i => X.dc i * g i),
    (u.n : ℝ)⁻¹ • ∑ i, g i • X.detail i), decide (fits X w))

def family (u : Input)
    (A : Algorithm (ℝ × Features u.d) ((ℝ × Features u.d) × Bool) (ℝ × Features u.d)) : Prop :=
  ∃ (η : ℝ) (point : A.State → ℝ × Features u.d), 0 < η ∧
    (∀ seed, point (A.initial seed) = u.start) ∧ (∀ s, A.query s = (0,point s)) ∧
    (∀ s z, point (A.update s z) = if z.2 then point s else point s + η • z.1) ∧
    ∀ s, A.output s = point s

structure Params where
  d : ℕ
  n : ℕ+
  R : ℝ
  t : ℝ
  w : Features d
  dc : Fin n → ℝ
  z : Fin n → Features d
  m : ℝ
  D : ℝ
  H : ℝ
  L : ℝ
  δ : ℝ
  debt : ℝ

@[reducible] noncomputable def Params.input (p : Params) : Input := ⟨p.d,p.n,(p.t / p.R,p.w)⟩

noncomputable def Params.rows (p : Params) : Rows p.input := ⟨fun i => p.R*p.dc i,p.z⟩

noncomputable def Params.b (p : Params) : ℝ :=
  mean (fun i => p.dc i * vote (p.t*p.dc i+⟪p.w,p.z i⟫))

noncomputable def Params.threshold (p : Params) : ℝ :=
  16 * (1+|p.t| * p.D+p.H*‖p.w‖) / (p.m*p.δ)

structure Valid (p : Params) : Prop where
  scale : 1 ≤ Real.log p.R
  positiveScale : 0 < p.R
  minPos : 0 < p.m
  gapPos : 0 < p.δ
  detailPos : 0 < p.H
  debtPos : 0 < p.debt
  latticePos : 0 < p.L
  minDC : ∀ i, p.dc i ≠ 0 → p.m ≤ |p.dc i|
  maxDC : ∀ i, |p.dc i| ≤ p.D
  detail : ∀ i, ‖p.z i‖ ≤ p.H
  positiveMass : ∃ k : ℤ, mean (fun i => if 0 < p.dc i then p.dc i else 0) = k*p.L
  negativeMass : ∃ k : ℤ, mean (fun i => if p.dc i < 0 then p.dc i else 0) = k*p.L
  clearance : ∀ k : ℤ, p.δ ≤ |p.b+k*p.L|
  balanced : ∃ (i j : Fin p.n) (a : ℝ), 0 < p.dc i ∧ p.dc j < 0 ∧
    0 ≤ a ∧ a ≤ 1 ∧ a*p.dc i+(1-a)*p.dc j=0 ∧
    a*⟪p.w,p.z i⟫+(1-a)*⟪p.w,p.z j⟫ ≤ -p.debt
  size : 16*p.D*(1+p.m*p.δ/(8*p.H^2)) ≤ p.δ*p.R^2

noncomputable def spec : Setup where
  Params := Params
  Public := Input
  publicInput := Params.input
  valid := Valid
  Instance := Rows
  Query u := ℝ × Features u.d
  Reply u := (ℝ × Features u.d) × Bool
  Output u := ℝ × Features u.d
  admissible p X o := X=p.rows ∧ ∀ k q seed, o.answer k q seed = answer X q.2
  successful _ X out _ := ∀ seed, fits X (out seed)
  allowedAlgorithm := family

end LongTails.Setups.BrightnessLogisticRaw
