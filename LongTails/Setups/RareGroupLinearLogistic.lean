import LongTails.Setups.TwoSampleQuadraticPerceptron
import Mathlib.Analysis.SpecialFunctions.Sigmoid

open OracleTemplate
open scoped RealInnerProductSpace

namespace LongTails.Setups.RareGroupLinearLogistic

open LongTails.Setups.TwoSampleQuadraticPerceptron (Features)

structure Public where
  d : ℕ
  m : ℕ
  n : ℕ
  p : ℝ
  start : Features d

structure Data (P : Public) where
  core : Fin P.m → Features P.d
  rare : Fin P.n → Features P.d

def Fits {P : Public} (D : Data P) (w : Features P.d) : Prop :=
  (∀ i, 0 < ⟪w, D.core i⟫) ∧ ∀ j, 0 < ⟪w, D.rare j⟫

noncomputable def meanVote {d n : ℕ} (x : Fin n → Features d) (w : Features d) : Features d :=
  (n : ℝ)⁻¹ • ∑ i, Real.sigmoid (-⟪w, x i⟫) • x i

noncomputable def vote {P : Public} (D : Data P) (w : Features P.d) : Features P.d :=
  (1 - P.p) • meanVote D.core w + P.p • meanVote D.rare w

noncomputable def answer {P : Public} (D : Data P) (w : Features P.d) : Bool × Features P.d :=
  by classical exact (decide (Fits D w), vote D w)

structure Params extends Public where
  data : Data toPublic
  v : Features d
  g : ℝ
  C : ℝ
  g_eq : g = ⟪v, vote data start⟫
  C_eq : C = (n : ℝ)⁻¹ * ∑ j, max ⟪v, data.rare j⟫ 0

noncomputable def capacity (p : Params) : ℝ :=
  (p.n : ℝ)⁻¹ * ∑ j, max ⟪p.v, p.data.rare j⟫ 0

def Obstruction (p : Params) : Prop :=
  (∀ w, Fits p.data w → 0 < ⟪p.v, w⟫) ∧ ⟪p.v, p.start⟫ ≤ 0 ∧
    ∀ i, ⟪p.v, p.data.core i⟫ ≤ 0

noncomputable def meanLoss {d n : ℕ} (x : Fin n → Features d) (w : Features d) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, Real.log (1 + Real.exp (-⟪w, x i⟫))

noncomputable def loss {P : Public} (D : Data P) (w : Features P.d) : ℝ :=
  (1-P.p)*meanLoss D.core w + P.p*meanLoss D.rare w

def family (P : Public) (A : Algorithm (Features P.d) (Bool × Features P.d) (Features P.d)) :
    Prop :=
  ∃ (point : A.State → Features P.d) (h : ℝ), 0 < h ∧
    (∀ seed, point (A.initial seed) = P.start) ∧
    (∀ state, A.query state = (0, point state)) ∧
    (∀ state r, point (A.update state r) =
      if r.1 then point state else point state + h • r.2) ∧
    ∀ state, A.output state = point state

noncomputable def spec : Setup where
  Params := Params
  Public := Public
  Instance := Data
  Query P := Features P.d
  Reply P := Bool × Features P.d
  Output P := Features P.d
  publicInput := Params.toPublic
  valid p := 0 < p.m ∧ 0 < p.n ∧ 0 < p.p ∧ p.p < 1 ∧ 0 < capacity p ∧
    (∃ w, Fits p.data w) ∧ Obstruction p
  admissible p D O := D = p.data ∧ ∀ history q seed, O.answer history q seed = answer D q.2
  successful _ D output _ := ∀ ω, Fits D (output ω)
  allowedAlgorithm := family

end LongTails.Setups.RareGroupLinearLogistic
