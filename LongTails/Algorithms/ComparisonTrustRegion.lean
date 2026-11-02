import LongTails.Algorithms.QueryPlan
import LongTails.Algorithms.GuardedMetricAcceleration
import LongTails.Setups.ComparisonHessianLipschitz
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Algorithms.ComparisonTrustRegion

open OracleTemplate LongTails.Algorithms.GuardedMetricAcceleration
open scoped RealInnerProductSpace

noncomputable section

structure Tuning where
  m : ℕ
  mt : ℕ
  N : ℕ
  J : ℕ
  T : ℕ
  τ : ℝ
  τ0 : ℝ
  r : ℝ
  γ : ℝ
  μ : ℝ
  LA : ℝ
  a : ℝ
  η : ℝ
  ε : ℝ

abbrev Plan (E : Type*) (U : Type*) (k : ℕ) := QueryPlan (E × E) Bool U k

section Generic

variable {E S U : Type*}

def loop (c : ℕ) (step : ℕ → S → Plan E S c) : (k : ℕ) → ℕ → S → Plan E S (c * k)
  | 0, _, s => .done s
  | k + 1, i, s => QueryPlan.bind (step i s) (fun s' => loop c step k (i + 1) s')

def loopPure (step : ℕ → S → S) : ℕ → ℕ → S → S
  | 0, _, s => s
  | k + 1, i, s => loopPure step k (i + 1) (step i s)

def cmpPlan (a b : E) : Plan E Bool 1 := .ask (a, b) (fun reply => .done reply)

end Generic

section Vectors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def basisVec (i : ℕ) : E :=
  if h : i < Module.finrank ℝ E then stdOrthonormalBasis ℝ E ⟨i, h⟩ else 0

def testPlan (τ : ℝ) (y w : E) : Plan E Bool 1 := cmpPlan (y - τ • w) (y + τ • w)

def signStep (τ : ℝ) (y : E) (i : ℕ) (σ : ℕ → ℝ) : Plan E (ℕ → ℝ) 1 :=
  QueryPlan.map (fun b => Function.update σ i (if b then 1 else -1)) (testPlan τ y (basisVec i))

def champStep (τ : ℝ) (y : E) (σ : ℕ → ℝ) (i j : ℕ) : Plan E ℕ 1 :=
  QueryPlan.map (fun b => if b then i else j)
    (testPlan τ y (σ i • basisVec i - σ j • basisVec j))

def bisectStep (τ : ℝ) (y : E) (σ : ℕ → ℝ) (i j : ℕ) (_ : ℕ) (lh : ℝ × ℝ) :
    Plan E (ℝ × ℝ) 1 :=
  QueryPlan.map (fun b => if b then ((lh.1 + lh.2) / 2, lh.2) else (lh.1, (lh.1 + lh.2) / 2))
    (testPlan τ y (basisVec i - ((lh.1 + lh.2) / 2 * σ j) • basisVec j))

def ratioStep (t : Tuning) (y : E) (σ : ℕ → ℝ) (j : ℕ) (i : ℕ) (coef : ℕ → ℝ) :
    Plan E (ℕ → ℝ) (1 * t.m) :=
  QueryPlan.map (fun lh => Function.update coef i ((lh.1 + lh.2) / 2))
    (loop 1 (bisectStep t.τ y σ i j) t.m 0 (-2, 2))

def assemble (σ : ℕ → ℝ) (j : ℕ) (coef : ℕ → ℝ) : E :=
  let v : E := ∑ i ∈ Finset.range (Module.finrank ℝ E),
    (if i = j then σ j else coef i) • basisVec i
  ‖v‖⁻¹ • v

def dirPlan (t : Tuning) (y : E) :=
  QueryPlan.bind (loop 1 (signStep t.τ y) (Module.finrank ℝ E) 0 (fun _ => 1)) fun σ =>
    QueryPlan.bind (loop 1 (fun i j => champStep t.τ y σ i j) (Module.finrank ℝ E) 0 0) fun j =>
      QueryPlan.map (assemble (E := E) σ j)
        (loop (1 * t.m) (ratioStep t y σ j) (Module.finrank ℝ E) 0 (fun _ => 0))

def ternaryStep (x u : E) (_ : ℕ) (lh : ℝ × ℝ) : Plan E (ℝ × ℝ) 1 :=
  let m1 := lh.1 + (lh.2 - lh.1) / 3
  let m2 := lh.2 - (lh.2 - lh.1) / 3
  QueryPlan.map (fun b => if b then (lh.1, m2) else (m1, lh.2)) (cmpPlan (x - m1 • u) (x - m2 • u))

def ternaryPlan (t : Tuning) (x u : E) : Plan E (ℝ × ℝ) (1 * t.mt) :=
  loop 1 (ternaryStep x u) t.mt 0 (0, t.r)

structure Frame (E : Type*) where
  x : E
  u : E
  Tu : E
  κ : ℝ

open Classical in
def probeStep (t : Tuning) (v : E) : ℝ := if v = 0 then 0 else t.τ0 / ‖v‖

open Classical in
def tangential (t : Tuning) (_x u v d : E) : E :=
  if v = 0 then 0 else (probeStep t v)⁻¹ • (d - ⟪u, d⟫ • u)

def hvpPlan (t : Tuning) (F : Frame E) (v : E) :=
  QueryPlan.map (fun d => tangential t F.x F.u v d + (⟪F.Tu, v⟫ + F.κ * ⟪F.u, v⟫) • F.u)
    (dirPlan t (F.x + probeStep t v • v))

structure AgdState (E : Type*) where
  x : E
  z : E
  hist : ℕ → E × E

def modelGrad (t : Tuning) (F : Frame E) (chat : ℝ) (y Av : E) : E :=
  chat • F.u + (chat • Av + (2 * t.γ) • y)

def agdStep (t : Tuning) (F : Frame E) (chat : ℝ) (k : ℕ) (s : AgdState E) :=
  let y := extrapolate t.a s.x s.z
  QueryPlan.map (fun Av =>
      let G := modelGrad t F chat y Av
      ({ x := gradientStep t.LA y G, z := centerStep t.a t.μ y s.z G,
         hist := Function.update s.hist k (s.x, y) } : AgdState E))
    (hvpPlan t F y)

def checkVec (s : AgdState E) (w : E) (i : ℕ) : E :=
  let k := i / 4
  let xk := (s.hist k).1
  let yk := (s.hist k).2
  let xk1 := (s.hist (k + 1)).1
  match i % 4 with
  | 0 => xk - yk
  | 1 => yk
  | 2 => xk1
  | _ => w - yk

def passes (t : Tuning) (chat : ℝ) (d Av : E) : Prop :=
  (t.μ + 12 * t.η) * ‖d‖ ^ 2 ≤ ⟪d, chat • Av + (2 * t.γ) • d⟫

structure GuessResult (E : Type*) where
  fail : E
  xN : E

open Classical in
def firstFail (t : Tuning) (chat : ℝ) (vecs : List (E × E)) : E :=
  match vecs.find? (fun p => ¬ passes t chat p.1 p.2) with
  | some p => p.1
  | none => 0

def guessPlan (t : Tuning) (F : Frame E) (chat : ℝ) :=
  QueryPlan.bind (loop _ (agdStep t F chat) t.N 0 ⟨0, 0, fun _ => (0, 0)⟩) fun s =>
    QueryPlan.bind (hvpPlan t F s.x) fun AxN =>
      let s' : AgdState E := { s with hist := Function.update s.hist t.N (s.x, s.x) }
      let w := gradientStep t.LA s.x (modelGrad t F chat s.x AxN)
      QueryPlan.map (fun (pairs : List (E × E)) =>
          ({ fail := firstFail t chat pairs, xN := s.x } : GuessResult E))
        (QueryPlan.traverse (4 * t.N) (fun i =>
          QueryPlan.map (fun Av => (checkVec s' w i, Av)) (hvpPlan t F (checkVec s' w i))))

def guessCands (t : Tuning) (x : E) (res : GuessResult E) : List E :=
  let d := res.fail
  [x + (t.r * ‖d‖⁻¹) • d, x - (t.r * ‖d‖⁻¹) • d, x + res.xN,
    x + (min 1 (t.r * ‖res.xN‖⁻¹)) • res.xN]

def guessScale (t : Tuning) (j : ℕ) : ℝ := 2 ^ j * t.ε

def selectStep (cands : List E) (i : ℕ) (best : E) : Plan E E 1 :=
  QueryPlan.map (fun b => if b then cands.getD i best else best)
    (cmpPlan (cands.getD i best) best)

def epochPlan (t : Tuning) (x : E) :=
  QueryPlan.bind (dirPlan t x) fun u =>
    QueryPlan.bind (ternaryPlan t x u) fun lh =>
      QueryPlan.bind (dirPlan t (x + probeStep t u • u)) fun du =>
        let F : Frame E := { x := x, u := u, Tu := tangential t x u u du, κ := lh.2⁻¹ }
        QueryPlan.bind (QueryPlan.traverse t.J (fun j : Fin t.J => guessPlan t F (guessScale t j)))
          fun results =>
            let cands := (x - (t.r / 8) • u) :: (results.map (guessCands t x)).flatten
            QueryPlan.map (fun best => (best, cands))
              (loop 1 (selectStep cands) (4 * t.J + 1) 0 x)

def outerStep (t : Tuning) (_ : ℕ) (st : E × List E) :=
  QueryPlan.map (fun (r : E × List E) => (r.1, st.2 ++ r.1 :: r.2)) (epochPlan t st.1)

def outerPlan (t : Tuning) (x0 : E) := loop _ (outerStep t) t.T 0 (x0, [x0])

end Vectors

section Public

open LongTails.Setups.ComparisonHessianLipschitz

def tuning (p : Params) : Tuning :=
  let n : ℝ := Module.finrank ℝ p.E
  let γ := Real.sqrt (p.ρ * p.ε)
  let r := Real.sqrt (p.ε / p.ρ) / 4
  let LA := 2 * p.L + 4 * γ
  let G := Real.sqrt (2 * p.L * p.Δ)
  let B0 := 2 + n + p.L / γ + G / p.ε
  let Rad := 4 * G / γ + r
  let K := Real.sqrt (γ / LA) * p.ε ^ 2 / (576000 * LA * Rad) / (8 * Rad)
  { m := ⌈18 * Real.log B0⌉₊ + 72
    mt := ⌈18 * Real.log B0⌉₊ + 72
    N := ⌈Real.sqrt (2 * p.L / γ + 4) * (8 * Real.log B0 + 40)⌉₊
    J := ⌈Real.logb 2 (G / p.ε)⌉₊ + 1
    T := ⌊400 * p.Δ * Real.sqrt p.ρ / p.ε ^ (3 / 2 : ℝ)⌋₊ + 1
    τ := 4 * r / (10 ^ 12 * B0 ^ 6)
    τ0 := K * p.ε / (6 * (p.L ^ 2 + γ ^ 2))
    r := r
    γ := γ
    μ := γ
    LA := LA
    a := Real.sqrt (γ / LA)
    η := γ / 192
    ε := p.ε }

def algorithm (p : Params) : Algorithm (p.E × p.E) Bool (List p.E) :=
  QueryPlan.algorithm ⟨MeasureTheory.Measure.dirac (), inferInstance⟩ (p.x0, p.x0) []
    _ (fun _ : Unit => QueryPlan.map Prod.snd (outerPlan (tuning p) p.x0))

end Public

end

end LongTails.Algorithms.ComparisonTrustRegion
