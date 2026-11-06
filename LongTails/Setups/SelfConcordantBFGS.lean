import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import LongTails.Setups.LinearPredictorBFGS
import LongTails.Template

open Set Matrix

namespace LongTails.Setups.SelfConcordantBFGS

open OracleTemplate

abbrev Vec (d : ℕ) := Fin d → ℝ

structure Public where
  d : ℕ
  x0 : Vec d
  B0 : Matrix (Fin d) (Fin d) ℝ

structure Params extends Public where
  c1 : ℝ
  c2 : ℝ
  Δ : ℝ
  Φ0 : ℝ
  ε : ℝ

structure Instance (p : Public) where
  D : Set (Vec p.d)
  f : Vec p.d → ℝ

def hessMatrix {d : ℕ} (H : Vec d →L[ℝ] Vec d →L[ℝ] ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => H (Pi.single i 1) (Pi.single j 1)

noncomputable def mismatch {d : ℕ} (B H : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  2 * Real.log (det (B + H)) - Real.log (det B) - Real.log (det H) - 2 * d * Real.log 2

def SelfConcordantOn {d : ℕ} (D : Set (Vec d)) (f : Vec d → ℝ) (Df : Vec d → Vec d →L[ℝ] ℝ)
    (D2f : Vec d → Vec d →L[ℝ] Vec d →L[ℝ] ℝ)
    (D3f : Vec d → Vec d →L[ℝ] Vec d →L[ℝ] Vec d →L[ℝ] ℝ) : Prop :=
  (∀ x ∈ D, HasFDerivAt f (Df x) x) ∧
  (∀ x ∈ D, HasFDerivAt Df (D2f x) x) ∧
  (∀ x ∈ D, HasFDerivAt D2f (D3f x) x) ∧
  (∀ x ∈ D, ∀ v, v ≠ 0 → 0 < D2f x v v) ∧
  (∀ x ∈ D, ∀ h v, |D3f x h v v| ≤ 2 * √(D2f x h h) * D2f x v v) ∧
  (∀ c : ℝ, IsClosed {x | x ∈ D ∧ f x ≤ c})

structure State (d : ℕ) where
  x : Vec d
  g : Vec d
  B : Matrix (Fin d) (Fin d) ℝ
  started : Bool

noncomputable def direction {d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ) (g : Vec d) : Vec d :=
  -(B⁻¹ *ᵥ g)

noncomputable def bfgs {d : ℕ} (x0 : Vec d) (B0 : Matrix (Fin d) (Fin d) ℝ) :
    Algorithm (Vec d × Vec d) (ℝ × Vec d) (Vec d) where
  State := State d
  initial _ := ⟨x0, 0, B0, false⟩
  query st := (0, (st.x, if st.started then direction st.B st.g else 0))
  update st r :=
    if st.started then
      ⟨st.x + r.1 • direction st.B st.g, r.2,
        LinearPredictorBFGS.bfgsUpdate st.B (r.1 • direction st.B st.g) (r.2 - st.g), true⟩
    else ⟨st.x, r.2, st.B, true⟩
  output st := st.x

abbrev spec : Setup where
  Params := Params
  Public := Public
  Instance := Instance
  Query p := Vec p.d × Vec p.d
  Reply p := ℝ × Vec p.d
  Output p := Vec p.d
  publicInput := Params.toPublic
  valid q := 0 < q.c1 ∧ q.c1 < q.c2 ∧ q.c2 < 1 ∧ Matrix.PosDef q.B0 ∧ 0 ≤ q.Δ ∧ 0 ≤ q.Φ0 ∧
    0 < q.ε
  admissible q I oracle :=
    IsOpen I.D ∧ Convex ℝ I.D ∧ q.x0 ∈ I.D ∧
    ∃ Df D2f D3f, SelfConcordantOn I.D I.f Df D2f D3f ∧
      (∃ xstar ∈ I.D, ∀ x ∈ I.D, I.f xstar ≤ I.f x) ∧
      (∀ x ∈ I.D, I.f q.x0 - q.Δ ≤ I.f x) ∧
      mismatch q.B0 (hessMatrix (D2f q.x0)) ≤ q.Φ0 ∧
      (∀ history x v seed, x ∈ I.D → Df x v ≤ 0 →
        x + (oracle.answer history (0, (x, v)) seed).1 • v ∈ I.D ∧
        (∀ w, Df (x + (oracle.answer history (0, (x, v)) seed).1 • v) w =
          (oracle.answer history (0, (x, v)) seed).2 ⬝ᵥ w) ∧
        (Df x v < 0 →
          0 < (oracle.answer history (0, (x, v)) seed).1 ∧
          I.f (x + (oracle.answer history (0, (x, v)) seed).1 • v) ≤
            I.f x + q.c1 * (oracle.answer history (0, (x, v)) seed).1 * Df x v ∧
          q.c2 * Df x v ≤ Df (x + (oracle.answer history (0, (x, v)) seed).1 • v) v))
  successful q I output P :=
    ∃ xstar ∈ I.D, (∀ x ∈ I.D, I.f xstar ≤ I.f x) ∧
      ∀ᵐ ω ∂(P : MeasureTheory.Measure _), output ω ∈ I.D ∧ I.f (output ω) - I.f xstar ≤ q.ε
  allowedAlgorithm p algorithm := algorithm = bfgs p.x0 p.B0

end LongTails.Setups.SelfConcordantBFGS
