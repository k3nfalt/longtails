import LongTails.Setups.QuasarConvexHessianLipschitz
import LongTails.Algorithms.ComponentEnvelope
import LongTails.Proofs.QuasarCubicStep
import LongTails.Proofs.QuasarCubicPotential

noncomputable section

namespace LongTails.Algorithms.QuasarCubicNewton

open LongTails.Setups.QuasarConvexHessianLipschitz
open LongTails.Proofs.QuasarCubicStep
open LongTails.Proofs.QuasarCubicPotential
open OracleTemplate.ComponentEnvelope (Program)
open scoped RealInnerProductSpace

def iterations (p : Params) : ℕ :=
  ⌈(8388608 * p.H * p.R ^ 3 / (p.γ ^ 4 * p.ε)) ^ (3 / 8 : ℝ)⌉₊

def reg (p : Params) : ℝ := 270 * p.H * (iterations p : ℝ) ^ (1 / 3 : ℝ) / p.γ

def est (p : Params) : ℝ := 7776 * reg p / p.γ ^ 3

def depth (p : Params) : ℕ :=
  Nat.log2 ⌈27 * (8388608 * p.H * p.R ^ 3 / (p.γ ^ 4 * p.ε) + 1) ^ 2 *
    (p.L₀ / (p.H * p.R) + 32768) / p.γ ^ 2⌉₊ + 1

abbrev Reply (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  ℝ × E × (E →L[ℝ] E)

structure Outer (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  x : E
  data : Reply E
  s : E
  c : ℝ
  k : ℕ

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def bisect (M : ℝ) (x d : E) (fx : ℝ) :
    ℕ → ℝ → ℝ → Reply E → Program E (Reply E) (ℝ × Reply E)
  | 0, lo, _, dlo => .done (lo, dlo)
  | j + 1, lo, hi, dlo => .ask (x + ((lo + hi) / 2) • d) fun r =>
      if envelope M r ≤ fx then bisect M x d fx j ((lo + hi) / 2) hi r
      else bisect M x d fx j lo ((lo + hi) / 2) dlo

def coupling (M : ℝ) (n : ℕ) (x v : E) (dx dv : Reply E) :
    Program E (Reply E) (ℝ × Reply E) :=
  if envelope M dv ≤ dx.1 then .done (1, dv) else bisect M x (v - x) dx.1 n 0 1 dx

def outerStep (M N γ : ℝ) (n : ℕ) (x0 : E) (st : Outer E) : Program E (Reply E) (Outer E) :=
  let v := center N x0 st.s
  .ask v fun dv =>
    (coupling M n st.x v st.data dv).bind fun choice =>
      let y := st.x + choice.1 • (v - st.x)
      let z := y + cubicStep choice.2.2.1 choice.2.2.2 M
      .ask z fun dz =>
        .done ⟨z, dz, st.s + (weight st.k / γ) • dz.2.1,
          st.c + weight st.k * (dz.1 - ⟪dz.2.1, z⟫ / γ), st.k + 1⟩

def outerLoop (M N γ : ℝ) (n : ℕ) (x0 : E) : ℕ → Outer E → Program E (Reply E) E
  | 0, st => .done st.x
  | j + 1, st => (outerStep M N γ n x0 st).bind (outerLoop M N γ n x0 j)

def plan (p : Params) : Program p.E (Reply p.E) p.E :=
  .ask p.x0 fun r0 =>
    outerLoop (reg p) (est p) p.γ (depth p) p.x0 (iterations p) ⟨p.x0, r0, 0, 0, 0⟩

def algorithm (p : Params) : OracleTemplate.Algorithm p.E (Reply p.E) p.E where
  State := Program p.E (Reply p.E) p.E
  initial := fun _ => plan p
  query := fun state => (0, state.query p.x0)
  update := Program.update
  output := Program.output p.x0

end LongTails.Algorithms.QuasarCubicNewton
