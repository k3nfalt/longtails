import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Probability.Distributions.Uniform
import LongTails.Setups.FiniteSumSmoothAndConvex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace OracleTemplate.ReshuffledConvex

def Orders (n K : ℕ) := Fin K → Equiv.Perm (Fin n)

instance (n K : ℕ) : Fintype (Orders n K) := inferInstanceAs (Fintype (Fin K → Equiv.Perm (Fin n)))
instance (n K : ℕ) : Nonempty (Orders n K) := ⟨fun _ => Equiv.refl _⟩
instance (n K : ℕ) : MeasurableSpace (Orders n K) := ⊤
instance (n K : ℕ) : MeasurableSingletonClass (Orders n K) := ⟨fun _ => trivial⟩

def schedule {n K : ℕ} (orders : Orders n K) (k : ℕ) : Equiv.Perm (Fin n) :=
  if h : k < K then orders ⟨k, h⟩ else Equiv.refl _

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def reshuffledGradient {n : ℕ} [NeZero n] (K : ℕ) (η : ℕ → ℝ) (x0 : E) :
    Algorithm (Fin n × E) E E where
  Seed := Orders n K
  law := ⟨(PMF.uniformOfFintype (Orders n K)).toMeasure, inferInstance⟩
  State := (ℕ → Equiv.Perm (Fin n)) × ℕ × E
  initial orders := (schedule orders, 0, x0)
  query s := (0, (s.1 (s.2.1 / n) ⟨s.2.1 % n, Nat.mod_lt s.2.1 (NeZero.pos n)⟩, s.2.2))
  update s g := (s.1, s.2.1 + 1, s.2.2 - η (s.2.1 / n) • g)
  output s := s.2.2

end OracleTemplate.ReshuffledConvex

open MeasureTheory

namespace LongTails.Setups.ReshuffledSmoothConvex

open OracleTemplate OracleTemplate.ReshuffledConvex

structure Params where
  E : Type u
  [normedE : NormedAddCommGroup E]
  [linearE : InnerProductSpace ℝ E]
  [completeE : CompleteSpace E]
  [measurableE : MeasurableSpace E]
  [borelE : BorelSpace E]
  n : ℕ
  [nonzero : NeZero n]
  Lavg : ℝ
  Lmax : ℝ
  R : ℝ
  σ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Params.normedE Params.linearE Params.completeE Params.measurableE
  Params.borelE Params.nonzero

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Fin p.n → p.E → ℝ
  Query p := Fin p.n × p.E
  Reply p := p.E
  Output p := p.E
  allowedAlgorithm q algorithm :=
    ∃ (K : ℕ) (η : ℕ → ℝ), algorithm = reshuffledGradient K η q.x0
  publicInput p := p
  valid q := 0 < q.Lavg ∧ q.Lavg ≤ q.Lmax ∧ 0 ≤ q.R ∧ 0 ≤ q.σ ∧ 0 < q.ε
  admissible q f oracle :=
    (∀ i, ConvexOn ℝ Set.univ (f i)) ∧
    (∀ k seed i x, HasGradientAt (f i) (oracle.answer k (0, (i, x)) seed) x) ∧
    (∃ ℓ : Fin q.n → ℝ, (∀ i, 0 ≤ ℓ i) ∧ (∀ i, ℓ i ≤ q.Lmax) ∧
      (q.n : ℝ)⁻¹ * ∑ i, ℓ i ≤ q.Lavg ∧
      ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ ℓ i * ‖x - y‖) ∧
    (∃ xstar, IsMinOn (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) Set.univ xstar ∧ ‖q.x0 - xstar‖ ≤ q.R ∧
      (q.n : ℝ)⁻¹ * ∑ i, ‖gradient (f i) xstar‖ ^ 2 ≤ q.σ ^ 2)
  successful q f output P :=
    Measurable output ∧
    ∃ xstar, IsMinOn (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) Set.univ xstar ∧
      Integrable (fun ω => LongTails.Setups.FiniteSumSmoothAndConvex.objective f (output ω) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar)
        (P : Measure _) ∧
      (∫ ω, LongTails.Setups.FiniteSumSmoothAndConvex.objective f (output ω) - LongTails.Setups.FiniteSumSmoothAndConvex.objective f xstar ∂(P : Measure _)) ≤ q.ε

end LongTails.Setups.ReshuffledSmoothConvex
