import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Probability.Distributions.Uniform

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
