import LongTails.Algorithms.WeakMintyHybrid

open scoped RealInnerProductSpace
namespace OracleTemplate.FullRangeWeakMintyHalpern

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def count (δ : ℝ) : ℕ := ⌈2 + 32 / Real.sqrt δ⌉₊

noncomputable def next (c : E) (j : ℕ) (g : E) :=
  c - (((j : ℝ) + 1) / (j + 2)) • g

noncomputable def center (w b : E) := w - (1/2 : ℝ) • b
noncomputable def average (w y : E) := (1/3 : ℝ) • w + (2/3 : ℝ) • y
noncomputable def depth (δ : ℝ) (w y f : E) := ⟪f, w - y⟫ / ‖f‖ - (1 - δ) * ‖f‖
noncomputable def project (δ : ℝ) (w y f : E) := w - (depth δ w y f / ‖f‖) • f

inductive State (E : Type*) where
  | anchor (w : E)
  | solve (w b c y : E) (second : Bool) (index remaining : ℕ)
  | done (y : E)

def point : State E → E
  | .anchor w => w
  | .solve _ _ _ y _ _ _ | .done y => y

noncomputable def update (δ e : ℝ) (st : State E) (g : E) : State E :=
  match st with
  | .anchor w =>
    if ‖g‖ ≤ e then .done w else .solve w g (center w g) (center w g) false 0 (count δ)
  | .solve w b c _ s j (n+1) => .solve w b c (next c j g) s (j+1) n
  | .solve w b _ y s _ 0 =>
    if ‖g‖ ≤ e then .done y
    else if s = false ∧ ‖b‖ < Real.sqrt (Real.sqrt δ) * ‖g‖ then
      .solve w b (average w y) (average w y) true 0 (count δ)
    else .anchor (project δ w y g)
  | .done y => .done y

noncomputable def values (L ρ ε : ℝ) (x0 : E) :
    Algorithm (E ⊕ E) (E × (E →L[ℝ] E)) E where
  State := State E
  initial := fun _ => .anchor x0
  query := fun st => (0, .inl (point st))
  update := fun st reply => update (WeakMintyHybrid.margin L ρ) (ε / L) st (L⁻¹ • reply.1)
  output := point

noncomputable def useValues (L M ρ ε : ℝ) : Prop :=
  let δ := WeakMintyHybrid.margin L ρ
  let H := 1048576 * Real.log (2 / δ) / δ ^ 5
  (2 * (count δ : ℝ) + 3) * 256 * L ^ 2 / (Real.sqrt δ * ε ^ 2) ≤ H * M / ε

noncomputable def select [FiniteDimensional ℝ E] (L M ρ ε : ℝ) (x0 : E) := by
  classical
  exact if useValues L M ρ ε then values L ρ ε x0 else WeakMintyHybrid.hybrid L M ρ ε x0

end OracleTemplate.FullRangeWeakMintyHalpern
