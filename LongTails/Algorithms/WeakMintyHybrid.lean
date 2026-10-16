import LongTails.Template
import LongTails.Proofs.RegularizedLinearRoot
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OracleTemplate.WeakMintyHybrid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def modelStep (J : E →L[ℝ] E) (g : E) (k : ℝ) : E :=
  if hk : 0 < k then Classical.choose (RegularizedLinearRoot.exists_root J g hk) else 0

noncomputable def margin (L₁ ρ : ℝ) : ℝ := 1 - ρ * L₁ / 2

noncomputable def innerCount (δ : ℝ) : ℕ := ⌈(4 / δ) * Real.log (1024 / δ ^ 2)⌉₊

noncomputable def picardPoint (F : E → E) (x : E) (η : ℝ) (K : ℕ) : E :=
  (fun y => x - η • F y)^[K] x

inductive State (E : Type*) where
  | anchor (x : E)
  | jacobian (x g : E)
  | picard (x y : E) (remaining : ℕ)
  | trial (x y : E) (η : ℝ)
  | done (y : E)

noncomputable def finish (δ ε : ℝ) (x y : E) (η : ℝ) (v : E) : State E :=
  if ‖v‖ ≤ ε then .done y else .anchor (x - (δ / 4 * η) • v)

noncomputable def hybrid (L₁ L₂ ρ ε : ℝ) (x0 : E) :
    Algorithm (E ⊕ E) (E × (E →L[ℝ] E)) E where
  State := State E
  initial := fun _ => .anchor x0
  query := fun st => (0, match st with
    | .anchor x => .inl x
    | .jacobian x _ => .inr x
    | .picard _ y _ => .inl y
    | .trial _ y _ => .inl y
    | .done y => .inl y)
  update := fun st reply =>
    let δ := margin L₁ ρ
    let η := (1 - δ / 4) / L₁
    match st with
    | .anchor x =>
      if ‖reply.1‖ ≤ ε then .done x
      else if ‖reply.1‖ ≤ δ ^ 2 * L₁ ^ 2 / (64 * L₂) then .jacobian x reply.1
      else .picard x (x - η • reply.1) (innerCount δ - 1)
    | .jacobian x g =>
      let s := modelStep reply.2 g (16 * L₂ / δ)
      .trial x (x + s) (1 / ((16 * L₂ / δ) * ‖s‖))
    | .picard x y n =>
      match n with
      | 0 => finish δ ε x y η reply.1
      | m + 1 => .picard x (x - η • reply.1) m
    | .trial x y η => finish δ ε x y η reply.1
    | .done y => .done y
  output := fun st => match st with
    | .anchor x => x
    | .jacobian x _ => x
    | .picard x _ _ => x
    | .trial x _ _ => x
    | .done y => y

end OracleTemplate.WeakMintyHybrid
