import LongTails.Setups.DistributedOptimumHeterogeneity

namespace LongTails.Algorithms.OptimumHeterogeneityDesign

open LongTails.Setups.DistributedOptimumHeterogeneity

def admissibleCurvatures (p : Params) : Set (Fin p.n → ℝ) :=
  {a | (∀ i, 0 ≤ a i ∧ a i ≤ p.L i) ∧ p.n * p.μ ≤ ∑ i, a i}

noncomputable def centeredEnergy (p : Params) (w : Fin p.n → ℝ) : ℝ :=
  ∑ i, (w i - (∑ j, w j) / p.n) ^ 2

noncomputable def designs (p : Params) : Set (Fin p.n → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ (∀ a ∈ admissibleCurvatures p, 1 ≤ ∑ i, w i * a i) ∧
    4096 * p.n * p.ζ ^ 2 * centeredEnergy p w ≤ p.ε ^ 2}

noncomputable def cost (p : Params) (w : Fin p.n → ℝ) : ℝ :=
  ∑ i, (p.h i : ℝ) * w i ^ 2

noncomputable def minimizer {α : Type*} [Nonempty α] (S : Set α) (c : α → ℝ) : α :=
  Classical.epsilon (fun x => x ∈ S ∧ IsMinOn c S x)

noncomputable def weights (p : Params) : Fin p.n → ℝ := minimizer (designs p) (cost p)

end LongTails.Algorithms.OptimumHeterogeneityDesign
