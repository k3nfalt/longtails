import LongTails.Algorithms.ClippedTwoPoint
import LongTails.Proofs.QueryLayers

namespace LongTails.Proofs.ClippedTwoPointLayers

open OracleTemplate LongTails.Algorithms.ClippedTwoPoint
open LongTails.Algorithms.QueryLayers LongTails.Proofs.QueryLayers

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma pair_fixed (d : ℕ) (τ γ : ℝ) (x u : E) :
    FixedQueries (pairPlan d τ γ x u) [x + γ • u, x - γ • u] :=
  .ask _ _ _ (fun _ => .ask _ _ _ (fun _ => .done _))

lemma batch_fixed (d : ℕ) (τ γ : ℝ) (x : E) {B : ℕ} (u : Fin B → E) :
    FixedQueries (batchPlan d τ γ x u)
      (List.ofFn (fun i : Fin B => [x + γ • u i, x - γ • u i])).flatten := by
  exact fixed_queries_map
    (fixed_queries_traverse B (fun i => pairPlan d τ γ x (u i))
      (fun i => [x + γ • u i, x - γ • u i]) (fun i => pair_fixed d τ γ x (u i))) _

lemma round_fixed (d : ℕ) (τ γ h : ℝ) (project : E → E) (t : ℕ)
    (state : E × E) {B : ℕ} (u : Fin B → E) :
    ∃ qs, FixedQueries (roundPlan d τ γ h project t state u) qs := by
  exact ⟨_, fixed_queries_map (batch_fixed d τ γ (acceleratedMix t state.1 state.2) u) _⟩

lemma dual_round_fixed (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (project : E → E) (t : ℕ)
    (states : (E × E) × (E × E)) {B : ℕ} (u v : Fin B → E) :
    ∃ qs, FixedQueries
      ((roundPlan d τ₁ γ₁ h project t states.1 u).bind
        (fun first => (roundPlan d τ₂ γ₂ h project t states.2 v).map
          (fun second => (first, second)))) qs := by
  obtain ⟨qs, hq⟩ := round_fixed d τ₁ γ₁ h project t states.1 u
  obtain ⟨rs, hr⟩ := round_fixed d τ₂ γ₂ h project t states.2 v
  exact ⟨qs ++ rs, fixed_queries_bind hq _ (fun _ => fixed_queries_map hr _)⟩

lemma dual_solver_layers (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h : ℝ) (project : E → E)
    (initial : E × E) (B : ℕ → ℕ) (u v : (t : ℕ) → Fin (B t) → E) (N : ℕ) :
    Layers (dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B u v N) N := by
  induction N with
  | zero => exact .done _
  | succ N ih =>
    change Layers ((dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B u v N).bind
      (fun states => (roundPlan d τ₁ γ₁ h project N states.1 (u N)).bind
        (fun first => (roundPlan d τ₂ γ₂ h project N states.2 (v N)).map
          (fun second => (first, second))))) (N + 1)
    apply Layers.bind _ _ ih
    intro states
    obtain ⟨qs, hq⟩ := dual_round_fixed d τ₁ τ₂ γ₁ γ₂ h project N states (u N) (v N)
    exact .fixed _ qs hq

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma comparison_fixed (s : ℝ) (a b : E) :
    FixedQueries (comparisonPairPlan s a b) [a, b] :=
  .ask _ _ _ (fun _ => .ask _ _ _ (fun _ => .done _))

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma selection_fixed (s : ℝ) (a b : E) (T : ℕ) :
    ∃ qs, FixedQueries (selectionPlan s a b T) qs := by
  exact ⟨_, fixed_queries_map
    (fixed_queries_traverse T (fun _ => comparisonPairPlan s a b)
      (fun _ => [a, b]) (fun _ => comparison_fixed s a b)) _⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma selection_padded_fixed (s : ℝ) (a b q0 : E) (T padding : ℕ) :
    ∃ qs, FixedQueries (paddedPlan q0 (selectionPlan s a b T) padding) qs := by
  obtain ⟨qs, hq⟩ := selection_fixed s a b T
  exact ⟨qs ++ List.replicate padding q0,
    fixed_queries_bind hq _ (fun value => padding_plan_fixed q0 value padding)⟩

lemma adaptive_padded_layers (d : ℕ) (τ₁ τ₂ γ₁ γ₂ h s : ℝ) (project : E → E)
    (initial : E × E) (B : ℕ → ℕ) (u v : (t : ℕ) → Fin (B t) → E) (N T padding : ℕ) :
    Layers (paddedPlan initial.1
      (adaptiveSelectionPlan d τ₁ τ₂ γ₁ γ₂ h s project initial B u v N T) padding) (N + 1) := by
  change Layers (((dualSolverPlan d τ₁ τ₂ γ₁ γ₂ h project initial B u v N).bind
    (fun states => selectionPlan s states.1.1 states.2.1 T)).bind
      (fun value => paddingPlan initial.1 value padding)) (N + 1)
  apply layers_of_heq (Nat.add_assoc padding (2 * T) (dualSolverCalls B N)).symm
    (bind_assoc_heq _ _ _)
  apply Layers.bind _ _ (dual_solver_layers d τ₁ τ₂ γ₁ γ₂ h project initial B u v N)
  intro states
  obtain ⟨qs, hq⟩ := selection_padded_fixed s states.1.1 states.2.1 initial.1 T padding
  exact .fixed _ qs hq

end LongTails.Proofs.ClippedTwoPointLayers
