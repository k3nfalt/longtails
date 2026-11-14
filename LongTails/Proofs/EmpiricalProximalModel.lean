import LongTails.Proofs.EmpiricalProximalStability
import LongTails.Proofs.AffineSoftmaxRegularization
import LongTails.Proofs.AcceleratedFiniteSum

open Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.EmpiricalProximalModel

open OracleTemplate
open OracleTemplate.ComponentEnvelope
open LongTails.Proofs.RecursiveEnvelopeGeometry
open LongTails.Setups.FiniteSumSmoothAndConvex
open EmpiricalProximalStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def batchPoint {n b : ℕ} (g : Fin n × E → E)
    (μ : ℝ) (c : E) (ξ : Fin b → Fin n) : E :=
  prox (FiniteSum.fullGradient (fun q => g (ξ q.1, q.2))) μ c

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma regularized_objective {n : ℕ} [NeZero n] (f : Fin n → E → ℝ)
    (μ : ℝ) (c x : E) :
    objective (fun i => regularized (f i) μ c) x = regularized (objective f) μ c x := by
  simp only [FiniteSum.objective_eq_expect, regularized, Finset.expect_add_distrib,
    Fintype.expect_const]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma batch_minimum {n b : ℕ} (f : Fin n → E → ℝ) (ξ : Fin b → Fin n)
    {u : E} (hu : ∀ i x, f i u ≤ f i x) (x : E) :
    objective (fun j => f (ξ j)) u ≤ objective (fun j => f (ξ j)) x := by
  simp only [FiniteSum.objective_eq_expect]
  exact Finset.expect_le_expect (s := Finset.univ) (fun j _ => hu (ξ j) x)

lemma batch_point_field [ProperSpace E] {n b : ℕ} {f : Fin n → E → ℝ}
    {g : Fin n × E → E} (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    {μ : ℝ} (hμ : 0 < μ) {u : E} (hu : ∀ i x, f i u ≤ f i x)
    (c : E) (ξ : Fin b → Fin n) :
    FiniteSum.fullGradient (fun q => g (ξ q.1, q.2)) (batchPoint g μ c ξ) =
      μ • (c - batchPoint g μ c ξ) :=
  component_prox_field (FiniteSum.objective_gradient (fun i x => hg (ξ i) x)) hμ
    (batch_minimum f ξ hu) c

lemma batch_point_minimum [ProperSpace E] {n b : ℕ} [NeZero b]
    {f : Fin n → E → ℝ} {g : Fin n × E → E}
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    {μ : ℝ} (hμ : 0 < μ) {u : E} (hu : ∀ i x, f i u ≤ f i x)
    (c : E) (ξ : Fin b → Fin n) (x : E) :
    objective (fun j => regularized (f (ξ j)) μ c) (batchPoint g μ c ξ) ≤
      objective (fun j => regularized (f (ξ j)) μ c) x := by
  rw [regularized_objective, regularized_objective]
  have hh := component_prox_minimum (FiniteSum.objective_convex (fun j => hc (ξ j)))
    (FiniteSum.objective_gradient (oracle := fun q => g (ξ q.1, q.2))
      (fun j x => hg (ξ j) x)) hμ
    (batch_minimum f ξ hu) c x
  change regularized (objective (fun j => f (ξ j))) μ c (batchPoint g μ c ξ) +
    μ / 2 * ‖x - batchPoint g μ c ξ‖ ^ 2 ≤ _ at hh
  have hn : 0 ≤ μ / 2 * ‖x - batchPoint g μ c ξ‖ ^ 2 := by positivity
  linarith

lemma batch_point_replacement [ProperSpace E] {n b : ℕ} [NeZero b]
    {f : Fin n → E → ℝ} {g : Fin n × E → E}
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x) {L μ : ℝ} (hμ : 0 < μ)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖)
    {u : E} (hu : ∀ i x, f i u ≤ f i x)
    (c : E) (ξ : Fin b → Fin n) (j : Fin b) (i : Fin n) :
    ((b : ℝ) * μ - (L + μ)) * ‖batchPoint g μ c (Function.update ξ j i) - batchPoint g μ c ξ‖ ≤
      ‖g (ξ j, batchPoint g μ c (Function.update ξ j i)) +
        μ • (batchPoint g μ c (Function.update ξ j i) - c)‖ +
      ‖g (i, batchPoint g μ c ξ) + μ • (batchPoint g μ c ξ - c)‖ := by
  have hr := replacement_distance hμ (show 0 < (b : ℝ) by exact_mod_cast NeZero.pos b)
    (FiniteSum.objective_convex (fun k => hc (ξ k)))
    (FiniteSum.objective_gradient (fun k x => hg (ξ k) x))
    (FiniteSum.objective_gradient (fun k x => hg (Function.update ξ j i k) x))
    (batch_minimum f ξ hu) (batch_minimum f (Function.update ξ j i) hu)
    (h := fun x => g (ξ j, x) + μ • (x - c))
    (h' := fun x => g (i, x) + μ • (x - c))
    (fun x => by simpa only [add_sub_add_right_eq_sub] using batch_gradient_replace g ξ j i x)
    (fun x y => AffineSoftmaxRegularization.regularized_field_lipschitz
      (fun x (_ : x ∈ (univ : Set E)) y _ => hlip i x y) hμ.le c (mem_univ x) (mem_univ y)) c
  simpa only [batchPoint, norm_sub_rev] using hr

lemma batch_generalization [ProperSpace E] {n b : ℕ} [NeZero n] [NeZero b]
    {f : Fin n → E → ℝ} {g : Fin n × E → E}
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x) {L μ ρ : ℝ}
    (hL : 0 < L) (hμ : 0 < μ) (hsize : 18 * (L + μ) ≤ (b : ℝ) * μ)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖)
    (hsg : ∀ x, (𝔼 i, ‖g (i, x)‖ ^ 2) ≤ ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    {u : E} (hu : ∀ i x, f i u ≤ f i x) (c : E) :
    (b : ℝ) * (𝔼 ξ : Fin b → Fin n,
      (objective f (batchPoint g μ c ξ) -
        objective (fun j => f (ξ j)) (batchPoint g μ c ξ))) ≤
      8 * ρ * μ * ‖c - prox (FiniteSum.fullGradient g) μ c‖ ^ 2 := by
  let y := prox (FiniteSum.fullGradient g) μ c
  let φ := fun i => regularized (f i) μ c
  let q := fun r : Fin n × E => g r + μ • (r.2 - c)
  have hφc : ∀ i, ConvexOn ℝ univ (φ i) := fun i =>
    AffineSoftmaxRegularization.regularized_convexOn (hc i) hμ.le c
  have hφg : ∀ i x, HasGradientAt (φ i) (q (i, x)) x := fun i x =>
    AffineSoftmaxRegularization.regularized_hasGradientAt (hg i x) μ c
  have hφl : ∀ i x z, ‖q (i, x) - q (i, z)‖ ≤ (L + μ) * ‖x - z‖ := by
    intro i x z
    exact AffineSoftmaxRegularization.regularized_field_lipschitz
      (fun x (_ : x ∈ (univ : Set E)) z _ => hlip i x z) hμ.le c (mem_univ x) (mem_univ z)
  have hym : IsMinOn (objective φ) univ y := by
    intro x _
    exact batch_point_minimum hc hg hμ hu c (fun i : Fin n => i) x
  have hmin (ξ : Fin b → Fin n) :
      (𝔼 j, φ (ξ j) (batchPoint g μ c ξ)) ≤ 𝔼 j, φ (ξ j) y := by
    simpa only [FiniteSum.objective_eq_expect] using batch_point_minimum hc hg hμ hu c ξ y
  have hr := relative_generalization_bound (show 0 < L + μ by positivity) hsize
    hφc hφg hφl hym (batchPoint g μ c) hmin
    (fun ξ j i => batch_point_replacement hc hg hμ hlip hu c ξ j i)
  have hfield : FiniteSum.fullGradient g y = μ • (c - y) := by
    exact batch_point_field hg hμ hu c (fun i : Fin n => i)
  have hq (i : Fin n) : q (i, y) = g (i, y) - FiniteSum.fullGradient g y := by
    dsimp [q]
    rw [hfield]
    module
  have hvar : (𝔼 i, ‖q (i, y)‖ ^ 2) ≤ ρ * μ ^ 2 * ‖c - y‖ ^ 2 := by
    simp_rw [hq]
    have hh := (FiniteSum.centered_second_moment (fun i => g (i, y))).trans (hsg y)
    change (𝔼 i, ‖g (i, y) - FiniteSum.fullGradient g y‖ ^ 2) ≤ _ at hh
    rw [hfield, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hh
    rw [hfield]
    simpa only [mul_assoc] using hh
  have hbound : (b : ℝ) * μ * (𝔼 ξ : Fin b → Fin n,
      (objective f (batchPoint g μ c ξ) -
        objective (fun j => f (ξ j)) (batchPoint g μ c ξ))) ≤
      8 * (𝔼 i, ‖q (i, y)‖ ^ 2) := by
    simpa only [φ, regularized_objective, regularized, Finset.expect_add_distrib,
      Fintype.expect_const, add_sub_add_right_eq_sub, FiniteSum.objective_eq_expect] using hr
  apply (mul_le_mul_iff_right₀ hμ).mp
  change _ ≤ μ * (8 * ρ * μ * ‖c - y‖ ^ 2)
  nlinarith only [hbound, hvar]

end LongTails.Proofs.EmpiricalProximalModel
