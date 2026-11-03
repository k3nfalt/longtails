import LongTails.Proofs.StrongGrowthBatchModel
import LongTails.Algorithms.StrongGrowthBatchProx
import LongTails.Proofs.KatyushaConvergence
import LongTails.Proofs.KatyushaAccuracy

open Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

set_option backward.isDefEq.respectTransparency false

namespace LongTails.Proofs.StrongGrowthBatchProx

open OracleTemplate
open LongTails.Setups.FiniteSumStrongGrowthStronglyConvex
open LongTails.Algorithms.StrongGrowthBatchProx
open LongTails.Proofs.RecursiveEnvelopeGeometry

lemma quadratic_strong (p : Params) (c : p.E) :
    StrongConvexOn univ p.μ (fun x => p.μ / 2 * ‖x - c‖ ^ 2) := by
  have hzero : StrongConvexOn (univ : Set p.E) 0 (fun _ => (0 : ℝ)) :=
    strongConvexOn_zero.mpr (convexOn_const (0 : ℝ) convex_univ)
  simpa only [zero_add, add_zero] using
    NearZeroSum.strong_convex_add_quadratic (β := p.μ) (k := 0) hzero c

lemma quadratic_prox_equation (p : Params) (hμ : 0 < p.μ)
    (c : p.E) {a : ℝ} (ha : 0 < a) (z v : p.E) :
    (1 / a) • (quadraticProx p c a z v - z) + v +
      p.μ • (quadraticProx p c a z v - c) = 0 := by
  have hd : 1 + a * p.μ ≠ 0 := by positivity
  have hq : (1 + a * p.μ) • quadraticProx p c a z v =
      z - a • v + (a * p.μ) • c := by
    simp only [quadraticProx, smul_smul, mul_inv_cancel₀ hd, one_smul]
  have he : a • ((1 / a) • (quadraticProx p c a z v - z) + v +
      p.μ • (quadraticProx p c a z v - c)) =
      (1 + a * p.μ) • quadraticProx p c a z v - (z - a • v + (a * p.μ) • c) := by
    rw [smul_add, smul_add, smul_smul, mul_one_div_cancel ha.ne', one_smul]
    module
  rw [hq, sub_self] at he
  exact (smul_eq_zero.mp he).resolve_left ha.ne'

lemma quadratic_prox_minimum (p : Params) (hμ : 0 < p.μ)
    (c : p.E) {a : ℝ} (ha : 0 < a) (z v : p.E) :
    IsMinOn (Composite.proxObjective (fun x => p.μ / 2 * ‖x - c‖ ^ 2) a z v)
      univ (quadraticProx p c a z v) := by
  let F := Composite.proxObjective (fun x => p.μ / 2 * ‖x - c‖ ^ 2) a z v
  have hgrad (x : p.E) : HasGradientAt F
      ((1 / a) • (x - z) + v + p.μ • (x - c)) x := by
    have h₁ := hasGradientWithinAt_univ.mp
      (NearZeroSum.gradient_translated_quadratic (1 / a) z x univ)
    have h₂ : HasGradientAt (fun w : p.E => ⟪v, w - z⟫) v x := by
      change HasFDerivAt _ ((toDual ℝ p.E) v) x
      convert ((toDual ℝ p.E) v).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const z) using 1 <;>
        simp [Function.comp_def, toDual_apply_apply]
    have h₃ := hasGradientWithinAt_univ.mp
      (NearZeroSum.gradient_translated_quadratic p.μ c x univ)
    have hh := NearZeroSum.gradient_add_within
      (NearZeroSum.gradient_add_within (hasGradientWithinAt_univ.mpr h₁)
        (hasGradientWithinAt_univ.mpr h₂)) (hasGradientWithinAt_univ.mpr h₃)
    have he : F = (fun w => (1 / a / 2 * ‖w - z‖ ^ 2 + ⟪v, w - z⟫) +
        p.μ / 2 * ‖w - c‖ ^ 2) := by
      funext w
      dsimp [F, Composite.proxObjective]
      ring
    rw [he]
    exact hasGradientWithinAt_univ.mp hh
  have hc : ConvexOn ℝ univ F := strongConvexOn_zero.mp
    ((Composite.prox_strong (quadratic_strong p c) z v).mono (by positivity))
  intro x _
  have hh := Gradient.convex_support hc hgrad (quadraticProx p c a z v) x
  rw [quadratic_prox_equation p hμ c ha z v, inner_zero_left] at hh
  exact sub_nonneg.mp hh

lemma inner_gap_bound (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ p.L * ‖x - y‖)
    (c : p.E) (ι : BatchIndices p) (u : p.E) {D : ℝ} (hD : 0 ≤ D)
    (hu : IsMinOn
      (fun x => LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ι i)) x +
        p.μ / 2 * ‖x - c‖ ^ 2) univ u)
    (hgap : LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ι i)) c -
      (LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ι i)) u +
        p.μ / 2 * ‖u - c‖ ^ 2) ≤ (p.L + p.μ) / 2 * D) :
    (𝔼 ξ : InnerSeeds p,
      ((LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ι i))
          (innerOutput p g c ι ξ) + p.μ / 2 * ‖innerOutput p g c ι ξ - c‖ ^ 2) -
        (LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ι i)) u +
          p.μ / 2 * ‖u - c‖ ^ 2))) ≤ p.μ / 1024 * D := by
  let q := innerParams p c
  let q' : LongTails.Setups.CompositeFiniteSumStronglyConvex.Params :=
    { q with Δ := (p.L + p.μ) / 2 * D }
  have hr := Katyusha.run_rate q' hL hμ (by dsimp [q']; positivity)
    (fun i => f (ι i)) (fun x : p.E => p.μ / 2 * ‖x - c‖ ^ 2)
    (fun r => g (ι r.1, r.2)) (quadraticProx p c)
    (fun i => hc (ι i)) (fun i x => hg (ι i) x) (fun i x y => hlip (ι i) x y)
    (quadratic_strong p c) (fun a ha z v => quadratic_prox_minimum p hμ c ha z v)
    u hu (by simpa only [q', q, innerParams, sub_self, norm_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using hgap) (innerEpochs p)
  let F := fun x => LongTails.Setups.FiniteSumSmoothAndConvex.objective
    (fun i => f (ι i)) x + p.μ / 2 * ‖x - c‖ ^ 2
  have hr' : Katyusha.theta q ^ (2 * batchSize p * innerEpochs p) *
    (𝔼 ξ : InnerSeeds p, (F (innerOutput p g c ι ξ) - F u)) ≤
      14 * ((p.L + p.μ) / 2 * D) := by
    simpa only [q', q, innerParams, innerOutput, Katyusha.theta, Katyusha.alpha,
      Katyusha.tau, Katyusha.tuning, F] using hr
  have he : 14 * q.Δ / q.ε = 7168 * (p.L + p.μ) / p.μ := by
    dsimp [q, innerParams]
    field_simp
    ring
  have hS : 12 * Katyusha.tuning q * Nat.clog 2 ⌈14 * q.Δ / q.ε⌉₊ =
      innerEpochs p := by rw [he]; rfl
  have hb := Katyusha.katyusha_budget_accuracy q hL hμ (by dsimp [q, innerParams]; positivity)
  dsimp only at hb
  rw [hS] at hb
  have hm := mul_le_mul_of_nonneg_right hb hD
  have hα := (Katyusha.tuning_bounds q hL hμ).2.2.1
  have hθ : 0 < Katyusha.theta q := by unfold Katyusha.theta; positivity
  apply (mul_le_mul_iff_right₀ (pow_pos hθ (2 * batchSize p * innerEpochs p))).mp
  change Katyusha.theta q ^ (2 * batchSize p * innerEpochs p) *
    (𝔼 ξ : InnerSeeds p, (F (innerOutput p g c ι ξ) - F u)) ≤ _
  change 14 * ((p.L + p.μ) / 2) * D ≤
    Katyusha.theta q ^ (2 * batchSize p * innerEpochs p) * (p.μ / 1024) * D at hm
  nlinarith only [hr', hm]

lemma inner_distance_bound (p : Params) (hL : 0 < p.L) (hμ : 0 < p.μ)
    (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ p.L * ‖x - y‖)
    {u : p.E} (hu : ∀ i x, f i u ≤ f i x) (c : p.E) (ι : BatchIndices p) :
    (𝔼 ξ : InnerSeeds p, ‖innerOutput p g c ι ξ -
      prox (FiniteSum.fullGradient (fun q => g (ι q.1, q.2))) p.μ c‖ ^ 2) ≤
      ‖c - u‖ ^ 2 / 512 := by
  let fb := LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ι i))
  let gb : p.E → p.E := FiniteSum.fullGradient (fun q => g (ι q.1, q.2))
  let y := prox gb p.μ c
  have hcb : ConvexOn ℝ univ fb := FiniteSum.objective_convex (fun i => hc (ι i))
  have hgb : ∀ x, HasGradientAt fb (gb x) x :=
    FiniteSum.objective_gradient (fun i x => hg (ι i) x)
  have hlb : ∀ x z, ‖gb x - gb z‖ ≤ p.L * ‖x - z‖ :=
    FiniteSum.fullGradient_lipschitz (fun i x z => hlip (ι i) x z)
  have hminb (x : p.E) : fb u ≤ fb x := by
    simp only [fb, FiniteSum.objective_eq_expect]
    exact Finset.expect_le_expect (s := Finset.univ) (fun i _ => hu (ι i) x)
  have hym : IsMinOn (fun x => fb x + p.μ / 2 * ‖x - c‖ ^ 2) univ y := by
    intro x _
    have hh := ComponentEnvelope.component_prox_minimum hcb hgb hμ hminb c x
    have hn : 0 ≤ p.μ / 2 * ‖x - y‖ ^ 2 := by positivity
    change (fb y + p.μ / 2 * ‖y - c‖ ^ 2) + p.μ / 2 * ‖x - y‖ ^ 2 ≤
      fb x + p.μ / 2 * ‖x - c‖ ^ 2 at hh
    change fb y + p.μ / 2 * ‖y - c‖ ^ 2 ≤ fb x + p.μ / 2 * ‖x - c‖ ^ 2
    linarith
  have hi := regularized_initial_gap hcb hgb hL.le hμ hlb hminb c
  have hgap : fb c - (fb y + p.μ / 2 * ‖y - c‖ ^ 2) ≤
      (p.L + p.μ) / 2 * ‖c - u‖ ^ 2 := by
    simpa only [regularized, envelope,
      sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, y] using hi
  have hr := inner_gap_bound p hL hμ f g hc hg hlip c ι y (sq_nonneg ‖c - u‖) hym hgap
  have hsc := Composite.strong_add_convex hcb (quadratic_strong p c)
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ =>
    Composite.strong_minimum_bound hsc hym (innerOutput p g c ι ξ))
  rw [← Finset.mul_expect] at hh
  apply (mul_le_mul_iff_right₀ hμ).mp
  change p.μ * (𝔼 ξ : InnerSeeds p, ‖innerOutput p g c ι ξ - y‖ ^ 2) ≤ _
  change (𝔼 ξ : InnerSeeds p, ((fb (innerOutput p g c ι ξ) +
    p.μ / 2 * ‖innerOutput p g c ι ξ - c‖ ^ 2) -
      (fb y + p.μ / 2 * ‖y - c‖ ^ 2))) ≤ _ at hr
  nlinarith only [hh, hr]

end LongTails.Proofs.StrongGrowthBatchProx
