import LongTails.Algorithms.EmpiricalProximalAcceleration
import LongTails.Proofs.StrongGrowthBatchInner
import LongTails.Proofs.EmpiricalProximalModel
import LongTails.Proofs.EmpiricalProximalMoments
import LongTails.Proofs.EmpiricalProximalApproximation

open Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.EmpiricalProximalInner

open OracleTemplate
open LongTails.Setups.FiniteSumStrongGrowthConvex
open LongTails.Algorithms.EmpiricalProximalAcceleration

noncomputable def quadraticParams (p : Params) :
    LongTails.Setups.FiniteSumStrongGrowthStronglyConvex.Params where
  E := p.E
  n := p.n
  L := p.L
  μ := regularization p
  ρ := p.ρ
  R := p.R
  ε := p.ε
  x0 := p.x0

lemma regularization_pos (p : Params) (hL : 0 < p.L) : 0 < regularization p := by
  unfold regularization
  have hb : 0 < (batchSize p : ℝ) := by exact_mod_cast NeZero.pos (batchSize p)
  positivity

lemma quadratic_strong (p : Params) (c : p.E) :
    StrongConvexOn univ (regularization p) (fun x => regularization p / 2 * ‖x - c‖ ^ 2) :=
  StrongGrowthBatchProx.quadratic_strong (quadraticParams p) c

lemma quadratic_prox_minimum (p : Params) (hL : 0 < p.L)
    (c : p.E) {a : ℝ} (ha : 0 < a) (z v : p.E) :
    IsMinOn (Composite.proxObjective (fun x => regularization p / 2 * ‖x - c‖ ^ 2) a z v)
      univ (quadraticProx p c a z v) :=
  StrongGrowthBatchProx.quadratic_prox_minimum (quadraticParams p)
    (regularization_pos p hL) c ha z v

lemma inner_gap_bound (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ)
    (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ p.L * ‖x - y‖)
    (c : p.E) (ι : BatchIndices p) (u : p.E) {G : ℝ} (hG : 0 ≤ G)
    (hu : IsMinOn (fun x =>
      LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ι i)) x +
        regularization p / 2 * ‖x - c‖ ^ 2) univ u)
    (hgap : LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ι i)) c -
      (LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ι i)) u +
        regularization p / 2 * ‖u - c‖ ^ 2) ≤ G) :
    (𝔼 ξ : InnerSeeds p,
      ((LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ι i))
        (innerOutput p g c ι ξ) + regularization p / 2 * ‖innerOutput p g c ι ξ - c‖ ^ 2) -
        (LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ι i)) u +
          regularization p / 2 * ‖u - c‖ ^ 2))) ≤ (innerParams p c).ε * G := by
  let q := innerParams p c
  let q' : LongTails.Setups.CompositeFiniteSumStronglyConvex.Params := { q with Δ := G }
  have hμ := regularization_pos p hL
  have hr := Katyusha.run_rate q' hL hμ hG
    (fun i => f (ι i)) (fun x : p.E => regularization p / 2 * ‖x - c‖ ^ 2)
    (fun r => g (ι r.1, r.2)) (quadraticProx p c)
    (fun i => hc (ι i)) (fun i x => hg (ι i) x) (fun i x y => hlip (ι i) x y)
    (quadratic_strong p c) (fun a ha z v => quadratic_prox_minimum p hL c ha z v)
    u hu (by simpa only [q', q, innerParams, sub_self, norm_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using hgap) (innerEpochs p)
  let F := fun x => LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ι i)) x +
    regularization p / 2 * ‖x - c‖ ^ 2
  change Katyusha.theta q ^ (2 * batchSize p * innerEpochs p) *
    (𝔼 ξ : InnerSeeds p, (F (innerOutput p g c ι ξ) - F u)) ≤ 14 * G at hr
  have hε : 0 < q.ε := by dsimp [q, innerParams]; positivity
  have he : 14 * q.Δ / q.ε = 14 * (2 ^ 20 * p.ρ * (1 + p.L / regularization p) ^ 4) := by
    dsimp [q, innerParams]
    field_simp
  have hS : 12 * Katyusha.tuning q * Nat.clog 2 ⌈14 * q.Δ / q.ε⌉₊ = innerEpochs p := by
    rw [he]
    rfl
  have hb := Katyusha.katyusha_budget_accuracy q hL hμ hε
  dsimp only at hb
  rw [hS] at hb
  change 14 * 1 ≤ Katyusha.theta q ^ (2 * batchSize p * innerEpochs p) * q.ε at hb
  rw [mul_one] at hb
  have hm := mul_le_mul_of_nonneg_right hb hG
  have hθ : 0 < Katyusha.theta q := by
    have hα := (Katyusha.tuning_bounds q hL hμ).2.2.1
    unfold Katyusha.theta
    positivity
  apply (mul_le_mul_iff_right₀ (pow_pos hθ (2 * batchSize p * innerEpochs p))).mp
  change Katyusha.theta q ^ (2 * batchSize p * innerEpochs p) *
    (𝔼 ξ : InnerSeeds p, (F (innerOutput p g c ι ξ) - F u)) ≤ _
  nlinarith only [hr, hm]

lemma inner_distance_bound (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ)
    (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ p.L * ‖x - y‖)
    {u : p.E} (hu : ∀ i x, f i u ≤ f i x) (c : p.E) (ι : BatchIndices p) :
    (regularization p) ^ 2 * (𝔼 ξ : InnerSeeds p,
      ‖innerOutput p g c ι ξ - EmpiricalProximalModel.batchPoint g (regularization p) c ι‖ ^ 2) ≤
      (innerParams p c).ε * ‖FiniteSum.fullGradient (fun q => g (ι q.1, q.2)) c‖ ^ 2 := by
  let μ := regularization p
  let fb := LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ι i))
  let gb : p.E → p.E := FiniteSum.fullGradient (fun q => g (ι q.1, q.2))
  let y := EmpiricalProximalModel.batchPoint g μ c ι
  let G := ‖gb c‖ ^ 2 / (2 * μ)
  have hμ : 0 < μ := regularization_pos p hL
  have hfb : ConvexOn ℝ univ fb := FiniteSum.objective_convex (fun i => hc (ι i))
  have hgb : ∀ x, HasGradientAt fb (gb x) x :=
    FiniteSum.objective_gradient (fun i x => hg (ι i) x)
  have hym : IsMinOn (fun x => fb x + μ / 2 * ‖x - c‖ ^ 2) univ y := by
    intro x _
    have hh := EmpiricalProximalModel.batch_point_minimum hc hg hμ hu c ι x
    change fb y + μ / 2 * ‖y - c‖ ^ 2 ≤ fb x + μ / 2 * ‖x - c‖ ^ 2
    simpa only [fb, y, EmpiricalProximalModel.regularized_objective,
      RecursiveEnvelopeGeometry.regularized] using hh
  have hgap : fb c - (fb y + μ / 2 * ‖y - c‖ ^ 2) ≤ G := by
    apply (le_div_iff₀ (show 0 < 2 * μ by positivity)).mpr
    have hh := EmpiricalProximalApproximation.regularized_initial_gap hμ hfb hgb c y
    simpa only [RecursiveEnvelopeGeometry.regularized, mul_comm] using hh
  have hr := inner_gap_bound p hL hρ f g hc hg hlip c ι y
    (show 0 ≤ G by dsimp [G]; positivity) hym hgap
  have hs := Composite.strong_add_convex hfb (quadratic_strong p c)
  have hd := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ =>
    Composite.strong_minimum_bound hs hym (innerOutput p g c ι ξ))
  rw [← Finset.mul_expect] at hd
  have he : 2 * μ * G = ‖gb c‖ ^ 2 := by dsimp [G]; field_simp
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * μ by positivity)
  change μ ^ 2 * (𝔼 ξ : InnerSeeds p, ‖innerOutput p g c ι ξ - y‖ ^ 2) ≤
    (innerParams p c).ε * ‖gb c‖ ^ 2
  have hm' := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * μ by positivity)
  have he' := congrArg (fun t : ℝ => (innerParams p c).ε * t) he
  dsimp only [fb, μ] at hm hm' he' ⊢
  nlinarith only [hm, hm', he']

lemma inner_population_distance {B : Type*} [Fintype B]
    (p : Params) (hL : 0 < p.L) (hρ : 0 < p.ρ)
    (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ p.L * ‖x - y‖)
    {u : p.E} (hu : ∀ i x, f i u ≤ f i x) (c : p.E) (ι : B → BatchIndices p)
    (hsampling : (𝔼 β, ‖FiniteSum.fullGradient (fun q => g (ι β q.1, q.2)) c‖ ^ 2) ≤
      p.ρ * ‖FiniteSum.fullGradient g c‖ ^ 2) :
    (p.L + regularization p) ^ 2 * (𝔼 β, 𝔼 ξ : InnerSeeds p,
      ‖innerOutput p g c (ι β) ξ - EmpiricalProximalModel.batchPoint g (regularization p) c (ι β)‖ ^ 2) ≤
      (regularization p) ^ 2 * ‖c - RecursiveEnvelopeGeometry.prox (FiniteSum.fullGradient g)
        (regularization p) c‖ ^ 2 / 2 ^ 20 := by
  let μ := regularization p
  let y := RecursiveEnvelopeGeometry.prox (FiniteSum.fullGradient g) μ c
  let M := p.L + μ
  let U := 𝔼 β, 𝔼 ξ : InnerSeeds p,
    ‖innerOutput p g c (ι β) ξ - EmpiricalProximalModel.batchPoint g μ c (ι β)‖ ^ 2
  have hμ : 0 < μ := regularization_pos p hL
  have hM : 0 < M := by dsimp [M]; positivity
  have he := Finset.expect_le_expect (s := Finset.univ) (fun β _ =>
    inner_distance_bound p hL hρ f g hc hg hlip hu c (ι β))
  simp only [← Finset.mul_expect] at he
  have hε : 0 < (innerParams p c).ε := by dsimp [innerParams]; positivity
  have hb := mul_le_mul_of_nonneg_left hsampling hε.le
  have hfield : FiniteSum.fullGradient g y = μ • (c - y) :=
    EmpiricalProximalModel.batch_point_field hg hμ hu c (fun i : Fin p.n => i)
  have hcenter := EmpiricalProximalApproximation.gradient_at_center hμ.le
    (FiniteSum.fullGradient_lipschitz hlip) hfield
  have hcenter2 := pow_le_pow_left₀ (norm_nonneg _) hcenter 2
  rw [mul_pow] at hcenter2
  have hc' := mul_le_mul_of_nonneg_left hcenter2 (mul_nonneg hε.le hρ.le)
  have hbound : μ ^ 2 * U ≤ (innerParams p c).ε * p.ρ * M ^ 2 * ‖c - y‖ ^ 2 := by
    dsimp only [U, M, μ]
    nlinarith only [he, hb, hc']
  have hid : (innerParams p c).ε * p.ρ * M ^ 4 = μ ^ 4 / 2 ^ 20 := by
    have hk : 1 + p.L / μ = M / μ := by
      dsimp [M]
      field_simp
      ring
    change (1 / (2 ^ 20 * p.ρ * (1 + p.L / μ) ^ 4)) * p.ρ * M ^ 4 = _
    rw [hk]
    field_simp [hμ.ne', hρ.ne', hM.ne']
  have hh := mul_le_mul_of_nonneg_left hbound (sq_nonneg M)
  have heq : M ^ 2 * ((innerParams p c).ε * p.ρ * M ^ 2 * ‖c - y‖ ^ 2) =
      (μ ^ 4 / 2 ^ 20) * ‖c - y‖ ^ 2 := by
    rw [← hid]
    ring
  rw [heq] at hh
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hμ)).mp
  change μ ^ 2 * (M ^ 2 * U) ≤ μ ^ 2 * (μ ^ 2 * ‖c - y‖ ^ 2 / 2 ^ 20)
  nlinarith only [hh]

end LongTails.Proofs.EmpiricalProximalInner
