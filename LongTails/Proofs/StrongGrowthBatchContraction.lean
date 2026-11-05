import LongTails.Proofs.StrongGrowthBatchInner
import LongTails.Proofs.StrongGrowthBatchBudget

open Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.StrongGrowthBatchProx

open OracleTemplate
open OracleTemplate.ComponentEnvelope
open LongTails.Proofs.RecursiveEnvelopeGeometry
open LongTails.Setups.FiniteSumStrongGrowthStronglyConvex
open LongTails.Algorithms.StrongGrowthBatchProx

lemma sampled_prox_variance (p : Params) (hμ : 0 < p.μ) (hρ : 0 ≤ p.ρ)
    (m : ℕ) [NeZero m] (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hsg : ∀ x, (p.n : ℝ)⁻¹ * ∑ i, ‖g (i, x)‖ ^ 2 ≤
      p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    {u : p.E} (hu : ∀ i x, f i u ≤ f i x) (c : p.E) :
    (𝔼 ξ : Fin m → Fin p.n,
      ‖prox (FiniteSum.fullGradient (fun q => g (ξ q.1, q.2))) p.μ c -
        prox (FiniteSum.fullGradient g) p.μ c‖ ^ 2) ≤
      p.ρ * ‖c - u‖ ^ 2 / m := by
  let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let G := FiniteSum.fullGradient g
  let y := prox G p.μ c
  let FB := fun ξ : Fin m → Fin p.n =>
    LongTails.Setups.FiniteSumSmoothAndConvex.objective (fun i => f (ξ i))
  let GB := fun ξ : Fin m → Fin p.n =>
    FiniteSum.fullGradient (fun q => g (ξ q.1, q.2))
  have hF : ConvexOn ℝ univ F := FiniteSum.objective_convex hc
  have hG : ∀ x, HasGradientAt F (G x) x := FiniteSum.objective_gradient hg
  have hmin (x : p.E) : F u ≤ F x := by
    simp only [F, FiniteSum.objective_eq_expect]
    exact Finset.expect_le_expect (s := Finset.univ) (fun i _ => hu i x)
  have hCB (ξ : Fin m → Fin p.n) : ConvexOn ℝ univ (FB ξ) :=
    FiniteSum.objective_convex (fun i => hc (ξ i))
  have hGB (ξ : Fin m → Fin p.n) (x : p.E) : HasGradientAt (FB ξ) (GB ξ x) x :=
    FiniteSum.objective_gradient (fun i z => hg (ξ i) z) x
  have hminB (ξ : Fin m → Fin p.n) (x : p.E) : FB ξ u ≤ FB ξ x := by
    simp only [FB, FiniteSum.objective_eq_expect]
    exact Finset.expect_le_expect (s := Finset.univ) (fun i _ => hu (ξ i) x)
  have hsgy : (𝔼 i, ‖g (i, y)‖ ^ 2) ≤ p.ρ * ‖G y‖ ^ 2 := by
    simpa only [Fintype.expect_eq_sum_div_card, Fintype.card_fin,
      div_eq_mul_inv, mul_comm] using hsg y
  have hv := batch_variance (fun i => g (i, y)) (NeZero.pos m) hsgy
  change (𝔼 ξ : Fin m → Fin p.n, ‖GB ξ y - G y‖ ^ 2) ≤
    (p.ρ * ‖G y‖ ^ 2) / m at hv
  have hfield : G y = p.μ • (c - y) := component_prox_field hG hμ hmin c
  have hp := mean_prox_perturbation hCB hGB hμ hminB c y hfield hv
  rw [hfield, norm_smul, Real.norm_eq_abs, abs_of_pos hμ, mul_pow] at hp
  have he : (p.ρ * (p.μ ^ 2 * ‖c - y‖ ^ 2) / (m : ℝ)) / p.μ ^ 2 =
      p.ρ * ‖c - y‖ ^ 2 / m := by
    have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
    field_simp [hμ.ne', hm]
  rw [he] at hp
  have hd := component_prox_distance hF hG hμ hmin c
  have hd₂ := pow_le_pow_left₀ (norm_nonneg (c - y)) hd 2
  apply hp.trans
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd₂ hρ) (Nat.cast_nonneg m)

lemma capped_field (p : Params) (g : Fin p.n × p.E → p.E)
    (hcap : batchSize p = p.n) (ξ : BatchIndices p) :
    FiniteSum.fullGradient (fun q => g (indices p ξ q.1, q.2)) =
      FiniteSum.fullGradient g := by
  have hi : indices p ξ = (fun i => Fin.cast hcap i) := by
    simp only [indices, dite_eq_left hcap]
  rw [hi]
  funext x
  have hs : (∑ i : Fin (batchSize p), g (Fin.cast hcap i, x)) =
      ∑ i : Fin p.n, g (i, x) :=
    Fintype.sum_equiv (finCongr hcap) _ _ (fun _ => rfl)
  simp only [FiniteSum.fullGradient, hs, hcap]

lemma selected_prox_variance (p : Params) (hμ : 0 < p.μ) (hρ : 1 ≤ p.ρ)
    (f : Fin p.n → p.E → ℝ) (g : Fin p.n × p.E → p.E)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hsg : ∀ x, (p.n : ℝ)⁻¹ * ∑ i, ‖g (i, x)‖ ^ 2 ≤
      p.ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    {u : p.E} (hu : ∀ i x, f i u ≤ f i x) (c : p.E) :
    (𝔼 ξ : BatchIndices p,
      ‖prox (FiniteSum.fullGradient (fun q => g (indices p ξ q.1, q.2))) p.μ c -
        prox (FiniteSum.fullGradient g) p.μ c‖ ^ 2) ≤ ‖c - u‖ ^ 2 / 128 := by
  by_cases hcap : batchSize p = p.n
  · simp only [capped_field p g hcap, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Fintype.expect_const]
    positivity
  · have hv := sampled_prox_variance p hμ (by linarith : 0 ≤ p.ρ)
      (batchSize p) f g hc hg hsg hu c
    simp only [indices, dite_eq_right hcap]
    apply hv.trans
    have hb := uncapped_batch_lower p hρ hcap
    have hm : 0 < (batchSize p : ℝ) := by exact_mod_cast NeZero.pos (batchSize p)
    apply (div_le_iff₀ hm).mpr
    nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg ‖c - u‖)]

end LongTails.Proofs.StrongGrowthBatchProx
