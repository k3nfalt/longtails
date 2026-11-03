import LongTails.Proofs.StrongGrowthBatchProx
import LongTails.Proofs.NearZeroSumCalculus

open Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.StrongGrowthBatchProx

open OracleTemplate
open OracleTemplate.ComponentEnvelope
open LongTails.Proofs.RecursiveEnvelopeGeometry
open LongTails.Setups.FiniteSumSmoothAndConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma common_minima_of_strong_growth {n : ℕ} [NeZero n]
    {f : Fin n → E → ℝ} {g : Fin n × E → E} {ρ : ℝ}
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hsg : ∀ x, (n : ℝ)⁻¹ * ∑ i, ‖g (i, x)‖ ^ 2 ≤
      ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    {u : E} (hu : IsMinOn (objective f) univ u) :
    ∀ i, IsMinOn (f i) univ u := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast NeZero.pos n
  have hs := hsg u
  rw [FiniteSum.fullGradient_minimizer hg hu, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero] at hs
  have hz : (n : ℝ)⁻¹ * ∑ i, ‖g (i, u)‖ ^ 2 = 0 :=
    le_antisymm hs (mul_nonneg (inv_nonneg.mpr hn.le)
      (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hsum : ∑ i, ‖g (i, u)‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hz).resolve_left (inv_ne_zero hn.ne')
  intro i x _
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => sq_nonneg ‖g (j, u)‖)).mp hsum i (Finset.mem_univ i)
  have hgi : g (i, u) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  have hh := Gradient.convex_support (hc i) (hg i) u x
  rw [hgi, inner_zero_left] at hh
  exact sub_nonneg.mp hh

lemma population_prox_contraction [ProperSpace E] {f : E → ℝ} {g : E → E}
    (hg : ∀ x, HasGradientAt f (g x) x) {μ : ℝ} (hμ : 0 < μ)
    (hsc : StrongConvexOn univ μ f) {u : E} (hu : IsMinOn f univ u) (c : E) :
    ‖prox g μ c - u‖ ≤ ‖c - u‖ / 2 := by
  have hmin : ∀ x, f u ≤ f x := fun x => hu (mem_univ x)
  have hfield := component_prox_field hg hμ hmin c
  have hzero : g u = 0 := by
    apply (toDual ℝ E).injective
    simpa using (hu.isLocalMin (by simp)).hasFDerivAt_eq_zero (hg u).hasFDerivAt
  apply stationary_contraction hμ hzero hfield
  have hs (x y : E) := NearZeroSum.strong_support_within hsc (mem_univ x)
    (mem_univ y) (hasGradientWithinAt_univ.mpr (hg x))
  have h₁ := hs u (prox g μ c)
  have h₂ := hs (prox g μ c) u
  rw [norm_sub_rev u (prox g μ c),
    show u - prox g μ c = -(prox g μ c - u) by abel, inner_neg_right] at h₂
  rw [inner_sub_left]
  linarith

lemma regularized_initial_gap [ProperSpace E] {f : E → ℝ} {g : E → E}
    (hc : ConvexOn ℝ univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    {L μ : ℝ} (hL : 0 ≤ L) (hμ : 0 < μ)
    (hlip : ∀ x y, ‖g x - g y‖ ≤ L * ‖x - y‖)
    {u : E} (hu : ∀ x, f u ≤ f x) (c : E) :
    regularized f μ c c - envelope f g μ c ≤ (L + μ) / 2 * ‖c - u‖ ^ 2 := by
  have hs := Gradient.smooth_upper_bound hg hlip (prox g μ c) c
  rw [component_prox_field hg hμ hu c, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hs
  have hd := component_prox_distance hc hg hμ hu c
  have hd₂ := pow_le_pow_left₀ (norm_nonneg (c - prox g μ c)) hd 2
  have hm := mul_le_mul_of_nonneg_left hd₂
    (show 0 ≤ (L + μ) / 2 by positivity)
  simp only [regularized, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero, envelope] at *
  rw [norm_sub_rev (prox g μ c) c]
  linarith

end LongTails.Proofs.StrongGrowthBatchProx
