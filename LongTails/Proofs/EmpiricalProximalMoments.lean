import LongTails.Proofs.EmpiricalProximalModel
import LongTails.Proofs.RecursiveGradientStep

open Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.EmpiricalProximalMoments

open OracleTemplate
open OracleTemplate.ComponentEnvelope
open LongTails.Proofs.RecursiveEnvelopeGeometry
open LongTails.Setups.FiniteSumSmoothAndConvex
open EmpiricalProximalModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma batch_raw_moment {n b : ℕ} [NeZero n] [NeZero b]
    (g : Fin n × E → E) (x : E) :
    (𝔼 ξ : Fin b → Fin n, ‖FiniteSum.fullGradient (fun q => g (ξ q.1, q.2)) x‖ ^ 2) ≤
      𝔼 i, ‖g (i, x)‖ ^ 2 := by
  have he := Finset.expect_le_expect (s := Finset.univ) (fun (ξ : Fin b → Fin n) _ =>
    NonconvexFiniteSum.norm_mean_sq_le (fun j : Fin b => g (ξ j, x)))
  rw [CappedProximalSampling.uniform_cohort_mean (fun i : Fin n => ‖g (i, x)‖ ^ 2)] at he
  exact he

omit [CompleteSpace E] in
lemma displacement_bound (v y z w h : E) (lam : ℝ) :
    ‖v - y‖ ^ 2 ≤ 4 * lam ^ 2 * ‖h‖ ^ 2 +
      4 * ‖lam • h + w - v‖ ^ 2 + 4 * ‖w - z‖ ^ 2 + 4 * ‖z - y‖ ^ 2 := by
  have h₁ := FiniteSum.norm_sub_sq_le (v - w) (y - w)
  have h₂ := FiniteSum.norm_sub_sq_le (lam • h) (lam • h + w - v)
  have h₃ := FiniteSum.norm_sub_sq_le (y - z) (w - z)
  rw [show (v - w) - (y - w) = v - y by abel] at h₁
  rw [show lam • h - (lam • h + w - v) = v - w by abel,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h₂
  rw [show (y - z) - (w - z) = y - w by abel, norm_sub_rev y z] at h₃
  nlinarith

omit [CompleteSpace E] in
lemma mean_displacement_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (v y : E) (z w h : Ω → E) (lam : ℝ) :
    ‖v - y‖ ^ 2 ≤ 4 * lam ^ 2 * (𝔼 ξ, ‖h ξ‖ ^ 2) +
      4 * (𝔼 ξ, ‖lam • h ξ + w ξ - v‖ ^ 2) +
      4 * (𝔼 ξ, ‖w ξ - z ξ‖ ^ 2) + 4 * (𝔼 ξ, ‖z ξ - y‖ ^ 2) := by
  have he := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ =>
    displacement_bound v y (z ξ) (w ξ) (h ξ) lam)
  simpa only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] using he

lemma displacement_absorption {D H R U V lam : ℝ}
    (hD : 0 ≤ D) (hbase : D ≤ 4 * lam ^ 2 * H + 4 * R + 4 * U + 4 * V)
    (hR : R ≤ D / 2 ^ 20) (hU : U ≤ D / 2 ^ 20) (hV : V ≤ D / 1024) :
    D ≤ 8 * lam ^ 2 * H := by
  nlinarith only [hD, hbase, hR, hU, hV]

lemma normalized_certificate {L μ D U V R G G₀ H : ℝ}
    (hL : 0 ≤ L) (hμ : 0 < μ) (hD : 0 ≤ D) (hU : 0 ≤ U) (hH : 0 ≤ H)
    (hgen : μ * G ≤ μ * G₀ + μ ^ 2 / 2 * V + (L + μ) ^ 2 * U)
    (hG₀ : G₀ ≤ μ * D / 64) (hV : V ≤ D / 1024)
    (hinner : (L + μ) ^ 2 * U ≤ μ ^ 2 * D / 2 ^ 20)
    (hres : μ ^ 2 * R ≤ (L + μ) ^ 2 * U)
    (hbase : D ≤ 4 * (μ⁻¹) ^ 2 * H + 4 * R + 4 * U + 4 * V) :
    G ≤ μ⁻¹ / 4 * H ∧ R ≤ (μ⁻¹) ^ 2 / 16 * H := by
  have hμsq : 0 < μ ^ 2 := sq_pos_of_pos hμ
  have hMG := mul_le_mul_of_nonneg_left hG₀ hμ.le
  have hMV := mul_le_mul_of_nonneg_left hV (show 0 ≤ μ ^ 2 / 2 by positivity)
  have hpos := mul_nonneg (sq_nonneg μ) hD
  have hGs : μ * G ≤ μ ^ 2 * D / 32 := by
    nlinarith only [hgen, hMG, hMV, hinner, hpos]
  have hG : G ≤ μ * D / 32 := by
    apply (mul_le_mul_iff_right₀ hμ).mp
    nlinarith only [hGs]
  have hR : R ≤ D / 2 ^ 20 := by
    apply (mul_le_mul_iff_right₀ hμsq).mp
    nlinarith only [hres, hinner]
  have hM : μ ^ 2 ≤ (L + μ) ^ 2 := by
    nlinarith [mul_nonneg hL hμ.le, sq_nonneg L]
  have hU' : U ≤ D / 2 ^ 20 := by
    apply (mul_le_mul_iff_right₀ hμsq).mp
    nlinarith only [mul_le_mul_of_nonneg_right hM hU, hinner]
  have hd := displacement_absorption hD hbase hR hU' hV
  constructor
  · have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ μ / 32 by positivity)
    have hid : μ / 32 * (8 * (μ⁻¹) ^ 2 * H) = μ⁻¹ / 4 * H := by
      field_simp
      ring
    rw [hid] at hh
    nlinarith only [hG, hh]
  · have hnon : 0 ≤ (μ⁻¹) ^ 2 * H := mul_nonneg (sq_nonneg _) hH
    nlinarith only [hR, hd, hnon]

lemma batch_point_variance [ProperSpace E] {n b : ℕ} [NeZero n] [NeZero b]
    {f : Fin n → E → ℝ} {g : Fin n × E → E}
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x) {μ ρ : ℝ} (hμ : 0 < μ)
    (hsg : ∀ x, (𝔼 i, ‖g (i, x)‖ ^ 2) ≤ ρ * ‖FiniteSum.fullGradient g x‖ ^ 2)
    {u : E} (hu : ∀ i x, f i u ≤ f i x) (c : E) :
    (b : ℝ) * (𝔼 ξ : Fin b → Fin n,
      ‖batchPoint g μ c ξ - prox (FiniteSum.fullGradient g) μ c‖ ^ 2) ≤
        ρ * ‖c - prox (FiniteSum.fullGradient g) μ c‖ ^ 2 := by
  let y := prox (FiniteSum.fullGradient g) μ c
  have hb : 0 < (b : ℝ) := by exact_mod_cast NeZero.pos b
  have hfield : FiniteSum.fullGradient g y = μ • (c - y) :=
    batch_point_field hg hμ hu c (fun i : Fin n => i)
  have hv := StrongGrowthBatchProx.batch_variance (fun i => g (i, y)) (NeZero.pos b) (hsg y)
  have hp := StrongGrowthBatchProx.mean_prox_perturbation
    (fun ξ : Fin b → Fin n => FiniteSum.objective_convex (fun j => hc (ξ j)))
    (fun ξ x => FiniteSum.objective_gradient (oracle := fun q => g (ξ q.1, q.2))
      (fun j x => hg (ξ j) x) x) hμ
    (fun ξ x => batch_minimum f ξ hu x) c y hfield hv
  change (𝔼 ξ : Fin b → Fin n, ‖batchPoint g μ c ξ - y‖ ^ 2) ≤
    (ρ * ‖FiniteSum.fullGradient g y‖ ^ 2 / b) / μ ^ 2 at hp
  rw [hfield, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hp
  have he : (ρ * (μ ^ 2 * ‖c - y‖ ^ 2) / b) / μ ^ 2 =
      ρ * ‖c - y‖ ^ 2 / b := by field_simp
  rw [he] at hp
  exact (mul_comm _ _).trans_le ((le_div_iff₀ hb).mp hp)

end LongTails.Proofs.EmpiricalProximalMoments
