import LongTails.Proofs.StrongGrowthBatchProx
import LongTails.Proofs.CappedProximalSampling

open Set InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.EmpiricalProximalStability

open OracleTemplate
open OracleTemplate.ComponentEnvelope
open LongTails.Proofs.RecursiveEnvelopeGeometry
open LongTails.Setups.FiniteSumSmoothAndConvex

def replacementSwap {ι Ω : Type*} [DecidableEq ι] (j : ι) :
    ((ι → Ω) × Ω) ≃ ((ι → Ω) × Ω) where
  toFun p := (Function.update p.1 j p.2, p.1 j)
  invFun p := (Function.update p.1 j p.2, p.1 j)
  left_inv p := by simp
  right_inv p := by simp

lemma expect_replacement {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (j : ι) (H : (ι → Ω) → Ω → ℝ) :
    (𝔼 ξ, 𝔼 i, H (Function.update ξ j i) (ξ j)) = 𝔼 ξ, 𝔼 i, H ξ i := by
  rw [← Finset.expect_product', ← Finset.expect_product']
  exact Fintype.expect_equiv (replacementSwap j)
    (fun p => H (Function.update p.1 j p.2) (p.1 j)) (fun p => H p.1 p.2)
    (fun _ => rfl)

lemma generalization_identity {ι Ω E : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype Ω] [Nonempty Ω]
    (f : Ω → E → ℝ) (w : (ι → Ω) → E) :
    (𝔼 ξ, ((𝔼 i, f i (w ξ)) - (𝔼 j, f (ξ j) (w ξ)))) =
      𝔼 j, 𝔼 ξ, 𝔼 i, (f (ξ j) (w (Function.update ξ j i)) - f (ξ j) (w ξ)) := by
  simp only [Finset.expect_sub_distrib, Fintype.expect_const]
  have he (j : ι) := expect_replacement j (fun ξ i => f i (w ξ))
  simp_rw [he]
  rw [Fintype.expect_const, Finset.expect_comm (f := fun ξ j => f (ξ j) (w ξ))]

lemma empirical_excess_le_generalization {ι Ω E : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype Ω] [Nonempty Ω]
    (f : Ω → E → ℝ) (w : (ι → Ω) → E) (u : E)
    (hw : ∀ ξ, (𝔼 j, f (ξ j) (w ξ)) ≤ 𝔼 j, f (ξ j) u) :
    (𝔼 ξ, ((𝔼 i, f i (w ξ)) - (𝔼 i, f i u))) ≤
      𝔼 ξ, ((𝔼 i, f i (w ξ)) - (𝔼 j, f (ξ j) (w ξ))) := by
  have he := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ => hw ξ)
  rw [CappedProximalSampling.uniform_cohort_mean (fun i => f i u)] at he
  simp only [Finset.expect_sub_distrib, Fintype.expect_const]
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma generalization_le_fresh_moment {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [Fintype Ω] [Nonempty Ω]
    {f : Ω → E → ℝ} {g : Ω → E → E}
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g i x) x)
    (w : (ι → Ω) → E) {d : ℝ} (hd : 0 < d)
    (hr : ∀ ξ j i, d * ‖w (Function.update ξ j i) - w ξ‖ ≤
      ‖g (ξ j) (w (Function.update ξ j i))‖ + ‖g i (w ξ)‖) :
    d * (𝔼 ξ, ((𝔼 i, f i (w ξ)) - (𝔼 j, f (ξ j) (w ξ)))) ≤
      2 * (𝔼 ξ, 𝔼 i, ‖g i (w ξ)‖ ^ 2) := by
  have hp (ξ : ι → Ω) (j : ι) (i : Ω) :
      d * (f (ξ j) (w (Function.update ξ j i)) - f (ξ j) (w ξ)) ≤
        3 / 2 * ‖g (ξ j) (w (Function.update ξ j i))‖ ^ 2 +
          1 / 2 * ‖g i (w ξ)‖ ^ 2 := by
    set y := w ξ
    set z := w (Function.update ξ j i)
    have hs := Gradient.convex_support (hc (ξ j)) (hg (ξ j)) z y
    have he : y - z = -(z - y) := by abel
    rw [he, inner_neg_right] at hs
    have hi := real_inner_le_norm (g (ξ j) z) (z - y)
    have hv : f (ξ j) z - f (ξ j) y ≤ ‖g (ξ j) z‖ * ‖z - y‖ := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hv hd.le
    have hrep := mul_le_mul_of_nonneg_left (hr ξ j i) (norm_nonneg (g (ξ j) z))
    change d * (f (ξ j) z - f (ξ j) y) ≤ _
    change ‖g (ξ j) z‖ * (d * ‖z - y‖) ≤
      ‖g (ξ j) z‖ * (‖g (ξ j) z‖ + ‖g i y‖) at hrep
    nlinarith [sq_nonneg (‖g (ξ j) z‖ - ‖g i y‖)]
  have he := Finset.expect_le_expect (s := Finset.univ) (fun j _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun ξ _ =>
      Finset.expect_le_expect (s := Finset.univ) (fun i _ => hp ξ j i)))
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at he
  have hs (j : ι) := expect_replacement j (fun ξ i => ‖g i (w ξ)‖ ^ 2)
  simp_rw [hs, Fintype.expect_const] at he
  rw [generalization_identity f w]
  linarith

lemma gradient_second_moment {n : ℕ} {f : Fin n → E → ℝ}
    {g : Fin n × E → E} {L : ℝ} (hL : 0 < L)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖)
    {u : E} (hu : IsMinOn (objective f) univ u) (x : E) :
    (𝔼 i, ‖g (i, x)‖ ^ 2) ≤ 2 * (𝔼 i, ‖g (i, u)‖ ^ 2) +
      4 * L * (objective f x - objective f u) := by
  have hd := FiniteSum.component_second_moment hL hc hg hlip hu x
  have hp (i : Fin n) : ‖g (i, x)‖ ^ 2 ≤
      2 * ‖g (i, x) - g (i, u)‖ ^ 2 + 2 * ‖g (i, u)‖ ^ 2 := by
    have hn := norm_add_le (g (i, x) - g (i, u)) (g (i, u))
    rw [sub_add_cancel] at hn
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖g (i, x) - g (i, u)‖ - ‖g (i, u)‖)]
  have he := Finset.expect_le_expect (s := Finset.univ) (fun i _ => hp i)
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect] at he
  linarith

lemma fresh_moment_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]
    {f : Fin n → E → ℝ} {g : Fin n × E → E} {L : ℝ} (hL : 0 < L)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖)
    {u : E} (hu : IsMinOn (objective f) univ u) (w : (ι → Fin n) → E) :
    (𝔼 ξ, 𝔼 i, ‖g (i, w ξ)‖ ^ 2) ≤ 2 * (𝔼 i, ‖g (i, u)‖ ^ 2) +
      4 * L * (𝔼 ξ, (objective f (w ξ) - objective f u)) := by
  have he := Finset.expect_le_expect (s := Finset.univ) (fun ξ _ =>
    gradient_second_moment hL hc hg hlip hu (w ξ))
  simpa only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const] using he

lemma relative_generalization_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {n : ℕ} [NeZero n]
    {f : Fin n → E → ℝ} {g : Fin n × E → E} {L t : ℝ} (hL : 0 < L)
    (ht : 18 * L ≤ t)
    (hc : ∀ i, ConvexOn ℝ univ (f i))
    (hg : ∀ i x, HasGradientAt (f i) (g (i, x)) x)
    (hlip : ∀ i x y, ‖g (i, x) - g (i, y)‖ ≤ L * ‖x - y‖)
    {u : E} (hu : IsMinOn (objective f) univ u) (w : (ι → Fin n) → E)
    (hw : ∀ ξ, (𝔼 j, f (ξ j) (w ξ)) ≤ 𝔼 j, f (ξ j) u)
    (hr : ∀ ξ j i, (t - L) * ‖w (Function.update ξ j i) - w ξ‖ ≤
      ‖g (ξ j, w (Function.update ξ j i))‖ + ‖g (i, w ξ)‖) :
    t * (𝔼 ξ, (objective f (w ξ) - (𝔼 j, f (ξ j) (w ξ)))) ≤
      8 * (𝔼 i, ‖g (i, u)‖ ^ 2) := by
  let G := 𝔼 ξ, (objective f (w ξ) - (𝔼 j, f (ξ j) (w ξ)))
  let V := 𝔼 ξ, 𝔼 i, ‖g (i, w ξ)‖ ^ 2
  let S := 𝔼 i, ‖g (i, u)‖ ^ 2
  have hgen := generalization_le_fresh_moment hc (fun i x => hg i x) w
    (show 0 < t - L by linarith) hr
  have he := empirical_excess_le_generalization f w u hw
  have hgen' : (t - L) * G ≤ 2 * V := by
    simpa only [G, V, FiniteSum.objective_eq_expect] using hgen
  have he' : (𝔼 ξ, (objective f (w ξ) - objective f u)) ≤ G := by
    simpa only [G, FiniteSum.objective_eq_expect] using he
  have hm := fresh_moment_bound hL hc hg hlip hu w
  have hmoment : V ≤ 2 * S + 4 * L * G := by
    dsimp [V, S, G]
    linarith [mul_le_mul_of_nonneg_left he' (show 0 ≤ 4 * L by positivity)]
  have hex : 0 ≤ (𝔼 ξ, (objective f (w ξ) - objective f u)) :=
    Finset.expect_nonneg (fun ξ _ => sub_nonneg.mpr (hu (mem_univ _)))
  have hG : 0 ≤ G := le_trans hex he'
  have hs := mul_le_mul_of_nonneg_right ht hG
  change t * G ≤ 8 * S
  nlinarith only [hs, hgen', hmoment]

omit [CompleteSpace E] in
lemma batch_gradient_replace {n b : ℕ} (g : Fin n × E → E)
    (ξ : Fin b → Fin n) (j : Fin b) (i : Fin n) (x : E) :
    FiniteSum.fullGradient (fun q => g (ξ q.1, q.2)) x -
      FiniteSum.fullGradient (fun q => g (Function.update ξ j i q.1, q.2)) x =
        (b : ℝ)⁻¹ • (g (ξ j, x) - g (i, x)) := by
  simp only [FiniteSum.fullGradient, ← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Function.update_of_ne hk]
  · simp

lemma replacement_distance [ProperSpace E]
    {f f' : E → ℝ} {g g' h h' : E → E} {μ b L : ℝ}
    (hμ : 0 < μ) (hb : 0 < b) (hc : ConvexOn ℝ univ f)
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hg' : ∀ x, HasGradientAt f' (g' x) x)
    {u u' : E} (hmin : ∀ x, f u ≤ f x) (hmin' : ∀ x, f' u' ≤ f' x)
    (hdiff : ∀ x, g x - g' x = b⁻¹ • (h x - h' x))
    (hlip : ∀ x y, ‖h' x - h' y‖ ≤ L * ‖x - y‖) (c : E) :
    (b * μ - L) * ‖prox g μ c - prox g' μ c‖ ≤
      ‖h (prox g' μ c)‖ + ‖h' (prox g μ c)‖ := by
  have hp := StrongGrowthBatchProx.prox_perturbation hc hg hμ hmin c
    (prox g' μ c) (component_prox_field hg' hμ hmin' c)
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)] at hp
  have hscaled := mul_le_mul_of_nonneg_left hp hb.le
  simp only [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul] at hscaled
  have ht := norm_sub_le (h (prox g' μ c)) (h' (prox g' μ c))
  have hi := norm_sub_le_norm_sub_add_norm_sub
    (h' (prox g' μ c)) (h' (prox g μ c)) 0
  simp only [sub_zero] at hi
  have hl := hlip (prox g' μ c) (prox g μ c)
  rw [norm_sub_rev (prox g' μ c) (prox g μ c)] at hl
  nlinarith

lemma stability_absorption {G V S lam ell b : ℝ}
    (hlam : 0 ≤ lam) (hb : 0 < b)
    (hsize : 32 * lam * ell ≤ b)
    (hgen : G ≤ 4 * lam / b * V)
    (hmoment : V ≤ 2 * S + 4 * ell * G) (hG : 0 ≤ G) :
    G ≤ 16 * lam / b * S := by
  have hm := mul_le_mul_of_nonneg_left hmoment (show 0 ≤ 4 * lam by positivity)
  have hg := (le_div_iff₀ hb).mp (show G ≤ (4 * lam * V) / b by
    simpa only [div_mul_eq_mul_div] using hgen)
  have hs := mul_le_mul_of_nonneg_right hsize hG
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hb).mpr
  nlinarith only [hg, hs, hm]

end LongTails.Proofs.EmpiricalProximalStability
